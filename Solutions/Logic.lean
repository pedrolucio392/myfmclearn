section propositional

variable (P Q R : Prop)


------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro :
  P → ¬ ¬ P  := by
  intro hp
  intro hnp
  have hf : False := hnp hp
  exact hf

theorem doubleneg_elim :
  ¬ ¬ P → P  := by
  intro hp
  by_cases hf : P
  · exact hf
  · have hnf : False := hp hf
    contradiction

theorem doubleneg_law :
  ¬ ¬ P ↔ P  := by
  constructor
  · intro hp
    by_cases h : P
    · exact h
    · have hn : False := hp h
      contradiction
  · intro hp
    intro hpn
    have hf : False := hpn hp
    exact hf


------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  := by
  intro h
  rcases h with hp | hq
  · right
    exact hp
  · left
    exact hq


theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  intro h
  rcases h with ⟨hp, hq⟩
  constructor
  · exact hq
  · exact hp


------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

theorem impl_as_disj_converse :
  (¬ P ∨ Q) → (P → Q)  := by
  intros h1 h2
  rcases h1 with hpq | hp
  · have hf : False := hpq h2
    contradiction
  · exact hp


theorem disj_as_impl :
  (P ∨ Q) → (¬ P → Q)  := by
  intro h1 h2
  rcases h1 with hp | hq
  · have hf : False := h2 hp
    contradiction
  · exact hq


------------------------------------------------
-- Contrapositive
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬ Q → ¬ P)  := by
  intro h1 h2 h3
  have hq : Q := h1 h3
  exact h2 hq


theorem impl_as_contrapositive_converse :
  (¬ Q → ¬ P) → (P → Q)  := by
  intro h1 h2
  by_cases hq : Q
  · exact hq
  · have hnp : ¬P := h1 hq
    have hf : False := hnp h2
    contradiction


theorem contrapositive_law :
  (P → Q) ↔ (¬ Q → ¬ P)  := by
  constructor
  · intro h1 h2 h3
    have hq : Q := h1 h3
    have hf : False := h2 hq
    contradiction
  · intro h1 h2
    by_cases hq : Q
    · exact hq
    · have hnp : ¬P := h1 hq
      have hf : False := hnp h2
      contradiction


------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------

theorem lem_irrefutable :
  ¬ ¬ (P ∨ ¬ P)  := by
  intro h1
  have hp : (P ∨ ¬ P) := by
    right
    intro hnp
    have hpp : (P ∨ ¬ P) := by
      left
      exact hnp
    exact h1 hpp
  exact h1 hp



------------------------------------------------
-- Peirce's law
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬ ¬ P  := by
  intro h1 h2
  have hpq : P → Q := by
    intro hp
    have hf : False := h2 hp
    contradiction
  have hp : P := h1 hpq
  exact h2 hp


------------------------------------------------
-- Linearity of →
------------------------------------------------

theorem impl_linear :
  (P → Q) ∨ (Q → P)  := by
  by_cases lemP : P
  · right
    intro (q : Q)
    assumption
  · left
    intro (p : P)
    have hf : False := lemP p
    contradiction

------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

theorem disj_as_negconj :
  P ∨ Q → ¬ (¬ P ∧ ¬ Q)  := by
  intros h1 h2
  rcases h2 with ⟨hnp, hnq ⟩
  rcases h1 with hp | hq
  · exact hnp hp
  · exact hnq hq

theorem conj_as_negdisj :
  P ∧ Q → ¬ (¬ P ∨ ¬ Q)  := by
  intros h1 h2
  rcases h1 with ⟨hp, hq⟩
  rcases h2 with hnp | hnq
  · exact hnp hp
  · exact hnq hq


------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

theorem demorgan_disj :
  ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)  := by
  intro h1
  sorry

theorem demorgan_disj_converse :
  (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)  := by
  sorry

theorem demorgan_conj :
  ¬ (P ∧ Q) → (¬ Q ∨ ¬ P)  := by
  sorry

theorem demorgan_conj_converse :
  (¬ Q ∨ ¬ P) → ¬ (P ∧ Q)  := by
  sorry

theorem demorgan_conj_law :
  ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P)  := by
  sorry

theorem demorgan_disj_law :
  ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by
  sorry


------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by
  sorry

theorem distr_conj_disj_converse :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by
  sorry

theorem distr_disj_conj :
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by
  sorry

theorem distr_disj_conj_converse :
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by
  sorry


------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :
  ((P ∧ Q) → R) → (P → (Q → R))  := by
  sorry

theorem uncurry_prop :
  (P → (Q → R)) → ((P ∧ Q) → R)  := by
  sorry


------------------------------------------------
-- Reflexivity of →
------------------------------------------------

theorem impl_refl :
  P → P  := by
  sorry


------------------------------------------------
-- Weakening and contraction
------------------------------------------------

theorem weaken_disj_right :
  P → (P ∨ Q)  := by
  sorry

theorem weaken_disj_left :
  Q → (P ∨ Q)  := by
  sorry

theorem weaken_conj_right :
  (P ∧ Q) → P  := by
  sorry

theorem weaken_conj_left :
  (P ∧ Q) → Q  := by
  sorry


------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :
  (P ∨ P) ↔ P  := by
  sorry

theorem conj_idem :
  (P ∧ P) ↔ P := by
  sorry


------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :
  False → P := by
  sorry

theorem true_top :
  P → True  := by
  sorry


end propositional

----------------------------------------------------------------

section predicate

variable (U : Type)
variable (P Q : U → Type)


------------------------------------------------
-- De Morgan laws for ∃,∀
------------------------------------------------

theorem demorgan_exists :
  ¬ (∃ x, P x) → (∀ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_converse :
  (∀ x, ¬ P x) → ¬ (∃ x, P x)  := by
  sorry

theorem demorgan_forall :
  ¬ (∀ x, P x) → (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_forall_converse :
  (∃ x, ¬ P x) → ¬ (∀ x, P x)  := by
  sorry

theorem demorgan_forall_law :
  ¬ (∀ x, P x) ↔ (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_law :
  ¬ (∃ x, P x) ↔ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

theorem exists_as_neg_forall :
  (∃ x, P x) → ¬ (∀ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists :
  (∀ x, P x) → ¬ (∃ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists_converse :
  ¬ (∃ x, ¬ P x) → (∀ x, P x)  := by
  sorry

theorem exists_as_neg_forall_converse :
  ¬ (∀ x, ¬ P x) → (∃ x, P x)  := by
  sorry

theorem forall_as_neg_exists_law :
  (∀ x, P x) ↔ ¬ (∃ x, ¬ P x)  := by
  sorry

theorem exists_as_neg_forall_law :
  (∃ x, P x) ↔ ¬ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
--  Distributivity between quantifiers
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists :
  (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists_converse :
  (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x)  := by
  sorry

theorem forall_conj_as_conj_forall :
  (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)  := by
  sorry

theorem forall_conj_as_conj_forall_converse :
  (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
  sorry

theorem forall_disj_as_disj_forall_converse :
  (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x)  := by
  sorry


end predicate

------------------------------------------------

section bonus

------------------------------------------------
--  Drinker's paradox
------------------------------------------------

variable (D : U → Prop)

-- There is a person p such that:
-- if p drinks, then everybody drinks
-- p: «person»
-- D x: «x drinks»
theorem drinker :
  ∃ p, (D p → ∀ x, D x)  := by
  sorry

------------------------------------------------
--  Russell's paradox
------------------------------------------------

variable (S : U → U → Prop)

-- It is impossible to have a barber b such that
-- b shaves exactly those people who do not shave themselves
-- b: «barber»
-- S x y: «x shaves y»
theorem russell :
  ¬ ∃ b, ∀ x, (S b x ↔ ¬ S x x)  := by
  sorry


end bonus


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)  := by
  sorry

theorem exists_conj_as_conj_exists_converse :
  (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)  := by
  sorry

---------------------------------------------- -/
