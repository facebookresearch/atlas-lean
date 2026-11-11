/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.DeficiencyZero.Existence

/-! Tests for the deficiency-zero existence theorem: the reversible isomerization `A ⇌ B`
satisfies both network hypotheses, so it has a positive complex-balanced equilibrium for every
choice of positive rate constants and exactly one equilibrium per compatibility class; the
irreversible `A → B` shows weak reversibility cannot be dropped; a zero rate constant on
`A ⇌ B` shows strict positivity cannot be relaxed; and the weakly reversible network
`A ⇌ 2A, 0 ⇌ A` of deficiency one fails the deficiency-zero hypothesis. -/

namespace MathlibExtTest.Biology.Dynamics.DeficiencyZero.Existence

open MathlibExt.Biology.Dynamics.ComplexBalanced ReactionNetwork

/-- The reversible isomerization `A ⇌ B` on species `Fin 2` (`0 = A`, `1 = B`): reaction `0`
is `A → B`, reaction `1` is `B → A`. -/
def revAB : ReactionNetwork (Fin 2) (Fin 2) where
  src := ![![1, 0], ![0, 1]]
  prod := ![![0, 1], ![1, 0]]

/-- `A ⇌ B` has deficiency zero in the linear form: a zero net stoichiometric change forces
equal weights on the two reactions, which cancel on the complexes. -/
theorem deficiencyZero_revAB : ∀ α : Fin 2 → ℝ,
    ∑ r, α r • (fun s => (revAB.prod r s : ℝ) - revAB.src r s) = 0 →
      ∀ η : (Fin 2 → ℕ) → ℝ, ∑ r, α r * (η (revAB.prod r) - η (revAB.src r)) = 0 := by
  intro α hα η
  have h0 := congrFun hα 0
  simp [revAB, Fin.sum_univ_two] at h0
  simp only [revAB, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have : α 1 = α 0 := by linarith
  rw [this]
  ring

/-- `A ⇌ B` is weakly reversible: each reaction is undone by the other. -/
theorem weaklyReversible_revAB : ∀ r, Relation.ReflTransGen
    (fun y y' => ∃ r', revAB.src r' = y ∧ revAB.prod r' = y') (revAB.prod r) (revAB.src r) := by
  intro r
  fin_cases r
  · exact Relation.ReflTransGen.single ⟨1, rfl, rfl⟩
  · exact Relation.ReflTransGen.single ⟨0, rfl, rfl⟩

/-- **Non-vacuity.** For every choice of positive rate constants, `A ⇌ B` has a positive
complex-balanced equilibrium. -/
example {k : Fin 2 → ℝ} (hk : ∀ r, 0 < k r) :
    ∃ c : Fin 2 → ℝ, (∀ s, 0 < c s) ∧ revAB.IsComplexBalanced k c :=
  revAB.exists_pos_isComplexBalanced_of_deficiency_zero deficiencyZero_revAB
    weaklyReversible_revAB hk

/-- Exactly one positive equilibrium of `A ⇌ B` in the compatibility class of `(1, 2)`, for
every choice of positive rate constants. -/
example {k : Fin 2 → ℝ} (hk : ∀ r, 0 < k r) : ∃! x : Fin 2 → ℝ, (∀ s, 0 < x s) ∧
    x - ![1, 2] ∈ revAB.stoichiometricSubspace ∧ revAB.massActionField k x = 0 :=
  revAB.existsUnique_equilibrium_of_deficiency_zero deficiencyZero_revAB
    weaklyReversible_revAB hk (by intro s; fin_cases s <;> simp)

/-- Horn's construction directly: the weights `ψ(A) = 2`, `ψ(B) = 1` balance `A ⇌ B` with rate
constants `(1, 2)`, so some positive concentration is complex balanced. -/
example : ∃ c : Fin 2 → ℝ, (∀ s, 0 < c s) ∧ revAB.IsComplexBalanced ![1, 2] c := by
  refine revAB.exists_pos_isComplexBalanced_of_balanced_weights deficiencyZero_revAB
    (ψ := fun z => if z = ![1, 0] then 2 else 1) ?_ ?_
  · intro r
    fin_cases r <;> simp [revAB]
  · have hne : (![0, 1] : Fin 2 → ℕ) ≠ ![1, 0] := by decide
    intro z
    rw [Finset.sum_filter, Finset.sum_filter]
    simp only [Fin.sum_univ_two, revAB, Matrix.cons_val_zero, Matrix.cons_val_one]
    by_cases h1 : z = ![1, 0]
    · subst h1
      simp [hne]
    · by_cases h2 : z = ![0, 1]
      · subst h2
        simp [hne, hne.symm]
      · simp [Ne.symm h1, Ne.symm h2]

/-- With a zero rate constant on `B → A`, `A ⇌ B` has no positive complex-balanced state: the
complex `A` emits flux `c_A` and receives none. So the hypothesis `0 < k r` cannot be relaxed
to `0 ≤ k r`. -/
theorem not_isComplexBalanced_revAB_zero_rate {c : Fin 2 → ℝ} (hc : ∀ s, 0 < c s) :
    ¬ revAB.IsComplexBalanced ![1, 0] c := by
  intro h
  have hA := h ![1, 0]
  rw [Finset.sum_filter, Finset.sum_filter] at hA
  simp [Fin.sum_univ_two, revAB, rate] at hA
  exact (hc 0).ne' hA

/-- The irreversible isomerization `A → B`. -/
def irrAB : ReactionNetwork (Fin 2) (Fin 1) where
  src := ![![1, 0]]
  prod := ![![0, 1]]

/-- `A → B` has deficiency zero in the linear form: its only reaction vector is nonzero. -/
theorem deficiencyZero_irrAB : ∀ α : Fin 1 → ℝ,
    ∑ r, α r • (fun s => (irrAB.prod r s : ℝ) - irrAB.src r s) = 0 →
      ∀ η : (Fin 2 → ℕ) → ℝ, ∑ r, α r * (η (irrAB.prod r) - η (irrAB.src r)) = 0 := by
  intro α hα η
  have h0 := congrFun hα 0
  simp [irrAB] at h0
  simp [h0]

/-- `A → B` is not weakly reversible: no reaction leaves `B`. -/
theorem not_weaklyReversible_irrAB : ¬ ∀ r, Relation.ReflTransGen
    (fun y y' => ∃ r', irrAB.src r' = y ∧ irrAB.prod r' = y') (irrAB.prod r) (irrAB.src r) := by
  intro h
  rcases Relation.ReflTransGen.cases_head (h 0) with h' | ⟨c, ⟨r', hr', -⟩, -⟩
  · have := congrFun h' 0
    simp [irrAB] at this
  · fin_cases r'
    have := congrFun hr' 0
    simp [irrAB] at this

/-- `A → B` has no positive complex-balanced state for positive rate constants, although it
has deficiency zero: weak reversibility cannot be dropped. -/
theorem not_isComplexBalanced_irrAB {k : Fin 1 → ℝ} (hk : ∀ r, 0 < k r) {c : Fin 2 → ℝ}
    (hc : ∀ s, 0 < c s) : ¬ irrAB.IsComplexBalanced k c := by
  intro h
  have hA := h ![1, 0]
  rw [Finset.sum_filter, Finset.sum_filter] at hA
  simp [irrAB, rate] at hA
  rcases hA with h1 | h1
  · exact (hk 0).ne' h1
  · exact (hc 0).ne' h1

/-- The network `A → 2A`, `2A → A`, `0 → A`, `A → 0` on one species. -/
def defOne : ReactionNetwork (Fin 1) (Fin 4) where
  src := ![![1], ![2], ![0], ![1]]
  prod := ![![2], ![1], ![1], ![0]]

/-- `A ⇌ 2A, 0 ⇌ A` is weakly reversible. -/
example : ∀ r, Relation.ReflTransGen
    (fun y y' => ∃ r', defOne.src r' = y ∧ defOne.prod r' = y') (defOne.prod r) (defOne.src r) := by
  intro r
  fin_cases r
  · exact Relation.ReflTransGen.single ⟨1, rfl, rfl⟩
  · exact Relation.ReflTransGen.single ⟨0, rfl, rfl⟩
  · exact Relation.ReflTransGen.single ⟨3, rfl, rfl⟩
  · exact Relation.ReflTransGen.single ⟨2, rfl, rfl⟩

/-- `A ⇌ 2A, 0 ⇌ A` has deficiency `3 - 1 - 1 = 1` and fails the deficiency-zero hypothesis:
the weighting of `A → 2A` and `A → 0` has zero net stoichiometric change but nonzero change
on the complexes (tested against `η(y) = y_A²`). -/
example : ¬ ∀ α : Fin 4 → ℝ,
    ∑ r, α r • (fun s => (defOne.prod r s : ℝ) - defOne.src r s) = 0 →
      ∀ η : (Fin 1 → ℕ) → ℝ, ∑ r, α r * (η (defOne.prod r) - η (defOne.src r)) = 0 := by
  intro h
  have := h ![1, 0, 0, 1] (by
    funext s
    fin_cases s
    simp [defOne, Fin.sum_univ_four]
    norm_num) (fun y => (y 0 : ℝ) ^ 2)
  simp [defOne, Fin.sum_univ_four] at this
  norm_num at this

#print axioms ReactionNetwork.exists_pos_isComplexBalanced_of_deficiency_zero
#print axioms ReactionNetwork.existsUnique_equilibrium_of_deficiency_zero
#print axioms ReactionNetwork.exists_pos_isComplexBalanced_of_balanced_weights

end MathlibExtTest.Biology.Dynamics.DeficiencyZero.Existence
