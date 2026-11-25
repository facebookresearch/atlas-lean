/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MarkovBasis

@[expose] public section

open MvPolynomial MathlibExt.RingTheory.ToricIdeal MathlibExt.RingTheory.MarkovBasis

namespace MathlibExtTest.RingTheory.MarkovBasis

/-- The statistic of two cells that both record one unit of the same count (`x₀, x₁ ↦ t`). -/
noncomputable abbrev T₂ : Fin 2 → Unit →₀ ℕ := fun _ ↦ Finsupp.single () 1

/-- The basic move `e₀ - e₁` of the model `x₀, x₁ ↦ t`. -/
noncomputable abbrev move : Fin 1 → Fin 2 →₀ ℤ :=
  fun _ ↦ Finsupp.single 0 1 - Finsupp.single 1 1

/-- The move lies in the lattice of moves of `T₂`. -/
example : Finsupp.linearCombination ℤ (statInt T₂) (move 0) = 0 := by
  rw [linearCombination_eq_zero_iff]
  have hp : posPartNat (move 0) = Finsupp.single 0 1 := by
    ext x; fin_cases x <;> simp [posPartNat, move]
  have hn : negPartNat (move 0) = Finsupp.single 1 1 := by
    ext x; fin_cases x <;> simp [negPartNat, move]
  rw [hp, hn]
  simp [Finsupp.linearCombination_single]

/-- A single step of the chain: from the table `(0, 1)` to `(1, 0)` by adding the move. -/
example : MoveStep move (Finsupp.single 1 1) (Finsupp.single 0 1) := by
  refine ⟨0, 1, Or.inl rfl, ?_⟩
  ext x; fin_cases x <;> simp [toInt, move]

/-- Applying the theorem: the move binomials generate the toric ideal exactly when the move
`e₀ - e₁` connects every fibre of `T₂`. -/
example : IsMarkovBasis T₂ move ↔
    Ideal.span (Set.range fun i ↦ moveBinomial ℚ (move i)) = toricIdeal ℚ T₂ :=
  isMarkovBasis_iff_span_eq_toricIdeal ℚ T₂ move

/-- Boundary case: for a statistic with singleton fibres (one cell, `x ↦ t`), the empty family
is a Markov basis, so the toric ideal is zero. -/
example : toricIdeal ℚ (fun _ : Unit ↦ Finsupp.single () 1) = ⊥ := by
  have hM : IsMarkovBasis (fun _ : Unit ↦ (Finsupp.single () 1 : Unit →₀ ℕ))
      (Empty.elim : Empty → Unit →₀ ℤ) := by
    refine ⟨fun i ↦ i.elim, fun g g' h ↦ ?_⟩
    have : g = g' := by
      ext
      have := congrArg (fun v ↦ v ()) h
      simpa [Finsupp.linearCombination_apply, Finsupp.sum_fintype] using this
    subst this
    exact Relation.ReflTransGen.refl
  rw [← (isMarkovBasis_iff_span_eq_toricIdeal ℚ _ _).1 hM]
  simp

end MathlibExtTest.RingTheory.MarkovBasis
