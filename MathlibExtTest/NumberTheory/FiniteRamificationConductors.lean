/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FiniteRamificationConductors

@[expose] public section

namespace MathlibExtTest.NumberTheory.FiniteRamificationConductors

open ValuativeRel MathlibExt.NumberTheory.FiniteRamificationConductors

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [ValuativeRel L]

/-! ### The lower filtration -/

-- Indices `i ≤ -1` give the whole decomposition group.
example : lowerGroup K L (-1) = ⊤ :=
  lowerGroup_eq_top_of_le_neg_one K L le_rfl

-- The filtration decreases.
example : lowerGroup K L 2 ≤ lowerGroup K L 1 :=
  lowerGroup_antitone K L (by norm_num)

/-! ### Codimensions and weighted codimension sums -/

variable [FiniteDimensional K L] (ell : ℕ) [Fact ell.Prime] (V : Type*) [AddCommGroup V]
  [Module ℚ_[ell] V] [Module.Finite ℚ_[ell] V]
  (ρ : Representation ℚ_[ell] (DecompositionGroup K L) V)

-- The codimension (hence every conductor) is only defined for finite-dimensional
-- representations: without `Module.Finite`, `finrank` would collapse to `0`.
set_option linter.unusedVariables false in
example (W : Type) [AddCommGroup W] [Module ℚ_[ell] W]
    (σ : Representation ℚ_[ell] (DecompositionGroup K L) W)
    (H : Subgroup (DecompositionGroup K L)) : True := by
  fail_if_success have := invariantCodimension K L ell W σ H
  trivial

-- The trivial representation has no ramification codimension.
example (H : Subgroup (DecompositionGroup K L)) :
    invariantCodimension K L ell V
      (Representation.trivial ℚ_[ell] (DecompositionGroup K L) V) H = 0 := by
  have : Representation.invariants
      ((Representation.trivial ℚ_[ell] (DecompositionGroup K L) V).comp H.subtype) = ⊤ := by
    ext v
    simp [Representation.mem_invariants]
  rw [invariantCodimension, this, finrank_top, Nat.sub_self]

-- The weighted sum includes the inertia term `i = 0` with weight `#G₀/#G₀ = 1`, while the
-- positive sum omits it.
example : weightedCodimensionSum K L ell V ρ 1 =
    invariantCodimension K L ell V ρ (lowerGroup K L 0) := by
  simp [weightedCodimensionSum, conductorSummand_zero]

example : positiveWeightedCodimensionSum K L ell V ρ 1 = 0 := by
  simp [positiveWeightedCodimensionSum]

-- The sum up to `N` stops before index `N`.
example (N : ℕ) : weightedCodimensionSum K L ell V ρ (N + 1) =
    weightedCodimensionSum K L ell V ρ N + conductorSummand K L ell V ρ N := by
  simp [weightedCodimensionSum, Finset.sum_range_succ]

/-! ### Conductors of finite Galois extensions of local fields -/

section LocalField

variable [TopologicalSpace K] [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L]

-- The trivial representation has conductor zero.
example (N : {N : ℕ // lowerGroup K L N = ⊥}) :
    artinConductor K L ell V
      (Representation.trivial ℚ_[ell] (DecompositionGroup K L) V) N = 0 := by
  have hc (H : Subgroup (DecompositionGroup K L)) : invariantCodimension K L ell V
      (Representation.trivial ℚ_[ell] (DecompositionGroup K L) V) H = 0 := by
    have : Representation.invariants
        ((Representation.trivial ℚ_[ell] (DecompositionGroup K L) V).comp H.subtype) = ⊤ := by
      ext v
      simp [Representation.mem_invariants]
    rw [invariantCodimension, this, finrank_top, Nat.sub_self]
  simp [artinConductor, weightedCodimensionSum, conductorSummand, hc]

-- Artin = Swan + the codimension of the inertia invariants, for every certified bound.
example (N : {N : ℕ // lowerGroup K L N = ⊥}) :
    artinConductor K L ell V ρ N =
      swanConductor K L ell V ρ N + invariantCodimension K L ell V ρ (lowerGroup K L 0) :=
  artinConductor_eq_swanConductor_add K L ell V ρ N

-- Unramified case: when `G₀ = 1`, the bound `0` is certified and both conductors vanish.
example (hG : lowerGroup K L 0 = ⊥) : artinConductor K L ell V ρ ⟨0, hG⟩ = 0 := by
  simp [artinConductor, weightedCodimensionSum]

example (hG : lowerGroup K L 0 = ⊥) : swanConductor K L ell V ρ ⟨0, hG⟩ = 0 := by
  simp [swanConductor, positiveWeightedCodimensionSum]

-- Bound independence: any two certified bounds give the same conductors.
example (N : ℕ) (hN : lowerGroup K L N = ⊥) :
    swanConductor K L ell V ρ ⟨N, hN⟩ = swanConductor K L ell V ρ ⟨N + 5,
      lowerGroup_eq_bot_of_bound K L N hN (N + 5) (by omega)⟩ :=
  swanConductor_eq K L ell V ρ _ _

end LocalField

end MathlibExtTest.NumberTheory.FiniteRamificationConductors
