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

/-! ### Conductors -/

variable [FiniteDimensional K L] (ell : ℕ) [Fact ell.Prime] (V : Type*) [AddCommGroup V]
  [Module ℚ_[ell] V] [Module.Finite ℚ_[ell] V]
  (ρ : Representation ℚ_[ell] (DecompositionGroup K L) V)

-- The trivial representation has no ramification codimension, so both conductors vanish.
example (H : Subgroup (DecompositionGroup K L)) :
    invariantCodimension K L ell V
      (Representation.trivial ℚ_[ell] (DecompositionGroup K L) V) H = 0 := by
  have : Representation.invariants
      ((Representation.trivial ℚ_[ell] (DecompositionGroup K L) V).comp H.subtype) = ⊤ := by
    ext v
    simp [Representation.mem_invariants]
  rw [invariantCodimension, this, finrank_top, Nat.sub_self]

example (N : ℕ) :
    artinConductor K L ell V
      (Representation.trivial ℚ_[ell] (DecompositionGroup K L) V) N = 0 := by
  have (H : Subgroup (DecompositionGroup K L)) : Representation.invariants
      ((Representation.trivial ℚ_[ell] (DecompositionGroup K L) V).comp H.subtype) = ⊤ := by
    ext v
    simp [Representation.mem_invariants]
  have hc (H : Subgroup (DecompositionGroup K L)) : invariantCodimension K L ell V
      (Representation.trivial ℚ_[ell] (DecompositionGroup K L) V) H = 0 := by
    rw [invariantCodimension, this, finrank_top, Nat.sub_self]
  simp [artinConductor, conductorSummand, hc]

-- The Artin sum includes the inertia term `i = 0` with weight `#G₀/#G₀ = 1`, while the Swan
-- sum omits it.
example : artinConductor K L ell V ρ 1 = invariantCodimension K L ell V ρ (lowerGroup K L 0) := by
  simp [artinConductor, conductorSummand_zero]

example : swanConductor K L ell V ρ 1 = 0 := by
  simp [swanConductor]

-- The sum up to `N` stops before index `N`: the term `i = N` is not included.
example (N : ℕ) : artinConductor K L ell V ρ (N + 1) =
    artinConductor K L ell V ρ N + conductorSummand K L ell V ρ N := by
  simp [artinConductor, Finset.sum_range_succ]

-- For every positive bound, Artin = Swan + the codimension of the inertia invariants.
example (N : ℕ) : artinConductor K L ell V ρ (N + 1) =
    swanConductor K L ell V ρ (N + 1) + invariantCodimension K L ell V ρ (lowerGroup K L 0) :=
  artinConductor_eq_swanConductor_add K L ell V ρ (N + 1) N.succ_pos

-- Unramified case: when `G₀ = 1` both sums vanish for every bound.
example (hG : lowerGroup K L 0 = ⊥) (N : ℕ) : artinConductor K L ell V ρ N = 0 := by
  rw [artinConductor_independent K L ell V ρ N 0 (lowerGroup_eq_bot_of_bound K L 0 hG N
    (Nat.zero_le N)) hG]
  simp [artinConductor]

-- Bound independence: the sums do not change past a terminating index.
example (N : ℕ) (hN : lowerGroup K L N = ⊥) :
    swanConductor K L ell V ρ N = swanConductor K L ell V ρ (N + 5) :=
  swanConductor_independent K L ell V ρ N (N + 5) hN
    (lowerGroup_eq_bot_of_bound K L N hN (N + 5) (by omega))

end MathlibExtTest.NumberTheory.FiniteRamificationConductors
