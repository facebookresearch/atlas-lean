/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.CompactFiniteRankApprox
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

open Function Set Filter Topology
open MathlibExt.Analysis.InnerProductSpace.CompactFiniteRankApprox

namespace MathlibExtTest.Analysis.InnerProductSpace.CompactFiniteRankApprox

/-!
# Tests for finite-rank approximation of compact operators

The abstract examples check the theorems on a hypothetical compact
operator. The concrete examples are the zero operator and the identity
operator on `EuclideanSpace ℝ (Fin 2)`, both compact (the identity because
the space is finite-dimensional): the zero operator admits the zero
finite-rank approximant within any `ε`, and the identity admits a
finite-rank approximant within `1 / 2`.
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A compact operator on a Hilbert space admits a finite-rank
approximant within any `ε > 0`. -/
example (T : H →L[𝕜] H) (hc : IsCompactOperator (T : H → H)) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : H →L[𝕜] H,
      FiniteDimensional 𝕜 ↥(LinearMap.range (F : H →ₗ[𝕜] H)) ∧ ‖T - F‖ ≤ ε :=
  exists_finiteRank_approx T hc hε

/-- A compact operator on a Hilbert space is a norm limit of finite-rank
operators. -/
example (T : H →L[𝕜] H) (hc : IsCompactOperator (T : H → H)) :
    ∃ F : ℕ → H →L[𝕜] H,
      (∀ n, FiniteDimensional 𝕜 ↥(LinearMap.range (F n : H →ₗ[𝕜] H))) ∧
      Tendsto (fun n => ‖T - F n‖) atTop (𝓝 0) :=
  exists_tendsto_finiteRank_approx T hc

/-- The zero operator on `EuclideanSpace ℝ (Fin 2)` is compact. -/
example : IsCompactOperator
    ((0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
      EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) := by
  simpa using (isCompactOperator_zero :
    IsCompactOperator (0 : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)))

/-- The zero operator admits a finite-rank approximant of norm at most
`ε` (the zero approximant itself). -/
example {ε : ℝ} (hε : 0 < ε) :
    ∃ F : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2),
      FiniteDimensional ℝ ↥(LinearMap.range (F : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin 2))) ∧
      ‖(0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) - F‖ ≤ ε := by
  obtain ⟨F, hFfin, hFnorm⟩ :=
    exists_finiteRank_approx (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
      (by simpa using (isCompactOperator_zero :
        IsCompactOperator (0 : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)))) hε
  exact ⟨F, hFfin, hFnorm⟩

/-- The identity operator on `EuclideanSpace ℝ (Fin 2)` is compact. -/
example : IsCompactOperator
    ((1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
      EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) := by
  have hcoe : ((1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
      EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) = id := by
    funext x
    simp
  rw [hcoe]
  exact isCompactOperator_id

/-- The identity on `EuclideanSpace ℝ (Fin 2)` admits a finite-rank
approximant within `1 / 2`. -/
example :
    ∃ F : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2),
      FiniteDimensional ℝ ↥(LinearMap.range (F : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin 2))) ∧
      ‖(1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) - F‖ ≤ 1 / 2 := by
  have hc : IsCompactOperator
      ((1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
        EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) := by
    have hcoe : ((1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
        EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) = id := by
      funext x
      simp
    rw [hcoe]
    exact isCompactOperator_id
  exact exists_finiteRank_approx
    (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) hc
    (show (0 : ℝ) < 1 / 2 by norm_num)

end MathlibExtTest.Analysis.InnerProductSpace.CompactFiniteRankApprox
