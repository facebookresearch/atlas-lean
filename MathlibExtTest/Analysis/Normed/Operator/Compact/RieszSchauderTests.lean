/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Operator.Compact.RieszSchauder
public import MathlibExt.Analysis.InnerProductSpace.RieszSchauder
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

@[expose] public section

namespace MathlibExt.Analysis.Normed.Operator.Compact.RieszSchauderTest

open MathlibExt.Analysis.Normed.Operator.Compact.RieszSchauder
open MathlibExt.Analysis.InnerProductSpace.RieszSchauder
open scoped InnerProduct
open Filter Topology

noncomputable section

/-- The zero operator on a finite-dimensional space: `1 • 1 - 0 = 1` is
bijective, the first branch of the Fredholm alternative. -/
example : Function.Bijective
    (((1 : ℝ) • 1 - 0 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))) := by
  have hT : IsCompactOperator (0 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) :=
    isCompactOperator_of_locallyCompactSpace_dom 0
  have h := fredholm_alternative (T := (0 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)))
    hT (one_ne_zero (α := ℝ))
  rcases h with h | h
  · simpa using h
  · exfalso
    apply h.1
    rw [show ((1 : ℝ) • 1 - 0 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) = 1 by simp]
    exact LinearMap.ker_id

/-- The identity operator on a finite-dimensional space, at `μ = 1`: the kernel
of `1 • 1 - 1 = 0` is the whole space, which is finite-dimensional, and its
range `⊥` is closed. -/
example : LinearMap.ker
    (((1 : ℝ) • 1 - 1 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)).toLinearMap) = ⊤ := by
  simp

example : FiniteDimensional ℝ (LinearMap.ker
    (((1 : ℝ) • 1 - 1 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)).toLinearMap)) := by
  have hT : IsCompactOperator (1 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) :=
    isCompactOperator_of_locallyCompactSpace_dom 1
  exact finiteDimensional_ker hT (one_ne_zero (α := ℝ))

example : IsClosed (LinearMap.range
    (((1 : ℝ) • 1 - 1 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)).toLinearMap) : Set (Fin 2 → ℝ)) := by
  have hT : IsCompactOperator (1 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) :=
    isCompactOperator_of_locallyCompactSpace_dom 1
  exact isClosed_range_smul_one_sub hT (one_ne_zero (α := ℝ))

/-- The zero operator on `ℓ²(ℕ, ℝ)`: `1 • 1 - 0 = 1` is bijective, the first
branch of the Fredholm alternative in infinite dimensions. -/
example : Function.Bijective
    (((1 : ℝ) • 1 - 0 : (lp (fun _ : ℕ ↦ ℝ) 2) →L[ℝ] (lp (fun _ : ℕ ↦ ℝ) 2))) := by
  have hT : IsCompactOperator (0 : (lp (fun _ : ℕ ↦ ℝ) 2) →L[ℝ] (lp (fun _ : ℕ ↦ ℝ) 2)) :=
    isCompactOperator_zero
  have h := fredholm_alternative
    (T := (0 : (lp (fun _ : ℕ ↦ ℝ) 2) →L[ℝ] (lp (fun _ : ℕ ↦ ℝ) 2)))
    hT (one_ne_zero (α := ℝ))
  rcases h with h | h
  · simpa using h
  · exfalso
    apply h.1
    rw [show ((1 : ℝ) • 1 - 0 : (lp (fun _ : ℕ ↦ ℝ) 2) →L[ℝ] (lp (fun _ : ℕ ↦ ℝ) 2)) = 1
      by simp]
    exact LinearMap.ker_id

/-- Hilbert-space form for the identity operator at `μ = 1` on `ℂ²`: the range
of `1 • 1 - 1 = 0` is the orthogonal complement of the kernel of the adjoint. -/
example : LinearMap.range (((1 : ℂ) • 1 - 1 :
      EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)).toLinearMap)
      = (LinearMap.ker (((1 : ℂ) • 1 - 1 :
          EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))†.toLinearMap))ᗮ := by
  have hT : IsCompactOperator
      (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) :=
    isCompactOperator_of_locallyCompactSpace_dom 1
  exact range_eq_orthogonal_ker_adjoint hT (one_ne_zero (α := ℂ))

/-- Hilbert-space adjoint form for the zero operator at `μ = 1` on `ℂ²`: the
range is the orthogonal complement of the kernel of `star 1 • 1 - 0†`. -/
example : LinearMap.range (((1 : ℂ) • 1 - 0 :
      EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)).toLinearMap)
      = (LinearMap.ker (((star (1 : ℂ)) • 1 -
          (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))† :
          EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)).toLinearMap))ᗮ := by
  have hT : IsCompactOperator
      (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) :=
    isCompactOperator_zero
  exact range_eq_orthogonal_ker_smul_one_sub_adjoint hT (one_ne_zero (α := ℂ))

/-- Every compact operator at a nonzero scalar has a closed range: check the
statement on the zero operator on `ℓ²(ℕ, ℝ)`, where the range is `⊤`. -/
example : IsClosed (LinearMap.range
    (((1 : ℝ) • 1 - 0 : (lp (fun _ : ℕ ↦ ℝ) 2) →L[ℝ] (lp (fun _ : ℕ ↦ ℝ) 2)).toLinearMap)
      : Set (lp (fun _ : ℕ ↦ ℝ) 2)) := by
  have hT : IsCompactOperator (0 : (lp (fun _ : ℕ ↦ ℝ) 2) →L[ℝ] (lp (fun _ : ℕ ↦ ℝ) 2)) :=
    isCompactOperator_zero
  exact isClosed_range_smul_one_sub hT (one_ne_zero (α := ℝ))

end

end MathlibExt.Analysis.Normed.Operator.Compact.RieszSchauderTest
