/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finite weighted sums, rank-nullity, and linear balance maps

Reindexing invariance of finite weighted sums, rank-nullity for linear maps between real
function spaces on finite index types, the column expansion of `A *ᵥ ξ`, and the fact that a
linear functional vanishing on every column of `A` vanishes on every `A *ᵥ ξ`.

This is pure algebra: which functionals count as physically conserved quantities is supplied
separately, and no claim is made that a vector `ξ` is a chemically realizable set of reaction
extents.
-/

@[expose] public section

open scoped Matrix

namespace MathlibExt.LinearAlgebra.FiniteBalance

/-- Reindexing a finite weighted sum along an equivalence does not change it. -/
theorem weightedSum_comp_equiv {ι ι' R : Type*} [Fintype ι] [Fintype ι'] [CommRing R]
    (e : ι ≃ ι') (w x : ι' → R) :
    ∑ i, w (e i) * x (e i) = ∑ j, w j * x j := by
  exact e.sum_comp fun j => w j * x j

/-- Rank-nullity for a linear map between finite-dimensional real function spaces. -/
theorem finrank_ker_add_finrank_range {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    Module.finrank ℝ (LinearMap.ker f) + Module.finrank ℝ (LinearMap.range f) =
      Fintype.card ι := by
  rw [add_comm, LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]

/-- A matrix-vector product is the weighted sum of the matrix columns. -/
theorem mulVec_eq_sum_smul_col {κ ι : Type*} [Fintype ι] (A : Matrix κ ι ℝ) (ξ : ι → ℝ) :
    A *ᵥ ξ = ∑ s, ξ s • (fun b => A b s) := by
  ext b
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun s _ => mul_comm (A b s) (ξ s)

/-- A linear functional vanishing on every column of `A` vanishes on every real
combination of those columns, i.e. on every `A *ᵥ ξ`. -/
theorem map_mulVec_eq_zero_of_forall_col_eq_zero {κ ι : Type*} [Fintype ι]
    (φ : (κ → ℝ) →ₗ[ℝ] ℝ) (A : Matrix κ ι ℝ)
    (h : ∀ s, φ (fun b => A b s) = 0) (ξ : ι → ℝ) :
    φ (A *ᵥ ξ) = 0 := by
  rw [mulVec_eq_sum_smul_col, map_sum]
  exact Finset.sum_eq_zero fun s _ => by rw [map_smul, h, smul_zero]

end MathlibExt.LinearAlgebra.FiniteBalance
