/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.ToLin

open scoped ComplexOrder InnerProductSpace Matrix

/-!
# Rectangular isometries, coisometries, and unitary-between matrices

This module introduces generic rectangular predicates for isometries,
coisometries, and unitary isomorphisms between possibly distinct finite bases.

For `U : Matrix out inp R`, rows are indexed by the output basis `out` and
columns by the input basis `inp` (so `U` represents a linear map `inp → out`).

* `U` is an isometry when `Matrix.conjTranspose U * U = 1` on `inp`.
* `U` is a coisometry when `U * Matrix.conjTranspose U = 1` on `out`.
* `U` is unitary between `inp` and `out` when both equalities hold.

Requiring both equalities means `U` is a unitary isomorphism between possibly
differently named finite bases. When `out = inp = n` this specializes to ordinary
square unitarity `U ∈ Matrix.unitaryGroup n R`. Empty index types are supported
without `Nonempty`.

## Main definitions

* `Matrix.IsIsometry` – rectangular isometry predicate `Uᴴ * U = 1` on the input/column index.
* `Matrix.IsCoisometry` – rectangular coisometry predicate `U * Uᴴ = 1` on the output/row index.
* `Matrix.IsUnitaryBetween` – rectangular unitary predicate requiring both.

## Main results

* `Matrix.IsUnitaryBetween.star_mul` – left projection `conjTranspose U * U = 1`.
* `Matrix.IsUnitaryBetween.mul_star` – right projection `U * conjTranspose U = 1`.
* `Matrix.IsUnitaryBetween.isIsometry` – unitary-between implies isometry.
* `Matrix.IsUnitaryBetween.isCoisometry` – unitary-between implies coisometry.
* `Matrix.isUnitaryBetween_iff_isIsometry_and_isCoisometry` – `IsUnitaryBetween` iff
  `IsIsometry ∧ IsCoisometry`.
* `Matrix.isUnitaryBetween_iff_mem_unitaryGroup` – square specialization.
* `Matrix.exists_unitary_mul_eq_of_isometry` – two `out × inp` isometries differ by a
  square unitary on `out`.

-/

@[expose] public section

namespace Matrix

variable {out inp : Type*} {R : Type*} [CommRing R] [StarRing R]

/-- Let `R` be a commutative star ring and let `out`, `inp` be index types. Assume `out` is finite and
equality is decidable on `inp`. An `out × inp` matrix `U` is an isometry when `Uᴴ*U = 1` on the
input index. Empty index types are included.
-/
def IsIsometry [DecidableEq inp] [Fintype out]
    (U : Matrix out inp R) : Prop :=
  Matrix.conjTranspose U * U = 1

/-- Let `R` be a commutative star ring and let `out`, `inp` be index types. Assume `inp` is finite and
equality is decidable on `out`. An `out × inp` matrix `U` is a coisometry when `U*Uᴴ = 1` on the
output index. Empty index types are included.
-/
def IsCoisometry [DecidableEq out] [Fintype inp]
    (U : Matrix out inp R) : Prop :=
  U * Matrix.conjTranspose U = 1

/-- Let `R` be a commutative star ring and let `out`, `inp` be index types. If both index types are
finite with decidable equality, an `out × inp` matrix `U` is unitary between them when both `Uᴴ*U =
1` and `U*Uᴴ = 1` hold.
-/
def IsUnitaryBetween [DecidableEq out] [DecidableEq inp] [Fintype out] [Fintype inp]
    (U : Matrix out inp R) : Prop :=
  Matrix.conjTranspose U * U = 1 ∧ U * Matrix.conjTranspose U = 1

section Projections

variable [DecidableEq out] [DecidableEq inp] [Fintype out] [Fintype inp]

/-- Let `R` be a commutative star ring and let `out`, `inp` be index types. For finite decidable index
types and a unitary-between matrix `U`, the input-side identity is `Uᴴ*U = 1`.
-/
theorem IsUnitaryBetween.star_mul {U : Matrix out inp R}
    (h : IsUnitaryBetween U) : Matrix.conjTranspose U * U = 1 :=
  h.1

/-- Let `R` be a commutative star ring and let `out`, `inp` be index types. For finite decidable index
types and a unitary-between matrix `U`, the output-side identity is `U*Uᴴ = 1`.
-/
theorem IsUnitaryBetween.mul_star {U : Matrix out inp R}
    (h : IsUnitaryBetween U) : U * Matrix.conjTranspose U = 1 :=
  h.2

/-- Let `R` be a commutative star ring and let `out`, `inp` be index types. For finite decidable index
types, every unitary-between matrix is an isometry.
-/
theorem IsUnitaryBetween.isIsometry {U : Matrix out inp R}
    (h : IsUnitaryBetween U) : IsIsometry U :=
  h.1

/-- Let `R` be a commutative star ring and let `out`, `inp` be index types. For finite decidable index
types, every unitary-between matrix is a coisometry.
-/
theorem IsUnitaryBetween.isCoisometry {U : Matrix out inp R}
    (h : IsUnitaryBetween U) : IsCoisometry U :=
  h.2

/-- Let `R` be a commutative star ring and let `out`, `inp` be index types. For finite decidable index
types, a rectangular matrix is unitary between them exactly when it is both an isometry and a
coisometry.
-/
theorem isUnitaryBetween_iff_isIsometry_and_isCoisometry {U : Matrix out inp R} :
    IsUnitaryBetween U ↔ IsIsometry U ∧ IsCoisometry U :=
  Iff.rfl

end Projections

variable {n : Type*} [DecidableEq n] [Fintype n]

/-- Let `R` be a commutative star ring and `n` a finite index type with decidable equality. A square
matrix is unitary between `n` and itself exactly when it belongs to `Matrix.unitaryGroup n R`.
-/
theorem isUnitaryBetween_iff_mem_unitaryGroup {U : Matrix n n R} :
    IsUnitaryBetween U ↔ U ∈ unitaryGroup n R := by
  constructor
  · intro h
    rw [mem_unitaryGroup_iff']
    rw [Matrix.star_eq_conjTranspose]
    exact h.1
  · intro h
    constructor
    · have h1 : star U * U = 1 := mem_unitaryGroup_iff'.mp h
      rwa [Matrix.star_eq_conjTranspose] at h1
    · have h2 : U * star U = 1 := mem_unitaryGroup_iff.mp h
      rwa [Matrix.star_eq_conjTranspose] at h2

/-- Let `out`, `inp` be finite index types with decidable equality, and let `V`, `W` be complex `out ×
inp` matrices satisfying `Vᴴ*V = Wᴴ*W = 1`. There exists a square unitary matrix `U` on `out` with
`U*V = W`. Either index type may be empty.
-/
public theorem exists_unitary_mul_eq_of_isometry
    {out inp : Type*}
    [Fintype out] [DecidableEq out] [Finite inp] [DecidableEq inp]
    (V W : Matrix out inp ℂ)
    (hV : IsIsometry V) (hW : IsIsometry W) :
    ∃ U : Matrix out out ℂ, U ∈ unitaryGroup out ℂ ∧ U * V = W := by
  classical
  have : Fintype inp := Fintype.ofFinite inp
  by_cases hEmptyInp : IsEmpty inp
  · refine ⟨1, ?_, ?_⟩
    · rw [mem_unitaryGroup_iff']
      simp
    · ext i j
      exact (hEmptyInp.false j).elim
  · rw [not_isEmpty_iff] at hEmptyInp
    have hNonemptyInp : Nonempty inp := hEmptyInp
    have hNonemptyOut : Nonempty out := by
      by_contra h
      rw [not_nonempty_iff] at h
      have hIsEmptyOut : IsEmpty out := h
      have hZero : Vᴴ * V = (0 : Matrix inp inp ℂ) := by
        have hVzero : V = 0 :=
          Matrix.ext fun i _ => (hIsEmptyOut.false i).elim
        rw [hVzero, Matrix.conjTranspose_zero, Matrix.zero_mul]
      have h01 : (0 : Matrix inp inp ℂ) = 1 := by
        calc (0 : Matrix inp inp ℂ) = Vᴴ * V := hZero.symm
          _ = 1 := hV
      have q0 := hNonemptyInp.some
      have h0 : (0 : Matrix inp inp ℂ) q0 q0 = (0 : ℂ) := by simp
      have h1 : (1 : Matrix inp inp ℂ) q0 q0 = (1 : ℂ) := by simp
      have hEq : (0 : ℂ) = 1 := by
        calc (0 : ℂ) = (0 : Matrix inp inp ℂ) q0 q0 := h0.symm
          _ = (1 : Matrix inp inp ℂ) q0 q0 := by rw [h01]
          _ = 1 := h1
      exact zero_ne_one hEq
    let Er := EuclideanSpace ℂ out
    let Eq := EuclideanSpace ℂ inp
    have : FiniteDimensional ℂ Er := inferInstance
    have : FiniteDimensional ℂ Eq := inferInstance
    let aLin : Eq →ₗ[ℂ] Er := Matrix.toEuclideanLin V
    let bLin : Eq →ₗ[ℂ] Er := Matrix.toEuclideanLin W
    have haAdj : aLin.adjoint ∘ₗ aLin = 1 := by
      have h1 : Matrix.toEuclideanLin (Vᴴ * V) =
          Matrix.toEuclideanLin Vᴴ ∘ₗ Matrix.toEuclideanLin V := by
        calc Matrix.toEuclideanLin (Vᴴ * V) =
            Matrix.toLpLin 2 2 (Vᴴ * V) := rfl
          _ = Matrix.toLpLin 2 2 Vᴴ ∘ₗ Matrix.toLpLin 2 2 V := by
            rw [Matrix.toLpLin_mul_same]
          _ = Matrix.toEuclideanLin Vᴴ ∘ₗ Matrix.toEuclideanLin V := rfl
      have h2 : Matrix.toEuclideanLin Vᴴ = aLin.adjoint := by
        simp only [aLin]
        rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      have h3 : Matrix.toEuclideanLin (Vᴴ * V) =
          Matrix.toEuclideanLin (1 : Matrix inp inp ℂ) := by rw [hV]
      have h4 : Matrix.toEuclideanLin (1 : Matrix inp inp ℂ) =
          LinearMap.id := by simp
      calc aLin.adjoint ∘ₗ aLin =
          Matrix.toEuclideanLin Vᴴ ∘ₗ Matrix.toEuclideanLin V := by rw [← h2]
        _ = Matrix.toEuclideanLin (Vᴴ * V) := h1.symm
        _ = Matrix.toEuclideanLin (1 : Matrix inp inp ℂ) := h3
        _ = 1 := h4
    have hbAdj : bLin.adjoint ∘ₗ bLin = 1 := by
      have h1 : Matrix.toEuclideanLin (Wᴴ * W) =
          Matrix.toEuclideanLin Wᴴ ∘ₗ Matrix.toEuclideanLin W := by
        calc Matrix.toEuclideanLin (Wᴴ * W) =
            Matrix.toLpLin 2 2 (Wᴴ * W) := rfl
          _ = Matrix.toLpLin 2 2 Wᴴ ∘ₗ Matrix.toLpLin 2 2 W := by
            rw [Matrix.toLpLin_mul_same]
          _ = Matrix.toEuclideanLin Wᴴ ∘ₗ Matrix.toEuclideanLin W := rfl
      have h2 : Matrix.toEuclideanLin Wᴴ = bLin.adjoint := by
        simp only [bLin]
        rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      have h3 : Matrix.toEuclideanLin (Wᴴ * W) =
          Matrix.toEuclideanLin (1 : Matrix inp inp ℂ) := by rw [hW]
      have h4 : Matrix.toEuclideanLin (1 : Matrix inp inp ℂ) =
          LinearMap.id := by simp
      calc bLin.adjoint ∘ₗ bLin =
          Matrix.toEuclideanLin Wᴴ ∘ₗ Matrix.toEuclideanLin W := by rw [← h2]
        _ = Matrix.toEuclideanLin (Wᴴ * W) := h1.symm
        _ = Matrix.toEuclideanLin (1 : Matrix inp inp ℂ) := h3
        _ = 1 := h4
    have haInner : ∀ x y : Eq, ⟪aLin x, aLin y⟫_ℂ = ⟪x, y⟫_ℂ := by
      intro x y
      have hEq : aLin.adjoint (aLin y) = y := by
        calc aLin.adjoint (aLin y) = (aLin.adjoint ∘ₗ aLin) y := rfl
          _ = (1 : Eq →ₗ[ℂ] Eq) y := by rw [haAdj]
          _ = y := rfl
      calc ⟪aLin x, aLin y⟫_ℂ = ⟪x, aLin.adjoint (aLin y)⟫_ℂ :=
          (LinearMap.adjoint_inner_right aLin x (aLin y)).symm
        _ = ⟪x, y⟫_ℂ := by rw [hEq]
    have hbInner : ∀ x y : Eq, ⟪bLin x, bLin y⟫_ℂ = ⟪x, y⟫_ℂ := by
      intro x y
      have hEq : bLin.adjoint (bLin y) = y := by
        calc bLin.adjoint (bLin y) = (bLin.adjoint ∘ₗ bLin) y := rfl
          _ = (1 : Eq →ₗ[ℂ] Eq) y := by rw [hbAdj]
          _ = y := rfl
      calc ⟪bLin x, bLin y⟫_ℂ = ⟪x, bLin.adjoint (bLin y)⟫_ℂ :=
          (LinearMap.adjoint_inner_right bLin x (bLin y)).symm
        _ = ⟪x, y⟫_ℂ := by rw [hEq]
    have haNorm : ∀ x : Eq, ‖aLin x‖ = ‖x‖ := by
      intro x
      have hSelf : ⟪aLin x, aLin x⟫_ℂ = ⟪(x : Eq), x⟫_ℂ := haInner x x
      have h1 : RCLike.re ⟪aLin x, aLin x⟫_ℂ = ‖aLin x‖ ^ 2 := by
        rw [inner_self_eq_norm_sq]
      have h2 : RCLike.re (⟪(x : Eq), x⟫_ℂ) = ‖(x : Eq)‖ ^ 2 := by
        rw [inner_self_eq_norm_sq]
      have hEq : ‖aLin x‖ ^ 2 = ‖(x : Eq)‖ ^ 2 := by
        calc ‖aLin x‖ ^ 2 = RCLike.re ⟪aLin x, aLin x⟫_ℂ := h1.symm
          _ = RCLike.re ⟪(x : Eq), x⟫_ℂ := by rw [hSelf]
          _ = ‖(x : Eq)‖ ^ 2 := h2
      nlinarith [norm_nonneg (aLin x), norm_nonneg (x : Eq)]
    have hbNorm : ∀ x : Eq, ‖bLin x‖ = ‖x‖ := by
      intro x
      have hSelf : ⟪bLin x, bLin x⟫_ℂ = ⟪(x : Eq), x⟫_ℂ := hbInner x x
      have h1 : RCLike.re ⟪bLin x, bLin x⟫_ℂ = ‖bLin x‖ ^ 2 := by
        rw [inner_self_eq_norm_sq]
      have h2 : RCLike.re (⟪(x : Eq), x⟫_ℂ) = ‖(x : Eq)‖ ^ 2 := by
        rw [inner_self_eq_norm_sq]
      have hEq : ‖bLin x‖ ^ 2 = ‖(x : Eq)‖ ^ 2 := by
        calc ‖bLin x‖ ^ 2 = RCLike.re ⟪bLin x, bLin x⟫_ℂ := h1.symm
          _ = RCLike.re ⟪(x : Eq), x⟫_ℂ := by rw [hSelf]
          _ = ‖(x : Eq)‖ ^ 2 := h2
      nlinarith [norm_nonneg (bLin x), norm_nonneg (x : Eq)]
    let aIso : Eq →ₗᵢ[ℂ] Er :=
      { toLinearMap := aLin, norm_map' := haNorm }
    let bIso : Eq →ₗᵢ[ℂ] Er :=
      { toLinearMap := bLin, norm_map' := hbNorm }
    let S : Submodule ℂ Er := LinearMap.range aIso.toLinearMap
    let T : Submodule ℂ Er := LinearMap.range bIso.toLinearMap
    let aEquiv : Eq ≃ₗᵢ[ℂ] S := aIso.equivRange
    let bEquiv : Eq ≃ₗᵢ[ℂ] T := bIso.equivRange
    let rangeEquiv : S ≃ₗᵢ[ℂ] T := aEquiv.symm.trans bEquiv
    let L0 : S →ₗᵢ[ℂ] Er := T.subtypeₗᵢ.comp rangeEquiv.toLinearIsometry
    let ext : Er →ₗᵢ[ℂ] Er := L0.extend
    have hExtApply : ∀ (s : S), ext (s : Er) = L0 s := by
      intro s
      exact LinearIsometry.extend_apply L0 s
    have hExtA : ∀ x : Eq, ext (aIso x) = bIso x := by
      intro x
      calc ext (aIso x) = ext ((aEquiv x : S) : Er) := rfl
        _ = L0 (aEquiv x) := hExtApply (aEquiv x)
        _ = T.subtypeₗᵢ (rangeEquiv (aEquiv x)) := rfl
        _ = (rangeEquiv (aEquiv x) : Er) := rfl
        _ = (bEquiv x : Er) := by simp [rangeEquiv]
        _ = bIso x := rfl
    have hExtComp : ext.toLinearMap ∘ₗ aLin = bLin := by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply]
      calc ext.toLinearMap (aLin x) = ext (aIso x) := rfl
        _ = bIso x := hExtA x
        _ = bLin x := rfl
    have hInj : Function.Injective ext.toLinearMap := ext.injective
    have hSurj : Function.Surjective ext.toLinearMap :=
      (LinearMap.injective_iff_surjective.mp hInj)
    have hSurjExt : Function.Surjective ext := by
      intro y
      obtain ⟨x, hx⟩ := hSurj y
      use x
      exact hx
    let eEquiv : Er ≃ₗᵢ[ℂ] Er := LinearIsometryEquiv.ofSurjective ext hSurjExt
    have heEquivCoe : eEquiv.toLinearMap = ext.toLinearMap := rfl
    let U : Matrix out out ℂ :=
      (Matrix.toEuclideanLin (m := out) (n := out)).symm eEquiv.toLinearMap
    have hULin : Matrix.toEuclideanLin U = eEquiv.toLinearMap := by simp [U]
    have hUMem : U ∈ unitaryGroup out ℂ := by
      rw [mem_unitaryGroup_iff']
      have hStar : Matrix.toEuclideanLin Uᴴ =
          (Matrix.toEuclideanLin U).adjoint := by
        rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      have hMul : Matrix.toEuclideanLin (Uᴴ * U) = LinearMap.id := by
        calc Matrix.toEuclideanLin (Uᴴ * U) =
            Matrix.toLpLin 2 2 (Uᴴ * U) := rfl
          _ = Matrix.toLpLin 2 2 Uᴴ ∘ₗ Matrix.toLpLin 2 2 U := by
            rw [Matrix.toLpLin_mul_same]
          _ = Matrix.toEuclideanLin Uᴴ ∘ₗ Matrix.toEuclideanLin U := rfl
          _ = (Matrix.toEuclideanLin U).adjoint ∘ₗ Matrix.toEuclideanLin U := by
            rw [hStar]
          _ = eEquiv.toLinearMap.adjoint ∘ₗ eEquiv.toLinearMap := by rw [hULin]
          _ = ext.toLinearMap.adjoint ∘ₗ ext.toLinearMap := by rw [heEquivCoe]
          _ = 1 := LinearIsometry.adjoint_comp_self' ext
      have hOne : Matrix.toEuclideanLin (1 : Matrix out out ℂ) = LinearMap.id := by
        simp
      have : Matrix.toEuclideanLin (Uᴴ * U) =
          Matrix.toEuclideanLin (1 : Matrix out out ℂ) := by
        calc Matrix.toEuclideanLin (Uᴴ * U) = LinearMap.id := hMul
          _ = Matrix.toEuclideanLin (1 : Matrix out out ℂ) := hOne.symm
      have hUHU : Uᴴ * U = 1 :=
        (Matrix.toEuclideanLin (m := out) (n := out)).injective this
      rw [Matrix.star_eq_conjTranspose]
      exact hUHU
    have hMul : U * V = W := by
      have hMap : Matrix.toEuclideanLin (U * V) = Matrix.toEuclideanLin W := by
        calc Matrix.toEuclideanLin (U * V) =
            Matrix.toLpLin 2 2 (U * V) := rfl
          _ = Matrix.toLpLin 2 2 U ∘ₗ Matrix.toLpLin 2 2 V := by
            rw [Matrix.toLpLin_mul_same]
          _ = Matrix.toEuclideanLin U ∘ₗ Matrix.toEuclideanLin V := rfl
          _ = eEquiv.toLinearMap ∘ₗ aLin := by rw [hULin]
          _ = ext.toLinearMap ∘ₗ aLin := by rw [heEquivCoe]
          _ = bLin := hExtComp
          _ = Matrix.toEuclideanLin W := rfl
      exact (Matrix.toEuclideanLin (m := out) (n := inp)).injective hMap
    exact ⟨U, hUMem, hMul⟩

end Matrix
