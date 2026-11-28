/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.KoszulComplexFamily
public import Mathlib.Data.ZMod.Basic

/-!
# Finite-family Koszul signs over a ring with zero divisors

The family `(3, 2)` over `ZMod 6` has top boundary `4e₀ + 3e₁`.
The ordered standard wedge gives a nonzero boundary, and its next boundary
is zero by the actual coefficient functional. The index type is lifted
to universe one while the coefficients remain in universe zero.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace KoszulFamilyZeroDivisorSigns

private abbrev R := ZMod 6

private abbrev I := ULift.{1} (Fin 2)

private abbrev M := I → R

private abbrev i0 : I := ULift.up 0

private abbrev i1 : I := ULift.up 1

private def a (i : I) : R := if i.down = 0 then 3 else 2

private theorem a_i0 : a i0 = 3 := by decide

private theorem a_i1 : a i1 = 2 := by decide

private abbrev φ := KoszulComplex.familyFunctional R a

private abbrev K : ChainComplex (ModuleCat.{1} R) ℕ := KoszulComplex.familyComplex R a

private def top : K.X 2 := by
  change ⋀[R]^2 M
  exact exteriorPower.ιMulti R 2 (fun j : Fin 2 => (Pi.single (ULift.up j) 1 : M))

private def boundary : K.X 1 := (K.d 2 1).hom top

private theorem boundary_vector :
    exteriorPower.oneEquiv R M boundary =
      (4 : R) • (Pi.single i0 1 : M) + (3 : R) • (Pi.single i1 1 : M) := by
  have hd : K.d 2 1 = ModuleCat.ofHom (KoszulComplex.differential R M φ 1) :=
    KoszulComplex.complex_d_succ R M φ 1
  rw [boundary, hd]
  change exteriorPower.oneEquiv R M
    (KoszulComplex.differential R M φ 1
      (exteriorPower.ιMulti R 2 (fun j : Fin 2 => (Pi.single (ULift.up j) 1 : M)))) = _
  rw [KoszulComplex.familyDifferential_apply_basis R a 1 (fun j => ULift.up j),
    Fin.sum_univ_two]
  have h0 : (0 : Fin 2).succAbove (0 : Fin 1) = 1 := by decide
  have h1 : (1 : Fin 2).succAbove (0 : Fin 1) = 0 := by decide
  simp only [map_add, map_smul, exteriorPower.oneEquiv_ιMulti,
    Fin.val_zero, pow_zero, one_mul, Fin.val_one, pow_one, h0, h1, a_i0, a_i1]
  rw [show (-1 : R) * 2 = 4 from by decide]
  exact add_comm _ _

private theorem boundary_coordinate_zero :
    (exteriorPower.oneEquiv R M boundary) i0 = 4 := by
  rw [boundary_vector]
  simp [Pi.single_apply, i0, i1, smul_eq_mul]

private theorem boundary_coordinate_one :
    (exteriorPower.oneEquiv R M boundary) i1 = 3 := by
  rw [boundary_vector]
  simp [Pi.single_apply, i0, i1, smul_eq_mul]

private theorem boundary_nonzero : boundary ≠ 0 := by
  intro hzero
  have h := congrArg (fun z : K.X 1 => (exteriorPower.oneEquiv R M z) i1) hzero
  rw [boundary_coordinate_one] at h
  simp only [map_zero, Pi.zero_apply] at h
  change (3 : R) = 0 at h
  exact (by decide : (3 : R) ≠ 0) h

private theorem next_boundary_zero : (K.d 1 0).hom boundary = 0 := by
  have hd : K.d 1 0 = ModuleCat.ofHom (KoszulComplex.differential R M φ 0) :=
    KoszulComplex.complex_d_succ R M φ 0
  rw [hd]
  apply (exteriorPower.zeroEquiv R M).injective
  change exteriorPower.zeroEquiv R M (KoszulComplex.differential R M φ 0 boundary) =
    exteriorPower.zeroEquiv R M (0 : ⋀[R]^0 M)
  rw [(exteriorPower.zeroEquiv R M).map_zero]
  have h := LinearMap.congr_fun (KoszulComplex.differential_zero_equiv R M φ) boundary
  change exteriorPower.zeroEquiv R M (KoszulComplex.differential R M φ 0 boundary) =
    φ (exteriorPower.oneEquiv R M boundary) at h
  change exteriorPower.zeroEquiv R M (KoszulComplex.differential R M φ 0 boundary) = 0
  rw [h, boundary_vector]
  change KoszulComplex.familyFunctional R a
    ((4 : R) • (Pi.single i0 1 : M) + (3 : R) • (Pi.single i1 1 : M)) = 0
  simp only [map_add, map_smul, KoszulComplex.familyFunctional_single, a_i0, a_i1,
    smul_eq_mul]
  decide

example : (3 : R) ≠ 0 ∧ (2 : R) ≠ 0 ∧ (3 : R) * 2 = 0 := by decide

example : (exteriorPower.oneEquiv R M boundary) i0 = 4 := boundary_coordinate_zero

example : (exteriorPower.oneEquiv R M boundary) i1 = 3 := boundary_coordinate_one

example : boundary ≠ 0 := boundary_nonzero

example : (K.d 1 0).hom boundary = 0 := next_boundary_zero

end KoszulFamilyZeroDivisorSigns
