/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_WeierstrassCurve_GenusOnePic0.lean`
`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import MathlibExt.AlgebraicGeometry.Curve.DivisorClassGroup

@[expose] public section

/-!
# Genus-one place gate and the point class equivalence
-/

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F]

variable (W : Affine F) in

class GenusOnePlaceGate : Type u where

  pointEquivPlace : W.Point ≃ AlgebraicCurve.Place F W.FunctionField

  deg_eq_one : ∀ v : AlgebraicCurve.Place F W.FunctionField, v.deg = 1

variable {W : Affine F} [GenusOnePlaceGate W]

abbrev pointEquivPlace : W.Point ≃ AlgebraicCurve.Place F W.FunctionField :=
  GenusOnePlaceGate.pointEquivPlace (W := W)

def placeOfPoint : W.Point → AlgebraicCurve.Place F W.FunctionField :=
  pointEquivPlace (W := W)

@[simp]
theorem pointEquivPlace_apply (P : W.Point) :
    (pointEquivPlace (W := W)) P = placeOfPoint P := rfl

@[simp]
theorem pointEquivPlace_symm_placeOfPoint (P : W.Point) :
    (pointEquivPlace (W := W)).symm (placeOfPoint P) = P :=
  (pointEquivPlace (W := W)).symm_apply_apply P

theorem deg_eq_one (v : AlgebraicCurve.Place F W.FunctionField) : v.deg = 1 :=
  GenusOnePlaceGate.deg_eq_one v

@[simp]
theorem deg_placeOfPoint (P : W.Point) : (placeOfPoint (W := W) P).deg = 1 :=
  deg_eq_one _

theorem degree_eq_sum (D : AlgebraicCurve.Divisor F W.FunctionField) :
    Divisor.degree D = D.sum fun _ n => n := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply]
  exact Finsupp.sum_congr fun v _ => by
    rw [AddMonoidHom.mulRight_apply, deg_eq_one v, Nat.cast_one, mul_one]

def divisorSum : AlgebraicCurve.Divisor F W.FunctionField →+ W.Point :=
  Finsupp.liftAddHom fun v => zmultiplesHom W.Point ((pointEquivPlace (W := W)).symm v)

@[simp]
theorem divisorSum_single (v : AlgebraicCurve.Place F W.FunctionField) (n : ℤ) :
    divisorSum (Finsupp.single v n) = n • (pointEquivPlace (W := W)).symm v :=
  Finsupp.liftAddHom_apply_single _ v n

theorem divisorSum_single_placeOfPoint (P : W.Point) (n : ℤ) :
    divisorSum (Finsupp.single (placeOfPoint P) n) = n • P := by
  rw [divisorSum_single, pointEquivPlace_symm_placeOfPoint]

def pointDivisor (P : W.Point) : Divisor.degZero (K := F) (F := W.FunctionField) :=
  ⟨Finsupp.single (placeOfPoint P) 1 - Finsupp.single (placeOfPoint (0 : W.Point)) 1, by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single,
      deg_placeOfPoint, deg_placeOfPoint, sub_self]⟩

@[simp]
theorem coe_pointDivisor (P : W.Point) :
    (pointDivisor P : AlgebraicCurve.Divisor F W.FunctionField)
      = Finsupp.single (placeOfPoint P) 1 - Finsupp.single (placeOfPoint (0 : W.Point)) 1 :=
  rfl

@[simp]
theorem pointDivisor_zero : pointDivisor (0 : W.Point) = 0 :=
  Subtype.ext (sub_self _)

theorem divisorSum_pointDivisor (P : W.Point) :
    divisorSum (pointDivisor P : AlgebraicCurve.Divisor F W.FunctionField) = P := by
  rw [coe_pointDivisor, map_sub, divisorSum_single_placeOfPoint, divisorSum_single_placeOfPoint,
    one_smul, one_smul, sub_zero]

def pointClass (P : W.Point) : AlgebraicCurve.Pic0 F W.FunctionField :=
  Pic0.mk (pointDivisor P)

@[simp]
theorem pointClass_zero : pointClass (0 : W.Point) = 0 := by
  rw [pointClass, pointDivisor_zero, Pic0.mk_zero]

variable (W) in

class AbelTheorem : Prop where

  isPrincipal_iff_divisorSum_eq_zero :
    ∀ D : AlgebraicCurve.Divisor F W.FunctionField, Divisor.degree D = 0 →
      (Divisor.IsPrincipal D ↔ divisorSum D = 0)

section AbelTheorem

variable [AbelTheorem W]

theorem divisorSum_eq_zero_of_isPrincipal {D : AlgebraicCurve.Divisor F W.FunctionField}
    (h0 : Divisor.degree D = 0) (hD : Divisor.IsPrincipal D) : divisorSum D = 0 :=
  (AbelTheorem.isPrincipal_iff_divisorSum_eq_zero D h0).mp hD

theorem isPrincipal_of_divisorSum_eq_zero {D : AlgebraicCurve.Divisor F W.FunctionField}
    (h0 : Divisor.degree D = 0) (hD : divisorSum D = 0) : Divisor.IsPrincipal D :=
  (AbelTheorem.isPrincipal_iff_divisorSum_eq_zero D h0).mpr hD

def pic0ToPoint : AlgebraicCurve.Pic0 F W.FunctionField →+ W.Point :=
  QuotientAddGroup.lift _
    (divisorSum.comp (Divisor.degZero (K := F) (F := W.FunctionField)).subtype)
    (by
      rintro ⟨D, hD0⟩ hD
      rw [AddSubgroup.mem_addSubgroupOf] at hD
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype]
      exact divisorSum_eq_zero_of_isPrincipal (Divisor.mem_degZero.mp hD0)
        (Divisor.mem_principal.mp hD))

@[simp]
theorem pic0ToPoint_mk (D : Divisor.degZero (K := F) (F := W.FunctionField)) :
    pic0ToPoint (Pic0.mk D) = divisorSum (D : AlgebraicCurve.Divisor F W.FunctionField) :=
  rfl

@[simp]
theorem pic0ToPoint_pointClass (P : W.Point) : pic0ToPoint (pointClass P) = P := by
  rw [pointClass, pic0ToPoint_mk, divisorSum_pointDivisor]

theorem pic0ToPoint_surjective : Function.Surjective (pic0ToPoint (W := W)) := fun P =>
  ⟨pointClass P, pic0ToPoint_pointClass P⟩

theorem pic0ToPoint_injective : Function.Injective (pic0ToPoint (W := W)) := by
  rw [injective_iff_map_eq_zero]
  intro c
  induction c using QuotientAddGroup.induction_on with
  | H D =>
    intro hD
    obtain ⟨D, hD0⟩ := D
    replace hD : divisorSum D = 0 := hD
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact Divisor.mem_principal.mpr
      (isPrincipal_of_divisorSum_eq_zero (Divisor.mem_degZero.mp hD0) hD)

variable (W) in

def genusOnePic0Equiv : AlgebraicCurve.Pic0 F W.FunctionField ≃+ W.Point :=
  AddEquiv.ofBijective pic0ToPoint ⟨pic0ToPoint_injective, pic0ToPoint_surjective⟩

@[simp]
theorem genusOnePic0Equiv_apply (c : AlgebraicCurve.Pic0 F W.FunctionField) :
    genusOnePic0Equiv W c = pic0ToPoint c := rfl

@[simp]
theorem genusOnePic0Equiv_symm_apply (P : W.Point) :
    (genusOnePic0Equiv W).symm P = pointClass P :=
  (genusOnePic0Equiv W).injective (by
    rw [AddEquiv.apply_symm_apply, genusOnePic0Equiv_apply, pic0ToPoint_pointClass])

theorem pointClass_add (P Q : W.Point) :
    pointClass (P + Q) = pointClass P + pointClass Q := by
  rw [← genusOnePic0Equiv_symm_apply, ← genusOnePic0Equiv_symm_apply,
    ← genusOnePic0Equiv_symm_apply, ← map_add]

end AbelTheorem

end WeierstrassCurve.Affine

end
