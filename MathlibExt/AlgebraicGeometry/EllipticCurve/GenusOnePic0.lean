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
public import MathlibExt.AlgebraicGeometry.Curve.PointDifference

@[expose] public section

/-!
# Genus-one place gate and the point class equivalence

For an affine Weierstrass curve `W` over a field `F`, this file builds an additive isomorphism
`genusOnePic0Equiv W : Pic0 F W.FunctionField ≃+ W.Point` from two hypothesis classes:

* `GenusOnePlaceGate W` supplies a bijection `pointEquivPlace` from the points of `W` to the places
  of its function field over `F`, together with the condition that every place has degree one;
* `AbelTheorem W` supplies Abel's criterion relative to that bijection: a divisor of degree zero is
  principal exactly when the points attached to its places sum to zero with multiplicities.

Both are hypotheses, and an instance has to supply the bijection and the criterion. The intended
setting is an elliptic curve over an algebraically closed field, with each point sent to the place
centred at it. That centring condition is `GenusOnePlaceGate.IsCentred`, in
`MathlibExt.AlgebraicGeometry.EllipticCurve.GenusOnePlaceGateCentred`, and the declarations here do
not assume it: `divisorSum`, `pointClass` and `genusOnePic0Equiv` depend on the chosen bijection.
For the centred bijection, `AbelTheorem` is Abel's theorem in genus one (Silverman, *The Arithmetic
of Elliptic Curves*, Corollary III.3.5) and `genusOnePic0Equiv` is the isomorphism of Proposition
III.3.4 there, whose inverse sends a point `P` to the class of `(P) - (0)`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F]

variable (W : Affine F) in
/-- **Genus-one place gate.** A hypothesis on an affine Weierstrass curve `W` over `F`: a bijection
`pointEquivPlace` from the points of `W` to the places of its function field over `F`, and the
condition `deg_eq_one` that every place has degree one. The bijection is data, and nothing in the
class ties it to the geometry of `W`; `GenusOnePlaceGate.IsCentred` is the condition that does. The
intended instance is an elliptic curve over an algebraically closed field `F`, with each point sent
to the place centred at it. When `F` is algebraically closed and `IsCurveOver F W.FunctionField`
holds, `deg_eq_one` follows from `AlgebraicCurve.IsCurveOver.forall_deg_eq_one_of_isAlgClosed`. -/
class GenusOnePlaceGate : Type u where
  /-- The chosen bijection from the points of `W` to the places of its function field. -/
  pointEquivPlace : W.Point ≃ AlgebraicCurve.Place F W.FunctionField
  deg_eq_one : ∀ v : AlgebraicCurve.Place F W.FunctionField, v.deg = 1

section Gate

variable {W : Affine F} [GenusOnePlaceGate W]

/-- The bijection from the points of `W` to the places of its function field chosen by
`GenusOnePlaceGate W`. -/
abbrev pointEquivPlace : W.Point ≃ AlgebraicCurve.Place F W.FunctionField :=
  GenusOnePlaceGate.pointEquivPlace (W := W)

/-- The place that the chosen bijection `pointEquivPlace` attaches to a point. Under
`GenusOnePlaceGate.IsCentred` an affine point `(x, y)` goes to the place centred at `(x, y)`;
without it nothing relates the place to the point. -/
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

/-- Degree one forces the residue field to be finite over `F`. -/
instance GenusOnePlaceGate.instFiniteResidueField (v : AlgebraicCurve.Place F W.FunctionField) :
    Module.Finite F v.ResidueField :=
  Module.finite_of_finrank_pos (by
    have h : Module.finrank F v.ResidueField = 1 := deg_eq_one (W := W) v
    omega)

theorem degree_eq_sum (D : AlgebraicCurve.Divisor F W.FunctionField) :
    Divisor.degree D = D.sum fun _ n => n := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply]
  exact Finsupp.sum_congr fun v _ => by
    rw [AddMonoidHom.mulRight_apply, deg_eq_one v, Nat.cast_one, mul_one]

/-- The divisor `(P) - (0)` of a point `P`, where `0` is the point at infinity, formed from the
places that the chosen bijection `pointEquivPlace` attaches to `P` and to `0`. It has degree zero
because every place has degree one. -/
def pointDivisor (P : W.Point) : Divisor.degZero (K := F) (F := W.FunctionField) :=
  ⟨CurveDivisor.pointDiff (placeOfPoint P) (placeOfPoint 0),
    (Divisor.pointDiff_mem_degZero_iff _ _).mpr (by rw [deg_placeOfPoint, deg_placeOfPoint])⟩

@[simp]
theorem coe_pointDivisor (P : W.Point) :
    (pointDivisor P : AlgebraicCurve.Divisor F W.FunctionField)
      = Finsupp.single (placeOfPoint P) 1 - Finsupp.single (placeOfPoint (0 : W.Point)) 1 :=
  rfl

@[simp]
theorem pointDivisor_zero : pointDivisor (0 : W.Point) = 0 :=
  Subtype.ext (CurveDivisor.pointDiff_self _)

/-- The class of `pointDivisor P` in `Pic0`. Like `pointDivisor`, it depends on the chosen
bijection `pointEquivPlace`. -/
def pointClass (P : W.Point) : AlgebraicCurve.Pic0 F W.FunctionField :=
  Pic0.mk (pointDivisor P)

@[simp]
theorem pointClass_zero : pointClass (0 : W.Point) = 0 := by
  rw [pointClass, pointDivisor_zero, Pic0.mk_zero]

end Gate

variable [DecidableEq F] {W : Affine F} [GenusOnePlaceGate W]

/-- The sum map from divisors to points: it sends a divisor `D` to `∑ᵥ D v • Pᵥ`, where `Pᵥ` is the
point that the chosen bijection `pointEquivPlace` attaches to the place `v`. It depends on that
choice. -/
def divisorSum : AlgebraicCurve.Divisor F W.FunctionField →+ W.Point :=
  Finsupp.liftAddHom fun v => zmultiplesHom W.Point ((pointEquivPlace (W := W)).symm v)

@[simp]
theorem divisorSum_single (v : AlgebraicCurve.Place F W.FunctionField) (n : ℤ) :
    divisorSum (Finsupp.single v n) = n • (pointEquivPlace (W := W)).symm v :=
  Finsupp.liftAddHom_apply_single _ v n

theorem divisorSum_single_placeOfPoint (P : W.Point) (n : ℤ) :
    divisorSum (Finsupp.single (placeOfPoint P) n) = n • P := by
  rw [divisorSum_single, pointEquivPlace_symm_placeOfPoint]

theorem divisorSum_pointDivisor (P : W.Point) :
    divisorSum (pointDivisor P : AlgebraicCurve.Divisor F W.FunctionField) = P := by
  rw [coe_pointDivisor, map_sub, divisorSum_single_placeOfPoint, divisorSum_single_placeOfPoint,
    one_smul, one_smul, sub_zero]

variable (W) in
/-- **Abel's criterion, as a hypothesis.** A divisor of degree zero is principal exactly when
`divisorSum` sends it to `0`, that is, when the points that the chosen bijection attaches to its
places sum to zero with multiplicities. For an elliptic curve with the centred bijection
(`GenusOnePlaceGate.IsCentred`) this is Abel's theorem in genus one (Silverman, *The Arithmetic of
Elliptic Curves*, Corollary III.3.5); relative to another bijection it is a separate assumption.
Equivalently, `divisorSum` descends to `Pic0` and the induced map `pic0ToPoint` is injective. -/
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

/-- `divisorSum` on divisors of degree zero, which Abel's criterion lets descend to `Pic0`. It
depends on the chosen bijection `pointEquivPlace`. -/
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
  intro c hc
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  exact (Pic0.mk_eq_zero_iff D).mpr
    (isPrincipal_of_divisorSum_eq_zero (Divisor.mem_degZero.mp D.2) hc)

variable (W) in
/-- **Genus-one `Pic0` as the group of points, under the two hypotheses.** The additive isomorphism
`Pic0 F W.FunctionField ≃+ W.Point` induced by `GenusOnePlaceGate W` and `AbelTheorem W`: it sends
the class of a divisor `D` of degree zero to `divisorSum D`, and its inverse is `pointClass`
(`genusOnePic0Equiv_symm_apply`). It depends on the chosen bijection `pointEquivPlace`. For an
elliptic curve over an algebraically closed field with the centred bijection
(`GenusOnePlaceGate.IsCentred`), it is the isomorphism of Silverman, *The Arithmetic of Elliptic
Curves*, Proposition III.3.4. -/
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
