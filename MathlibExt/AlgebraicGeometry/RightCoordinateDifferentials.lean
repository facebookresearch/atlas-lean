/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RightDifferentialModules
public import Mathlib.RingTheory.Derivation.Basic

/-!
# The actual coordinate and derivative operators on right D-modules

A coordinate system consists of a compatible coefficient section and its
actual natural derivation, normalized by partial(t)=1. Both operators are
constructed in the original finite-order differential-operator presheaf.
The right Euler operator is partial*t+alpha, using the original operator
composition and the native right module action.

Source: Saito1307.2140v5, Sections1.4,2.1 and2.4; the right-module
index convention is the nilpotence of partial*t+alpha on grV^alpha.
Native derivations are Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679,
Apache2.0, Kenny Lau and the Mathlib contributors.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RightCoordinateDifferentials

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open DifferentialOperatorSheaves DifferentialOperatorScalars RightDifferentialModules
open MathlibExt.RingTheory.GeometricDifferentialOperators

variable (k : Type) [CommRing k] (M : Type) [TopologicalSpace M]
  (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)

/-- An actual coefficient coordinate and its natural coefficient derivation. -/
structure CoordinateDerivation where
  function : ∀ U : Opens M, O.obj (op U)
  restrictFunction : ∀ (U V : Opens M) (h : V ≤ U),
    (O.map (homOfLE h).op).hom (function U) = function V
  derivative : ∀ U : Opens M, Derivation k (O.obj (op U)) (O.obj (op U))
  restrictDerivative : ∀ (U V : Opens M) (h : V ≤ U),
    (restrictionLinear k M O h).comp (derivative U).toLinearMap =
      (derivative V).toLinearMap.comp (restrictionLinear k M O h)
  coordinate : ∀ U : Opens M, derivative U (function U) = 1

/-- A genuine coefficient derivation is an order-one differential operator. -/
theorem derivation_order_one (A : Type) [CommRing A] [Algebra k A]
    (d : Derivation k A A) : OrderLE k A 1 d.toLinearMap := by
  intro a b x
  change d (a * (b * x)) - a * d (b * x) = b * (d (a * x) - a * d x)
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

/-- The partial derivative acts naturally on every subopen of the coordinate chart. -/
def derivativeNatural (C : CoordinateDerivation k M O) (U : Opens M) :
    naturalOperators k M O U :=
  ⟨fun V ↦ (C.derivative V.val).toLinearMap,
    fun V W h ↦ C.restrictDerivative V.val W.val h⟩

/-- The original finite-order operator containing that actual natural derivative. -/
def partialFinite (C : CoordinateDerivation k M O) (U : Opens M) :
    finiteOperatorRing k M O U :=
  ⟨derivativeNatural k M O C U, Subring.subset_closure
    ⟨1, fun V ↦ derivation_order_one k (O.obj (op V.val)) (C.derivative V.val)⟩⟩

/-- Multiplication by the actual coordinate section. -/
def coordinateFinite (C : CoordinateDerivation k M O) (U : Opens M) :
    finiteOperatorRing k M O U := scalarFinite k M O U (C.function U)

/-- The coordinate multiplication law retains the original coefficient restrictions. -/
theorem coordinateFinite_apply (C : CoordinateDerivation k M O) (U : Opens M)
    (V : Inside M U) (x : O.obj (op V.val)) :
    (coordinateFinite k M O C U).val.val V x = C.function V.val * x := by
  change (O.map (homOfLE V.property).op).hom (C.function U) * x = _
  rw [C.restrictFunction U V.val V.property]

/-- The Weyl relation is proved in the actual local differential-operator ring. -/
theorem partial_coordinate_weyl (C : CoordinateDerivation k M O) (U : Opens M) :
    partialFinite k M O C U * coordinateFinite k M O C U -
      coordinateFinite k M O C U * partialFinite k M O C U = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro x
  change C.derivative V.val ((coordinateFinite k M O C U).val.val V x) -
    (coordinateFinite k M O C U).val.val V (C.derivative V.val x) = x
  rw [coordinateFinite_apply, coordinateFinite_apply]
  simp only [Derivation.leibniz, C.coordinate V.val, smul_eq_mul, mul_one]
  ring

/-- The right Euler operator has the source sign and multiplication order. -/
def eulerFinite (C : CoordinateDerivation k M O) (U : Opens M) (a : k) :
    finiteOperatorRing k M O U :=
  partialFinite k M O C U * coordinateFinite k M O C U +
    scalarFinite k M O U (algebraMap k (O.obj (op U)) a)

variable [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]

/-- Right multiplication by t is the native opposite-ring action of the coefficient operator. -/
def rightCoordinate (C : CoordinateDerivation k M O) (N : RightModule k M O)
    (U : Opens M) (s : N.val.obj (op U)) : N.val.obj (op U) :=
  rightAct k M O N U (coordinateFinite k M O C U) s

/-- Right multiplication by partial is the native action of the same order-one operator. -/
def rightPartial (C : CoordinateDerivation k M O) (N : RightModule k M O)
    (U : Opens M) (s : N.val.obj (op U)) : N.val.obj (op U) :=
  rightAct k M O N U (partialFinite k M O C U) s

/-- The source right Euler action is s*(partial*t+alpha). -/
def rightEuler (C : CoordinateDerivation k M O) (N : RightModule k M O)
    (U : Opens M) (a : k) (s : N.val.obj (op U)) : N.val.obj (op U) :=
  rightAct k M O N U (eulerFinite k M O C U a) s

/-- The partial*t term acts first by partial and then by t, as required for right modules. -/
theorem right_partial_coordinate (C : CoordinateDerivation k M O)
    (N : RightModule k M O) (U : Opens M) (s : N.val.obj (op U)) :
    rightAct k M O N U (partialFinite k M O C U * coordinateFinite k M O C U) s =
      rightCoordinate k M O C N U (rightPartial k M O C N U s) :=
  rightAct_mul k M O N U (partialFinite k M O C U) (coordinateFinite k M O C U) s

end MathlibExt.AlgebraicGeometry.RightCoordinateDifferentials
