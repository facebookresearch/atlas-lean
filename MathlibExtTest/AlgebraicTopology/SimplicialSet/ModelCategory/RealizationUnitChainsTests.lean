/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationUnitChains
import Mathlib.Data.Matrix.Mul

/-!
# Tests for chains of the realization--singular unit

The canonical unit theorem is exercised on empty, representable,
disconnected, and non-Kan simplicial sets, with zero and noncommutative-ring
coefficients and at the supported universe boundaries.  Negative controls
prevent an `IsIso`, Kan-source, arbitrary-map, or commutative-ring
strengthening from being inferred.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory
namespace RealizationUnitChainsTests

section PublicContract

variable {R : Type u} [Ring R] (A : ModuleCat.{u} R) (X : SSet.{u})

example :
    QuasiIso
      (SSet.chainComplexMap (sSetTopAdj.unit.app X) A) :=
  SSet.quasiIso_chainComplexMap_sSetTopAdj_unit_app A X

end PublicContract

section ConcreteSpaces

private abbrev emptySSet : SSet.{u} :=
  (⊥ : (Δ[0] : SSet.{u}).Subcomplex)

private abbrev twoPointSSet : SSet.{u} :=
  (Δ[0] : SSet.{u}) ⨿ (Δ[0] : SSet.{u})

variable {R : Type u} [Ring R] (A : ModuleCat.{u} R)

example :
    QuasiIso
      (SSet.chainComplexMap
        (sSetTopAdj.unit.app emptySSet.{u}) A) :=
  SSet.quasiIso_chainComplexMap_sSetTopAdj_unit_app A emptySSet

example :
    QuasiIso
      (SSet.chainComplexMap
        (sSetTopAdj.unit.app (Δ[0] : SSet.{u})) A) :=
  SSet.quasiIso_chainComplexMap_sSetTopAdj_unit_app A Δ[0]

example :
    QuasiIso
      (SSet.chainComplexMap
        (sSetTopAdj.unit.app (Δ[1] : SSet.{u})) A) :=
  SSet.quasiIso_chainComplexMap_sSetTopAdj_unit_app A Δ[1]

example :
    QuasiIso
      (SSet.chainComplexMap
        (sSetTopAdj.unit.app (Δ[2] : SSet.{u})) A) :=
  SSet.quasiIso_chainComplexMap_sSetTopAdj_unit_app A Δ[2]

example :
    QuasiIso
      (SSet.chainComplexMap
        (sSetTopAdj.unit.app twoPointSSet.{u}) A) :=
  SSet.quasiIso_chainComplexMap_sSetTopAdj_unit_app A twoPointSSet

end ConcreteSpaces

section NonKanSource

/-- The standard simplicial circle is deliberately not supplied with a Kan
instance; the canonical unit theorem nevertheless applies. -/
example :
    QuasiIso
      (SSet.chainComplexMap
        (sSetTopAdj.unit.app SSet.S1)
        (ModuleCat.of ℤ ℤ)) :=
  SSet.quasiIso_chainComplexMap_sSetTopAdj_unit_app
    (ModuleCat.of ℤ ℤ) SSet.S1

example : True := by
  fail_if_success let _ : SSet.KanComplex SSet.S1 := inferInstance
  trivial

end NonKanSource

section Coefficients

variable {R : Type u} [Ring R]

example (X : SSet.{u}) :
    QuasiIso
      (SSet.chainComplexMap
        (sSetTopAdj.unit.app X) (⊥_ (ModuleCat.{u} R))) :=
  SSet.quasiIso_chainComplexMap_sSetTopAdj_unit_app
    (⊥_ (ModuleCat.{u} R)) X

private abbrev MatrixRing := Matrix (Fin 2) (Fin 2) ℤ

example : True := by
  fail_if_success let _ : CommRing MatrixRing := inferInstance
  trivial

example :
    QuasiIso
      (SSet.chainComplexMap
        (sSetTopAdj.unit.app (Δ[2] : SSet.{0}))
        (ModuleCat.of MatrixRing MatrixRing)) :=
  SSet.quasiIso_chainComplexMap_sSetTopAdj_unit_app
    (ModuleCat.of MatrixRing MatrixRing) Δ[2]

/-- The existing coefficient naturality square is reused without adding a
unit-specific wrapper. -/
example {A B : ModuleCat.{u} R} (a : A ⟶ B) (X : SSet.{u}) :
    SSet.chainComplexMap (sSetTopAdj.unit.app X) A ≫
        ((SSet.chainComplexFunctor (ModuleCat.{u} R)).map a).app
          (TopCat.toSSet.obj (SSet.toTop.obj X)) =
      ((SSet.chainComplexFunctor (ModuleCat.{u} R)).map a).app X ≫
        SSet.chainComplexMap (sSetTopAdj.unit.app X) B :=
  ((SSet.chainComplexFunctor (ModuleCat.{u} R)).map a).naturality
    (sSetTopAdj.unit.app X)

end Coefficients

section ExplicitUniverses

example {R : Type 1} [Ring R] (A : ModuleCat.{1} R) (X : SSet.{1}) :
    QuasiIso
      (SSet.chainComplexMap (sSetTopAdj.unit.app X) A) :=
  SSet.quasiIso_chainComplexMap_sSetTopAdj_unit_app A X

example {R : Type} [Ring R] (A : ModuleCat.{0} R) (X : SSet.{0}) :
    QuasiIso
      (SSet.chainComplexMap (sSetTopAdj.unit.app X) A) :=
  SSet.quasiIso_chainComplexMap_sSetTopAdj_unit_app A X

end ExplicitUniverses

section NegativeControls

private abbrev emptyToPoint :
    emptySSet.{0} ⟶ (Δ[0] : SSet.{0}) :=
  (⊥ : (Δ[0] : SSet.{0}).Subcomplex).ι

example : True := by
  fail_if_success
    let _ := inferInstanceAs
      (QuasiIso
        (SSet.chainComplexMap emptyToPoint (ModuleCat.of ℤ ℤ)))
  trivial

example (_X : SSet.{u}) : True := by
  fail_if_success
    let _ := inferInstanceAs (IsIso (sSetTopAdj.unit.app _X))
  trivial

end NegativeControls

#print axioms SSet.quasiIso_chainComplexMap_sSetTopAdj_unit_app

end RealizationUnitChainsTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory
