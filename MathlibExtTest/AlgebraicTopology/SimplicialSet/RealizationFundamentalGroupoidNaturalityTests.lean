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

import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationFundamentalGroupoidNaturality

/-!
# Realization fundamental-groupoid naturality tests

These tests pin the two functors, the mapped-vertex equality direction, and
the source/target equality transports in edge naturality.  Identity and
composite simplicial maps instantiate the same comparison without claiming
extra coherence between comparison isomorphisms.

Negative checks guard against a strict definitional equality, a global
`IsEquivalence` instance, or undeclared strict identity/composition laws.
-/

noncomputable section

open CategoryTheory Simplicial
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace RealizationFundamentalGroupoidNaturalityTests

variable (X Y : SSet.{u}) (f : X ⟶ Y)

/-- The public comparison has exactly the expected forward orientation. -/
example :
    SSet.mapFundamentalGroupoid f ⋙
        SSet.realizationFundamentalGroupoidFunctor Y ≅
      SSet.realizationFundamentalGroupoidFunctor X ⋙
        _root_.FundamentalGroupoid.map (SSet.toTop.map f).hom :=
  SSet.realizationFundamentalGroupoidNaturality f

/-- At a vertex, direct realization of its image equals the image of its
direct realization. -/
example (x : X _⦋0⦌) :
    (SSet.mapFundamentalGroupoid f ⋙
      SSet.realizationFundamentalGroupoidFunctor Y).obj
        (SSet.FundamentalGroupoid.mk x) =
    (SSet.realizationFundamentalGroupoidFunctor X ⋙
      _root_.FundamentalGroupoid.map (SSet.toTop.map f).hom).obj
        (SSet.FundamentalGroupoid.mk x) :=
  SSet.realizationFundamentalGroupoidNaturality_obj_mk_eq f x

/-- The component is the equality isomorphism in that same direction. -/
example (x : X _⦋0⦌) :
    (SSet.realizationFundamentalGroupoidNaturality f).hom.app
        (SSet.FundamentalGroupoid.mk x) =
      eqToHom
        (SSet.realizationFundamentalGroupoidNaturality_obj_mk_eq f x) :=
  SSet.realizationFundamentalGroupoidNaturality_app_mk f x

/-- Edge naturality uses the target component on the left and the source
component on the right. -/
example {x y : X _⦋0⦌} (e : X.Edge x y) :
    (SSet.mapFundamentalGroupoid f ⋙
        SSet.realizationFundamentalGroupoidFunctor Y).map
          (SSet.FundamentalGroupoid.homMk e) ≫
      eqToHom
        (SSet.realizationFundamentalGroupoidNaturality_obj_mk_eq f y) =
    eqToHom
        (SSet.realizationFundamentalGroupoidNaturality_obj_mk_eq f x) ≫
      (SSet.realizationFundamentalGroupoidFunctor X ⋙
        _root_.FundamentalGroupoid.map
          (SSet.toTop.map f).hom).map
            (SSet.FundamentalGroupoid.homMk e) := by
  simpa only [SSet.realizationFundamentalGroupoidNaturality_app_mk] using
    SSet.realizationFundamentalGroupoidNaturality_hom_naturality_homMk f e

/-- Identity maps use the same equality-isomorphism construction; no strict
identity comparison law is asserted. -/
example (x : X _⦋0⦌) :
    (SSet.realizationFundamentalGroupoidNaturality (𝟙 X)).hom.app
        (SSet.FundamentalGroupoid.mk x) =
      eqToHom
        (SSet.realizationFundamentalGroupoidNaturality_obj_mk_eq (𝟙 X) x) :=
  SSet.realizationFundamentalGroupoidNaturality_app_mk (𝟙 X) x

variable (Z : SSet.{u}) (g : Y ⟶ Z)

/-- Composite maps have the direct `f ≫ g` comparison orientation. -/
example (x : X _⦋0⦌) :
    (SSet.realizationFundamentalGroupoidNaturality (f ≫ g)).hom.app
        (SSet.FundamentalGroupoid.mk x) =
      eqToHom
        (SSet.realizationFundamentalGroupoidNaturality_obj_mk_eq
          (f ≫ g) x) :=
  SSet.realizationFundamentalGroupoidNaturality_app_mk (f ≫ g) x

/-- The two object images are propositionally, not definitionally, equal. -/
example (_x : X _⦋0⦌) : True := by
  fail_if_success
    exact (rfl :
        (SSet.mapFundamentalGroupoid f ⋙
          SSet.realizationFundamentalGroupoidFunctor Y).obj
            (SSet.FundamentalGroupoid.mk _x) =
        (SSet.realizationFundamentalGroupoidFunctor X ⋙
          _root_.FundamentalGroupoid.map (SSet.toTop.map f).hom).obj
            (SSet.FundamentalGroupoid.mk _x))
  trivial

/-- This module installs no global realization equivalence instance. -/
example : True := by
  fail_if_success
    exact inferInstanceAs
      ((SSet.realizationFundamentalGroupoidFunctor X).IsEquivalence)
  trivial

#guard_msgs (error, substring := true) in
#check SSet.realizationFundamentalGroupoidNaturality_id

#guard_msgs (error, substring := true) in
#check SSet.realizationFundamentalGroupoidNaturality_comp

section UniverseZero

variable (X0 Y0 : SSet.{0}) (f0 : X0 ⟶ Y0)

/-- The comparison elaborates in universe zero. -/
example :
    SSet.mapFundamentalGroupoid f0 ⋙
        SSet.realizationFundamentalGroupoidFunctor Y0 ≅
      SSet.realizationFundamentalGroupoidFunctor X0 ⋙
        _root_.FundamentalGroupoid.map (SSet.toTop.map f0).hom :=
  SSet.realizationFundamentalGroupoidNaturality f0

end UniverseZero

section UniverseOne

variable (X1 Y1 : SSet.{1}) (f1 : X1 ⟶ Y1)

/-- The same comparison elaborates one universe higher. -/
example :
    SSet.mapFundamentalGroupoid f1 ⋙
        SSet.realizationFundamentalGroupoidFunctor Y1 ≅
      SSet.realizationFundamentalGroupoidFunctor X1 ⋙
        _root_.FundamentalGroupoid.map (SSet.toTop.map f1).hom :=
  SSet.realizationFundamentalGroupoidNaturality f1

end UniverseOne

end RealizationFundamentalGroupoidNaturalityTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet
