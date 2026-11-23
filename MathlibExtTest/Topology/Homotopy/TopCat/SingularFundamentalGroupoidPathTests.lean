/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.TopCat.SingularFundamentalGroupoidPath

/-!
# Tests for singular fundamental-groupoid paths and endomorphisms

The matrix checks the explicit based object transport, edge characteristic,
both inverse cancellations, path laws, map naturality, and universes zero,
one, and symbolic.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory
open scoped Simplicial

namespace MathlibExtTest.Topology.Homotopy.TopCat
namespace SingularFundamentalGroupoidPathTests

section BasedEndomorphisms

variable (X : TopCat.{u}) (x : X)

example :
    CategoryTheory.End
        (SSet.FundamentalGroupoid.mk
          (TopCat.toSSetObj₀Equiv.symm x)) ≃*
      CategoryTheory.End (_root_.FundamentalGroupoid.mk x) :=
  TopCat.singularFundamentalGroupoidEndMulEquiv X x

example (q : CategoryTheory.End
    (SSet.FundamentalGroupoid.mk
      (TopCat.toSSetObj₀Equiv.symm x))) :
    (TopCat.singularFundamentalGroupoidEndMulEquiv X x).symm
        (TopCat.singularFundamentalGroupoidEndMulEquiv X x q) = q :=
  (TopCat.singularFundamentalGroupoidEndMulEquiv X x).symm_apply_apply q

example (q : CategoryTheory.End (_root_.FundamentalGroupoid.mk x)) :
    TopCat.singularFundamentalGroupoidEndMulEquiv X x
        ((TopCat.singularFundamentalGroupoidEndMulEquiv X x).symm q) = q :=
  (TopCat.singularFundamentalGroupoidEndMulEquiv X x).apply_symm_apply q

example (e : (TopCat.toSSet.obj X).Edge
    (TopCat.toSSetObj₀Equiv.symm x)
    (TopCat.toSSetObj₀Equiv.symm x)) :
    TopCat.singularFundamentalGroupoidEndMulEquiv X x
        (End.of (SSet.FundamentalGroupoid.homMk e)) =
      End.of (Path.Homotopic.Quotient.mk
        (TopCat.pathEquiv
          ((TopCat.toSSetObjEdgeEquiv (X := X) (x := x) (y := x)) e))) :=
  TopCat.singularFundamentalGroupoidEndMulEquiv_homMk X x e

end BasedEndomorphisms

section Paths

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  {x y z : X} (p : _root_.Path x y) (q : _root_.Path y z)

example :
    SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x) ⟶
      SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y) :=
  TopCat.singularPathHom X p

example :
    TopCat.singularPathHom X (_root_.Path.refl x) = 𝟙 _ :=
  TopCat.singularPathHom_refl X x

example :
    TopCat.singularPathHom X (p.trans q) =
      TopCat.singularPathHom X p ≫ TopCat.singularPathHom X q :=
  TopCat.singularPathHom_trans X p q

example :
    (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).map
        (TopCat.singularPathHom X p) =
      TopCat.singularPathHom Y (p.map f.hom.continuous) :=
  TopCat.singularPathHom_map f p

end Paths

section UniverseZero

variable (X : TopCat.{0}) (x : X)

example :
    CategoryTheory.End
        (SSet.FundamentalGroupoid.mk
          (TopCat.toSSetObj₀Equiv.symm x)) ≃*
      CategoryTheory.End (_root_.FundamentalGroupoid.mk x) :=
  TopCat.singularFundamentalGroupoidEndMulEquiv X x

end UniverseZero

section UniverseOne

variable (X : TopCat.{1}) (x : X)

example :
    CategoryTheory.End
        (SSet.FundamentalGroupoid.mk
          (TopCat.toSSetObj₀Equiv.symm x)) ≃*
      CategoryTheory.End (_root_.FundamentalGroupoid.mk x) :=
  TopCat.singularFundamentalGroupoidEndMulEquiv X x

end UniverseOne

#print axioms TopCat.singularFundamentalGroupoidEndMulEquiv
#print axioms TopCat.singularFundamentalGroupoidEndMulEquiv_homMk
#print axioms TopCat.singularPathHom
#print axioms TopCat.singularPathHom_refl
#print axioms TopCat.singularPathHom_trans
#print axioms TopCat.singularPathHom_map

end SingularFundamentalGroupoidPathTests
end MathlibExtTest.Topology.Homotopy.TopCat
