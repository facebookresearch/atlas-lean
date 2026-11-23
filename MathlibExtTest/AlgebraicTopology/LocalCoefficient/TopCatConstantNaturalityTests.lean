/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatConstantNaturality

/-!
# Tests for constant local-coefficient naturality on TopCat

These clients pin the direction of the constant pullback comparison and the
chain- and homology-level squares.  Identity and nonidentity interval maps
exercise the same map-first orientation at concrete boundaries.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe uR uX

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.TopCatConstantNaturalityTests

section Generic

variable {R : Type uR} [CommRing R]
variable {X Y : TopCat.{uX}} (f : X ⟶ Y)
variable (M : ModuleCat.{max uR uX} R)

example :
    (TopCat.constantLocalSystem (X := Y) M).pullback f ≅
      TopCat.constantLocalSystem (X := X) M :=
  TopCat.LocalSystem.constantPullbackIso f M

example (x : _root_.FundamentalGroupoid X) :
    (TopCat.LocalSystem.constantPullbackIso f M).hom.app x = 𝟙 M :=
  TopCat.LocalSystem.constantPullbackIso_hom_app f M x

example (x : _root_.FundamentalGroupoid X) :
    (TopCat.LocalSystem.constantPullbackIso f M).inv.app x = 𝟙 M :=
  TopCat.LocalSystem.constantPullbackIso_inv_app f M x

example :
    TopCat.localCoefficientPullbackChainMap f
          (TopCat.constantLocalSystem (X := Y) M) ≫
        (TopCat.constantLocalCoefficientChainIso (X := Y) M).hom =
      SSet.localCoefficientChainMap
            (TopCat.LocalSystem.toSingularMap
              (TopCat.LocalSystem.constantPullbackIso f M).hom) ≫
        (TopCat.constantLocalCoefficientChainIso (X := X) M).hom ≫
        ((AlgebraicTopology.singularChainComplexFunctor
          (ModuleCat.{max uR uX} R)).obj M).map f :=
  TopCat.ConstantNaturality.chainMap f M

example (n : ℕ) :
    TopCat.localCoefficientPullbackHomologyMap f
          (TopCat.constantLocalSystem (X := Y) M) n ≫
        (TopCat.constantLocalCoefficientHomologyIso (X := Y) M n).hom =
      TopCat.localCoefficientHomologyMap
            (TopCat.LocalSystem.constantPullbackIso f M).hom n ≫
        (TopCat.constantLocalCoefficientHomologyIso (X := X) M n).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor
          (ModuleCat.{max uR uX} R) n).obj M).map f :=
  TopCat.ConstantNaturality.homologyMap f M n

end Generic

section IdentityMap

variable {R : Type uR} [CommRing R]
variable (X : TopCat.{uX}) (M : ModuleCat.{max uR uX} R)

example :
    TopCat.localCoefficientPullbackChainMap (𝟙 X)
          (TopCat.constantLocalSystem (X := X) M) ≫
        (TopCat.constantLocalCoefficientChainIso (X := X) M).hom =
      SSet.localCoefficientChainMap
            (TopCat.LocalSystem.toSingularMap
              (TopCat.LocalSystem.constantPullbackIso (𝟙 X) M).hom) ≫
        (TopCat.constantLocalCoefficientChainIso (X := X) M).hom ≫
        ((AlgebraicTopology.singularChainComplexFunctor
          (ModuleCat.{max uR uX} R)).obj M).map (𝟙 X) :=
  TopCat.ConstantNaturality.chainMap (𝟙 X) M

end IdentityMap

section NonidentityIntervalMap

private noncomputable def collapse : TopCat.I ⟶ TopCat.I :=
  TopCat.const (X := TopCat.I) (0 : TopCat.I)

example : collapse (1 : TopCat.I) = 0 := rfl

variable {R : Type uR} [CommRing R]
variable (M : ModuleCat.{uR} R)

example (n : ℕ) :
    TopCat.localCoefficientPullbackHomologyMap collapse
          (TopCat.constantLocalSystem (X := TopCat.I) M) n ≫
        (TopCat.constantLocalCoefficientHomologyIso
          (X := TopCat.I) M n).hom =
      TopCat.localCoefficientHomologyMap
            (TopCat.LocalSystem.constantPullbackIso collapse M).hom n ≫
        (TopCat.constantLocalCoefficientHomologyIso
          (X := TopCat.I) M n).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor
          (ModuleCat.{uR} R) n).obj M).map collapse :=
  TopCat.ConstantNaturality.homologyMap collapse M n

end NonidentityIntervalMap

section RaisedUniverses

variable (R : Type 1) [CommRing R]
variable {X Y : TopCat.{2}} (f : X ⟶ Y)
variable (M : ModuleCat.{2} R)

example :
    TopCat.localCoefficientPullbackChainMap f
          (TopCat.constantLocalSystem (X := Y) M) ≫
        (TopCat.constantLocalCoefficientChainIso (X := Y) M).hom =
      SSet.localCoefficientChainMap
            (TopCat.LocalSystem.toSingularMap
              (TopCat.LocalSystem.constantPullbackIso f M).hom) ≫
        (TopCat.constantLocalCoefficientChainIso (X := X) M).hom ≫
        ((AlgebraicTopology.singularChainComplexFunctor
          (ModuleCat.{2} R)).obj M).map f :=
  TopCat.ConstantNaturality.chainMap f M

end RaisedUniverses

#print axioms TopCat.LocalSystem.constantPullbackIso
#print axioms TopCat.ConstantNaturality.chainMap
#print axioms TopCat.ConstantNaturality.homologyMap

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.TopCatConstantNaturalityTests
