/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.Monoidal.Universe
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Monoidal.Tor

/-!
# Compatibility of module tensor across carrier universes

When the ring and coefficient universes coincide, the tensor object and
map functor agree with the Mathlib tensor functor. The unit is identified
by its module equivalence, and deriving this tensor functor gives the
same Tor functor.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory

universe u
namespace ModuleCat.UniverseTensor

/-- The larger tensor uses the SAME original tensor functor when both
original carriers are in the ring universe. -/
theorem curriedTensor_sameUniverse (R : Type u) [CommRing R] :
    (letI : MonoidalCategory (ModuleCat.{u} R) := monoidalCategory.{u,0};
      curriedTensor (ModuleCat.{u} R)) =
      (letI : MonoidalCategory (ModuleCat.{u} R) := ModuleCat.monoidalCategory;
        curriedTensor (ModuleCat.{u} R)) := rfl

/-- The actual tensoring-left functor agrees with the explicitly bound
original Mathlib tensoring-left functor at the original native universe. -/
theorem tensoringLeft_sameUniverse (R : Type u) [CommRing R] :
    (letI : MonoidalCategory (ModuleCat.{u} R) := monoidalCategory.{u,0};
      tensoringLeft (ModuleCat.{u} R)) =
      (letI : MonoidalCategory (ModuleCat.{u} R) := ModuleCat.monoidalCategory;
        tensoringLeft (ModuleCat.{u} R)) := rfl

/-- The original tensor unit has its canonical actual module isomorphism. -/
def tensorUnitSameUniverseIso (R : Type u) [CommRing R] :
    ModuleCat.of R (ULift.{0} R) ≅ ModuleCat.of R R :=
  (ULift.moduleEquiv : ULift.{0} R ≃ₗ[R] R).toModuleIso

/-- The larger tensor gives the SAME original native Tor functor when
the original ring and module carrier universes coincide. -/
theorem nativeTor_sameUniverse (R : Type u) [CommRing R] (q : ℕ) :
    (letI : MonoidalCategory (ModuleCat.{u} R) := monoidalCategory.{u,0};
      letI : MonoidalPreadditive (ModuleCat.{u} R) := monoidalPreadditive.{u,0};
      Tor (ModuleCat.{u} R) q) =
      (letI : MonoidalCategory (ModuleCat.{u} R) := ModuleCat.monoidalCategory;
        letI : MonoidalPreadditive (ModuleCat.{u} R) := ModuleCat.instMonoidalPreadditive;
        Tor (ModuleCat.{u} R) q) := rfl

end ModuleCat.UniverseTensor
