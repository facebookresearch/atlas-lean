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
# Tensor and Tor compatibility in the ring's carrier universe

Let R be a commutative ring in universe u and take R-module carriers in that same universe.
Specializing the coefficient-universe tensor construction to zero additional lift height gives
the ordinary module tensor bifunctor and tensoring-left functor, with the same objects and
morphisms.

Its copied tensor unit has the canonical linear isomorphism to R. Deriving the tensoring
functors therefore gives the same Tor bifunctor in every homological degree q∈ℕ. These
identities describe the specialization at the ring's own carrier universe.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory

universe u
namespace ModuleCat.UniverseTensor

/-- For a commutative ring R in universe u and R-modules with carriers in u, the curried tensor
bifunctor from the coefficient-universe construction at additional height zero equals the
ordinary module tensor bifunctor. The equality includes the tensor objects M⊗_R N and all maps
f⊗g. -/
theorem curriedTensor_sameUniverse (R : Type u) [CommRing R] :
    (letI : MonoidalCategory (ModuleCat.{u} R) := monoidalCategory.{u,0};
      curriedTensor (ModuleCat.{u} R)) =
      (letI : MonoidalCategory (ModuleCat.{u} R) := ModuleCat.monoidalCategory;
        curriedTensor (ModuleCat.{u} R)) := rfl

/-- Let R be commutative in universe u and all coefficient carriers lie in u. The
zero-additional-height tensoring-left functor equals the ordinary module tensoring-left functor:
it sends M to N↦M⊗_R N and coefficient morphisms to their tensor natural transformations. -/
theorem tensoringLeft_sameUniverse (R : Type u) [CommRing R] :
    (letI : MonoidalCategory (ModuleCat.{u} R) := monoidalCategory.{u,0};
      tensoringLeft (ModuleCat.{u} R)) =
      (letI : MonoidalCategory (ModuleCat.{u} R) := ModuleCat.monoidalCategory;
        tensoringLeft (ModuleCat.{u} R)) := rfl

/-- For a commutative ring R in universe u, the copied tensor-unit module R̃ at additional lift
height zero is canonically R-linearly isomorphic to the scalar module R. The forward map removes
the copy tag and the inverse inserts it; both preserve addition and scalar multiplication. -/
def tensorUnitSameUniverseIso (R : Type u) [CommRing R] :
    ModuleCat.of R (ULift.{0} R) ≅ ModuleCat.of R R :=
  (ULift.moduleEquiv : ULift.{0} R ≃ₗ[R] R).toModuleIso

/-- Let R be commutative in universe u and q∈ℕ. On R-modules with carriers in u, Tor_q obtained from
the coefficient-universe tensor structure at additional height zero equals the ordinary Tor_q
bifunctor. This is equality of the derived tensor functors, including both object values and
coefficient maps. -/
theorem nativeTor_sameUniverse (R : Type u) [CommRing R] (q : ℕ) :
    (letI : MonoidalCategory (ModuleCat.{u} R) := monoidalCategory.{u,0};
      letI : MonoidalPreadditive (ModuleCat.{u} R) := monoidalPreadditive.{u,0};
      Tor (ModuleCat.{u} R) q) =
      (letI : MonoidalCategory (ModuleCat.{u} R) := ModuleCat.monoidalCategory;
        letI : MonoidalPreadditive (ModuleCat.{u} R) := ModuleCat.instMonoidalPreadditive;
        Tor (ModuleCat.{u} R) q) := rfl

end ModuleCat.UniverseTensor
