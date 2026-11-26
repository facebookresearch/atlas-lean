/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedBimoduleTensor
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# Tensor functors on bounded finite-module localizations

For an associative ring `R`, localize bounded finite-module cochain complexes at their ambient
module quasi-isomorphisms. An `S`-left, `R`-right bimodule `E` finite over `S` and satisfying
`Tor¹_R(E,N)=0` for every left module `N` gives an exact tensor functor preserving these
morphisms. It therefore descends to the bounded localization, with a natural factorization
through the quotient functors.

Bimodule contractions `P ⊗_S Q ≅ R` and `Q ⊗_R P ≅ S` supply the finite and exact coefficients
for both directions. The bounded tensor return isomorphisms descend to an equivalence of the
two localizations, retaining the specified counit and its adjointified unit.

These localizations also have canonical functors to the ambient derived categories. The
bounded tensor square agrees with the ambient derived functor of exact tensor. Rings,
coefficients, and underived module carriers here use universe `u`; the two ambient derived-
category universes are independent.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Localization
open CategoryTheory.Functor

universe u wR wS

attribute [local instance] ModuleCat.BalancedTensor.Left.additive

namespace CochainComplex.Bounded

variable (R : Type u) [Ring R]

/-- Localization of bounded finite-module cochains.

For a ring `R`, localize `Bounded (FGModuleCat R)` at the morphisms that become quasi-
isomorphisms in the ambient module cochain category. This defines `FGModuleDerived R`. -/
abbrev FGModuleDerived := (fgModuleQuasiIsomorphisms R).Localization

/-- Localization functor for bounded finite-module cochains.

The functor from bounded finite-module cochains to `FGModuleDerived R` is the canonical
localization at ambient module quasi-isomorphisms. -/
abbrev fgModuleDerivedQ : Bounded (FGModuleCat.{u} R) ⥤ FGModuleDerived R :=
  (fgModuleQuasiIsomorphisms R).Q

variable {R}
variable {S : Type u} [Ring S]
  (E : Type u) [AddCommGroup E] [Module S E] [Module Rᵐᵒᵖ E]
  [SMulCommClass S Rᵐᵒᵖ E] [Module.Finite S E]
  (hE : ∀ N : ModuleCat.{u} R,
    IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj (ModuleCat.of Rᵐᵒᵖ E)).obj N))

/-- Exact finite-coefficient tensor preserves the bounded localizer.

Let `E` be an `S`-left, `R`-right bimodule finite over `S`, with `Tor¹_R(E,N)=0` for every
left `R`-module `N`. Tensoring bounded finite-module cochains by `E` preserves their ambient
quasi-isomorphisms and gives a localizer morphism. -/
abbrev bimoduleTensorLocalizer :
    LocalizerMorphism (fgModuleQuasiIsomorphisms R) (fgModuleQuasiIsomorphisms S) where
  functor := bimoduleTensor (R := R) (S := S) E
  map := bimoduleTensor_map_quasiIsomorphisms E hE

/-- Localized tensor functor on bounded finite-module cochains.

The exact left-finite coefficient tensor functor descends to `FGModuleDerived R ⥤
FGModuleDerived S` through the two localization functors. -/
abbrev bimoduleTensorDerived : FGModuleDerived R ⥤ FGModuleDerived S :=
  (bimoduleTensorLocalizer (R := R) (S := S) E hE).localizedFunctor
    (fgModuleDerivedQ R) (fgModuleDerivedQ S)

/-- Factorization data for localized bounded tensor.

The localized tensor functor has the canonical lifting data for the natural factorization `Q_R
⋙ D_E ≅ F_E ⋙ Q_S`, where `F_E` is bounded tensor by `E`. -/
instance bimoduleTensorDerivedLifting :
    Lifting (fgModuleDerivedQ R) (fgModuleQuasiIsomorphisms R)
      (bimoduleTensor (R := R) (S := S) E ⋙ fgModuleDerivedQ S)
      (bimoduleTensorDerived (S := S) E hE) :=
  LocalizerMorphism.liftingLocalizedFunctor
    (bimoduleTensorLocalizer (R := R) (S := S) E hE)
    (fgModuleDerivedQ R) (fgModuleDerivedQ S)

/-- Localized bounded tensor commutes with the localization functors.

There is a natural isomorphism `fgModuleDerivedQ R ⋙ bimoduleTensorDerived E ≅ bimoduleTensor
E ⋙ fgModuleDerivedQ S`. -/
def bimoduleTensorDerivedFactors :
    fgModuleDerivedQ R ⋙ bimoduleTensorDerived (S := S) E hE ≅
      bimoduleTensor (R := R) (S := S) E ⋙ fgModuleDerivedQ S :=
  Lifting.iso (fgModuleDerivedQ R) (fgModuleQuasiIsomorphisms R)
    (bimoduleTensor (R := R) (S := S) E ⋙ fgModuleDerivedQ S)
    (bimoduleTensorDerived (S := S) E hE)

/-- Bounded tensor localization factorization is natural in morphisms.

For a bounded finite-module cochain morphism `f : K ⟶ L`, the localized image of `f` followed
by the factorization component at `L` equals the component at `K` followed by localization of
its tensor image. -/
theorem bimoduleTensorDerivedFactors_hom_naturality
    {K L : Bounded (FGModuleCat.{u} R)} (f : K ⟶ L) :
    (bimoduleTensorDerived (S := S) E hE).map ((fgModuleDerivedQ R).map f) ≫
        (bimoduleTensorDerivedFactors E hE).hom.app L =
      (bimoduleTensorDerivedFactors E hE).hom.app K ≫
        (fgModuleDerivedQ S).map ((bimoduleTensor (S := S) E).map f) :=
  (bimoduleTensorDerivedFactors E hE).hom.naturality f

end CochainComplex.Bounded

namespace CochainComplex.Bounded

variable (R S P Q : Type u) [Ring R] [Ring S]
  [AddCommGroup P] [AddCommGroup Q]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  (a : letI := TensorProduct.Balanced.leftModule ℤ S R P Q
    letI := TensorProduct.Balanced.rightModule ℤ S R P Q
    TensorProduct.Balanced ℤ S P Q ≃ₗ[Rᵐᵒᵖ] R)
  (ha : letI := TensorProduct.Balanced.leftModule ℤ S R P Q
    letI := TensorProduct.Balanced.rightModule ℤ S R P Q
    ∀ (r : R) (x : TensorProduct.Balanced ℤ S P Q), a (r • x) = r * a x)
  (b : letI := TensorProduct.Balanced.leftModule ℤ R S Q P
    letI := TensorProduct.Balanced.rightModule ℤ R S Q P
    TensorProduct.Balanced ℤ R Q P ≃ₗ[Sᵐᵒᵖ] S)
  (hb : letI := TensorProduct.Balanced.leftModule ℤ R S Q P
    letI := TensorProduct.Balanced.rightModule ℤ R S Q P
    ∀ (s : S) (x : TensorProduct.Balanced ℤ R Q P), b (s • x) = s * b x)

local notation "eB" => bimoduleTensorMoritaEquivalence R S P Q a ha b hb

/-- Forward bounded Morita tensor functor preserves quasi-isomorphisms.

Given bimodule contractions `P ⊗_S Q ≅ R` and `Q ⊗_R P ≅ S`, the forward bounded finite-module
tensor equivalence, with coefficient `Q`, defines a localizer morphism from the `R` quasi-
isomorphisms to the `S` quasi-isomorphisms. -/
abbrev bimoduleTensorMoritaLocalizer :
    LocalizerMorphism (fgModuleQuasiIsomorphisms R) (fgModuleQuasiIsomorphisms S) where
  functor := (eB).functor
  map := bimoduleTensorMoritaEquivalence_map_quasiIsomorphisms R S P Q a ha b hb

/-- Inverse bounded Morita tensor functor preserves quasi-isomorphisms.

The inverse bounded tensor functor, with coefficient `P`, defines the localizer morphism in
the opposite direction, using the same invertible bimodule contractions. -/
abbrev bimoduleTensorMoritaInverseLocalizer :
    LocalizerMorphism (fgModuleQuasiIsomorphisms S) (fgModuleQuasiIsomorphisms R) where
  functor := (eB).inverse
  map := bimoduleTensorMoritaEquivalence_inverse_map_quasiIsomorphisms R S P Q a ha b hb

/-- Forward Morita tensor functor on bounded localizations.

Localize the forward bounded finite-module tensor functor to obtain `FGModuleDerived R ⥤
FGModuleDerived S`. -/
abbrev bimoduleTensorMoritaDerivedFunctor : FGModuleDerived R ⥤ FGModuleDerived S :=
  (bimoduleTensorMoritaLocalizer R S P Q a ha b hb).localizedFunctor
    (fgModuleDerivedQ R) (fgModuleDerivedQ S)

/-- Inverse Morita tensor functor on bounded localizations.

Localize the inverse bounded finite-module tensor functor to obtain `FGModuleDerived S ⥤
FGModuleDerived R`. -/
abbrev bimoduleTensorMoritaDerivedInverseFunctor : FGModuleDerived S ⥤ FGModuleDerived R :=
  (bimoduleTensorMoritaInverseLocalizer R S P Q a ha b hb).localizedFunctor
    (fgModuleDerivedQ S) (fgModuleDerivedQ R)

local notation "D" => bimoduleTensorMoritaDerivedFunctor R S P Q a ha b hb
local notation "D'" => bimoduleTensorMoritaDerivedInverseFunctor R S P Q a ha b hb

/-- Localization lifting data for forward Morita tensor.

The forward localized Morita tensor functor has the lifting data relating it to the forward
bounded tensor equivalence followed by localization in `S`. -/
instance bimoduleTensorMoritaDerivedFunctorLifting :
    Lifting (fgModuleDerivedQ R) (fgModuleQuasiIsomorphisms R)
      ((eB).functor ⋙ fgModuleDerivedQ S) D :=
  LocalizerMorphism.liftingLocalizedFunctor
    (bimoduleTensorMoritaLocalizer R S P Q a ha b hb)
    (fgModuleDerivedQ R) (fgModuleDerivedQ S)

/-- Localization lifting data for inverse Morita tensor.

The inverse localized Morita tensor functor has the lifting data relating it to the inverse
bounded tensor equivalence followed by localization in `R`. -/
instance bimoduleTensorMoritaDerivedInverseFunctorLifting :
    Lifting (fgModuleDerivedQ S) (fgModuleQuasiIsomorphisms S)
      ((eB).inverse ⋙ fgModuleDerivedQ R) D' :=
  LocalizerMorphism.liftingLocalizedFunctor
    (bimoduleTensorMoritaInverseLocalizer R S P Q a ha b hb)
    (fgModuleDerivedQ S) (fgModuleDerivedQ R)

/-- Forward Morita tensor commutes with bounded localization.

The forward localized functor composed after `Q_R` is naturally isomorphic to the forward
bounded tensor equivalence composed before `Q_S`. -/
def bimoduleTensorMoritaDerivedFactors :
    fgModuleDerivedQ R ⋙ D ≅ (eB).functor ⋙ fgModuleDerivedQ S :=
  Lifting.iso (fgModuleDerivedQ R) (fgModuleQuasiIsomorphisms R)
    ((eB).functor ⋙ fgModuleDerivedQ S) D

/-- Inverse Morita tensor commutes with bounded localization.

The inverse localized functor composed after `Q_S` is naturally isomorphic to the inverse
bounded tensor equivalence composed before `Q_R`. -/
def bimoduleTensorMoritaDerivedInverseFactors :
    fgModuleDerivedQ S ⋙ D' ≅ (eB).inverse ⋙ fgModuleDerivedQ R :=
  Lifting.iso (fgModuleDerivedQ S) (fgModuleQuasiIsomorphisms S)
    ((eB).inverse ⋙ fgModuleDerivedQ R) D'

local notation "qF" => bimoduleTensorMoritaDerivedFactors R S P Q a ha b hb
local notation "qG" => bimoduleTensorMoritaDerivedInverseFactors R S P Q a ha b hb

/-- R-return comparison for the localized Morita functors.

The forward bounded tensor functor, followed by localization in `S` and the inverse localized
functor, is naturally isomorphic to localization in `R`. The comparison combines the inverse-
functor factorization with the bounded equivalence's return isomorphism. -/
def bimoduleTensorMoritaDerivedLeftSourceIso :
    ((eB).functor ⋙ fgModuleDerivedQ S) ⋙ D' ≅ fgModuleDerivedQ R :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft (eB).functor qG ≪≫
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (eB).unitIso.symm (fgModuleDerivedQ R) ≪≫
        Functor.leftUnitor _

/-- S-return comparison for the localized Morita functors.

The inverse bounded tensor functor, followed by localization in `R` and the forward localized
functor, is naturally isomorphic to localization in `S`. -/
def bimoduleTensorMoritaDerivedRightSourceIso :
    ((eB).inverse ⋙ fgModuleDerivedQ R) ⋙ D ≅ fgModuleDerivedQ S :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft (eB).inverse qF ≪≫
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (eB).counitIso (fgModuleDerivedQ S) ≪≫
        Functor.leftUnitor _

/-- Morita equivalence of bounded finite-module localizations.

The two invertible bimodule contractions give an equivalence `FGModuleDerived R ≌
FGModuleDerived S`, with the forward and inverse localized tensor functors. -/
def bimoduleTensorMoritaDerivedEquivalence : FGModuleDerived R ≌ FGModuleDerived S :=
  Localization.equivalence
    (fgModuleDerivedQ R) (fgModuleQuasiIsomorphisms R)
    (fgModuleDerivedQ S) (fgModuleQuasiIsomorphisms S)
    ((eB).functor ⋙ fgModuleDerivedQ S) D
    ((eB).inverse ⋙ fgModuleDerivedQ R) D'
    (bimoduleTensorMoritaDerivedLeftSourceIso R S P Q a ha b hb)
    (bimoduleTensorMoritaDerivedRightSourceIso R S P Q a ha b hb)

/-- Forward functor of the bounded localized Morita equivalence.

The equivalence's forward functor is `bimoduleTensorMoritaDerivedFunctor R S P Q a ha b hb`. -/
theorem bimoduleTensorMoritaDerivedEquivalence_functor :
    (bimoduleTensorMoritaDerivedEquivalence R S P Q a ha b hb).functor = D := rfl

/-- Inverse functor of the bounded localized Morita equivalence.

The equivalence's inverse functor is `bimoduleTensorMoritaDerivedInverseFunctor R S P Q a ha b
hb`. -/
theorem bimoduleTensorMoritaDerivedEquivalence_inverse :
    (bimoduleTensorMoritaDerivedEquivalence R S P Q a ha b hb).inverse = D' := rfl

/-- Forward localized Morita functor is exact tensor by Q.

The forward localized Morita functor equals the localized tensor functor of `Q`, with its left
finiteness and right Tor-one vanishing obtained from the bimodule contractions. -/
theorem bimoduleTensorMoritaDerivedFunctor_eq :
    D = let H := ModuleCat.bimoduleTensorMorita_properties R S P Q a ha b hb
      letI : Module.Finite S Q := H.2.1
      bimoduleTensorDerived (R := R) (S := S) Q H.2.2.2 := rfl

/-- Inverse localized Morita functor is exact tensor by P.

The inverse localized Morita functor equals the localized tensor functor of `P`, using the
finiteness and Tor-one vanishing supplied by the contractions. -/
theorem bimoduleTensorMoritaDerivedInverseFunctor_eq :
    D' = let H := ModuleCat.bimoduleTensorMorita_properties R S P Q a ha b hb
      letI : Module.Finite R P := H.1
      bimoduleTensorDerived (R := S) (S := R) P H.2.2.1 := rfl

/-- Unit of the localized Morita equivalence is adjointified.

The unit is the adjointification of the localized inverse `R`-return comparison with the
localized `S`-return counit. Both return comparisons are lifted from the bounded tensor
equivalence through localization. -/
theorem bimoduleTensorMoritaDerivedEquivalence_unitIso :
    (bimoduleTensorMoritaDerivedEquivalence R S P Q a ha b hb).unitIso =
      Equivalence.adjointifyη
        (Localization.liftNatIso (fgModuleDerivedQ R) (fgModuleQuasiIsomorphisms R)
          (fgModuleDerivedQ R) (((eB).functor ⋙ fgModuleDerivedQ S) ⋙ D')
          (𝟭 (FGModuleDerived R)) (D ⋙ D')
          (bimoduleTensorMoritaDerivedLeftSourceIso R S P Q a ha b hb).symm)
        (Localization.liftNatIso (fgModuleDerivedQ S) (fgModuleQuasiIsomorphisms S)
          (((eB).inverse ⋙ fgModuleDerivedQ R) ⋙ D) (fgModuleDerivedQ S)
          (D' ⋙ D) (𝟭 (FGModuleDerived S))
          (bimoduleTensorMoritaDerivedRightSourceIso R S P Q a ha b hb)) := rfl

/-- Localized Morita counit on a bounded cochain image.

At `Q_S K`, the counit is the canonical lifting coordinate for the inverse-then-forward
composite, followed by the `S`-return source isomorphism at the bounded finite-module cochain
complex `K`. -/
theorem bimoduleTensorMoritaDerivedEquivalence_counitIso_app_Q
    (K : Bounded (FGModuleCat.{u} S)) :
    (bimoduleTensorMoritaDerivedEquivalence R S P Q a ha b hb).counitIso.app
        ((fgModuleDerivedQ S).obj K) =
      (Lifting.iso (fgModuleDerivedQ S) (fgModuleQuasiIsomorphisms S)
        (((eB).inverse ⋙ fgModuleDerivedQ R) ⋙ D) (D' ⋙ D)).app K ≪≫
        (bimoduleTensorMoritaDerivedRightSourceIso R S P Q a ha b hb).app K :=
  Localization.equivalence_counitIso_app _ _ _ _ _ _ _ _ _ _ K

end CochainComplex.Bounded

namespace ModuleCat

variable {R S : Type u} [Ring R] [Ring S]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
  [HasDerivedCategory.{wS} (ModuleCat.{u} S)]
  (E : Type u) [AddCommGroup E] [Module S E] [Module Rᵐᵒᵖ E]
  [SMulCommClass S Rᵐᵒᵖ E]
  (hE : ∀ N : ModuleCat.{u} R,
    IsZero (((BalancedTensor.torFirst R 1).obj (ModuleCat.of Rᵐᵒᵖ E)).obj N))

include hE

/-- Exact bimodule tensor functor on ambient derived categories.

For an `S`-left, `R`-right bimodule `E` with `Tor¹_R(E,-)=0`, the exact module tensor functor
induces a functor between the ambient derived categories, assuming both derived categories
exist in their chosen universes. -/
abbrev bimoduleTensorDerivedCategory :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S) := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let : PreservesFiniteLimits F := bimoduleTensor_preservesFiniteLimits_of_torFirst_one E hE
  let : PreservesFiniteColimits F := bimoduleTensor_preservesFiniteColimits E
  exact F.mapDerivedCategory

/-- Ambient derived tensor commutes with the derived-category quotient.

The ambient cochain tensor functor followed by the target derived-category quotient is
naturally isomorphic to the source quotient followed by the induced exact derived tensor
functor. -/
def bimoduleTensorDerivedCategoryFactors :
    DerivedCategory.Q ⋙ bimoduleTensorDerivedCategory (R := R) (S := S) E hE ≅
      bimoduleTensorCochain (R := R) (S := S) E ⋙ DerivedCategory.Q := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let : PreservesFiniteLimits F := bimoduleTensor_preservesFiniteLimits_of_torFirst_one E hE
  let : PreservesFiniteColimits F := bimoduleTensor_preservesFiniteColimits E
  exact F.mapDerivedCategoryFactors

/-- Exact ambient bimodule tensor gives a triangulated derived functor.

The functor on ambient derived categories induced by the exact bimodule tensor functor is
triangulated. -/
theorem bimoduleTensorDerivedCategory_isTriangulated :
    (bimoduleTensorDerivedCategory (R := R) (S := S) E hE).IsTriangulated := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let : PreservesFiniteLimits F := bimoduleTensor_preservesFiniteLimits_of_torFirst_one E hE
  let : PreservesFiniteColimits F := bimoduleTensor_preservesFiniteColimits E
  change F.mapDerivedCategory.IsTriangulated
  infer_instance

end ModuleCat

namespace CochainComplex.Bounded

variable (R : Type u) [Ring R] [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- Ambient derived quotient inverts bounded finite-module quasi-isomorphisms.

The inclusion of bounded finite-module cochains in ambient module cochains, followed by the
derived-category quotient, inverts their ambient quasi-isomorphisms. -/
theorem fgModuleAmbient_Q_inverts :
    (fgModuleQuasiIsomorphisms R).IsInvertedBy (fgModuleAmbient R ⋙ DerivedCategory.Q) := by
  intro K L f hf
  exact Localization.inverts DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
    ((fgModuleAmbient R).map f) hf

/-- Functor from bounded finite-module localization to the ambient derived category.

The ambient cochain inclusion followed by the derived quotient descends to a functor
`FGModuleDerived R ⥤ DerivedCategory (ModuleCat R)`. -/
abbrev fgModuleDerivedAmbient : FGModuleDerived R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Localization.lift (fgModuleAmbient R ⋙ DerivedCategory.Q)
    (fgModuleAmbient_Q_inverts R) (fgModuleDerivedQ R)

/-- Bounded localization to ambient derived factorization.

The bounded localization functor followed by `fgModuleDerivedAmbient R` is naturally
isomorphic to the ambient cochain inclusion followed by the derived-category quotient. -/
def fgModuleDerivedAmbientFactors :
    fgModuleDerivedQ R ⋙ fgModuleDerivedAmbient R ≅ fgModuleAmbient R ⋙ DerivedCategory.Q :=
  Lifting.iso (fgModuleDerivedQ R) (fgModuleQuasiIsomorphisms R)
    (fgModuleAmbient R ⋙ DerivedCategory.Q) (fgModuleDerivedAmbient R)

/-- Bounded-to-ambient derived factorization is natural in cochain maps.

For a bounded finite-module morphism, its localized image followed by the target factorization
component equals the source component followed by the ambient derived quotient of the
morphism. -/
theorem fgModuleDerivedAmbientFactors_hom_naturality
    {K L : Bounded (FGModuleCat.{u} R)} (f : K ⟶ L) :
    (fgModuleDerivedAmbient R).map ((fgModuleDerivedQ R).map f) ≫
        (fgModuleDerivedAmbientFactors R).hom.app L =
      (fgModuleDerivedAmbientFactors R).hom.app K ≫
        DerivedCategory.Q.map ((fgModuleAmbient R).map f) :=
  (fgModuleDerivedAmbientFactors R).hom.naturality f

variable {R}
variable {S : Type u} [Ring S] [HasDerivedCategory.{wS} (ModuleCat.{u} S)]
  (E : Type u) [AddCommGroup E] [Module S E] [Module Rᵐᵒᵖ E]
  [SMulCommClass S Rᵐᵒᵖ E] [Module.Finite S E]
  (hE : ∀ N : ModuleCat.{u} R,
    IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj (ModuleCat.of Rᵐᵒᵖ E)).obj N))

/-- Bounded localized tensor agrees with ambient derived tensor.

For a coefficient finite over `S` with vanishing right Tor one, localized bounded tensor
followed by the ambient derived functor in `S` is naturally isomorphic to the ambient derived
functor in `R` followed by exact ambient tensor. The two ambient derived-category universes
are independently chosen. -/
def bimoduleTensorDerivedAmbientIso :
    bimoduleTensorDerived (S := S) E hE ⋙ fgModuleDerivedAmbient S ≅
      fgModuleDerivedAmbient R ⋙ ModuleCat.bimoduleTensorDerivedCategory (S := S) E hE := by
  let B := bimoduleTensor (R := R) (S := S) E
  let T := ModuleCat.bimoduleTensorCochain (R := R) (S := S) E
  let DT := ModuleCat.bimoduleTensorDerivedCategory (R := R) (S := S) E hE
  let U₁ := B ⋙ fgModuleAmbient S ⋙ DerivedCategory.Q
  let U₂ := fgModuleAmbient R ⋙ T ⋙ DerivedCategory.Q
  let : Lifting (fgModuleDerivedQ R) (fgModuleQuasiIsomorphisms R) U₁
      (bimoduleTensorDerived (S := S) E hE ⋙ fgModuleDerivedAmbient S) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (bimoduleTensorDerivedFactors E hE) (fgModuleDerivedAmbient S) ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft B (fgModuleDerivedAmbientFactors S)⟩
  let : Lifting (fgModuleDerivedQ R) (fgModuleQuasiIsomorphisms R) U₂
      (fgModuleDerivedAmbient R ⋙ DT) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (fgModuleDerivedAmbientFactors R) DT ≪≫
        Functor.associator _ _ _ ≪≫
          isoWhiskerLeft (fgModuleAmbient R) (ModuleCat.bimoduleTensorDerivedCategoryFactors E hE)⟩
  let e : U₁ ≅ U₂ :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (bimoduleTensorAmbientIso (S := S) E) DerivedCategory.Q ≪≫
        Functor.associator _ _ _
  exact Localization.liftNatIso (fgModuleDerivedQ R) (fgModuleQuasiIsomorphisms R)
    U₁ U₂ _ _ e

end CochainComplex.Bounded

end
