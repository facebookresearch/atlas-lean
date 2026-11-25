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
# Derived bounded bimodule tensor functors

The bounded derived category localizes bounded finite-module cochains at
ambient module quasi-isomorphisms. Exact tensor functors preserve this
localizer. Invertible bimodule contractions give bounded tensor functors
and their return isomorphisms, which descend to an equivalence.

The bounded cochains also map to the ambient derived category. Their tensor
comparison is induced by the exact derived functor and ambient tensor
square.
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

/-- Localize the original bounded finite-module category at its ambient quasi-isomorphisms. -/
abbrev FGModuleDerived := (fgModuleQuasiIsomorphisms R).Localization

/-- The canonical original bounded-derived localization functor. -/
abbrev fgModuleDerivedQ : Bounded (FGModuleCat.{u} R) ⥤ FGModuleDerived R :=
  (fgModuleQuasiIsomorphisms R).Q

variable {R}
variable {S : Type u} [Ring S]
  (E : Type u) [AddCommGroup E] [Module S E] [Module Rᵐᵒᵖ E]
  [SMulCommClass S Rᵐᵒᵖ E] [Module.Finite S E]
  (hE : ∀ N : ModuleCat.{u} R,
    IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj (ModuleCat.of Rᵐᵒᵖ E)).obj N))

/-- Earn the bounded localizer morphism from the original right-flatness input. -/
abbrev bimoduleTensorLocalizer :
    LocalizerMorphism (fgModuleQuasiIsomorphisms R) (fgModuleQuasiIsomorphisms S) where
  functor := bimoduleTensor (R := R) (S := S) E
  map := bimoduleTensor_map_quasiIsomorphisms E hE

/-- Descend that same actual bounded tensor through the canonical localization. -/
abbrev bimoduleTensorDerived : FGModuleDerived R ⥤ FGModuleDerived S :=
  (bimoduleTensorLocalizer (R := R) (S := S) E hE).localizedFunctor
    (fgModuleDerivedQ R) (fgModuleDerivedQ S)

/-- Register the canonical lifting for this original bounded tensor, without new comparison data. -/
instance bimoduleTensorDerivedLifting :
    Lifting (fgModuleDerivedQ R) (fgModuleQuasiIsomorphisms R)
      (bimoduleTensor (R := R) (S := S) E ⋙ fgModuleDerivedQ S)
      (bimoduleTensorDerived (S := S) E hE) :=
  LocalizerMorphism.liftingLocalizedFunctor
    (bimoduleTensorLocalizer (R := R) (S := S) E hE)
    (fgModuleDerivedQ R) (fgModuleDerivedQ S)

/-- The original-Q square relates the actual tensor lift to the same original bounded functor. -/
def bimoduleTensorDerivedFactors :
    fgModuleDerivedQ R ⋙ bimoduleTensorDerived (S := S) E hE ≅
      bimoduleTensor (R := R) (S := S) E ⋙ fgModuleDerivedQ S :=
  Lifting.iso (fgModuleDerivedQ R) (fgModuleQuasiIsomorphisms R)
    (bimoduleTensor (R := R) (S := S) E ⋙ fgModuleDerivedQ S)
    (bimoduleTensorDerived (S := S) E hE)

/-- Every original bounded morphism enters the derived tensor through the same original-Q square. -/
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

/-- Original contractions earn the localizer morphism of the forward bounded Morita tensor. -/
abbrev bimoduleTensorMoritaLocalizer :
    LocalizerMorphism (fgModuleQuasiIsomorphisms R) (fgModuleQuasiIsomorphisms S) where
  functor := (eB).functor
  map := bimoduleTensorMoritaEquivalence_map_quasiIsomorphisms R S P Q a ha b hb

/-- The original inverse bounded tensor earns its actual inverse localizer morphism. -/
abbrev bimoduleTensorMoritaInverseLocalizer :
    LocalizerMorphism (fgModuleQuasiIsomorphisms S) (fgModuleQuasiIsomorphisms R) where
  functor := (eB).inverse
  map := bimoduleTensorMoritaEquivalence_inverse_map_quasiIsomorphisms R S P Q a ha b hb

/-- The actual forward tensor functor on the original bounded-derived model. -/
abbrev bimoduleTensorMoritaDerivedFunctor : FGModuleDerived R ⥤ FGModuleDerived S :=
  (bimoduleTensorMoritaLocalizer R S P Q a ha b hb).localizedFunctor
    (fgModuleDerivedQ R) (fgModuleDerivedQ S)

/-- The actual inverse tensor functor on that same original bounded-derived model. -/
abbrev bimoduleTensorMoritaDerivedInverseFunctor : FGModuleDerived S ⥤ FGModuleDerived R :=
  (bimoduleTensorMoritaInverseLocalizer R S P Q a ha b hb).localizedFunctor
    (fgModuleDerivedQ S) (fgModuleDerivedQ R)

local notation "D" => bimoduleTensorMoritaDerivedFunctor R S P Q a ha b hb
local notation "D'" => bimoduleTensorMoritaDerivedInverseFunctor R S P Q a ha b hb

/-- The original forward Morita tensor uses the canonical localizer lifting data. -/
instance bimoduleTensorMoritaDerivedFunctorLifting :
    Lifting (fgModuleDerivedQ R) (fgModuleQuasiIsomorphisms R)
      ((eB).functor ⋙ fgModuleDerivedQ S) D :=
  LocalizerMorphism.liftingLocalizedFunctor
    (bimoduleTensorMoritaLocalizer R S P Q a ha b hb)
    (fgModuleDerivedQ R) (fgModuleDerivedQ S)

/-- The original inverse Morita tensor uses the same canonical inverse lifting construction. -/
instance bimoduleTensorMoritaDerivedInverseFunctorLifting :
    Lifting (fgModuleDerivedQ S) (fgModuleQuasiIsomorphisms S)
      ((eB).inverse ⋙ fgModuleDerivedQ R) D' :=
  LocalizerMorphism.liftingLocalizedFunctor
    (bimoduleTensorMoritaInverseLocalizer R S P Q a ha b hb)
    (fgModuleDerivedQ S) (fgModuleDerivedQ R)

/-- The original forward-Q factorization uses the actual bounded Morita tensor. -/
def bimoduleTensorMoritaDerivedFactors :
    fgModuleDerivedQ R ⋙ D ≅ (eB).functor ⋙ fgModuleDerivedQ S :=
  Lifting.iso (fgModuleDerivedQ R) (fgModuleQuasiIsomorphisms R)
    ((eB).functor ⋙ fgModuleDerivedQ S) D

/-- The original inverse-Q factorization uses the actual bounded inverse tensor. -/
def bimoduleTensorMoritaDerivedInverseFactors :
    fgModuleDerivedQ S ⋙ D' ≅ (eB).inverse ⋙ fgModuleDerivedQ R :=
  Lifting.iso (fgModuleDerivedQ S) (fgModuleQuasiIsomorphisms S)
    ((eB).inverse ⋙ fgModuleDerivedQ R) D'

local notation "qF" => bimoduleTensorMoritaDerivedFactors R S P Q a ha b hb
local notation "qG" => bimoduleTensorMoritaDerivedInverseFactors R S P Q a ha b hb

/-- The actual left return before localization is the original bounded Morita unit inverse. -/
def bimoduleTensorMoritaDerivedLeftSourceIso :
    ((eB).functor ⋙ fgModuleDerivedQ S) ⋙ D' ≅ fgModuleDerivedQ R :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft (eB).functor qG ≪≫
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (eB).unitIso.symm (fgModuleDerivedQ R) ≪≫
        Functor.leftUnitor _

/-- The actual right return before localization is the original bounded Morita counit. -/
def bimoduleTensorMoritaDerivedRightSourceIso :
    ((eB).inverse ⋙ fgModuleDerivedQ R) ⋙ D ≅ fgModuleDerivedQ S :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft (eB).inverse qF ≪≫
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (eB).counitIso (fgModuleDerivedQ S) ≪≫
        Functor.leftUnitor _

/-- The canonical localization descends both original tensors and both original return families. -/
def bimoduleTensorMoritaDerivedEquivalence : FGModuleDerived R ≌ FGModuleDerived S :=
  Localization.equivalence
    (fgModuleDerivedQ R) (fgModuleQuasiIsomorphisms R)
    (fgModuleDerivedQ S) (fgModuleQuasiIsomorphisms S)
    ((eB).functor ⋙ fgModuleDerivedQ S) D
    ((eB).inverse ⋙ fgModuleDerivedQ R) D'
    (bimoduleTensorMoritaDerivedLeftSourceIso R S P Q a ha b hb)
    (bimoduleTensorMoritaDerivedRightSourceIso R S P Q a ha b hb)

/-- Its entire forward functor is the actual localized original bounded Q tensor. -/
theorem bimoduleTensorMoritaDerivedEquivalence_functor :
    (bimoduleTensorMoritaDerivedEquivalence R S P Q a ha b hb).functor = D := rfl

/-- Its entire inverse is the actual localized original bounded P tensor. -/
theorem bimoduleTensorMoritaDerivedEquivalence_inverse :
    (bimoduleTensorMoritaDerivedEquivalence R S P Q a ha b hb).inverse = D' := rfl

/-- Original contraction properties identify the whole forward lift with Q's right-flat tensor. -/
theorem bimoduleTensorMoritaDerivedFunctor_eq :
    D = let H := ModuleCat.bimoduleTensorMorita_properties R S P Q a ha b hb
      letI : Module.Finite S Q := H.2.1
      bimoduleTensorDerived (R := R) (S := S) Q H.2.2.2 := rfl

/-- Original contraction properties identify the whole inverse lift with P's right-flat tensor. -/
theorem bimoduleTensorMoritaDerivedInverseFunctor_eq :
    D' = let H := ModuleCat.bimoduleTensorMorita_properties R S P Q a ha b hb
      letI : Module.Finite R P := H.1
      bimoduleTensorDerived (R := S) (S := R) P H.2.2.1 := rfl

/-- The chosen unit is the canonical refinement of the two original localized return families. -/
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

/-- The original localized counit is evaluated on the original bounded-complex representative. -/
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

/-- Right flatness earns the canonical derived functor of the original ambient module tensor. -/
abbrev bimoduleTensorDerivedCategory :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S) := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let : PreservesFiniteLimits F := bimoduleTensor_preservesFiniteLimits_of_torFirst_one E hE
  let : PreservesFiniteColimits F := bimoduleTensor_preservesFiniteColimits E
  exact F.mapDerivedCategory

/-- The standard ambient original-Q square is the canonical exact-functor factorization. -/
def bimoduleTensorDerivedCategoryFactors :
    DerivedCategory.Q ⋙ bimoduleTensorDerivedCategory (R := R) (S := S) E hE ≅
      bimoduleTensorCochain (R := R) (S := S) E ⋙ DerivedCategory.Q := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := BalancedTensor.Left.functor ℤ R S E
  let : PreservesFiniteLimits F := bimoduleTensor_preservesFiniteLimits_of_torFirst_one E hE
  let : PreservesFiniteColimits F := bimoduleTensor_preservesFiniteColimits E
  exact F.mapDerivedCategoryFactors

/-- The actual ambient derived tensor is triangulated by the canonical exact-functor theorem. -/
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

/-- The original bounded ambient inclusion inverts exactly the weak maps used by this model. -/
theorem fgModuleAmbient_Q_inverts :
    (fgModuleQuasiIsomorphisms R).IsInvertedBy (fgModuleAmbient R ⋙ DerivedCategory.Q) := by
  intro K L f hf
  exact Localization.inverts DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
    ((fgModuleAmbient R).map f) hf

/-- Factor the original bounded cochains into the standard ambient derived category. -/
abbrev fgModuleDerivedAmbient : FGModuleDerived R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Localization.lift (fgModuleAmbient R ⋙ DerivedCategory.Q)
    (fgModuleAmbient_Q_inverts R) (fgModuleDerivedQ R)

/-- The entire original bounded-Q ambient square is the canonical localization factorization. -/
def fgModuleDerivedAmbientFactors :
    fgModuleDerivedQ R ⋙ fgModuleDerivedAmbient R ≅ fgModuleAmbient R ⋙ DerivedCategory.Q :=
  Lifting.iso (fgModuleDerivedQ R) (fgModuleQuasiIsomorphisms R)
    (fgModuleAmbient R ⋙ DerivedCategory.Q) (fgModuleDerivedAmbient R)

/-- Every original bounded cochain morphism is retained in the actual ambient derived square. -/
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

/-- The actual bounded tensor factorization commutes with the canonical ambient derived tensor. -/
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
