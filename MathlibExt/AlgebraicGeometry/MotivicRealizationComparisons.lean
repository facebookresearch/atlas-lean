/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicEilenbergMacLaneModels
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# The reduced-free and Dold--Kan motivic comparison

The comparison evaluates the actual reduced-free simplices, applies the
native normalized Moore functor and Dold--Kan counit, and then includes the
native good truncation in the resolved coefficient complex. In the derived
category it uses the inverse of the *specified augmentation*, with the
native compatibility of the localization and shift. No cohomology
isomorphism is supplied to define this map.

Termwise injectivity is kept separate from K-injectivity. The stronger
injective Nisnevich fibrancy assertion needs this refinement of the
published resolution source.

Sources: Voevodsky, arXiv:math/0107109v1, Section 2, pp. 3--6;
Mazza--Voevodsky--Weibel, Lectures 3 and 14. Dold--Kan and reduced free
modules retain their Mathlib/Tau Ceti Apache source credits in the imports.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicRealizationComparisons

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open FiniteTransferCycleModels FiniteTransferProductModels
open NisnevichTransferModels MotivicStandardSchemes
open EffectiveMotivicComplexModels PointedMotivicModels
open ReducedMotivicCohomologyModels MotivicEilenbergMacLaneModels
open MathlibExt.SpectraSource
open scoped Simplicial ZeroObject

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]

/-- Reduced-free Nisnevich simplicial modules before normalized chains. -/
def reducedSimplicialFunctor (F : ReducedFreeNisSystem k) :
    PointedSpaces (k := k) ⥤ SimplicialObject (NisModules (k := k)) :=
  F.functor ⋙ (Functor.whiskeringRight SimplexCategoryᵒᵖ
    ((SmoothScheme k)ᵒᵖ ⥤ ModuleCat.{1} ℤ) (NisModules (k := k))).obj
      (presheafToSheaf (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ))

/-- The reduced-free/underlying-zero-point adjunction, with its actual
evaluation on every module generator after the native sheafification unit. -/
structure ReducedFreeAdjunction (F : ReducedFreeNisSystem k)
    (Q : PointedSimplicialModuleFunctor k) where
  adjunction : reducedSimplicialFunctor F ⊣ Q.functor
  counit_generator : ∀ (J : SimplicialObject (NisModules (k := k)))
    (n : SimplexCategoryᵒᵖ) (U : (SmoothScheme k)ᵒᵖ)
    (t : ((𝟙_ (Spaces (k := k))).obj U).obj n) (x : (J.obj n).obj.obj U),
    (((adjunction.counit.app J).app n).hom.app U)
      ((((sheafificationAdjunction (nisnevichTopology (k := k))
        (ModuleCat.{1} ℤ)).unit.app
          ((F.functor.obj (Q.functor.obj J)).obj n)).app U)
        ((F.valueIso (Q.functor.obj J) n U t).inv
          (ReducedFreeModule.mk ℤ
            ((((Q.underlyingIso.app J).inv.app U).app n) x)))) = x

/-- Evaluation through the actual native Dold--Kan counit and good
truncation inclusion, on the fixed reduced source complex. -/
def evaluation (F : ReducedFreeNisSystem k)
    (Q : PointedSimplicialModuleFunctor k) (J : ReducedFreeAdjunction F Q)
    (I : CochainComplex (NisModules (k := k)) ℤ) (p : ℤ) :
    (reducedComplexFunctor F).obj (doldKanRealization Q I p) ⟶ I⟦p⟧ :=
  (negativeEmbedding.extendFunctor (NisModules (k := k))).map
    ((AlgebraicTopology.normalizedMooreComplex (NisModules (k := k))).map
      (J.adjunction.counit.app
        ((Abelian.DoldKan.Γ : ChainComplex (NisModules (k := k)) ℕ ⥤
          SimplicialObject (NisModules (k := k))).obj
            ((negativeEmbedding.truncLE'Functor (NisModules (k := k))).obj
              (I⟦p⟧))))) ≫
  (negativeEmbedding.extendFunctor (NisModules (k := k))).map
    ((Abelian.DoldKan.equivalence : SimplicialObject (NisModules (k := k)) ≌
      ChainComplex (NisModules (k := k)) ℕ).counitIso.hom.app
        ((negativeEmbedding.truncLE'Functor (NisModules (k := k))).obj
          (I⟦p⟧))) ≫
    ((I⟦p⟧).truncLEIso negativeEmbedding).inv ≫
      (I⟦p⟧).ιTruncLE negativeEmbedding

/-- A resolution refinement that states only ordinary termwise
injectivity, without a motivic locality or representability field. -/
def IsTermwiseInjective (I : KInjectiveResolutionSystem k) : Prop :=
  ∀ (C : CochainComplex (NisModules (k := k)) ℤ) (n : ℤ),
    Injective ((I.functor.obj C).X n)

attribute [local instance] HasDerivedCategory.standard

/-- The derived isomorphism is the image of the fixed resolution
augmentation, whose quasi-isomorphism is part of that source. -/
def augmentationIso (I : KInjectiveResolutionSystem k)
    (C : CochainComplex (NisModules (k := k)) ℤ) :
    DerivedCategory.Q.obj C ≅ DerivedCategory.Q.obj (I.functor.obj C) := by
  letI : QuasiIso (I.augmentation.app C) := I.quasi C
  exact asIso (DerivedCategory.Q.map (I.augmentation.app C))

variable {D : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D G P E} {A : StandardSchemes P}
  {R : RepresentableSystem D G} {S : TransferSheafificationModel D G}
  {T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R)} {N : NisTensorSystem k}
  (B : CoefficientComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R) (S := S) T N)
  (I : KInjectiveResolutionSystem k) (Q : PointedSimplicialModuleFunctor k)
  (F : ReducedFreeNisSystem k) (J : ReducedFreeAdjunction F Q)

/-- The literal pointed map is sent to its reduced derived class by
free evaluation, Dold--Kan, truncation and the augmentation inverse. -/
def realizationToCohomology (X : PointedSpaces (k := k)) (p q : ℤ)
    (V : ModuleCat.{1} ℤ) (a : X ⟶ K B I Q p q V) :
    ReducedCohomology B F X p q V :=
  DerivedCategory.Q.map ((reducedComplexFunctor F).map a) ≫
    DerivedCategory.Q.map
      (evaluation F Q J (I.functor.obj ((B.weightFunctor q).obj V)) p) ≫
    (DerivedCategory.Q.commShiftIso p).hom.app
      (I.functor.obj ((B.weightFunctor q).obj V)) ≫
    ((augmentationIso I ((B.weightFunctor q).obj V)).inv)⟦p⟧'

/-- Descent of this *fixed* comparison to the pointed A1 localization.
Bijectivity and naturality of the descended map are separate conclusions. -/
structure RepresentabilityMap where
  map : ∀ (X : PointedSpaces (k := k)) (p q : ℤ) (V : ModuleCat.{1} ℤ),
    ((motivicQ A).obj X ⟶ (motivicQ A).obj (K B I Q p q V)) →
      ReducedCohomology B F X p q V
  literal_map : ∀ (X : PointedSpaces (k := k)) (p q : ℤ)
    (V : ModuleCat.{1} ℤ) (a : X ⟶ K B I Q p q V),
    map X p q V ((motivicQ A).map a) =
      realizationToCohomology B I Q F J X p q V a

end MathlibExt.AlgebraicGeometry.MotivicRealizationComparisons
