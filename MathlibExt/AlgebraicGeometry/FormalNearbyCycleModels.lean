/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FormalGenericFibreModels
public import MathlibExt.AlgebraicGeometry.FiniteTateRootCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Actual formal/analytic étale nearby-cycle objects

Formal étale objects retain their original maps on every nilpotent level.
Their generic-fibre functor is normalized by the same model-ring maps on
every actual affine chart. Nearby cycles are the native right-derived
pushforward of that site functor, applied to the actual root-of-unity Tate
coefficients. The target truncation is native good truncation at the signed
twist degree, not a freely chosen nearby object or coefficient label.

References: BMS19 arXiv:1802.03261v2, Theorem 10.1 and Remark 10.3;
SGA4, Exposé IX; EGA, formal étale morphisms and their nilpotent levels.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FormalNearbyCycleModels

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open FormalGenericFibreModels AnalyticTateAdicModels AnalyticDiamondEtaleSites

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (C : CompletePadicField p)

def IsFormalEtale {X Y : FormalGenericFibreModels.FormalScheme p C} (f : X ⟶ Y) : Prop :=
  ∀ n : ℕ, Etale ((PadicFormalSchemes.FormalScheme.Hom.diagram f).app n)

abbrev FormalEtaleSite (X : FormalGenericFibreModels.FormalScheme p C) :=
  (show ObjectProperty (Over X) from fun U ↦ IsFormalEtale p C U.hom).FullSubcategory

def formalEtaleTopology (X : FormalGenericFibreModels.FormalScheme p C) :
    GrothendieckTopology (FormalEtaleSite p C X) :=
  sInf {J | ∀ (I : Type 1) (T : FormalEtaleSite p C X)
    (U : I → FormalEtaleSite p C X) (f : ∀ i, U i ⟶ T),
    (∀ i, IsFormalEtale p C (f i).hom.left) →
    (∀ x : T.obj.left.diagram.obj 0,
      ∃ i, x ∈ Set.range ((PadicFormalSchemes.FormalScheme.Hom.diagram (f i).hom.left).app 0)) →
      Sieve.ofArrows U f ∈ J T}

variable {X : FormalGenericFibreModels.FormalScheme p C} {G : AnalyticAdicSpace p}

/-- A site functor whose every image and arrow is the original generic fibre. -/
structure GenericEtaleModel (A : GenericAtlas p C X G) where
  functor : FormalEtaleSite p C X ⥤ AnalyticEtaleSite p G
  atlas : ∀ U : FormalEtaleSite p C X,
    GenericAtlas p C U.obj.left (functor.obj U).obj.left
  structural : ∀ U : FormalEtaleSite p C X,
    FormalGenericFibreModels.Morphism p C (atlas U) A U.obj.hom (functor.obj U).obj.hom
  arrows : ∀ {U V : FormalEtaleSite p C X} (f : U ⟶ V),
    FormalGenericFibreModels.Morphism p C (atlas U) (atlas V) f.hom.left (functor.map f).hom.left

def analyticEtaleRings (G : AnalyticAdicSpace p) : (AnalyticEtaleSite p G)ᵒᵖ ⥤ CommRingCat.{0} :=
  (ObjectProperty.ι _ ⋙ Over.forget G ⋙ ObjectProperty.ι (HasAnalyticAtlas p) ⋙
    forgetValuations).op ⋙ LocallyRingedSpace.Γ

def analyticProEtaleRings (G : AnalyticAdicSpace p) :
    (AnalyticProEtaleSiteModels.ProEtaleSite p G)ᵒᵖ ⥤ CommRingCat.{0} :=
  (AnalyticProEtaleSiteModels.forget p G ⋙ ObjectProperty.ι (HasAnalyticAtlas p) ⋙
    forgetValuations).op ⋙ LocallyRingedSpace.Γ

abbrev FormalSheaves (X : FormalGenericFibreModels.FormalScheme p C) :=
  Sheaf (formalEtaleTopology p C X) (ModuleCat.{1} ℤ)

abbrev GenericSheaves (G : AnalyticAdicSpace p) :=
  Sheaf (analyticEtaleTopology p G) (ModuleCat.{1} ℤ)

instance moduleSheafify {D : Type 1} [Category.{0} D] (J : GrothendieckTopology D) :
    HasSheafify J (ModuleCat.{1} ℤ) := by
  let : HasLimits (ModuleCat.{1} ℤ) := ModuleCat.hasLimitsOfSize.{1, 1, 1, 0}
  let : PreservesColimitsOfSize.{1, 1} (forget₂ (ModuleCat.{1} ℤ) AddCommGrpCat.{1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{1, 0, 1, 1} ℤ
  let : PreservesFilteredColimits (forget (ModuleCat.{1} ℤ)) :=
    comp_preservesFilteredColimits.{1, 1}
      (forget₂ (ModuleCat.{1} ℤ) AddCommGrpCat.{1}) (forget AddCommGrpCat.{1})
  let : PreservesFilteredColimitsOfSize.{1, 1} (forget (ModuleCat.{1} ℤ)) := inferInstance
  infer_instance

def finiteTate (G : AnalyticAdicSpace p) (r : ℕ) (i : ℤ) : GenericSheaves p G :=
  FiniteTateRootCoefficients.integerTate p r (analyticEtaleRings p G) (analyticEtaleTopology p G) i

namespace GenericEtaleModel

variable {p C} {A : GenericAtlas p C X G} (E : GenericEtaleModel p C A)

variable [E.functor.IsContinuous (formalEtaleTopology p C X) (analyticEtaleTopology p G)]

def pushforward : GenericSheaves p G ⥤ FormalSheaves p C X :=
  E.functor.sheafPushforwardContinuous (ModuleCat.{1} ℤ)
    (formalEtaleTopology p C X) (analyticEtaleTopology p G)

instance pushforward_additive : E.pushforward.Additive where
  map_add := by intros; rfl

def nearbySource : CochainComplex (GenericSheaves p G) ℤ ⥤ DerivedCategory (FormalSheaves p C X) :=
  E.pushforward.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

class HasDerivedNearby : Prop where
  exists_derived : E.nearbySource.HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (GenericSheaves p G) (.up ℤ))

attribute [instance] HasDerivedNearby.exists_derived

def nearby [E.HasDerivedNearby] : DerivedCategory (GenericSheaves p G) ⥤
    DerivedCategory (FormalSheaves p C X) :=
  E.nearbySource.totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (GenericSheaves p G) (.up ℤ))

def nearbyUnit [E.HasDerivedNearby] : E.nearbySource ⟶ DerivedCategory.Q ⋙ E.nearby :=
  E.nearbySource.totalRightDerivedUnit DerivedCategory.Q
    (HomologicalComplex.quasiIso (GenericSheaves p G) (.up ℤ))

def finiteNearby [E.HasDerivedNearby] (r : ℕ) (i : ℤ) : DerivedCategory (FormalSheaves p C X) :=
  E.nearby.obj ((DerivedCategory.singleFunctor (GenericSheaves p G) 0).obj (finiteTate p G r i))

def truncatedNearby [E.HasDerivedNearby] (r : ℕ) (i : ℤ) : DerivedCategory (FormalSheaves p C X) :=
  DerivedCategory.Q.obj ((DerivedCategory.Q.objPreimage (E.finiteNearby r i)).truncLE i)

end GenericEtaleModel

end MathlibExt.AlgebraicGeometry.FormalNearbyCycleModels
