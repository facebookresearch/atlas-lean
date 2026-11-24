/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FormalNearbyCycleModels
public import MathlibExt.AlgebraicGeometry.AnalyticProObjectSites
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# Formal pro-étale objects and the actual generic-fibre extension

Objects and arrows are native formal pro-objects of the formal étale
category. Finite étaleness is tested on every original nilpotent level.
Presentations have finite-étale surjective transitions; the covering rule
records the source's well-ordered refinements, including limit stages.

The generic-fibre extension is fixed on every original étale object,
every presentation projection and its native limit universal property.
Its nearby functor is the right-derived pushforward of that very site
functor. Good truncation is the canonical derived t-structure functor.

References: BMS19 arXiv:1802.03261v2, Theorem 1.15(2), Theorem 10.1
and Remark 10.3; BMS18 arXiv:1602.03148v3, Section 5.1;
Scholze arXiv:1205.3463v2, Definitions 3.1/3.9.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FormalProObjectSites

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open FormalGenericFibreModels FormalNearbyCycleModels AnalyticTateAdicModels

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (C : CompletePadicField p)
  (X : FormalGenericFibreModels.FormalScheme p C)

abbrev Etale := FormalEtaleSite p C X
abbrev Presheaves := (Etale p C X)ᵒᵖᵒᵖ ⥤ Type
abbrev ProCategory := ((show ObjectProperty (Presheaves p C X) from
  IsIndObject (C := (Etale p C X)ᵒᵖ)).FullSubcategory)ᵒᵖ

def IsFormalFiniteEtale {U V : FormalGenericFibreModels.FormalScheme p C} (f : U ⟶ V) : Prop :=
  ∀ n : ℕ, IsFinite ((PadicFormalSchemes.FormalScheme.Hom.diagram f).app n) ∧
    _root_.AlgebraicGeometry.Etale ((PadicFormalSchemes.FormalScheme.Hom.diagram f).app n)

structure ProEtalePresentation (F : Presheaves p C X) where
  ind : IndObjectPresentation F
  finite_etale : ∀ {i j : ind.I} (h : i ⟶ j),
    IsFormalFiniteEtale p C (ind.F.map h).unop.hom.left
  surjective : ∀ {i j : ind.I} (h : i ⟶ j),
    Function.Surjective ((PadicFormalSchemes.FormalScheme.Hom.diagram
      (ind.F.map h).unop.hom.left).app 0)

def IsProEtaleObject (F : Presheaves p C X) : Prop := Nonempty (ProEtalePresentation p C X F)
abbrev ProEtaleSite := ((show ObjectProperty (Presheaves p C X) from
  IsProEtaleObject p C X).FullSubcategory)ᵒᵖ

def forget : ProEtaleSite p C X ⥤ ProCategory p C X :=
  (ObjectProperty.ιOfLE (show IsProEtaleObject p C X ≤ IsIndObject (C := (Etale p C X)ᵒᵖ) from
    fun F h ↦ by obtain ⟨P⟩ := h; exact IsIndObject.mk P.ind)).op

def representable : Etale p C X ⥤ ProCategory p C X :=
  (opOpEquivalence (Etale p C X)).inverse ⋙
    (ObjectProperty.lift (IsIndObject (C := (Etale p C X)ᵒᵖ)) yoneda
      (fun U ↦ isIndObject_yoneda U)).op

def etalePresentation (U : Etale p C X) :
    ProEtalePresentation p C X (yoneda.obj (op U)) where
  ind := IndObjectPresentation.yoneda (op U)
  finite_etale := by
    intro i j h n
    change IsFinite (𝟙 (U.obj.left.diagram.obj n)) ∧
      _root_.AlgebraicGeometry.Etale (𝟙 (U.obj.left.diagram.obj n))
    constructor <;> infer_instance
  surjective := fun _ ↦ Function.surjective_id

def etaleEmbedding : Etale p C X ⥤ ProEtaleSite p C X :=
  (opOpEquivalence (Etale p C X)).inverse ⋙
    (ObjectProperty.lift (IsProEtaleObject p C X) yoneda
      (fun U ↦ ⟨etalePresentation p C X U.unop⟩)).op

def etalePoints : Etale p C X ⥤ TopCat where
  obj U := Scheme.forgetToTop.obj (U.obj.left.diagram.obj 0)
  map f := Scheme.forgetToTop.map ((PadicFormalSchemes.FormalScheme.Hom.diagram f.hom.left).app 0)

def diagram {F : Presheaves p C X} (P : ProEtalePresentation p C X F) : P.ind.Iᵒᵖ ⥤ Etale p C X :=
  P.ind.F.op ⋙ (opOpEquivalence (Etale p C X)).functor

def presentedObject {F : Presheaves p C X} (P : ProEtalePresentation p C X F) :
    ProEtaleSite p C X := op ⟨F, ⟨P⟩⟩

def projection {F : Presheaves p C X} (P : ProEtalePresentation p C X F) (i : P.ind.I) :
    (forget p C X).obj (presentedObject p C X P) ⟶
      (representable p C X).obj (P.ind.F.obj i).unop :=
  (ObjectProperty.homMk (P.ind.ι.app i)).op

structure PointRealization where
  functor : ProEtaleSite p C X ⥤ TopCat
  iso : ∀ {F : Presheaves p C X} (P : ProEtalePresentation p C X F),
    functor.obj (presentedObject p C X P) ≅ limit (diagram p C X P ⋙ etalePoints p C X)
  realization : ProCategory p C X ⥤ TopCat
  restriction : functor ≅ forget p C X ⋙ realization
  original : representable p C X ⋙ realization ≅ etalePoints p C X
  normalized : ∀ {F : Presheaves p C X} (P : ProEtalePresentation p C X F) (i : P.ind.I),
    restriction.hom.app (presentedObject p C X P) ≫ realization.map (projection p C X P i) ≫
      original.hom.app (P.ind.F.obj i).unop =
        (iso P).hom ≫ limit.π (diagram p C X P ⋙ etalePoints p C X) (op i)

variable (R : PointRealization p C X)

def IsEtaleMap {U V : ProEtaleSite p C X} (f : U ⟶ V) : Prop :=
  ∃ (A B : Etale p C X) (a : A ⟶ B)
    (h : (forget p C X).obj V ⟶ (representable p C X).obj B)
    (g : (forget p C X).obj U ⟶ (representable p C X).obj A),
    IsFormalEtale p C a.hom.left ∧
      IsPullback g ((forget p C X).map f) ((representable p C X).map a) h

def IsFiniteEtaleMap {U V : ProEtaleSite p C X} (f : U ⟶ V) : Prop :=
  ∃ (A B : Etale p C X) (a : A ⟶ B)
    (h : (forget p C X).obj V ⟶ (representable p C X).obj B)
    (g : (forget p C X).obj U ⟶ (representable p C X).obj A),
    IsFormalFiniteEtale p C a.hom.left ∧
      IsPullback g ((forget p C X).map f) ((representable p C X).map a) h

structure TransfiniteCoverPresentation {U V : ProEtaleSite p C X} (f : U ⟶ V) where
  index : Type
  [linearOrder : LinearOrder index]
  [wellOrder : IsWellOrder index (· < ·)]
  [orderBot : OrderBot index]
  diagram : indexᵒᵖ ⥤ Over V
  first_etale : IsEtaleMap p C X (diagram.obj (op ⊥)).hom
  previous : ∀ i : index, Over V
  previousCone : ∀ i : index,
    Cone ((show Monotone (fun j : Set.Iio i ↦ j.val) from fun _ _ h ↦ h).functor.op ⋙ diagram)
  previous_point : ∀ i, (previousCone i).pt = previous i
  previous_isLimit : ∀ i, IsLimit (previousCone i)
  step : ∀ i : index, diagram.obj (op i) ⟶ previous i
  step_triangle : ∀ (i : index) (j : Set.Iio i),
    step i ≫ eqToHom (previous_point i).symm ≫ (previousCone i).π.app (op j) =
      diagram.map (homOfLE (le_of_lt j.property)).op
  step_finite_etale : ∀ i : index, i ≠ ⊥ → IsFiniteEtaleMap p C X (step i).left
  step_surjective : ∀ i : index, i ≠ ⊥ → Function.Surjective (R.functor.map (step i).left)
  cone : Cone diagram
  point : cone.pt = Over.mk f
  isLimit : IsLimit cone

def IsCoverMap {U V : ProEtaleSite p C X} (f : U ⟶ V) : Prop :=
  Nonempty (TransfiniteCoverPresentation p C X R f)

def topology : GrothendieckTopology (ProEtaleSite p C X) :=
  sInf {J | ∀ (I : Type 1) (T : ProEtaleSite p C X)
    (U : I → ProEtaleSite p C X) (f : ∀ i, U i ⟶ T),
    (∀ i, IsCoverMap p C X R (f i)) →
    (∀ x : R.functor.obj T, ∃ i, x ∈ Set.range (R.functor.map (f i))) →
      Sieve.ofArrows U f ∈ J T}

abbrev Sheaves := Sheaf (topology p C X R) (ModuleCat.{1} ℤ)

/-- Module sheafification on the native full pro-category, whose hom
universe includes all natural transformations on the large étale site. -/
instance fullModuleSheafify {D : Type 1} [Category.{1} D] (J : GrothendieckTopology D) :
    HasSheafify J (ModuleCat.{1} ℤ) := by
  let : HasLimits (ModuleCat.{1} ℤ) := ModuleCat.hasLimitsOfSize.{1, 1, 1, 0}
  let : PreservesColimitsOfSize.{1, 1} (forget₂ (ModuleCat.{1} ℤ) AddCommGrpCat.{1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{1, 0, 1, 1} ℤ
  let : PreservesFilteredColimits (_root_.CategoryTheory.forget (ModuleCat.{1} ℤ)) :=
    comp_preservesFilteredColimits.{1, 1}
      (forget₂ (ModuleCat.{1} ℤ) AddCommGrpCat.{1}) (_root_.CategoryTheory.forget AddCommGrpCat.{1})
  let : PreservesFilteredColimitsOfSize.{1, 1}
      (_root_.CategoryTheory.forget (ModuleCat.{1} ℤ)) := inferInstance
  infer_instance

variable {X} {G : AnalyticAdicSpace p} {A : GenericAtlas p C X G}
  (E : GenericEtaleModel p C A)

/-- Universal pro-extension of the same original formal/generic site map.
The limit cone and every projection fix the extension on full pro-arrows. -/
structure GenericProModel where
  extension : ProCategory p C X ⥤ AnalyticProObjectSites.ProCategory p G
  etale : representable p C X ⋙ extension ≅ E.functor ⋙ AnalyticProObjectSites.representable p G
  functor : ProEtaleSite p C X ⥤ AnalyticProObjectSites.ProEtaleSite p G
  restriction : forget p C X ⋙ extension ≅ functor ⋙ AnalyticProObjectSites.forget p G
  cone : ∀ {F : Presheaves p C X} (P : ProEtalePresentation p C X F),
    Cone (diagram p C X P ⋙ E.functor ⋙ AnalyticProObjectSites.representable p G)
  point : ∀ {F : Presheaves p C X} (P : ProEtalePresentation p C X F),
    (cone P).pt = extension.obj ((forget p C X).obj (presentedObject p C X P))
  isLimit : ∀ {F : Presheaves p C X} (P : ProEtalePresentation p C X F), IsLimit (cone P)
  normalized : ∀ {F : Presheaves p C X} (P : ProEtalePresentation p C X F) (i : P.ind.I),
    eqToHom (point P).symm ≫ (cone P).π.app (op i) =
      extension.map (projection p C X P i) ≫ etale.hom.app (P.ind.F.obj i).unop

namespace GenericProModel

variable {p C E R} (H : GenericProModel p C E)
  (S : AnalyticProObjectSites.PointRealization p G)
  [H.functor.IsContinuous (topology p C X R) (AnalyticProObjectSites.bmsTopology p G S)]

abbrev GenericSheaves := Sheaf (AnalyticProObjectSites.bmsTopology p G S) (ModuleCat.{1} ℤ)

def pushforward : GenericSheaves S ⥤ Sheaves p C X R :=
  H.functor.sheafPushforwardContinuous (ModuleCat.{1} ℤ)
    (topology p C X R) (AnalyticProObjectSites.bmsTopology p G S)

instance pushforward_additive : (H.pushforward S (R := R)).Additive where
  map_add := by intros; rfl

def nearbySource : CochainComplex (GenericSheaves S) ℤ ⥤ DerivedCategory (Sheaves p C X R) :=
  (H.pushforward S (R := R)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

class HasDerivedNearby : Prop where
  exists_derived : (H.nearbySource S (R := R)).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (GenericSheaves S) (.up ℤ))

attribute [instance] HasDerivedNearby.exists_derived

def nearby [H.HasDerivedNearby S (R := R)] : DerivedCategory (GenericSheaves S) ⥤
    DerivedCategory (Sheaves p C X R) :=
  (H.nearbySource S (R := R)).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (GenericSheaves S) (.up ℤ))

/-- Canonical good truncation, including its action on every coefficient map. -/
def truncatedNearby [H.HasDerivedNearby S (R := R)] (i : ℤ) :
    DerivedCategory (GenericSheaves S) ⥤ DerivedCategory (Sheaves p C X R) :=
  H.nearby S (R := R) ⋙ DerivedCategory.TStructure.t.truncLE i

end GenericProModel

end MathlibExt.AlgebraicGeometry.FormalProObjectSites
