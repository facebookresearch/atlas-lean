/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticProEtaleSiteModels
public import Mathlib.CategoryTheory.Limits.Indization.IndObject
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.Order.WellFounded
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# The full formal pro-object analytic site

The ambient category is the opposite of the native category of ind-object
presheaves on the opposite analytic étale category. Hence its arrows are
the full natural transformations representing pro-morphisms. Objects of
the pro-étale subcategory have actual cofiltered étale presentations with
finite-étale surjective transitions. Completed represented Tate spaces are
a separate presentation boundary, not the definition of this category.

Point realization and represented-basis comparison must be normalized on
every original presentation and arrow. Site coverings use the source's
relative pro-étale morphisms and joint surjectivity on these actual limits.

References: Scholze, arXiv:1205.3463v2, Definitions 3.1/3.9;
BMS18, arXiv:1602.03148v3, Section 5.1.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticProObjectSites

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AnalyticTateAdicModels AnalyticDiamondEtaleSites

variable (p : ℕ) [Fact p.Prime] (G : AnalyticAdicSpace p)

/-- Strong noetherianity is the source condition on every actual Tate
polynomial ring. Its coefficients are precisely the power series tending
to zero in the original Tate-ring topology. -/
def IsStronglyNoetherian (P : TatePair p) : Prop :=
  ∀ n : ℕ, ∃ S : Subring (MvPowerSeries (Fin n) P.ring),
    (∀ f, f ∈ S ↔ Filter.Tendsto (fun t ↦ MvPowerSeries.coeff t f)
      Filter.cofinite (nhds 0)) ∧ IsNoetherianRing S

/-- The actual locally noetherian hypothesis of Scholze and BMS18. -/
def IsLocallyNoetherian : Prop :=
  ∀ x : G.obj.space, ∃ A : Chart p G,
    x ∈ Set.range A.map.val.base ∧
      (IsStronglyNoetherian p A.pair ∨
        ∃ D : MathlibExt.RingTheory.CompleteHuberPairModels.PairOfDefinition A.pair.ring,
          IsNoetherianRing D.ring)

abbrev Etale := AnalyticEtaleSite p G
abbrev Presheaves := (Etale p G)ᵒᵖᵒᵖ ⥤ Type

abbrev ProCategory := ((show ObjectProperty (Presheaves p G) from
  IsIndObject (C := (Etale p G)ᵒᵖ)).FullSubcategory)ᵒᵖ

/-- A preferred source pro-étale presentation, before taking its isomorphism class. -/
structure ProEtalePresentation (F : Presheaves p G) where
  ind : IndObjectPresentation F
  finite_etale : ∀ {i j : ind.I} (h : i ⟶ j),
    IsAnalyticFiniteEtale p (ind.F.map h).unop.hom.left
  surjective : ∀ {i j : ind.I} (h : i ⟶ j),
    Function.Surjective (ind.F.map h).unop.hom.left.hom.val.base

def IsProEtaleObject (F : Presheaves p G) : Prop := Nonempty (ProEtalePresentation p G F)

abbrev ProEtaleSite := ((show ObjectProperty (Presheaves p G) from IsProEtaleObject p G).FullSubcategory)ᵒᵖ

def forget : ProEtaleSite p G ⥤ ProCategory p G :=
  (ObjectProperty.ιOfLE (show IsProEtaleObject p G ≤ IsIndObject (C := (Etale p G)ᵒᵖ) from
    fun F h ↦ by obtain ⟨P⟩ := h; exact IsIndObject.mk P.ind)).op

def representable : Etale p G ⥤ ProCategory p G :=
  (opOpEquivalence (Etale p G)).inverse ⋙
    (ObjectProperty.lift (IsIndObject (C := (Etale p G)ᵒᵖ)) yoneda
      (fun U ↦ isIndObject_yoneda U)).op

/-- Identity maps are finite étale on every original affinoid chart. -/
theorem finiteEtale_identity (X : AnalyticAdicSpace p) :
    IsAnalyticFiniteEtale p (𝟙 X) := by
  intro V
  let f : AffinoidMap p V V :=
    { ring := ⟨RingHom.id _, continuous_id, fun _ h ↦ h⟩
      valued := 𝟙 V.model.valued
      points := fun _ ↦ rfl
      coordinates := fun _ ↦ rfl }
  refine ⟨V, f, ?_, ?_, ?_⟩
  · simp [f]
  · refine ⟨Module.Finite.self _, inferInstanceAs (Algebra.Etale V.pair.ring V.pair.ring),
      fun s ↦ ?_⟩
    change s ∈ V.pair.plus ↔ V.pair.plus.subtype.IsIntegralElem s
    constructor
    · intro hs
      exact V.pair.plus.subtype.isIntegralElem_map (x := ⟨s, hs⟩)
    · intro hs
      have := V.pair.plus_integral
      obtain ⟨y, hy⟩ :=
        (IsIntegrallyClosedIn.isIntegral_iff (R := V.pair.plus) (A := V.pair.ring)).mp hs
      rw [← hy]
      exact y.property
  · rfl

/-- An original étale object has its native one-object pro-presentation. -/
def etalePresentation (U : Etale p G) :
    ProEtalePresentation p G (yoneda.obj (op U)) where
  ind := IndObjectPresentation.yoneda (op U)
  finite_etale := fun _ ↦ finiteEtale_identity p U.obj.left
  surjective := fun _ ↦ Function.surjective_id

/-- The étale inclusion retains the native Yoneda object and every original arrow. -/
def etaleEmbedding : Etale p G ⥤ ProEtaleSite p G :=
  (opOpEquivalence (Etale p G)).inverse ⋙
    (ObjectProperty.lift (IsProEtaleObject p G) yoneda
      (fun U ↦ ⟨etalePresentation p G U.unop⟩)).op

def etaleSpaces : Etale p G ⥤ TopCat where
  obj U := U.obj.left.obj.space.toTopCat
  map f := f.hom.left.hom.val.base

def diagram {F : Presheaves p G} (P : ProEtalePresentation p G F) : P.ind.Iᵒᵖ ⥤ Etale p G :=
  P.ind.F.op ⋙ (opOpEquivalence (Etale p G)).functor

def presentedObject {F : Presheaves p G} (P : ProEtalePresentation p G F) : ProEtaleSite p G :=
  op ⟨F, ⟨P⟩⟩

/-- All presentation-to-presheaf maps are the actual native colimit cocone. -/
def projection {F : Presheaves p G} (P : ProEtalePresentation p G F) (i : P.ind.I) :
    (forget p G).obj (presentedObject p G P) ⟶ (representable p G).obj (P.ind.F.obj i).unop :=
  (ObjectProperty.homMk (P.ind.ι.app i)).op

/-- A point realization of the pro-étale site of $G$: a functor `functor` from the pro-étale site to
topological spaces with, for every pro-étale presentation of an object, an isomorphism `iso` from
its value to the limit of the underlying spaces of the étale objects of the presentation; a functor
`realization` on the whole pro-category with isomorphisms exhibiting `functor` as its restriction
(`restriction`) and its composite with the representable embedding as the underlying-space functor
of the étale site (`original`); such that, for every presentation and index $i$, the realization of
the $i$th projection corresponds under these isomorphisms to the $i$th limit projection
(`normalized`). -/
structure PointRealization where
  functor : ProEtaleSite p G ⥤ TopCat
  iso : ∀ {F : Presheaves p G} (P : ProEtalePresentation p G F),
    functor.obj (presentedObject p G P) ≅ limit (diagram p G P ⋙ etaleSpaces p G)
  realization : ProCategory p G ⥤ TopCat
  restriction : functor ≅ forget p G ⋙ realization
  original : representable p G ⋙ realization ≅ etaleSpaces p G
  normalized : ∀ {F : Presheaves p G} (P : ProEtalePresentation p G F) (i : P.ind.I),
    (restriction.hom.app (presentedObject p G P)) ≫ realization.map (projection p G P i) ≫
      original.hom.app (P.ind.F.obj i).unop =
        (iso P).hom ≫ limit.π (diagram p G P ⋙ etaleSpaces p G) (op i)

variable (R : PointRealization p G)

/-- Relative étaleness is the pullback of an original étale map of charts. -/
def IsEtaleMap {U V : ProEtaleSite p G} (f : U ⟶ V) : Prop :=
  ∃ (A B : Etale p G) (a : A ⟶ B)
    (h : (forget p G).obj V ⟶ (representable p G).obj B)
    (g : (forget p G).obj U ⟶ (representable p G).obj A),
    IsAnalyticEtale p a.hom.left ∧
      IsPullback g ((forget p G).map f) ((representable p G).map a) h

def IsFiniteEtaleMap {U V : ProEtaleSite p G} (f : U ⟶ V) : Prop :=
  ∃ (A B : Etale p G) (a : A ⟶ B)
    (h : (forget p G).obj V ⟶ (representable p G).obj B)
    (g : (forget p G).obj U ⟶ (representable p G).obj A),
    IsAnalyticFiniteEtale p a.hom.left ∧
      IsPullback g ((forget p G).map f) ((representable p G).map a) h

/-- Source relative pro-étale presentations, including their actual limit over V. -/
structure ProEtaleMapPresentation {U V : ProEtaleSite p G} (f : U ⟶ V) where
  index : Type
  [category : SmallCategory index]
  [cofiltered : IsCofiltered index]
  diagram : index ⥤ Over V
  etale : ∀ i, IsEtaleMap p G (diagram.obj i).hom
  finite : ∀ {i j} (h : i ⟶ j), IsFiniteEtaleMap p G (diagram.map h).left
  surjective : ∀ {i j} (h : i ⟶ j), Function.Surjective (R.functor.map (diagram.map h).left)
  cone : Cone diagram
  identifies : cone.pt = Over.mk f
  isLimit : IsLimit cone

def IsProEtaleMap {U V : ProEtaleSite p G} (f : U ⟶ V) : Prop :=
  Nonempty (ProEtaleMapPresentation p G R f)

def topology : GrothendieckTopology (ProEtaleSite p G) :=
  sInf {J | ∀ (I : Type 1) (T : ProEtaleSite p G)
    (U : I → ProEtaleSite p G) (f : ∀ i, U i ⟶ T),
    (∀ i, IsProEtaleMap p G R (f i)) →
    (∀ x : R.functor.obj T, ∃ i, x ∈ Set.range (R.functor.map (f i))) → Sieve.ofArrows U f ∈ J T}

/-- BMS18 §5.1 uses well-ordered inverse towers for covering arrows. At
each noninitial stage the map is to the limit of *all* preceding stages,
including limit ordinals. A well-ordered small linear order is the native
set-sized presentation of an ordinal; no countability assumption is added. -/
structure TransfiniteCoverPresentation {U V : ProEtaleSite p G} (f : U ⟶ V) where
  index : Type
  [linearOrder : LinearOrder index]
  [wellOrder : IsWellOrder index (· < ·)]
  [orderBot : OrderBot index]
  diagram : indexᵒᵖ ⥤ Over V
  first_etale : IsEtaleMap p G (diagram.obj (op ⊥)).hom
  previous : ∀ i : index, Over V
  previousCone : ∀ i : index,
    Cone ((show Monotone (fun j : Set.Iio i ↦ j.val) from fun _ _ h ↦ h).functor.op ⋙ diagram)
  previous_point : ∀ i, (previousCone i).pt = previous i
  previous_isLimit : ∀ i, IsLimit (previousCone i)
  step : ∀ i : index, diagram.obj (op i) ⟶ previous i
  step_triangle : ∀ (i : index) (j : Set.Iio i),
    step i ≫ eqToHom (previous_point i).symm ≫ (previousCone i).π.app (op j) =
      diagram.map (homOfLE (le_of_lt j.property)).op
  step_finite_etale : ∀ i : index, i ≠ ⊥ → IsFiniteEtaleMap p G (step i).left
  step_surjective : ∀ i : index, i ≠ ⊥ → Function.Surjective (R.functor.map (step i).left)
  cone : Cone diagram
  point : cone.pt = Over.mk f
  isLimit : IsLimit cone

def IsBMSCoverMap {U V : ProEtaleSite p G} (f : U ⟶ V) : Prop :=
  Nonempty (TransfiniteCoverPresentation p G R f)

/-- The exact BMS18 covering topology. The weaker Scholze covering rule
above is recorded separately because arbitrary cofiltered presentations
need not satisfy this stronger transfinite condition. -/
def bmsTopology : GrothendieckTopology (ProEtaleSite p G) :=
  sInf {J | ∀ (I : Type 1) (T : ProEtaleSite p G)
    (U : I → ProEtaleSite p G) (f : ∀ i, U i ⟶ T),
    (∀ i, IsBMSCoverMap p G R (f i)) →
    (∀ x : R.functor.obj T, ∃ i, x ∈ Set.range (R.functor.map (f i))) →
      Sieve.ofArrows U f ∈ J T}

/-- A represented affinoid boundary object retains its full formal
pro-object and every original affine chart. Completing a ring never
changes the definition of the ambient pro-object. -/
structure RepresentedBoundary where
  presheaf : Presheaves p G
  presentation : ProEtalePresentation p G presheaf
  represented : AnalyticProEtaleSiteModels.ProEtaleSite p G
  chart : Chart p represented.obj.left
  [whole : IsIso chart.map]
  original : ∀ i : presentation.ind.I, Chart p (presentation.ind.F.obj i).unop.obj.left
  [original_whole : ∀ i, IsIso (original i).map]
  projectionMap : ∀ i, AffinoidMap p chart (original i)
  structural : ∀ i,
    chart.map ≫ represented.obj.hom.hom =
      (projectionMap i).valued ≫ (original i).map ≫ (presentation.ind.F.obj i).unop.obj.hom.hom
  transitionMap : ∀ {i j : presentation.ind.I} (h : i ⟶ j),
    AffinoidMap p (original j) (original i)
  transition_square : ∀ {i j : presentation.ind.I} (h : i ⟶ j),
    (original j).map ≫ (presentation.ind.F.map h).unop.hom.left.hom =
      (transitionMap h).valued ≫ (original i).map
  ring_triangle : ∀ {i j : presentation.ind.I} (h : i ⟶ j),
    (projectionMap j).ring.hom.comp (transitionMap h).ring.hom = (projectionMap i).ring.hom
  ring_universal : ∀ (Q : TatePair p)
    (g : ∀ i, TateRingMap p (original i).pair Q),
    (∀ {i j} (h : i ⟶ j), (g j).hom.comp (transitionMap h).ring.hom = (g i).hom) →
    ∃! h : TateRingMap p chart.pair Q,
      ∀ i, h.hom.comp (projectionMap i).ring.hom = (g i).hom
  points : R.functor.obj (presentedObject p G presentation) ≅
    represented.obj.left.obj.space.toTopCat
  point_projection : ∀ i,
    points.hom ≫ (inv chart.map).val.base ≫ (projectionMap i).valued.val.base ≫
      (original i).map.val.base =
      (R.iso presentation).hom ≫ limit.π (diagram p G presentation ⋙ etaleSpaces p G) (op i)

attribute [instance] RepresentedBoundary.whole RepresentedBoundary.original_whole

namespace RepresentedBoundary

def formal (B : RepresentedBoundary p G R) : ProEtaleSite p G :=
  presentedObject p G B.presentation

/-- Boundary arrows are the full native pro-morphisms, not levelwise maps
or unconstrained maps between their completed rings. -/
instance : Category (RepresentedBoundary p G R) where
  Hom B C := B.formal ⟶ C.formal
  id _ := 𝟙 _
  comp f g := f ≫ g
  id_comp _ := Category.id_comp _
  comp_id _ := Category.comp_id _
  assoc _ _ _ := Category.assoc _ _ _

def inclusion : RepresentedBoundary p G R ⥤ ProEtaleSite p G where
  obj B := B.formal
  map f := f

def boundaryTopology : GrothendieckTopology (RepresentedBoundary p G R) :=
  (inclusion p G R).inducedTopology (bmsTopology p G R)

instance inclusion_continuous : (inclusion p G R).IsContinuous
    (boundaryTopology p G R) (bmsTopology p G R) := by
  dsimp [boundaryTopology]
  infer_instance

/-- The completion functor must use every original finite-stage
factorization of a pro-morphism. These equations fix its actual maps on
the dense source coefficient rings; zero or arbitrary maps cannot satisfy
the universal complete-ring normalization. -/
structure GeometryComparison where
  functor : RepresentedBoundary p G R ⥤ AnalyticProEtaleSiteModels.ProEtaleSite p G
  objects : ∀ B, functor.obj B = B.represented
  arrowMap : ∀ {B C : RepresentedBoundary p G R} (f : B ⟶ C), B.represented ⟶ C.represented
  arrows : ∀ {B C : RepresentedBoundary p G R} (f : B ⟶ C),
    arrowMap f = eqToHom (objects B).symm ≫ functor.map f ≫ eqToHom (objects C)
  factorization : ∀ {B C : RepresentedBoundary p G R} (f : B ⟶ C) (j : C.presentation.ind.I),
    ∃ (i : B.presentation.ind.I)
      (a : (B.presentation.ind.F.obj i).unop ⟶ (C.presentation.ind.F.obj j).unop),
      (forget p G).map f ≫ projection p G C.presentation j =
        projection p G B.presentation i ≫ (representable p G).map a
  normalization : ∀ {B C : RepresentedBoundary p G R} (f : B ⟶ C)
    (i : B.presentation.ind.I) (j : C.presentation.ind.I)
    (a : (B.presentation.ind.F.obj i).unop ⟶ (C.presentation.ind.F.obj j).unop),
    (forget p G).map f ≫ projection p G C.presentation j =
      projection p G B.presentation i ≫ (representable p G).map a →
    B.chart.map ≫ (arrowMap f).hom.left.hom ≫ inv C.chart.map ≫
      (C.projectionMap j).valued ≫ (C.original j).map =
        (B.projectionMap i).valued ≫ (B.original i).map ≫ a.hom.left.hom
  point_naturality : ∀ {B C : RepresentedBoundary p G R} (f : B ⟶ C),
    R.functor.map f ≫ C.points.hom = B.points.hom ≫ (arrowMap f).hom.left.hom.val.base

end RepresentedBoundary

end MathlibExt.AlgebraicGeometry.AnalyticProObjectSites
