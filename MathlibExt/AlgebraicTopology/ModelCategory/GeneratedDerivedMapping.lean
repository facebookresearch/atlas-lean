/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

module

public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import MathlibExt.AlgebraicTopology.ModelCategory.BrownSourceFunctor
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedReplacementConstruction
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
public import MathlibExt.CategoryTheory.Enriched.Ordinary.Basic

/-!
# Compatible external simplicial actions and the original mapping spaces

An actual simplicial category has an external simplicial tensor and cotensor
with both complete parametrized adjunctions. The three source pushout-product
conditions imply SM7 for every original mapping pullback corner. Fixed
cofibrant sources give actual Quillen adjunctions and fibrant mapping spaces.
Brown's lemma then gives precomposition and postcomposition weak invariance
at the original cofibrant and fibrant endpoints.
-/

section

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section

universe u v

open CategoryTheory Limits MorphismProperty Opposite
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CompatibleSimplicialMapping

variable (C : Type u) [Category.{v} C] [ModelCategory C] [SimplicialCategory C]

/-- Actual action data and source PP laws on the selected Kan--Quillen simplicial-set model. -/
structure Action where
  /-- The external simplicial tensor, covariant in the coefficient object and simplicial set. -/
  tensor : C ⥤ SSet.{v} ⥤ C
  /-- The external cotensor, contravariant in the simplicial set and covariant in the coefficient
  object. -/
  cotensor : SSet.{v}ᵒᵖ ⥤ C ⥤ C
  /-- The parametrized tensor–simplicial-Hom adjunction for the given simplicial enrichment. -/
  tensorHom : tensor ⊣₂ SimplicialCategory.sHomFunctor C
  /-- The parametrized tensor–cotensor adjunction with the simplicial-set argument fixed. -/
  tensorCotensor : tensor.flip ⊣₂ cotensor
  cof_cof : ∀ {X X' : C} (i : X ⟶ X') {K L : SSet.{v}} (j : K ⟶ L)
    (sq : tensor.PushoutObjObj i j),
    cofibrations C i → cofibrations SSet.{v} j → cofibrations C sq.ι
  trivial_cof : ∀ {X X' : C} (i : X ⟶ X') {K L : SSet.{v}} (j : K ⟶ L)
    (sq : tensor.PushoutObjObj i j),
    trivialCofibrations C i → cofibrations SSet.{v} j → trivialCofibrations C sq.ι
  cof_trivial : ∀ {X X' : C} (i : X ⟶ X') {K L : SSet.{v}} (j : K ⟶ L)
    (sq : tensor.PushoutObjObj i j),
    cofibrations C i → trivialCofibrations SSet.{v} j → trivialCofibrations C sq.ι

variable {C} (a : Action C)

include a

/-- The original supplied mapping corner is a fibration under the source cofibration/fibration
tests. -/
theorem sm7_fibration {X X' Y Y' : C} {i : X ⟶ X'} {p : Y ⟶ Y'}
    (sq : (SimplicialCategory.sHomFunctor C).PullbackObjObj i p)
    (hi : cofibrations C i) (hp : fibrations C p) :
    fibrations SSet.{v} sq.π := by
  rw [← trivialCofibrations_rlp SSet.{v}]
  intro K L j hj
  let push := Functor.PushoutObjObj.ofHasPushout a.tensor i j
  exact (a.tensorHom.hasLiftingProperty_iff push sq).mp
    (hasLiftingProperty_of_wfs push.ι p (a.cof_trivial i j push hi hj) hp)

/-- A trivial original source cofibration gives a trivial fibration of the same supplied mapping
corner. -/
theorem sm7_trivial_left {X X' Y Y' : C} {i : X ⟶ X'} {p : Y ⟶ Y'}
    (sq : (SimplicialCategory.sHomFunctor C).PullbackObjObj i p)
    (hi : trivialCofibrations C i) (hp : fibrations C p) :
    trivialFibrations SSet.{v} sq.π := by
  rw [← cofibrations_rlp SSet.{v}]
  intro K L j hj
  let push := Functor.PushoutObjObj.ofHasPushout a.tensor i j
  exact (a.tensorHom.hasLiftingProperty_iff push sq).mp
    (hasLiftingProperty_of_wfs push.ι p (a.trivial_cof i j push hi hj) hp)

/-- A trivial original target fibration gives a trivial fibration of the same supplied mapping
corner. -/
theorem sm7_trivial_right {X X' Y Y' : C} {i : X ⟶ X'} {p : Y ⟶ Y'}
    (sq : (SimplicialCategory.sHomFunctor C).PullbackObjObj i p)
    (hi : cofibrations C i) (hp : trivialFibrations C p) :
    trivialFibrations SSet.{v} sq.π := by
  rw [← cofibrations_rlp SSet.{v}]
  intro K L j hj
  let push := Functor.PushoutObjObj.ofHasPushout a.tensor i j
  exact (a.tensorHom.hasLiftingProperty_iff push sq).mp
    (hasLiftingProperty_of_wfs push.ι p (a.cof_cof i j push hi hj) hp)

/-- The original cotensor adjunctions construct the initial-source pushout square. -/
def initialPushout (X : C) {K L : SSet.{v}} (j : K ⟶ L) :
    a.tensor.PushoutObjObj (initial.to X) j := by
  letI : PreservesColimitsOfSize.{0, 0} (a.tensor.flip.obj K) :=
    (a.tensorCotensor.adj K).leftAdjoint_preservesColimits
  letI : PreservesColimitsOfSize.{0, 0} (a.tensor.flip.obj L) :=
    (a.tensorCotensor.adj L).leftAdjoint_preservesColimits
  exact Functor.PushoutObjObj.ofIsInitialLeft a.tensor (initial.to X) j initialIsInitial

/-- The whole pushout-product arrow is exactly the original tensor's map. -/
@[simp]
theorem initialPushout_ι (X : C) {K L : SSet.{v}} (j : K ⟶ L) :
    (initialPushout a X j).ι = (a.tensor.obj X).map j := rfl

/-- A fixed original cofibrant object gives the actual external tensor/mapping Quillen adjunction.
-/
theorem tensor_isQuillen (X : C) [IsCofibrant X] :
    (a.tensorHom.adj X).IsQuillenAdjunction := by
  have hX : cofibrations C (initial.to X) := (cofibration_iff _).mp inferInstance
  constructor
  · intro K L j hj
    exact a.cof_cof (initial.to X) j (initialPushout a X j) hX hj
  · intro K L j hj
    exact a.cof_trivial (initial.to X) j (initialPushout a X j) hX hj

/-- Original cofibrant/fibrant endpoints give a fibrant original simplicial mapping space. -/
theorem mapping_isFibrant (X Y : C) [IsCofibrant X] [IsFibrant Y] :
    IsFibrant (SimplicialCategory.sHom X Y) := by
  let _ : (a.tensorHom.adj X).IsQuillenAdjunction := tensor_isQuillen a X
  exact CategoryTheory.Adjunction.IsQuillenAdjunction.preservesFibrantObjects
    (adj := a.tensorHom.adj X) inferInstance

/-- The actual raw target map is weak between original fibrant targets at a cofibrant source. -/
theorem postcomp_weak (X : C) [IsCofibrant X] {Y Y' : C} (p : Y ⟶ Y')
    [WeakEquivalence p] [IsFibrant Y] [IsFibrant Y'] :
    WeakEquivalence (((SimplicialCategory.sHomFunctor C).obj (op X)).map p) := by
  let _ : (a.tensorHom.adj X).IsQuillenAdjunction := tensor_isQuillen a X
  exact CategoryTheory.Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
    (adj := a.tensorHom.adj X) p

/-- Both actual fixed-source adjunctions construct the terminal-target mapping corner. -/
def terminalCorner {X X' : C} (i : X ⟶ X') (Y : C) :
    (SimplicialCategory.sHomFunctor C).PullbackObjObj i (terminal.from Y) := by
  letI : PreservesLimitsOfSize.{0, 0} ((SimplicialCategory.sHomFunctor C).obj (op X)) :=
    (a.tensorHom.adj X).rightAdjoint_preservesLimits
  letI : PreservesLimitsOfSize.{0, 0} ((SimplicialCategory.sHomFunctor C).obj (op X')) :=
    (a.tensorHom.adj X').rightAdjoint_preservesLimits
  exact Functor.PullbackObjObj.ofIsTerminal (SimplicialCategory.sHomFunctor C)
    i (terminal.from Y) terminalIsTerminal

/-- The entire terminal-target corner map is the original precomposition map. -/
@[simp]
theorem terminalCorner_π {X X' : C} (i : X ⟶ X') (Y : C) :
    (terminalCorner a i Y).π = ((SimplicialCategory.sHomFunctor C).map i.op).app Y := rfl

/-- Original trivial cofibrations induce raw trivial fibrations by precomposition into fibrant
targets. -/
theorem precomp_trivialFibration {X X' : C} (i : X ⟶ X') [Cofibration i] [WeakEquivalence i]
    (Y : C) [IsFibrant Y] :
    trivialFibrations SSet.{v} (((SimplicialCategory.sHomFunctor C).map i.op).app Y) := by
  exact sm7_trivial_left a (terminalCorner a i Y) (mem_trivialCofibrations i)
    ((fibration_iff _).mp inferInstance)

/-- Brown's original coefficient factorization gives raw source invariance at the actual cofibrant
endpoints. -/
theorem precomp_weak {X X' : C} (i : X ⟶ X') [WeakEquivalence i]
    [IsCofibrant X] [IsCofibrant X'] (Y : C) [IsFibrant Y] :
    WeakEquivalence (((SimplicialCategory.sHomFunctor C).map i.op).app Y) := by
  change WeakEquivalence (((SimplicialCategory.sHomFunctor C).flip.obj Y).map i.op)
  apply sourceFunctor_weak_of_trivialCofibrations
  intro A B j _ _
  exact ((mem_trivialFibrations_iff (f := ((SimplicialCategory.sHomFunctor C).map j.op).app Y)).mp
    (precomp_trivialFibration a j Y)).2

end HomotopicalAlgebra.CompatibleSimplicialMapping

end
end
end

section



/-!
# Original generated mapping objects and the actual bifibrant presentation

The mixed mapping bifunctor uses the same original generated Q and R.
The actual RQ objects are bifibrant, with every original RQ morphism.
Their simplicial composition is the original enrichment's composition.
The natural comparison to mixed Q/R spaces keeps the original R image
of the Q counit and the original R unit at Q. Homotopical calculations
require a compatible model action and are proved separately.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory Limits MorphismProperty
open scoped MonoidalCategory

namespace HomotopicalAlgebra.GeneratedDerivedMapping

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements

/-- The actual same original replacement functor R after Q. -/
abbrev rq : C ⥤ C := Q d ⋙ R d

/-- Every original RQ object is fibrant by the same generated R. -/
theorem rq_isFibrant (X : C) : IsFibrant ((rq d).obj X) := R_isFibrant d ((Q d).obj X)

/-- Every original RQ object is cofibrant from Q and the same trivial-cofibration R unit. -/
theorem rq_isCofibrant (X : C) : IsCofibrant ((rq d).obj X) := by
  let _ : IsCofibrant ((Q d).obj X) := Q_isCofibrant d X
  let _ : Cofibration ((unit d).app ((Q d).obj X)) :=
    (cofibration_iff _).mpr (unit_trivialCofibration d ((Q d).obj X)).1
  exact isCofibrant_of_cofibration (X := (Q d).obj X) ((unit d).app ((Q d).obj X))

/-- The actual RQ functor lands in the original full category of bifibrant objects. -/
def toBifibrant : C ⥤ BifibrantObject C where
  obj X :=
    { obj := (rq d).obj X
      property := ⟨rq_isCofibrant d X, rq_isFibrant d X⟩ }
  map f := ObjectProperty.homMk ((rq d).map f)
  map_id X := by
    apply ObjectProperty.hom_ext
    exact (rq d).map_id X
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (rq d).map_comp f g

/-- The original bifibrant presentation retains the whole original RQ functor. -/
theorem toBifibrant_comp_inclusion : toBifibrant d ⋙ BifibrantObject.ι = rq d := rfl

/-- Every bifibrant presentation object is the same original RQ object. -/
theorem toBifibrant_obj (X : C) : ((toBifibrant d).obj X).obj = (R d).obj ((Q d).obj X) := rfl

/-- Every bifibrant presentation arrow is the same original R map of the original Q map. -/
theorem toBifibrant_map {X Y : C} (f : X ⟶ Y) :
    ((toBifibrant d).map f).hom = (R d).map ((Q d).map f) := rfl

/-- The complete original R unit at Q gives the natural source comparison Q to RQ. -/
def rqInclusion : Q d ⟶ rq d :=
  (Q d).rightUnitor.inv ≫ Functor.whiskerLeft (Q d) (unit d)

/-- The complete original R image of the Q counit gives the natural target comparison RQ to R. -/
def rqProjection : rq d ⟶ R d :=
  Functor.whiskerRight (counit d) (R d) ≫ (R d).leftUnitor.hom

/-- Every source comparison is the same original generated R unit at Q. -/
theorem rqInclusion_app (X : C) :
    (rqInclusion d).app X = (unit d).app ((Q d).obj X) := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- Every target comparison is the same original R image of the original Q counit. -/
theorem rqProjection_app (X : C) :
    (rqProjection d).app X = (R d).map ((counit d).app X) := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The original R unit at Q is weak at every original input object. -/
theorem rqInclusion_weak (X : C) : weakEquivalences C ((rqInclusion d).app X) := by
  rw [rqInclusion_app]
  exact unit_weak d ((Q d).obj X)

/-- The original R image of the Q counit is weak by the same generated R preservation theorem. -/
theorem rqProjection_weak (X : C) : weakEquivalences C ((rqProjection d).app X) := by
  rw [rqProjection_app]
  exact R_map_weak d ((counit d).app X) (counit_weak d X)

/-- The comparison's complete middle arrow is the original Q counit followed by the original R unit.
-/
theorem rqInclusion_projection : rqInclusion d ≫ rqProjection d = counit d ≫ unit d := by
  apply NatTrans.ext
  funext X
  simp only [NatTrans.comp_app, rqInclusion_app, rqProjection_app]
  exact ((unit d).naturality ((counit d).app X)).symm

variable [SimplicialCategory C]

/-- The mixed mapping bifunctor uses exactly the original generated Q and R on objects and maps. -/
def bifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{vC} :=
  (Q d).op ⋙ SimplicialCategory.sHomFunctor C ⋙
    (Functor.whiskeringLeft C C SSet.{vC}).obj (R d)

/-- The original mixed replacement mapping space. -/
abbrev space (X Y : C) : SSet.{vC} := ((bifunctor d).obj (.op X)).obj Y

/-- Every mixed mapping object is the original simplicial Hom of original Q and R objects. -/
theorem space_eq (X Y : C) : space d X Y = SimplicialCategory.sHom ((Q d).obj X) ((R d).obj Y) :=
  rfl

/-- Original source precomposition in the same generated mixed mapping bifunctor. -/
def precomp {X Y : C} (f : X ⟶ Y) (Z : C) : space d Y Z ⟶ space d X Z :=
  ((bifunctor d).map f.op).app Z

/-- Original target postcomposition in the same generated mixed mapping bifunctor. -/
def postcomp (X : C) {Y Z : C} (f : Y ⟶ Z) : space d X Y ⟶ space d X Z :=
  ((bifunctor d).obj (.op X)).map f

/-- Every mixed source function is the original enriched precomposition by the same Q map. -/
theorem precomp_eq {X Y : C} (f : X ⟶ Y) (Z : C) :
    precomp d f Z = eHomWhiskerRight SSet ((Q d).map f) ((R d).obj Z) := rfl

/-- Every mixed target function is the original enriched postcomposition by the same R map. -/
theorem postcomp_eq (X : C) {Y Z : C} (f : Y ⟶ Z) :
    postcomp d X f = eHomWhiskerLeft SSet ((Q d).obj X) ((R d).map f) := rfl

/-- The source function retains every original identity. -/
@[simp]
theorem precomp_id (X Z : C) : precomp d (𝟙 X) Z = 𝟙 (space d X Z) := by
  simp [precomp]

/-- The source function reverses every original composition. -/
@[simp]
theorem precomp_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (W : C) :
    precomp d (f ≫ g) W = precomp d g W ≫ precomp d f W := by
  simp [precomp]

/-- The target function retains every original identity. -/
@[simp]
theorem postcomp_id (X Y : C) : postcomp d X (𝟙 Y) = 𝟙 (space d X Y) := by
  simp [postcomp]

/-- The target function preserves every original composition. -/
@[simp]
theorem postcomp_comp (X : C) {Y Z W : C} (f : Y ⟶ Z) (g : Z ⟶ W) :
    postcomp d X (f ≫ g) = postcomp d X f ≫ postcomp d X g := by
  simp [postcomp]

/-- Both original mixed variable functions commute on all original morphisms. -/
theorem precomp_postcomp {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    precomp d f Y ≫ postcomp d X g = postcomp d X' g ≫ precomp d f Y' := by
  simp [precomp, postcomp]

/-- The strict mapping bifunctor uses the actual original bifibrant RQ presentation. -/
def strictBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{vC} :=
  (rq d).op ⋙ SimplicialCategory.sHomFunctor C ⋙
    (Functor.whiskeringLeft C C SSet.{vC}).obj (rq d)

/-- The actual bifibrant presentation's original enriched mapping object. -/
abbrev strictSpace (X Y : C) : SSet.{vC} := ((strictBifunctor d).obj (.op X)).obj Y

/-- Strict spaces are the original enriched Hom of the actual original RQ objects. -/
theorem strictSpace_eq (X Y : C) :
    strictSpace d X Y = SimplicialCategory.sHom ((rq d).obj X) ((rq d).obj Y) := rfl

/-- The original enriched composition on the actual bifibrant replacement presentation. -/
def strictComp (X Y Z : C) : strictSpace d X Y ⊗ strictSpace d Y Z ⟶ strictSpace d X Z :=
  eComp SSet ((rq d).obj X) ((rq d).obj Y) ((rq d).obj Z)

/-- The original enriched identity on the actual bifibrant replacement presentation. -/
def strictUnit (X : C) : 𝟙_ SSet.{vC} ⟶ strictSpace d X X := eId SSet ((rq d).obj X)

/-- The same actual replacement objects carry the original strict simplicial enrichment.
This is an enriched presentation; it does not replace the original ordinary Hom types of C. -/
@[instance_reducible]
def strictEnrichment : EnrichedCategory SSet.{vC} C where
  Hom := strictSpace d
  id := strictUnit d
  comp := strictComp d
  id_comp X Y := e_id_comp SSet ((rq d).obj X) ((rq d).obj Y)
  comp_id X Y := e_comp_id SSet ((rq d).obj X) ((rq d).obj Y)
  assoc W X Y Z := e_assoc SSet ((rq d).obj W) ((rq d).obj X) ((rq d).obj Y) ((rq d).obj Z)

/-- The entire strict-to-mixed comparison retains both actual original replacement arrows. -/
def strictToMixed : strictBifunctor d ⟶ bifunctor d where
  app X :=
    { app Y :=
        eHomWhiskerLeft SSet ((rq d).obj X.unop) ((rqProjection d).app Y) ≫
          eHomWhiskerRight SSet ((rqInclusion d).app X.unop) ((R d).obj Y)
      naturality Y Z g := by
        change eHomWhiskerLeft SSet ((rq d).obj X.unop) ((rq d).map g) ≫
            (eHomWhiskerLeft SSet ((rq d).obj X.unop) ((rqProjection d).app Z) ≫
              eHomWhiskerRight SSet ((rqInclusion d).app X.unop) ((R d).obj Z)) =
          (eHomWhiskerLeft SSet ((rq d).obj X.unop) ((rqProjection d).app Y) ≫
              eHomWhiskerRight SSet ((rqInclusion d).app X.unop) ((R d).obj Y)) ≫
            eHomWhiskerLeft SSet ((Q d).obj X.unop) ((R d).map g)
        rw [← eHomWhiskerLeft_comp_assoc, (rqProjection d).naturality g]
        rw [eHomWhiskerLeft_comp_assoc, eHom_whisker_exchange]
        simp only [Category.assoc] }
  naturality X Y f := by
    apply NatTrans.ext
    funext Z
    change eHomWhiskerRight SSet ((rq d).map f.unop) ((rq d).obj Z) ≫
        (eHomWhiskerLeft SSet ((rq d).obj Y.unop) ((rqProjection d).app Z) ≫
          eHomWhiskerRight SSet ((rqInclusion d).app Y.unop) ((R d).obj Z)) =
      (eHomWhiskerLeft SSet ((rq d).obj X.unop) ((rqProjection d).app Z) ≫
          eHomWhiskerRight SSet ((rqInclusion d).app X.unop) ((R d).obj Z)) ≫
        eHomWhiskerRight SSet ((Q d).map f.unop) ((R d).obj Z)
    simp only [Category.assoc]
    rw [← eHom_whisker_exchange_assoc]
    slice_lhs 2 3 => rw [← eHomWhiskerRight_comp]
    slice_rhs 2 3 => rw [← eHomWhiskerRight_comp]
    rw [(rqInclusion d).naturality f.unop]

/-- Every comparison component is postcomposition by R(q), then precomposition by r at Q. -/
theorem strictToMixed_app (X Y : C) :
    ((strictToMixed d).app (.op X)).app Y =
      eHomWhiskerLeft SSet ((rq d).obj X) ((R d).map ((counit d).app Y)) ≫
        eHomWhiskerRight SSet ((unit d).app ((Q d).obj X)) ((R d).obj Y) := by
  simp only [strictToMixed, rqProjection_app, rqInclusion_app]
  rfl

end HomotopicalAlgebra.GeneratedDerivedMapping

end
end
end

section



/-!
# Actual generated mapping invariance from the compatible model action

The original tensor/cotensor adjunctions and their source pushout-product
laws supply the raw mapping calculus. The same original Q/R objects,
maps and natural arrows then give mapping fibrancy, all input weak-map
invariances, and the natural weak comparison from the actual strict
bifibrant RQ presentation to mixed Q/R mapping objects.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory Limits MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.GeneratedDerivedMapping

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [SimplicialCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (a : CompatibleSimplicialMapping.Action C)

open GeneratedFunctorialReplacements

section Homotopical

include a

/-- The actual original mixed Q/R mapping space is fibrant from the compatible action. -/
theorem space_isFibrant (X Y : C) : IsFibrant (space d X Y) := by
  let _ : IsCofibrant ((Q d).obj X) := Q_isCofibrant d X
  let _ : IsFibrant ((R d).obj Y) := R_isFibrant d Y
  exact CompatibleSimplicialMapping.mapping_isFibrant a ((Q d).obj X) ((R d).obj Y)

/-- The actual original bifibrant RQ presentation has fibrant enriched mapping spaces. -/
theorem strictSpace_isFibrant (X Y : C) : IsFibrant (strictSpace d X Y) := by
  let _ : IsCofibrant ((rq d).obj X) := rq_isCofibrant d X
  let _ : IsFibrant ((rq d).obj Y) := rq_isFibrant d Y
  exact CompatibleSimplicialMapping.mapping_isFibrant a ((rq d).obj X) ((rq d).obj Y)

/-- Every original weak source morphism gives a weak precomposition map through the same original Q.
-/
theorem precomp_weak {X Y : C} (f : X ⟶ Y) [WeakEquivalence f] (Z : C) :
    WeakEquivalence (precomp d f Z) := by
  let _ : IsCofibrant ((Q d).obj X) := Q_isCofibrant d X
  let _ : IsCofibrant ((Q d).obj Y) := Q_isCofibrant d Y
  let _ : IsFibrant ((R d).obj Z) := R_isFibrant d Z
  let _ : WeakEquivalence ((Q d).map f) :=
    (weakEquivalence_iff _).mpr (Q_map_weak d f (mem_weakEquivalences f))
  exact CompatibleSimplicialMapping.precomp_weak a ((Q d).map f) ((R d).obj Z)

/-- Every original weak target morphism gives a weak postcomposition map through the same original
R. -/
theorem postcomp_weak (X : C) {Y Z : C} (f : Y ⟶ Z) [WeakEquivalence f] :
    WeakEquivalence (postcomp d X f) := by
  let _ : IsCofibrant ((Q d).obj X) := Q_isCofibrant d X
  let _ : IsFibrant ((R d).obj Y) := R_isFibrant d Y
  let _ : IsFibrant ((R d).obj Z) := R_isFibrant d Z
  let _ : WeakEquivalence ((R d).map f) :=
    (weakEquivalence_iff _).mpr (R_map_weak d f (mem_weakEquivalences f))
  exact CompatibleSimplicialMapping.postcomp_weak a ((Q d).obj X) ((R d).map f)

/-- The original strict RQ presentation maps every original weak source morphism weakly. -/
theorem strict_precomp_weak {X Y : C} (f : X ⟶ Y) [WeakEquivalence f] (Z : C) :
    WeakEquivalence (((strictBifunctor d).map f.op).app Z) := by
  let _ : IsCofibrant ((rq d).obj X) := rq_isCofibrant d X
  let _ : IsCofibrant ((rq d).obj Y) := rq_isCofibrant d Y
  let _ : IsFibrant ((rq d).obj Z) := rq_isFibrant d Z
  let _ : WeakEquivalence ((rq d).map f) :=
    (weakEquivalence_iff _).mpr
      (R_map_weak d ((Q d).map f) (Q_map_weak d f (mem_weakEquivalences f)))
  exact CompatibleSimplicialMapping.precomp_weak a ((rq d).map f) ((rq d).obj Z)

/-- The original strict RQ presentation maps every original weak target morphism weakly. -/
theorem strict_postcomp_weak (X : C) {Y Z : C} (f : Y ⟶ Z) [WeakEquivalence f] :
    WeakEquivalence (((strictBifunctor d).obj (.op X)).map f) := by
  let _ : IsCofibrant ((rq d).obj X) := rq_isCofibrant d X
  let _ : IsFibrant ((rq d).obj Y) := rq_isFibrant d Y
  let _ : IsFibrant ((rq d).obj Z) := rq_isFibrant d Z
  let _ : WeakEquivalence ((rq d).map f) :=
    (weakEquivalence_iff _).mpr
      (R_map_weak d ((Q d).map f) (Q_map_weak d f (mem_weakEquivalences f)))
  exact CompatibleSimplicialMapping.postcomp_weak a ((rq d).obj X) ((rq d).map f)

/-- The full natural strict-to-mixed comparison is weak by its same two original replacement maps.
-/
theorem strictToMixed_weak (X Y : C) :
    WeakEquivalence (((strictToMixed d).app (.op X)).app Y) := by
  let _ : IsCofibrant ((rq d).obj X) := rq_isCofibrant d X
  let _ : IsCofibrant ((Q d).obj X) := Q_isCofibrant d X
  let _ : IsFibrant ((rq d).obj Y) := rq_isFibrant d Y
  let _ : IsFibrant ((R d).obj Y) := R_isFibrant d Y
  let _ : WeakEquivalence ((rqProjection d).app Y) :=
    (weakEquivalence_iff _).mpr (rqProjection_weak d Y)
  let _ : WeakEquivalence ((rqInclusion d).app X) :=
    (weakEquivalence_iff _).mpr (rqInclusion_weak d X)
  let _ : WeakEquivalence
      (eHomWhiskerLeft SSet ((rq d).obj X) ((rqProjection d).app Y)) :=
    CompatibleSimplicialMapping.postcomp_weak a ((rq d).obj X) ((rqProjection d).app Y)
  let _ : WeakEquivalence
      (eHomWhiskerRight SSet ((rqInclusion d).app X) ((R d).obj Y)) :=
    CompatibleSimplicialMapping.precomp_weak a ((rqInclusion d).app X) ((R d).obj Y)
  change WeakEquivalence
    (eHomWhiskerLeft SSet ((rq d).obj X) ((rqProjection d).app Y) ≫
      eHomWhiskerRight SSet ((rqInclusion d).app X) ((R d).obj Y))
  infer_instance

end Homotopical

/-- Every full original source square commutes with the same weak strict-to-mixed comparison. -/
theorem strictToMixed_source_naturality {X X' : C} (f : X ⟶ X') (Y : C) :
    ((strictBifunctor d).map f.op).app Y ≫ ((strictToMixed d).app (.op X)).app Y =
      ((strictToMixed d).app (.op X')).app Y ≫ precomp d f Y :=
  congrArg (fun t : ((strictBifunctor d).obj (.op X')) ⟶ ((bifunctor d).obj (.op X)) => t.app Y)
    ((strictToMixed d).naturality f.op)

/-- Every full original target square commutes with the same weak strict-to-mixed comparison. -/
theorem strictToMixed_target_naturality (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    ((strictBifunctor d).obj (.op X)).map f ≫ ((strictToMixed d).app (.op X)).app Y' =
      ((strictToMixed d).app (.op X)).app Y ≫ postcomp d X f :=
  ((strictToMixed d).app (.op X)).naturality f

end HomotopicalAlgebra.GeneratedDerivedMapping

end
end
end

section



/-!
# Original strict replacement coherence and its actual mixed unit

Composition on the genuine RQ presentation is the original strict
enriched composition. Its unit comparison to mixed Q/R spaces is the
same original Q counit followed by the same original R unit. Every
original input morphism preserves that unit square.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory Limits MorphismProperty MonoidalCategory
open scoped MonoidalCategory

namespace HomotopicalAlgebra.GeneratedDerivedMapping

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [SimplicialCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements

/-- The strict left unit law is the original enriched unit law on the actual RQ objects. -/
theorem strictComp_leftUnit (X Y : C) :
    (λ_ (strictSpace d X Y)).inv ≫ strictUnit d X ▷ _ ≫ strictComp d X X Y =
      𝟙 (strictSpace d X Y) := (strictEnrichment d).id_comp X Y

/-- The strict right unit law is the original enriched unit law on the actual RQ objects. -/
theorem strictComp_rightUnit (X Y : C) :
    (ρ_ (strictSpace d X Y)).inv ≫ _ ◁ strictUnit d Y ≫ strictComp d X Y Y =
      𝟙 (strictSpace d X Y) := (strictEnrichment d).comp_id X Y

/-- The strict associativity law retains the original three composable mapping objects. -/
theorem strictComp_assoc (W X Y Z : C) :
    (α_ (strictSpace d W X) (strictSpace d X Y) (strictSpace d Y Z)).inv ≫
        strictComp d W X Y ▷ _ ≫ strictComp d W Y Z =
      _ ◁ strictComp d X Y Z ≫ strictComp d W X Z :=
  (strictEnrichment d).assoc W X Y Z

/-- The mixed unit is the actual original Q counit followed by the original R unit. -/
def mixedUnit (X : C) : 𝟙_ SSet.{vC} ⟶ space d X X :=
  eHomEquiv SSet ((counit d).app X ≫ (unit d).app X)

/-- The original strict unit maps to that same actual mixed Q/R arrow. -/
theorem strictUnit_comparison (X : C) :
    strictUnit d X ≫ ((strictToMixed d).app (.op X)).app X = mixedUnit d X := by
  change eId SSet ((rq d).obj X) ≫
      (eHomWhiskerLeft SSet ((rq d).obj X) ((rqProjection d).app X) ≫
        eHomWhiskerRight SSet ((rqInclusion d).app X) ((R d).obj X)) = _
  rw [← eHomEquiv_id SSet, ← Category.assoc,
    eHomEquiv_comp_eHomWhiskerLeft SSet C, Category.id_comp,
    eHomEquiv_comp_eHomWhiskerRight SSet C]
  have hn : (rqInclusion d).app X ≫ (rqProjection d).app X =
      (counit d).app X ≫ (unit d).app X :=
    congrArg (fun t : Q d ⟶ R d => t.app X) (rqInclusion_projection d)
  rw [hn]
  rfl

/-- Every original input map retains the complete actual mixed unit square. -/
theorem mixedUnit_naturality {X Y : C} (f : X ⟶ Y) :
    mixedUnit d X ≫ postcomp d X f = mixedUnit d Y ≫ precomp d f Y := by
  rw [postcomp_eq, precomp_eq]
  change eHomEquiv SSet ((counit d).app X ≫ (unit d).app X) ≫
      eHomWhiskerLeft SSet ((Q d).obj X) ((R d).map f) =
    eHomEquiv SSet ((counit d).app Y ≫ (unit d).app Y) ≫
      eHomWhiskerRight SSet ((Q d).map f) ((R d).obj Y)
  rw [eHomEquiv_comp_eHomWhiskerLeft SSet C, eHomEquiv_comp_eHomWhiskerRight SSet C]
  congr 1
  rw [Category.assoc, ← (unit d).naturality f, ← Category.assoc, ← (counit d).naturality f,
    Category.assoc]

end HomotopicalAlgebra.GeneratedDerivedMapping

end
end
end

section



/-!
# Natural mapping comparison spans between all original generated choices

The two source-generation cardinals and their cell universes may be
independent. Both original Q comparison maps and both original R comparison
maps give natural weak comparison maps to one mapping-space center. The
same original counit/unit compatibility identifies both actual mixed units.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w₁ w₂ uC vC

open CategoryTheory Limits MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.GeneratedDerivedMapping

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [SimplicialCategory C]
  {κ₁ : Cardinal.{w₁}} [Fact κ₁.IsRegular] [OrderBot κ₁.ord.ToType]
  {κ₂ : Cardinal.{w₂}} [Fact κ₂.IsRegular] [OrderBot κ₂.ord.ToType]
  (d : CofibrantGenerationData C κ₁) (e : CofibrantGenerationData C κ₂)

open GeneratedFunctorialReplacements

/-- The actual mapping comparison center uses both original Q and both original R functors. -/
def comparisonCenter : Cᵒᵖ ⥤ C ⥤ SSet.{vC} :=
  (Q d ⋙ Q e).op ⋙ SimplicialCategory.sHomFunctor C ⋙
    (Functor.whiskeringLeft C C SSet.{vC}).obj (R d ⋙ R e)

/-- Both original left comparison arrows give the entire first mapping-space comparison. -/
def comparisonLeft : bifunctor d ⟶ comparisonCenter d e :=
  Functor.whiskerRight
      (Functor.whiskerRight (NatTrans.op (qComparisonLeft d e)) (SimplicialCategory.sHomFunctor C))
      ((Functor.whiskeringLeft C C SSet.{vC}).obj (R d)) ≫
    Functor.whiskerLeft ((Q d ⋙ Q e).op ⋙ SimplicialCategory.sHomFunctor C)
      ((Functor.whiskeringLeft C C SSet.{vC}).map (rComparisonLeft d e))

/-- Both original right comparison arrows give the entire second mapping-space comparison. -/
def comparisonRight : bifunctor e ⟶ comparisonCenter d e :=
  Functor.whiskerRight
      (Functor.whiskerRight (NatTrans.op (qComparisonRight d e)) (SimplicialCategory.sHomFunctor C))
      ((Functor.whiskeringLeft C C SSet.{vC}).obj (R e)) ≫
    Functor.whiskerLeft ((Q d ⋙ Q e).op ⋙ SimplicialCategory.sHomFunctor C)
      ((Functor.whiskeringLeft C C SSet.{vC}).map (rComparisonRight d e))

/-- The first whole mapping comparison retains both exact original left Q/R component maps. -/
theorem comparisonLeft_app (X Y : C) :
    ((comparisonLeft d e).app (.op X)).app Y =
      eHomWhiskerRight SSet ((qComparisonLeft d e).app X) ((R d).obj Y) ≫
        eHomWhiskerLeft SSet ((Q d ⋙ Q e).obj X) ((rComparisonLeft d e).app Y) := rfl

/-- The second whole mapping comparison retains both exact original right Q/R component maps. -/
theorem comparisonRight_app (X Y : C) :
    ((comparisonRight d e).app (.op X)).app Y =
      eHomWhiskerRight SSet ((qComparisonRight d e).app X) ((R e).obj Y) ≫
        eHomWhiskerLeft SSet ((Q d ⋙ Q e).obj X) ((rComparisonRight d e).app Y) := rfl

section Homotopical

variable (a : CompatibleSimplicialMapping.Action C)
include a

/-- The first full comparison is weak from the same original Q/R comparison arrows. -/
theorem comparisonLeft_weak (X Y : C) :
    WeakEquivalence (((comparisonLeft d e).app (.op X)).app Y) := by
  let _ : IsCofibrant ((Q d ⋙ Q e).obj X) := Q_comparison_center_isCofibrant d e X
  let _ : IsCofibrant ((Q d).obj X) := Q_isCofibrant d X
  let _ : IsFibrant ((R d).obj Y) := R_isFibrant d Y
  let _ : IsFibrant ((R d ⋙ R e).obj Y) := R_comparison_center_isFibrant d e Y
  let _ : WeakEquivalence ((qComparisonLeft d e).app X) :=
    (weakEquivalence_iff _).mpr (Q_comparison_left_weak d e X)
  let _ : WeakEquivalence ((rComparisonLeft d e).app Y) :=
    (weakEquivalence_iff _).mpr (R_comparison_left_weak d e Y)
  let _ : WeakEquivalence
      (eHomWhiskerRight SSet ((qComparisonLeft d e).app X) ((R d).obj Y)) :=
    CompatibleSimplicialMapping.precomp_weak a ((qComparisonLeft d e).app X) ((R d).obj Y)
  let _ : WeakEquivalence
      (eHomWhiskerLeft SSet ((Q d ⋙ Q e).obj X) ((rComparisonLeft d e).app Y)) :=
    CompatibleSimplicialMapping.postcomp_weak a ((Q d ⋙ Q e).obj X) ((rComparisonLeft d e).app Y)
  rw [comparisonLeft_app]
  exact (weakEquivalence_iff _).mpr ((weakEquivalences SSet.{vC}).comp_mem _ _
    (mem_weakEquivalences
      (eHomWhiskerRight SSet ((qComparisonLeft d e).app X) ((R d).obj Y)))
    (mem_weakEquivalences
      (eHomWhiskerLeft SSet ((Q d ⋙ Q e).obj X) ((rComparisonLeft d e).app Y))))

/-- The second full comparison is weak from the same original Q/R comparison arrows. -/
theorem comparisonRight_weak (X Y : C) :
    WeakEquivalence (((comparisonRight d e).app (.op X)).app Y) := by
  let _ : IsCofibrant ((Q d ⋙ Q e).obj X) := Q_comparison_center_isCofibrant d e X
  let _ : IsCofibrant ((Q e).obj X) := Q_isCofibrant e X
  let _ : IsFibrant ((R e).obj Y) := R_isFibrant e Y
  let _ : IsFibrant ((R d ⋙ R e).obj Y) := R_comparison_center_isFibrant d e Y
  let _ : WeakEquivalence ((qComparisonRight d e).app X) :=
    (weakEquivalence_iff _).mpr (Q_comparison_right_weak d e X)
  let _ : WeakEquivalence ((rComparisonRight d e).app Y) :=
    (weakEquivalence_iff _).mpr (R_comparison_right_weak d e Y)
  let _ : WeakEquivalence
      (eHomWhiskerRight SSet ((qComparisonRight d e).app X) ((R e).obj Y)) :=
    CompatibleSimplicialMapping.precomp_weak a ((qComparisonRight d e).app X) ((R e).obj Y)
  let _ : WeakEquivalence
      (eHomWhiskerLeft SSet ((Q d ⋙ Q e).obj X) ((rComparisonRight d e).app Y)) :=
    CompatibleSimplicialMapping.postcomp_weak a ((Q d ⋙ Q e).obj X) ((rComparisonRight d e).app Y)
  rw [comparisonRight_app]
  exact (weakEquivalence_iff _).mpr ((weakEquivalences SSet.{vC}).comp_mem _ _
    (mem_weakEquivalences
      (eHomWhiskerRight SSet ((qComparisonRight d e).app X) ((R e).obj Y)))
    (mem_weakEquivalences
      (eHomWhiskerLeft SSet ((Q d ⋙ Q e).obj X) ((rComparisonRight d e).app Y))))

end Homotopical

/-- The first full comparison retains every original source morphism. -/
theorem comparisonLeft_source_naturality {X X' : C} (f : X ⟶ X') (Y : C) :
    precomp d f Y ≫ ((comparisonLeft d e).app (.op X)).app Y =
      ((comparisonLeft d e).app (.op X')).app Y ≫ ((comparisonCenter d e).map f.op).app Y :=
  congrArg (fun t : ((bifunctor d).obj (.op X')) ⟶ ((comparisonCenter d e).obj (.op X)) => t.app Y)
    ((comparisonLeft d e).naturality f.op)

/-- The second full comparison retains every original source morphism. -/
theorem comparisonRight_source_naturality {X X' : C} (f : X ⟶ X') (Y : C) :
    precomp e f Y ≫ ((comparisonRight d e).app (.op X)).app Y =
      ((comparisonRight d e).app (.op X')).app Y ≫ ((comparisonCenter d e).map f.op).app Y :=
  congrArg (fun t : ((bifunctor e).obj (.op X')) ⟶ ((comparisonCenter d e).obj (.op X)) => t.app Y)
    ((comparisonRight d e).naturality f.op)

/-- The first full comparison retains every original target morphism. -/
theorem comparisonLeft_target_naturality (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    postcomp d X f ≫ ((comparisonLeft d e).app (.op X)).app Y' =
      ((comparisonLeft d e).app (.op X)).app Y ≫ ((comparisonCenter d e).obj (.op X)).map f :=
  ((comparisonLeft d e).app (.op X)).naturality f

/-- The second full comparison retains every original target morphism. -/
theorem comparisonRight_target_naturality (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    postcomp e X f ≫ ((comparisonRight d e).app (.op X)).app Y' =
      ((comparisonRight d e).app (.op X)).app Y ≫ ((comparisonCenter d e).obj (.op X)).map f :=
  ((comparisonRight d e).app (.op X)).naturality f

/-- Both original mixed units have the same image under the complete original replacement span. -/
theorem comparison_units (X : C) :
    mixedUnit d X ≫ ((comparisonLeft d e).app (.op X)).app X =
      mixedUnit e X ≫ ((comparisonRight d e).app (.op X)).app X := by
  rw [comparisonLeft_app, comparisonRight_app]
  change eHomEquiv SSet ((counit d).app X ≫ (unit d).app X) ≫
      (eHomWhiskerRight SSet ((qComparisonLeft d e).app X) ((R d).obj X) ≫
        eHomWhiskerLeft SSet ((Q d ⋙ Q e).obj X) ((rComparisonLeft d e).app X)) =
    eHomEquiv SSet ((counit e).app X ≫ (unit e).app X) ≫
      (eHomWhiskerRight SSet ((qComparisonRight d e).app X) ((R e).obj X) ≫
        eHomWhiskerLeft SSet ((Q d ⋙ Q e).obj X) ((rComparisonRight d e).app X))
  conv_lhs =>
    rw [← Category.assoc, eHomEquiv_comp_eHomWhiskerRight SSet C,
      eHomEquiv_comp_eHomWhiskerLeft SSet C]
  conv_rhs =>
    rw [← Category.assoc, eHomEquiv_comp_eHomWhiskerRight SSet C,
      eHomEquiv_comp_eHomWhiskerLeft SSet C]
  have hQ : (qComparisonLeft d e).app X ≫ (counit d).app X =
      (qComparisonRight d e).app X ≫ (counit e).app X :=
    congrArg (fun t : Q d ⋙ Q e ⟶ 𝟭 C => t.app X) (Q_comparison_counits d e)
  have hR : (unit d).app X ≫ (rComparisonLeft d e).app X =
      (unit e).app X ≫ (rComparisonRight d e).app X :=
    congrArg (fun t : 𝟭 C ⟶ R d ⋙ R e => t.app X) (R_comparison_units d e)
  congr 1
  calc
    ((qComparisonLeft d e).app X ≫ ((counit d).app X ≫ (unit d).app X)) ≫
        (rComparisonLeft d e).app X =
        ((qComparisonLeft d e).app X ≫ (counit d).app X) ≫
          ((unit d).app X ≫ (rComparisonLeft d e).app X) := by simp only [Category.assoc]
    _ = ((qComparisonRight d e).app X ≫ (counit e).app X) ≫
        ((unit e).app X ≫ (rComparisonRight d e).app X) := by rw [hQ, hR]
    _ = ((qComparisonRight d e).app X ≫ ((counit e).app X ≫ (unit e).app X)) ≫
        (rComparisonRight d e).app X := by simp only [Category.assoc]

end HomotopicalAlgebra.GeneratedDerivedMapping

end
end
end

section



/-!
# Cofibrant-source/fibrant-target calculations with the same original replacements

The original enriched mapping bifunctor compares naturally to the actual
mixed Q/R bifunctor by the same original R unit and Q counit. At genuine
cofibrant-source/fibrant-target endpoints, the compatible model action
proves that this complete original comparison is weak.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory Limits MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.GeneratedDerivedMapping

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [SimplicialCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements

/-- The full original enriched mapping functor compares by the original R unit and Q counit. -/
def ordinaryToMixed : SimplicialCategory.sHomFunctor C ⟶ bifunctor d where
  app X :=
    { app Y :=
        eHomWhiskerLeft SSet X.unop ((unit d).app Y) ≫
          eHomWhiskerRight SSet ((counit d).app X.unop) ((R d).obj Y)
      naturality Y Z g := by
        change eHomWhiskerLeft SSet X.unop g ≫
            (eHomWhiskerLeft SSet X.unop ((unit d).app Z) ≫
              eHomWhiskerRight SSet ((counit d).app X.unop) ((R d).obj Z)) =
          (eHomWhiskerLeft SSet X.unop ((unit d).app Y) ≫
              eHomWhiskerRight SSet ((counit d).app X.unop) ((R d).obj Y)) ≫
            eHomWhiskerLeft SSet ((Q d).obj X.unop) ((R d).map g)
        have hn := (unit d).naturality g
        simp only [Functor.id_map] at hn
        rw [← eHomWhiskerLeft_comp_assoc, hn]
        rw [eHomWhiskerLeft_comp_assoc, eHom_whisker_exchange]
        simp only [Category.assoc] }
  naturality X Y f := by
    apply NatTrans.ext
    funext Z
    change eHomWhiskerRight SSet f.unop Z ≫
        (eHomWhiskerLeft SSet Y.unop ((unit d).app Z) ≫
          eHomWhiskerRight SSet ((counit d).app Y.unop) ((R d).obj Z)) =
      (eHomWhiskerLeft SSet X.unop ((unit d).app Z) ≫
          eHomWhiskerRight SSet ((counit d).app X.unop) ((R d).obj Z)) ≫
        eHomWhiskerRight SSet ((Q d).map f.unop) ((R d).obj Z)
    simp only [Category.assoc]
    rw [← eHom_whisker_exchange_assoc]
    slice_lhs 2 3 => rw [← eHomWhiskerRight_comp]
    slice_rhs 2 3 => rw [← eHomWhiskerRight_comp]
    have hn := (counit d).naturality f.unop
    simp only [Functor.id_map] at hn
    rw [hn]

/-- Every endpoint comparison component retains the same original R and Q arrows. -/
theorem ordinaryToMixed_app (X Y : C) :
    ((ordinaryToMixed d).app (.op X)).app Y =
      eHomWhiskerLeft SSet X ((unit d).app Y) ≫
        eHomWhiskerRight SSet ((counit d).app X) ((R d).obj Y) := rfl

/-- The complete original enriched comparison is weak at original cofibrant/fibrant endpoints. -/
theorem ordinaryToMixed_weak (a : CompatibleSimplicialMapping.Action C)
    (X Y : C) [IsCofibrant X] [IsFibrant Y] :
    WeakEquivalence (((ordinaryToMixed d).app (.op X)).app Y) := by
  let _ : IsCofibrant ((Q d).obj X) := Q_isCofibrant d X
  let _ : IsFibrant ((R d).obj Y) := R_isFibrant d Y
  let _ : IsFibrant ((𝟭 C).obj Y) := by simpa only [Functor.id_obj] using
      (inferInstance : IsFibrant Y)
  let _ : IsCofibrant ((𝟭 C).obj X) := by simpa only [Functor.id_obj] using
      (inferInstance : IsCofibrant X)
  let _ : WeakEquivalence ((unit d).app Y) := (weakEquivalence_iff _).mpr (unit_weak d Y)
  let _ : WeakEquivalence ((counit d).app X) := (weakEquivalence_iff _).mpr (counit_weak d X)
  let _ : WeakEquivalence (eHomWhiskerLeft SSet X ((unit d).app Y)) :=
    CompatibleSimplicialMapping.postcomp_weak a X ((unit d).app Y)
  let _ : WeakEquivalence (eHomWhiskerRight SSet ((counit d).app X) ((R d).obj Y)) :=
    CompatibleSimplicialMapping.precomp_weak a ((counit d).app X) ((R d).obj Y)
  rw [ordinaryToMixed_app]
  exact (weakEquivalence_iff _).mpr ((weakEquivalences SSet.{vC}).comp_mem _ _
    (mem_weakEquivalences (eHomWhiskerLeft SSet X ((unit d).app Y)))
    (mem_weakEquivalences (eHomWhiskerRight SSet ((counit d).app X) ((R d).obj Y))))

/-- The original endpoint calculation keeps every original source morphism. -/
theorem ordinaryToMixed_source_naturality {X X' : C} (f : X ⟶ X') (Y : C) :
    ((SimplicialCategory.sHomFunctor C).map f.op).app Y ≫ ((ordinaryToMixed d).app (.op X)).app Y =
      ((ordinaryToMixed d).app (.op X')).app Y ≫ precomp d f Y :=
  congrArg
      (fun t : ((SimplicialCategory.sHomFunctor C).obj (.op X')) ⟶ ((bifunctor d).obj (.op X)) =>
      t.app Y) ((ordinaryToMixed d).naturality f.op)

/-- The original endpoint calculation keeps every original target morphism. -/
theorem ordinaryToMixed_target_naturality (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    ((SimplicialCategory.sHomFunctor C).obj (.op X)).map f ≫
        ((ordinaryToMixed d).app (.op X)).app Y' =
      ((ordinaryToMixed d).app (.op X)).app Y ≫ postcomp d X f :=
  ((ordinaryToMixed d).app (.op X)).naturality f

/-- The original enriched identity has the same actual mixed unit image. -/
theorem ordinaryUnit_comparison (X : C) :
    eId SSet X ≫ ((ordinaryToMixed d).app (.op X)).app X = mixedUnit d X := by
  rw [ordinaryToMixed_app]
  change eId SSet X ≫
      (eHomWhiskerLeft SSet X ((unit d).app X) ≫
        eHomWhiskerRight SSet ((counit d).app X) ((R d).obj X)) = _
  rw [← eHomEquiv_id SSet, ← Category.assoc,
    eHomEquiv_comp_eHomWhiskerLeft SSet C, Category.id_comp,
    eHomEquiv_comp_eHomWhiskerRight SSet C]
  rfl

end HomotopicalAlgebra.GeneratedDerivedMapping

end
end
end
