/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.CombinatorialSourceRecognition
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.LocalTrivialCofibrationClosure
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenFibrantCriterion
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import MathlibExt.AlgebraicTopology.ModelCategory.GivenFactorizationReplacements
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.Equivalence
import MathlibExt.AlgebraicTopology.ModelCategory.Combinatorial
import Mathlib.CategoryTheory.Presentable.Adjunction

/-!
# The actual enriched localization produced by combinatorial sources

The original source recognition theorem constructs the localization datum.
Its selected carrier retains the original enriched Hom objects, composition,
identity maps, and ordinary Hom equivalence. Local mapping tests use the actual
source tensor and cotensor adjunctions at all original arrow endpoints.
-/

set_option autoImplicit false
noncomputable section

universe w wS u v

open CategoryTheory Limits MorphismProperty Opposite
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.SelectedEnrichmentTransport

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
  [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
  [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]
  {K : Type wS} {S : K → Arrow C} (L : LeftBousfieldLocalizationData S)

/-- The original complete endofunctor on the selected localization carrier. -/
def functor (F : C ⥤ C) : LeftLocalized L ⥤ LeftLocalized L :=
  LeftLocalized.toBase L ⋙ F ⋙ LeftLocalized.ofBase L

/-- The whole original adjunction retains both original natural transformations and triangle laws. -/
def adjunction {F G : C ⥤ C} (adj : F ⊣ G) : functor L F ⊣ functor L G where
  unit :=
    { app X := InducedCategory.homMk (adj.unit.app X.1)
      naturality _ _ f := by
        apply InducedCategory.hom_ext
        exact adj.unit.naturality f.hom }
  counit :=
    { app X := InducedCategory.homMk (adj.counit.app X.1)
      naturality _ _ f := by
        apply InducedCategory.hom_ext
        exact adj.counit.naturality f.hom }
  left_triangle_components X := by
    apply InducedCategory.hom_ext
    exact adj.left_triangle_components X.1
  right_triangle_components X := by
    apply InducedCategory.hom_ext
    exact adj.right_triangle_components X.1

/-- The actual entire supplied factory is transported, including all Arrow maps and both factors. -/
def factors {P Q : MorphismProperty C} (data : FunctorialFactorizationData P Q) :
    FunctorialFactorizationData (P.inverseImage (LeftLocalized.toBase L))
      (Q.inverseImage (LeftLocalized.toBase L)) where
  Z := (LeftLocalized.toBase L).mapArrow ⋙ data.Z ⋙ LeftLocalized.ofBase L
  i :=
    { app F := InducedCategory.homMk (data.i.app ((LeftLocalized.toBase L).mapArrow.obj F))
      naturality _ _ a := by
        apply InducedCategory.hom_ext
        exact data.i.naturality ((LeftLocalized.toBase L).mapArrow.map a) }
  p :=
    { app F := InducedCategory.homMk (data.p.app ((LeftLocalized.toBase L).mapArrow.obj F))
      naturality _ _ a := by
        apply InducedCategory.hom_ext
        exact data.p.naturality ((LeftLocalized.toBase L).mapArrow.map a) }
  fac := by
    apply NatTrans.ext
    funext F
    apply InducedCategory.hom_ext
    exact data.fac_app
  hi F := data.hi ((LeftLocalized.toBase L).mapArrow.obj F)
  hp F := data.hp ((LeftLocalized.toBase L).mapArrow.obj F)

end HomotopicalAlgebra.SelectedEnrichmentTransport

namespace HomotopicalAlgebra.CompatibleSimplicialMapping

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
  (a : Action C)

/-- The actual initial parameter pushout product retains the original coefficient tensor map. -/
def parameterInitialPushout {X Y : C} (i : X ⟶ Y) (A : SSet.{v}) :
    a.tensor.PushoutObjObj i (initial.to A) := by
  letI : PreservesColimitsOfSize.{0, 0} (a.tensor.obj X) :=
    (a.tensorHom.adj X).leftAdjoint_preservesColimits
  letI : PreservesColimitsOfSize.{0, 0} (a.tensor.obj Y) :=
    (a.tensorHom.adj Y).leftAdjoint_preservesColimits
  exact Functor.PushoutObjObj.ofIsInitialRight a.tensor i (initial.to A) initialIsInitial

/-- Every simplicial parameter gives the original complete coefficient Quillen adjunction. -/
theorem parameterAdjunction_isQuillen (A : SSet.{v}) :
    (a.tensorCotensor.adj A).IsQuillenAdjunction := by
  have hA : cofibrations SSet.{v} (initial.to A) :=
    (cofibration_iff _).mp (CompatibleCotensorFraming.simplicial_isCofibrant A)
  constructor
  · intro X Y i hi
    exact a.cof_cof i (initial.to A) (parameterInitialPushout a i A) hi hA
  · intro X Y i hi
    exact a.trivial_cof i (initial.to A) (parameterInitialPushout a i A) hi hA

end HomotopicalAlgebra.CompatibleSimplicialMapping

namespace HomotopicalAlgebra.CombinatorialEnrichment

open CombinatorialSourceRecognition (localizationData)

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
  [IsLeftProper C] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (a : CompatibleSimplicialMapping.Action C)
  {K : Type wS} (S : K → Arrow C) [Small.{w} K]
  (κLP : Cardinal.{w}) [Fact κLP.IsRegular] [IsCardinalLocallyPresentable C κLP]

/-- The actual family-tagged carrier of the source-produced localization. -/
abbrev Localized :=
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  LeftLocalized (localizationData d a S κLP)

/-- The source-produced datum supplies the full model on its actual selected carrier. -/
@[instance_reducible]
def modelCategory : ModelCategory (Localized d a S κLP) := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  exact inferInstance

/-- Every selected enriched Hom is the unchanged original enriched Hom. -/
@[instance_reducible]
instance simplicialCategory : SimplicialCategory (Localized d a S κLP) where
  Hom X Y := SimplicialCategory.sHom X.1 Y.1
  id X := eId SSet X.1
  comp X Y Z := eComp SSet X.1 Y.1 Z.1
  id_comp X Y := e_id_comp SSet X.1 Y.1
  comp_id X Y := e_comp_id SSet X.1 Y.1
  assoc W X Y Z := e_assoc SSet W.1 X.1 Y.1 Z.1
  homEquiv :=
    { toFun := fun f => eHomEquiv SSet f.hom
      invFun := fun f => InducedCategory.homMk ((eHomEquiv SSet).symm f)
      left_inv := fun f => by
        apply InducedCategory.hom_ext
        exact (eHomEquiv SSet).symm_apply_apply f.hom
      right_inv := fun f => (eHomEquiv SSet).apply_symm_apply f }
  homEquiv_id X := eHomEquiv_id SSet X.1
  homEquiv_comp f g := eHomEquiv_comp SSet f.hom g.hom

/-- The selected carrier retains the original enriched Hom object at every pair. -/
theorem enrichedHom_eq (X Y : Localized d a S κLP) :
    SimplicialCategory.sHom X Y = SimplicialCategory.sHom X.1 Y.1 := rfl

/-- The selected enriched composition is the original complete composition map. -/
theorem enrichedComp_eq (X Y Z : Localized d a S κLP) :
    eComp SSet X Y Z = eComp SSet X.1 Y.1 Z.1 := rfl

/-- The selected enriched identity is the original complete identity map. -/
theorem enrichedUnit_eq (X : Localized d a S κLP) : eId SSet X = eId SSet X.1 := rfl

include a κLP in
/-- A source cofibration and a localized fibration give the same actual fibrant mapping corner. -/
theorem originalLocalCorner_fibration {X X' Y Y' : C} {i : X ⟶ X'} {p : Y ⟶ Y'}
    (sq : (SimplicialCategory.sHomFunctor C).PullbackObjObj i p)
    (hi : cofibrations C i)
    (hp : letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    localizedFibrations S p) :
    fibrations SSet.{v} sq.π := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩

  rw [← trivialCofibrations_rlp SSet.{v}]
  intro A B j hj
  let push := Functor.PushoutObjObj.ofHasPushout a.tensor i j
  have hpush : trivialCofibrations C push.ι := a.cof_trivial i j push hi hj
  exact (a.tensorHom.hasLiftingProperty_iff push sq).mp
    (hp push.ι ⟨hpush.1, (localizationData d a S κLP).baseWeak_le push.ι hpush.2⟩)

omit [Small.{w} K] in
include a in
/-- Every original local trivial cofibration has its actual raw trivial mapping fibration,
including all noncofibrant original endpoints and every original local-fibrant target. -/
theorem originalLocalPrecomp_trivialFibration {X Y : C} (i : X ⟶ Y)
    (hi : cofibrations C i)
    (hw : letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    localEquivalences S i) (Z : C)
    (hZ : letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    isLocalFibrant S Z) :
    trivialFibrations SSet.{v} (((SimplicialCategory.sHomFunctor C).map i.op).app Z) := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let _ : Cofibration i := (cofibration_iff i).mpr hi
  apply (LocalTrivialCofibrationClosure.rawTests_iff i Z).mp
  apply LocalTrivialCofibrationClosure.rawTests_of_nativeLocal_cofibration d a S i
  · rw [GeneratedLocalReplacement.generatedLocalEquivalences_eq_original d a S]
    exact hw
  · exact (GeneratedLocalReplacement.generatedLocalFibrant_iff_original d a S Z).mpr hZ


/-- The original fixed-target enriched mapping functor on the produced selected carrier. -/
def mappingToOpposite (Z : C) : Localized d a S κLP ⥤ SSet.{v}ᵒᵖ := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  exact LeftLocalized.toBase (localizationData d a S κLP) ⋙
    CompatibleCotensorFraming.mappingToOpposite Z

/-- The original fixed-target cotensor with the produced localization tag. -/
def cotensorAt (Z : C) : SSet.{v}ᵒᵖ ⥤ Localized d a S κLP := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  exact CompatibleCotensorFraming.cotensorAt a Z ⋙
    LeftLocalized.ofBase (localizationData d a S κLP)

/-- Both full original source adjunctions descend to the selected fixed-target cotensor. -/
def cotensorAdjunction (Z : C) : mappingToOpposite d a S κLP Z ⊣ cotensorAt d a S κLP Z := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  exact (LeftLocalized.equivalence (localizationData d a S κLP)).symm.toAdjunction.comp
    (CompatibleCotensorFraming.cotensorAdjunction a Z)

/-- The original local-fibrant mapping tests make the actual fixed-target cotensor adjunction Quillen. -/
theorem cotensorAdjunction_isQuillen (Z : C)
    (hZ : letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
      letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
        ⟨⟨d.fibrantFactorizationData⟩⟩
      isLocalFibrant S Z) : (cotensorAdjunction d a S κLP Z).IsQuillenAdjunction := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let _ : IsFibrant Z := hZ.1
  constructor
  · intro X Y i hi
    rw [cofibrations_op]
    change fibrations SSet.{v} (((SimplicialCategory.sHomFunctor C).map i.hom.op).app Z)
    change cofibrations C i.hom at hi
    exact CompatibleSimplicialMapping.sm7_fibration a
      (CompatibleSimplicialMapping.terminalCorner a i.hom Z) hi
      ((fibration_iff (terminal.from Z)).mp inferInstance)
  · intro X Y i hi
    rw [trivialCofibrations_op]
    change trivialFibrations SSet.{v} (((SimplicialCategory.sHomFunctor C).map i.hom.op).app Z)
    change cofibrations C i.hom ∧ localEquivalences S i.hom at hi
    exact originalLocalPrecomp_trivialFibration d a S i.hom hi.1 hi.2 Z hZ

include κLP in
/-- Every original simplicial parameter gives a local-fibrant cotensor of the same local-fibrant target. -/
theorem cotensor_isLocalFibrant (Z : C)
    (hZ : letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
      letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
        ⟨⟨d.fibrantFactorizationData⟩⟩
      isLocalFibrant S Z) (A : SSet.{v}) :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    isLocalFibrant S ((a.cotensor.obj (op A)).obj Z) := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let _ : (cotensorAdjunction d a S κLP Z).IsQuillenAdjunction :=
    cotensorAdjunction_isQuillen d a S κLP Z hZ
  let _ : IsFibrant (op A) :=
    (isFibrant_iff_of_isTerminal (initial.to A).op initialIsInitial.op).mpr (by
      apply (fibration_iff _).mpr
      rw [fibrations_op]
      change cofibrations SSet.{v} (initial.to A)
      exact (cofibration_iff (initial.to A)).mp
        ((SSet.modelCategoryQuillen.cofibration_iff (initial.to A)).mpr
          (inferInstanceAs (Mono (initial.to A)))))
  have h := Adjunction.IsQuillenAdjunction.preservesFibrantObjects
    (adj := cotensorAdjunction d a S κLP Z) (inferInstance : IsFibrant (op A))
  exact (LeftLocalized.fibrant_iff (localizationData d a S κLP) _).mp h

section SourceChoices

/-- Both variables and every component map of the original tensor retain their original values. -/
def tensor : Localized d a S κLP ⥤ SSet.{v} ⥤ Localized d a S κLP := by
  letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  exact
    LeftLocalized.toBase (localizationData d a S κLP) ⋙ a.tensor ⋙
      (Functor.whiskeringRight SSet.{v} C (Localized d a S κLP)).obj
        (LeftLocalized.ofBase (localizationData d a S κLP))

/-- Both variables and every component map of the original cotensor retain their original values. -/
def cotensor : SSet.{v}ᵒᵖ ⥤ Localized d a S κLP ⥤ Localized d a S κLP := by
  letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  exact
    a.cotensor ⋙
      (Functor.whiskeringLeft (Localized d a S κLP) C C).obj
        (LeftLocalized.toBase (localizationData d a S κLP)) ⋙
      (Functor.whiskeringRight (Localized d a S κLP) C (Localized d a S κLP)).obj
        (LeftLocalized.ofBase (localizationData d a S κLP))

/-- The entire original tensor/cotensor parametrized adjunction is transported. -/
def tensorCotensor : (tensor d a S κLP).flip ⊣₂ cotensor d a S κLP := by
  letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  exact {
    adj A := SelectedEnrichmentTransport.adjunction (localizationData d a S κLP)
      (a.tensorCotensor.adj A)
    unit_whiskerRight_map i := by
      apply NatTrans.ext
      funext X
      apply InducedCategory.hom_ext
      exact congrArg (fun t => t.app X.1) (a.tensorCotensor.unit_whiskerRight_map i) }

/-- The whole selected tensor/Hom adjunction uses the original Hom transpose in every degree. -/
def tensorHom : tensor d a S κLP ⊣₂ SimplicialCategory.sHomFunctor (Localized d a S κLP) := by
  letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  exact {
    adj X :=
      { unit :=
          { app A := (a.tensorHom.adj X.1).unit.app A
            naturality _ _ f := (a.tensorHom.adj X.1).unit.naturality f }
        counit :=
          { app Y := InducedCategory.homMk ((a.tensorHom.adj X.1).counit.app Y.1)
            naturality _ _ f := by
              apply InducedCategory.hom_ext
              exact (a.tensorHom.adj X.1).counit.naturality f.hom }
        left_triangle_components A := by
          apply InducedCategory.hom_ext
          exact (a.tensorHom.adj X.1).left_triangle_components A
        right_triangle_components Y := (a.tensorHom.adj X.1).right_triangle_components Y.1 }
    unit_whiskerRight_map i := by
      apply NatTrans.ext
      funext A
      exact congrArg (fun t => t.app A) (a.tensorHom.unit_whiskerRight_map i.hom) }

/-- A parameter cotensor preserves every local fibrant object in its original model dictionary. -/
theorem parameterAdjunction_isQuillen (A : SSet.{v}) :
    ((tensorCotensor d a S κLP).adj A).IsQuillenAdjunction := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let LC := localizationData d a S κLP
  let _ : (a.tensorCotensor.adj A).IsQuillenAdjunction :=
    CompatibleSimplicialMapping.parameterAdjunction_isQuillen a A
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesCofibrationsAndFibrationsBetweenFibrantObjects
  · intro X Y i hi
    change cofibrations C (((a.tensor.flip.obj A).map i.hom))
    change cofibrations C i.hom at hi
    exact Adjunction.IsQuillenAdjunction.preservesCofibrations (adj := a.tensorCotensor.adj A) i.hom hi
  · intro X Y p hp
    have hX : isLocalFibrant S X.1 := (LeftLocalized.fibrant_iff LC X).mp hp.2.1
    have hY : isLocalFibrant S Y.1 := (LeftLocalized.fibrant_iff LC Y).mp hp.2.2
    have hpBase : fibrations C p.hom := (LeftLocalized.fibration_iff_of_local LC p hX hY).mp hp.1
    have hpImage : fibrations C ((a.cotensor.obj (op A)).map p.hom) :=
      Adjunction.IsQuillenAdjunction.preservesFibrations (adj := a.tensorCotensor.adj A) p.hom hpBase
    exact (LeftLocalized.fibration_iff_of_local LC
      ((cotensor d a S κLP).obj (op A) |>.map p)
      (cotensor_isLocalFibrant d a S κLP X.1 hX A)
      (cotensor_isLocalFibrant d a S κLP Y.1 hY A)).mpr hpImage

include a κLP in
/-- Every original parameter tensor preserves all local trivial cofibrations at arbitrary endpoints. -/
theorem originalParameterTensor_localTrivial :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    ∀ {X Y : C} (i : X ⟶ Y), (cofibrations C ⊓ localEquivalences S) i →
      ∀ A : SSet.{v}, (cofibrations C ⊓ localEquivalences S) ((a.tensor.map i).app A) := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  intro X Y i hi A
  let LC := localizationData d a S κLP
  let _ : ((tensorCotensor d a S κLP).adj A).IsQuillenAdjunction :=
    parameterAdjunction_isQuillen d a S κLP A
  exact Adjunction.IsQuillenAdjunction.preservesTrivialCofibrations
    (adj := (tensorCotensor d a S κLP).adj A) ((LeftLocalized.ofBase LC).map i) hi

include a κLP in
/-- The actual full original pushout product is locally trivial without endpoint cofibrancy. -/
theorem originalPushoutProduct_localTrivial :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    ∀ {X Y : C} (i : X ⟶ Y), (cofibrations C ⊓ localEquivalences S) i →
      ∀ {A B : SSet.{v}} (j : A ⟶ B), cofibrations SSet.{v} j →
        ∀ sq : a.tensor.PushoutObjObj i j, (cofibrations C ⊓ localEquivalences S) sq.ι := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  intro X Y i hi A B j hj sq
  have hA := originalParameterTensor_localTrivial d a S κLP i hi A
  have hB := originalParameterTensor_localTrivial d a S κLP i hi B
  have hInr := LocalTrivialCofibrationClosure.original_of_isPushout d a S sq.isPushout hA
  let _ : (localEquivalences S).HasTwoOutOfThreeProperty := localEquivalences_hasTwoOutOfThreeProperty S
  refine ⟨a.cof_cof i j sq hi.1 hj, ?_⟩
  apply (localEquivalences S).of_precomp sq.inr sq.ι hInr.2
  rw [sq.inr_ι]
  exact hB.2

/-- Every supplied selected pushout retains its whole original tensor pushout square. -/
def originalPushout {X Y : Localized d a S κLP} (i : X ⟶ Y)
    {A B : SSet.{v}} (j : A ⟶ B) (sq : (tensor d a S κLP).PushoutObjObj i j) :
    a.tensor.PushoutObjObj i.hom j := by
  letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let LC := localizationData d a S κLP
  letI : (LeftLocalized.toBase LC).IsEquivalence := by
    change (LeftLocalized.equivalence LC).inverse.IsEquivalence
    infer_instance
  exact
    { pt := sq.pt.1
      inl := sq.inl.hom
      inr := sq.inr.hom
      isPushout := sq.isPushout.map (LeftLocalized.toBase LC)
      ι := sq.ι.hom
      inl_ι := congrArg (fun f => f.hom) sq.inl_ι
      inr_ι := congrArg (fun f => f.hom) sq.inr_ι }

/-- The actual produced localization has the complete original compatible simplicial action. -/
def action : CompatibleSimplicialMapping.Action (Localized d a S κLP) := by
  letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let LC := localizationData d a S κLP
  refine
    { tensor := tensor d a S κLP
      cotensor := cotensor d a S κLP
      tensorHom := tensorHom d a S κLP
      tensorCotensor := tensorCotensor d a S κLP
      cof_cof := ?_
      trivial_cof := ?_
      cof_trivial := ?_ }
  · intro X Y i A B j sq hi hj
    exact a.cof_cof i.hom j (originalPushout d a S κLP i j sq) hi hj
  · intro X Y i A B j sq hi hj
    exact originalPushoutProduct_localTrivial d a S κLP i.hom hi j hj
      (originalPushout d a S κLP i j sq)
  · intro X Y i A B j sq hi hj
    obtain ⟨hc, hw⟩ := a.cof_trivial i.hom j (originalPushout d a S κLP i j sq) hi hj
    exact ⟨hc, LC.baseWeak_le sq.ι.hom hw⟩

/-- Every original tensor object survives literally in the full produced action. -/
theorem action_tensor_obj (X : Localized d a S κLP) (A : SSet.{v}) :
    (((action d a S κLP).tensor.obj X).obj A).1 = (a.tensor.obj X.1).obj A := rfl

/-- Every original tensor coefficient map survives in the full produced action. -/
theorem action_tensor_map {X Y : Localized d a S κLP} (i : X ⟶ Y) (A : SSet.{v}) :
    (((action d a S κLP).tensor.map i).app A).hom = (a.tensor.map i.hom).app A := rfl

/-- Every original cotensor object survives literally in the full produced action. -/
theorem action_cotensor_obj (A : SSet.{v}) (X : Localized d a S κLP) :
    (((action d a S κLP).cotensor.obj (op A)).obj X).1 = (a.cotensor.obj (op A)).obj X.1 := rfl

/-- Every original cotensor coefficient map survives in the full produced action. -/
theorem action_cotensor_map (A : SSet.{v}) {X Y : Localized d a S κLP} (i : X ⟶ Y) :
    (((action d a S κLP).cotensor.obj (op A)).map i).hom =
      (a.cotensor.obj (op A)).map i.hom := rfl

/-- The original I factory supplies the entire cofibrant factor record on the actual selected carrier. -/
def cofibrantFactors :
    FunctorialFactorizationData (cofibrations (Localized d a S κLP))
      (trivialFibrations (Localized d a S κLP)) := by
  letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let LC := localizationData d a S κLP
  exact (SelectedEnrichmentTransport.factors LC d.cofibrantFactorizationData).ofLE le_rfl
    (by rw [LeftLocalized.trivialFibrations_eq LC])

/-- The source-produced actual Smith J factory supplies the complete selected fibrant factor record. -/
def fibrantFactors :
    FunctorialFactorizationData (trivialCofibrations (Localized d a S κLP))
      (fibrations (Localized d a S κLP)) := by
  letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let LC := localizationData d a S κLP
  let M := CombinatorialSourceRecognition.smithData d a S κLP
  have hI : d.I.rlp.llp = cofibrations C := by rw [d.I_rlp, trivialFibrations_llp]
  have hJ : M.J.rlp.llp = cofibrations C ⊓ localEquivalences S := by
    rw [M.trivialCofibrations_eq, hI]
  have hF : M.J.rlp = localizedFibrations S := by
    rw [M.fibrations_eq, hI]
    rfl
  let data : FunctorialFactorizationData (cofibrations C ⊓ localEquivalences S)
      (localizedFibrations S) :=
    (CombinatorialSourceRecognition.fibrantFactors d a S κLP).ofLE (by rw [hJ]) (by rw [hF])
  exact SelectedEnrichmentTransport.factors LC data

/-- The entire original I middle functor, with both unchanged endpoint identities, is retained. -/
theorem cofibrantFactors_middle :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    (cofibrantFactors d a S κLP).Z =
      (LeftLocalized.toBase (localizationData d a S κLP)).mapArrow ⋙
        d.cofibrantFactorizationData.Z ⋙ LeftLocalized.ofBase (localizationData d a S κLP) := rfl

/-- Every actual Smith J square map remains the original complete generated middle map. -/
theorem fibrantFactors_map {F G : Arrow (Localized d a S κLP)} (t : F ⟶ G) :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    ((fibrantFactors d a S κLP).Z.map t).hom =
      (CombinatorialSourceRecognition.fibrantFactors d a S κLP).Z.map
        ((LeftLocalized.toBase (localizationData d a S κLP)).mapArrow.map t) := rfl

/-- Both selected factories retain their complete factorization equations on every Arrow. -/
theorem factors_fac (F : Arrow (Localized d a S κLP)) :
    (cofibrantFactors d a S κLP).i.app F ≫ (cofibrantFactors d a S κLP).p.app F = F.hom ∧
      (fibrantFactors d a S κLP).i.app F ≫ (fibrantFactors d a S κLP).p.app F = F.hom :=
  ⟨(cofibrantFactors d a S κLP).fac_app, (fibrantFactors d a S κLP).fac_app⟩

/-- Both selected factories retain both natural factor squares at every original Arrow morphism. -/
theorem factors_naturality {F G : Arrow (Localized d a S κLP)} (t : F ⟶ G) :
    t.left ≫ (cofibrantFactors d a S κLP).i.app G =
        (cofibrantFactors d a S κLP).i.app F ≫ (cofibrantFactors d a S κLP).Z.map t ∧
      (cofibrantFactors d a S κLP).Z.map t ≫ (cofibrantFactors d a S κLP).p.app G =
        (cofibrantFactors d a S κLP).p.app F ≫ t.right ∧
      t.left ≫ (fibrantFactors d a S κLP).i.app G =
        (fibrantFactors d a S κLP).i.app F ≫ (fibrantFactors d a S κLP).Z.map t ∧
      (fibrantFactors d a S κLP).Z.map t ≫ (fibrantFactors d a S κLP).p.app G =
        (fibrantFactors d a S κLP).p.app F ≫ t.right :=
  ⟨(cofibrantFactors d a S κLP).i.naturality t, (cofibrantFactors d a S κLP).p.naturality t,
    (fibrantFactors d a S κLP).i.naturality t, (fibrantFactors d a S κLP).p.naturality t⟩

/-- The actual original I replacement functor at the caller's complete initial object. -/
def cofibrantReplacement (Z₀ : Localized d a S κLP) (h₀ : IsInitial Z₀) :
    Localized d a S κLP ⥤ Localized d a S κLP :=
  GivenFactorizationReplacements.initialReplacement (cofibrantFactors d a S κLP) Z₀ h₀

/-- The original actual I projection is the entire local replacement counit. -/
def cofibrantProjection (Z₀ : Localized d a S κLP) (h₀ : IsInitial Z₀) :
    cofibrantReplacement d a S κLP Z₀ h₀ ⟶ 𝟭 (Localized d a S κLP) :=
  GivenFactorizationReplacements.initialProjection (cofibrantFactors d a S κLP) Z₀ h₀

/-- The other complete original I factor retains the entire chosen initial-arrow family. -/
def initialLeg (Z₀ : Localized d a S κLP) (h₀ : IsInitial Z₀) :
    (Functor.const (Localized d a S κLP)).obj Z₀ ⟶ cofibrantReplacement d a S κLP Z₀ h₀ :=
  GivenFactorizationReplacements.initialLeg (cofibrantFactors d a S κLP) Z₀ h₀

/-- The actual source-produced Smith J replacement at the caller's complete terminal object. -/
def fibrantReplacement (Z₁ : Localized d a S κLP) (h₁ : IsTerminal Z₁) :
    Localized d a S κLP ⥤ Localized d a S κLP :=
  GivenFactorizationReplacements.terminalReplacement (fibrantFactors d a S κLP) Z₁ h₁

/-- The original actual Smith J inclusion is the complete local replacement unit. -/
def fibrantUnit (Z₁ : Localized d a S κLP) (h₁ : IsTerminal Z₁) :
    𝟭 (Localized d a S κLP) ⟶ fibrantReplacement d a S κLP Z₁ h₁ :=
  GivenFactorizationReplacements.terminalUnit (fibrantFactors d a S κLP) Z₁ h₁

/-- The other complete actual Smith J factor retains every chosen original terminal arrow. -/
def terminalLeg (Z₁ : Localized d a S κLP) (h₁ : IsTerminal Z₁) :
    fibrantReplacement d a S κLP Z₁ h₁ ⟶ (Functor.const (Localized d a S κLP)).obj Z₁ :=
  GivenFactorizationReplacements.terminalLeg (fibrantFactors d a S κLP) Z₁ h₁

/-- Both replacements retain the actual whole selected middle-map functions on every source arrow. -/
theorem replacements_map
    (Z₀ : Localized d a S κLP) (h₀ : IsInitial Z₀)
    (Z₁ : Localized d a S κLP) (h₁ : IsTerminal Z₁)
    {X Y : Localized d a S κLP} (f : X ⟶ Y) :
    (cofibrantReplacement d a S κLP Z₀ h₀).map f =
      (cofibrantFactors d a S κLP).Z.map (Arrow.homMk (𝟙 Z₀) f (h₀.hom_ext _ _)) ∧
      (fibrantReplacement d a S κLP Z₁ h₁).map f =
        (fibrantFactors d a S κLP).Z.map (Arrow.homMk f (𝟙 Z₁) (h₁.hom_ext _ _)) := ⟨rfl, rfl⟩

/-- Both complete original factor equations retain the entire caller endpoint families. -/
theorem replacements_fac
    (Z₀ : Localized d a S κLP) (h₀ : IsInitial Z₀)
    (Z₁ : Localized d a S κLP) (h₁ : IsTerminal Z₁) :
    initialLeg d a S κLP Z₀ h₀ ≫ cofibrantProjection d a S κLP Z₀ h₀ =
        GivenFactorizationReplacements.initialMapNatTrans Z₀ h₀ ∧
      fibrantUnit d a S κLP Z₁ h₁ ≫ terminalLeg d a S κLP Z₁ h₁ =
        GivenFactorizationReplacements.terminalMapNatTrans Z₁ h₁ :=
  ⟨GivenFactorizationReplacements.initial_fac _ Z₀ h₀,
    GivenFactorizationReplacements.terminal_fac _ Z₁ h₁⟩

/-- Both entire replacement naturality squares use the same original selected middle maps. -/
theorem replacements_naturality
    (Z₀ : Localized d a S κLP) (h₀ : IsInitial Z₀)
    (Z₁ : Localized d a S κLP) (h₁ : IsTerminal Z₁)
    {X Y : Localized d a S κLP} (f : X ⟶ Y) :
    (cofibrantReplacement d a S κLP Z₀ h₀).map f ≫ (cofibrantProjection d a S κLP Z₀ h₀).app Y =
        (cofibrantProjection d a S κLP Z₀ h₀).app X ≫ f ∧
      f ≫ (fibrantUnit d a S κLP Z₁ h₁).app Y =
        (fibrantUnit d a S κLP Z₁ h₁).app X ≫ (fibrantReplacement d a S κLP Z₁ h₁).map f :=
  ⟨(cofibrantProjection d a S κLP Z₀ h₀).naturality f, (fibrantUnit d a S κLP Z₁ h₁).naturality f⟩

/-- The actual full generated local replacement objects and maps have their exact local classes. -/
theorem replacements_membership
    (Z₀ : Localized d a S κLP) (h₀ : IsInitial Z₀)
    (Z₁ : Localized d a S κLP) (h₁ : IsTerminal Z₁) (X : Localized d a S κLP) :
    IsCofibrant ((cofibrantReplacement d a S κLP Z₀ h₀).obj X) ∧
      trivialFibrations (Localized d a S κLP) ((cofibrantProjection d a S κLP Z₀ h₀).app X) ∧
      IsFibrant ((fibrantReplacement d a S κLP Z₁ h₁).obj X) ∧
      trivialCofibrations (Localized d a S κLP) ((fibrantUnit d a S κLP Z₁ h₁).app X) := by
  refine ⟨?_, (cofibrantFactors d a S κLP).hp (Arrow.mk (h₀.to X)), ?_,
    (fibrantFactors d a S κLP).hi (Arrow.mk (h₁.from X))⟩
  · exact GivenFactorizationReplacements.initialReplacement_isCofibrant
      (inferInstance : ModelCategory (Localized d a S κLP)) (cofibrantFactors d a S κLP) Z₀ h₀ X
  · exact GivenFactorizationReplacements.terminalReplacement_isFibrant
      (inferInstance : ModelCategory (Localized d a S κLP)) (fibrantFactors d a S κLP) Z₁ h₁ X

include a κLP in
/-- One common source rank retains local presentability and both literal original I and Smith J families. -/
theorem generationAtCommonRank :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    let LC := localizationData d a S κLP
    let I := d.I
    let J := (CombinatorialSourceRecognition.smithData d a S κLP).J
    ∃ (χ : Cardinal.{w}) (hχ : Fact χ.IsRegular) (hbot : OrderBot χ.ord.ToType),
      letI : Fact χ.IsRegular := hχ
      letI : OrderBot χ.ord.ToType := hbot
      κLP ≤ χ ∧ κ ≤ χ ∧ IsCardinalLocallyPresentable C χ ∧
        IsCardinalLocallyPresentable (Localized d a S κLP) χ ∧
        (localEquivalences S).IsCardinalAccessible χ ∧
        ∃ g : CofibrantGenerationData (Localized d a S κLP) χ,
          g.I = I.strictMap (LeftLocalized.ofBase LC) ∧ g.J = J.strictMap (LeftLocalized.ofBase LC) := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let LC := localizationData d a S κLP
  let M := CombinatorialSourceRecognition.smithData d a S κLP
  obtain ⟨χ, hχ, hbot, hLP, hκ, hW, g, hgI, hgJ⟩ :=
    CombinatorialSourceRecognition.generationAtCommonRank d a S κLP
  let _ : Fact χ.IsRegular := hχ
  let _ : OrderBot χ.ord.ToType := hbot
  have hI : d.I.IsCardinalForSmallObjectArgument χ := by
    let _ : ModelCategory C := CombinatorialSourceRecognition.modelCategory d a S κLP
    exact hgI ▸ g.I_smallObject
  have hJ : M.J.IsCardinalForSmallObjectArgument χ := by
    let _ : ModelCategory C := CombinatorialSourceRecognition.modelCategory d a S κLP
    exact hgJ ▸ g.J_smallObject
  let e : Localized d a S κLP ≌ C := (LeftLocalized.equivalence LC).symm
  have hC : IsCardinalLocallyPresentable C χ := IsCardinalLocallyPresentable.of_le C hLP
  let _ : IsCardinalLocallyPresentable C χ := hC
  have hLC : IsCardinalLocallyPresentable (Localized d a S κLP) χ :=
    (LeftLocalized.equivalence LC).isCardinalLocallyPresentable χ
  have hJrlp : M.J.rlp = localizedFibrations S := by
    rw [M.fibrations_eq, d.I_rlp, trivialFibrations_llp]
    rfl
  refine ⟨χ, hχ, hbot, hLP, hκ, hC, hLC, hW, ?_⟩
  refine ⟨
    { I := d.I.strictMap e.inverse
      J := M.J.strictMap e.inverse
      I_smallObject := CofibrantGenerationData.Equivalence.family_eligible e d.I χ hI
      J_smallObject := CofibrantGenerationData.Equivalence.family_eligible e M.J χ hJ
      I_rlp := ?_
      J_rlp := ?_ }, rfl, rfl⟩
  · change (CofibrantGenerationData.Equivalence.family e d.I).rlp = _
    rw [CofibrantGenerationData.Equivalence.family_rlp, d.I_rlp, LeftLocalized.trivialFibrations_eq LC]
    rfl
  · change (CofibrantGenerationData.Equivalence.family e M.J).rlp = _
    rw [CofibrantGenerationData.Equivalence.family_rlp, hJrlp]
    rfl

/-- The source witness supplies presentability and both actual generating families at the same rank. -/
instance combinatorialModelCategory : IsCombinatorialModelCategory.{w} (Localized d a S κLP) := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  obtain ⟨χ, hχ, hbot, _hLP, _hκ, _hC, hLC, _hW, g, _hgI, _hgJ⟩ :=
    generationAtCommonRank d a S κLP
  exact { exists_cardinal := ⟨χ, hχ, hbot, hLC, ⟨g⟩⟩ }

/-- All five produced model classes are exactly the complete original inverse-image classes. -/
theorem fiveClasses :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    let L := localizationData d a S κLP
    weakEquivalences (Localized d a S κLP) = (localEquivalences S).inverseImage (LeftLocalized.toBase L) ∧
      cofibrations (Localized d a S κLP) = (cofibrations C).inverseImage (LeftLocalized.toBase L) ∧
      fibrations (Localized d a S κLP) = (localizedFibrations S).inverseImage (LeftLocalized.toBase L) ∧
      trivialCofibrations (Localized d a S κLP) =
        (cofibrations C ⊓ localEquivalences S).inverseImage (LeftLocalized.toBase L) ∧
      trivialFibrations (Localized d a S κLP) =
        (trivialFibrations C).inverseImage (LeftLocalized.toBase L) := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  exact ⟨rfl, rfl, rfl, rfl, LeftLocalized.trivialFibrations_eq (localizationData d a S κLP)⟩

/-- Every produced fibrant object is exactly an original base-fibrant S-local object. -/
theorem fibrant_iff (X : Localized d a S κLP) :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    IsFibrant X ↔ isLocalFibrant S X.1 := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  exact LeftLocalized.fibrant_iff (localizationData d a S κLP) X

/-- At both original local-fibrant endpoints the complete local weak class is exactly base weakness. -/
theorem weakEquivalence_iff_of_local :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    ∀ {X Y : Localized d a S κLP} (f : X ⟶ Y), isLocalFibrant S X.1 → isLocalFibrant S Y.1 →
      (weakEquivalences (Localized d a S κLP) f ↔ weakEquivalences C f.hom) := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  intro X Y f hX hY
  exact LeftLocalized.weakEquivalence_iff_of_local (localizationData d a S κLP) f hX hY

/-- Every original parameter map survives in the tensor of the full produced action. -/
theorem action_tensor_parameter (X : Localized d a S κLP) {A B : SSet.{v}} (j : A ⟶ B) :
    (((action d a S κLP).tensor.obj X).map j).hom = (a.tensor.obj X.1).map j := rfl

/-- Every original parameter map survives in the cotensor of the full produced action. -/
theorem action_cotensor_parameter {A B : SSet.{v}} (j : A ⟶ B) (X : Localized d a S κLP) :
    (((action d a S κLP).cotensor.map j.op).app X).hom = (a.cotensor.map j.op).app X.1 := rfl

/-- The entire original tensor/Hom transpose is retained by the produced action. -/
theorem action_tensorHom_homEquiv (X Y : Localized d a S κLP) (A : SSet.{v})
    (f : ((action d a S κLP).tensor.obj X).obj A ⟶ Y) :
    ((action d a S κLP).tensorHom.adj X).homEquiv A Y f =
      (a.tensorHom.adj X.1).homEquiv A Y.1 f.hom := rfl

/-- The inverse original tensor/Hom transpose is retained without replacing its function. -/
theorem action_tensorHom_homEquiv_symm (X Y : Localized d a S κLP) (A : SSet.{v})
    (f : A ⟶ SimplicialCategory.sHom X Y) :
    ((((action d a S κLP).tensorHom.adj X).homEquiv A Y).symm f).hom =
      ((a.tensorHom.adj X.1).homEquiv A Y.1).symm f := rfl

/-- The complete original tensor/cotensor transpose is retained by the produced action. -/
theorem action_tensorCotensor_homEquiv (A : SSet.{v}) (X Y : Localized d a S κLP)
    (f : ((action d a S κLP).tensor.flip.obj A).obj X ⟶ Y) :
    (((action d a S κLP).tensorCotensor.adj A).homEquiv X Y f).hom =
      (a.tensorCotensor.adj A).homEquiv X.1 Y.1 f.hom := rfl

/-- The inverse original tensor/cotensor transpose is retained with its actual full function. -/
theorem action_tensorCotensor_homEquiv_symm (A : SSet.{v}) (X Y : Localized d a S κLP)
    (f : X ⟶ ((action d a S κLP).cotensor.obj (op A)).obj Y) :
    ((((action d a S κLP).tensorCotensor.adj A).homEquiv X Y).symm f).hom =
      ((a.tensorCotensor.adj A).homEquiv X.1 Y.1).symm f.hom := rfl

/-- The complete canonical local Q/R data use exactly the two source-produced factor records. -/
def replacementData : GeneratedFunctorialReplacements.Data (C := Localized d a S κLP) where
  cofibrantFactor := cofibrantFactors d a S κLP
  fibrantFactor := fibrantFactors d a S κLP
  Q := cofibrantReplacement d a S κLP (⊥_ _) initialIsInitial
  R := fibrantReplacement d a S κLP (⊤_ _) terminalIsTerminal
  qInitial := initialLeg d a S κLP (⊥_ _) initialIsInitial
  q := cofibrantProjection d a S κLP (⊥_ _) initialIsInitial
  r := fibrantUnit d a S κLP (⊤_ _) terminalIsTerminal
  rTerminal := terminalLeg d a S κLP (⊤_ _) terminalIsTerminal
  q_fac := by
    apply NatTrans.ext
    funext X
    exact (cofibrantFactors d a S κLP).fac_app
  r_fac := by
    apply NatTrans.ext
    funext X
    exact (fibrantFactors d a S κLP).fac_app
  q_cofibrant X := (replacements_membership d a S κLP (⊥_ _) initialIsInitial (⊤_ _) terminalIsTerminal X).1
  r_fibrant X := (replacements_membership d a S κLP (⊥_ _) initialIsInitial (⊤_ _) terminalIsTerminal X).2.2.1
  q_trivialFibration X := (cofibrantFactors d a S κLP).hp (Arrow.mk (initial.to X))
  r_trivialCofibration X := (fibrantFactors d a S κLP).hi (Arrow.mk (terminal.from X))
  q_map_weak f hf := by
    apply (weakEquivalences (Localized d a S κLP)).of_postcomp
      ((cofibrantReplacement d a S κLP (⊥_ _) initialIsInitial).map f)
      ((cofibrantProjection d a S κLP (⊥_ _) initialIsInitial).app _)
      ((cofibrantFactors d a S κLP).hp (Arrow.mk (initial.to _))).2
    rw [(cofibrantProjection d a S κLP (⊥_ _) initialIsInitial).naturality]
    exact (weakEquivalences (Localized d a S κLP)).comp_mem _ _
      ((cofibrantFactors d a S κLP).hp (Arrow.mk (initial.to _))).2 hf
  r_map_weak f hf := by
    apply (weakEquivalences (Localized d a S κLP)).of_precomp
      ((fibrantUnit d a S κLP (⊤_ _) terminalIsTerminal).app _)
      ((fibrantReplacement d a S κLP (⊤_ _) terminalIsTerminal).map f)
      ((fibrantFactors d a S κLP).hi (Arrow.mk (terminal.from _))).2
    rw [← (fibrantUnit d a S κLP (⊤_ _) terminalIsTerminal).naturality]
    exact (weakEquivalences (Localized d a S κLP)).comp_mem _ _ hf
      ((fibrantFactors d a S κLP).hi (Arrow.mk (terminal.from _))).2

/-- The entire canonical replacement package retains both complete actual source factories. -/
theorem replacementData_factors :
    (replacementData d a S κLP).cofibrantFactor = cofibrantFactors d a S κLP ∧
      (replacementData d a S κLP).fibrantFactor = fibrantFactors d a S κLP := ⟨rfl, rfl⟩

/-- The canonical Q middle map uses the same actual original I factor function. -/
theorem replacementData_Q_map {X Y : Localized d a S κLP} (f : X ⟶ Y) :
    (replacementData d a S κLP).Q.map f = (cofibrantFactors d a S κLP).Z.map
      (Arrow.homMk (𝟙 (⊥_ _)) f (initialIsInitial.hom_ext _ _)) := rfl

/-- The canonical R middle map uses the same actual generated Smith J factor function. -/
theorem replacementData_R_map {X Y : Localized d a S κLP} (f : X ⟶ Y) :
    (replacementData d a S κLP).R.map f = (fibrantFactors d a S κLP).Z.map
      (Arrow.homMk f (𝟙 (⊤_ _)) (terminalIsTerminal.hom_ext _ _)) := rfl

end SourceChoices

end HomotopicalAlgebra.CombinatorialEnrichment
