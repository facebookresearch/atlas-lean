/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveGeneratorCells.Data

/-!# Entire original enriched-generation and generic fixed-factor contracts -/
set_option autoImplicit false
noncomputable section
universe w uA uV vV
open CategoryTheory Limits MorphismProperty Opposite MonoidalCategory HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective

namespace MathlibExtTest.EnrichedGeneratorCellsData

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} A] [LocallySmall.{w} V] [HasColimitsOfSize.{w, w} V]
  (d : CofibrantGenerationData V κ) (QI QJ : MorphismProperty V)
  [QI.RespectsIso] [QJ.RespectsIso]
  [QI.IsStableUnderCoproducts.{w}] [QJ.IsStableUnderCoproducts.{w}]
  [QI.IsStableUnderCobaseChange] [QJ.IsStableUnderCobaseChange]
  [QI.IsStableUnderTransfiniteComposition.{w}]
  [QJ.IsStableUnderTransfiniteComposition.{w}]
  (hI : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y), d.I f → QI (f ▷ (a ⟶[V] b)))
  (hJ : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y), d.J f → QJ (f ▷ (a ⟶[V] b)))
  (hSourceI : ∀ {X Y : V} (f : X ⟶ Y), d.I f →
    ∀ (F : κ.ord.ToType ⥤ V) [F.IsWellOrderContinuous],
      (∀ ⦃a b⦄ (φ : a ⟶ b), QI (F.map φ)) →
      PreservesColimit F (coyoneda.obj (op X)))
  (hSourceJ : ∀ {X Y : V} (f : X ⟶ Y), d.J f →
    ∀ (F : κ.ord.ToType ⥤ V) [F.IsWellOrderContinuous],
      (∀ ⦃a b⦄ (φ : a ⟶ b), QJ (F.map φ)) →
      PreservesColimit F (coyoneda.obj (op X)))
  (hCells : ∀ (b : A) {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y),
    RelativeCellComplex.{w}
      (fun _ : κ.ord.ToType => (generators (A := A) d.J).homFamily) f →
      weakEquivalences V ((EnrichedFunctorCat.evaluation b).map f))

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    CofibrantGenerationData (EnrichedFunctorCat V A) κ :=
  GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells).I =
      generators (A := A) d.I :=
  GeneratorCells.generationData_I d QI QJ hI hJ hSourceI hSourceJ hCells

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells).J =
      generators (A := A) d.J :=
  GeneratorCells.generationData_J d QI QJ hI hJ hSourceI hSourceJ hCells

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    (generators (A := A) d.I).rlp = trivialFibrations (EnrichedFunctorCat V A) :=
  GeneratorCells.generatorsI_rlp_eq d QI QJ hI hJ hSourceI hSourceJ hCells

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    (generators (A := A) d.J).rlp = fibrations (EnrichedFunctorCat V A) :=
  GeneratorCells.generatorsJ_rlp_eq d QI QJ hI hJ hSourceI hSourceJ hCells

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    (CofibrantGenerationData.cofibrantFactorizationData
      (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)) =
      GeneratorCells.cofibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells :=
  GeneratorCells.generationData_cofibrantFactorizationData
    d QI QJ hI hJ hSourceI hSourceJ hCells

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    (CofibrantGenerationData.fibrantFactorizationData
      (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)) =
      GeneratorCells.fibrantFactorizationData d QI QJ hI hJ hSourceI hSourceJ hCells :=
  GeneratorCells.generationData_fibrantFactorizationData
    d QI QJ hI hJ hSourceI hSourceJ hCells

example (f : Arrow (EnrichedFunctorCat V A)) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    let data := (CofibrantGenerationData.cofibrantFactorizationData
      (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells))
    data.i.app f ≫ data.p.app f = f.hom :=
  by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  exact (CofibrantGenerationData.cofibrantFactorizationData
    (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)).fac_app

example (f : Arrow (EnrichedFunctorCat V A)) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    let data := (CofibrantGenerationData.fibrantFactorizationData
      (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells))
    data.i.app f ≫ data.p.app f = f.hom :=
  by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  exact (CofibrantGenerationData.fibrantFactorizationData
    (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)).fac_app


example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    letI : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells).I_smallObject =
      generators_isCardinalForSmallObjectArgument d.I QI hI hSourceI :=
  GeneratorCells.generationData_I_smallObject d QI QJ hI hJ hSourceI hSourceJ hCells

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells).I.rlp.llp =
      cofibrations (EnrichedFunctorCat V A) :=
  GeneratorCells.generationData_I_left d QI QJ hI hJ hSourceI hSourceJ hCells

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    letI : d.J.IsSmall.{w} := d.J_smallObject.isSmall
    (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells).J_smallObject =
      generators_isCardinalForSmallObjectArgument d.J QJ hJ hSourceJ :=
  GeneratorCells.generationData_J_smallObject d QI QJ hI hJ hSourceI hSourceJ hCells

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells).J.rlp.llp =
      trivialCofibrations (EnrichedFunctorCat V A) :=
  GeneratorCells.generationData_J_left d QI QJ hI hJ hSourceI hSourceJ hCells

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    weakEquivalences (EnrichedFunctorCat V A) =
        EvaluationTransfer.evaluationProperty
          (fun a : A => EnrichedFunctorCat.evaluation a) (weakEquivalences V) ∧
      fibrations (EnrichedFunctorCat V A) =
        EvaluationTransfer.evaluationProperty
          (fun a : A => EnrichedFunctorCat.evaluation a) (fibrations V) ∧
      trivialFibrations (EnrichedFunctorCat V A) =
        EvaluationTransfer.evaluationProperty
          (fun a : A => EnrichedFunctorCat.evaluation a) (trivialFibrations V) ∧
      cofibrations (EnrichedFunctorCat V A) = (generators (A := A) d.I).rlp.llp ∧
      trivialCofibrations (EnrichedFunctorCat V A) = (generators (A := A) d.J).rlp.llp :=
  GeneratorCells.generationData_five_classes d QI QJ hI hJ hSourceI hSourceJ hCells

example (f : Arrow (EnrichedFunctorCat V A)) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    let data := CofibrantGenerationData.cofibrantFactorizationData
      (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)
    data.Z.map (𝟙 f) = 𝟙 (data.Z.obj f) :=
  by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  exact (CofibrantGenerationData.cofibrantFactorizationData
    (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)).Z.map_id f

example {f g h : Arrow (EnrichedFunctorCat V A)} (a : f ⟶ g) (b : g ⟶ h) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    let data := CofibrantGenerationData.cofibrantFactorizationData
      (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)
    data.Z.map (a ≫ b) = data.Z.map a ≫ data.Z.map b :=
  by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  exact (CofibrantGenerationData.cofibrantFactorizationData
    (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)).Z.map_comp a b

example {f g : Arrow (EnrichedFunctorCat V A)} (a : f ⟶ g) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    let data := CofibrantGenerationData.cofibrantFactorizationData
      (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)
    a.left ≫ data.i.app g = data.i.app f ≫ data.Z.map a :=
  by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  exact (CofibrantGenerationData.cofibrantFactorizationData
    (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)).i.naturality a

example {f g : Arrow (EnrichedFunctorCat V A)} (a : f ⟶ g) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    let data := CofibrantGenerationData.cofibrantFactorizationData
      (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)
    data.Z.map a ≫ data.p.app g = data.p.app f ≫ a.right :=
  by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  exact (CofibrantGenerationData.cofibrantFactorizationData
    (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)).p.naturality a

example (f : Arrow (EnrichedFunctorCat V A)) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    let data := CofibrantGenerationData.fibrantFactorizationData
      (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)
    data.Z.map (𝟙 f) = 𝟙 (data.Z.obj f) :=
  by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  exact (CofibrantGenerationData.fibrantFactorizationData
    (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)).Z.map_id f

example {f g h : Arrow (EnrichedFunctorCat V A)} (a : f ⟶ g) (b : g ⟶ h) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    let data := CofibrantGenerationData.fibrantFactorizationData
      (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)
    data.Z.map (a ≫ b) = data.Z.map a ≫ data.Z.map b :=
  by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  exact (CofibrantGenerationData.fibrantFactorizationData
    (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)).Z.map_comp a b

example {f g : Arrow (EnrichedFunctorCat V A)} (a : f ⟶ g) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    let data := CofibrantGenerationData.fibrantFactorizationData
      (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)
    a.left ≫ data.i.app g = data.i.app f ≫ data.Z.map a :=
  by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  exact (CofibrantGenerationData.fibrantFactorizationData
    (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)).i.naturality a

example {f g : Arrow (EnrichedFunctorCat V A)} (a : f ⟶ g) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
    let data := CofibrantGenerationData.fibrantFactorizationData
      (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)
    data.Z.map a ≫ data.p.app g = data.p.app f ≫ a.right :=
  by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    modelCategoryOfGeneratorCells d QI QJ hI hJ hSourceI hSourceJ hCells
  exact (CofibrantGenerationData.fibrantFactorizationData
    (GeneratorCells.generationData d QI QJ hI hJ hSourceI hSourceJ hCells)).p.naturality a

section CoefficientContracts

example (a b : A) {X Y : V} (f : X ⟶ Y) :
    EnrichedFunctorCat.component ((EnrichedFunctorCat.Free.functor (V := V) a).map f) b =
      f ▷ (a ⟶[V] b) :=
  EnrichedFunctorCat.Free.coefficientMap_component a f b

example (P : MorphismProperty V) {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y) :
    generators (A := A) P f ↔ ∃ q : A × P.toSet,
      Arrow.mk f = Arrow.mk ((EnrichedFunctorCat.Free.functor q.1).map q.2.1.hom) :=
  MorphismProperty.adjointFamilyGenerators_iff
    (fun a : A => EnrichedFunctorCat.Free.functor a) P f

example :
    (fun (a b : A) (X Y : V) (f : X ⟶ Y) =>
      EnrichedFunctorCat.component ((EnrichedFunctorCat.Free.functor a).map f) b) =
      (fun (a b : A) (X Y : V) (f : X ⟶ Y) => f ▷ (a ⟶[V] b)) :=
  by
  funext a b X Y f
  exact EnrichedFunctorCat.Free.coefficientMap_component a f b

example (a : A) (X : V) (F : EnrichedFunctorCat V A) :
    (EnrichedFunctorCat.Free.adjunction a).homEquiv X F =
      EnrichedFunctorCat.Free.homEquiv a X F :=
  congrFun (congrFun (EnrichedFunctorCat.Free.adjunction_homEquiv a) X) F

example (a : A) :
    (EnrichedFunctorCat.Free.adjunction (V := V) a).unit.app =
      (fun X => EnrichedFunctorCat.Free.evaluate a X
        ((EnrichedFunctorCat.Free.functor (V := V) (A := A) a).obj X) (𝟙 _)) :=
  GeneratorCells.original_free_unit_function a

example (a : A) :
    (EnrichedFunctorCat.Free.adjunction (V := V) a).counit.app =
      (fun F : EnrichedFunctorCat V A => EnrichedFunctorCat.Free.extend (V := V) (A := A) a
        ((EnrichedFunctorCat.evaluation (V := V) (A := A) a).obj F) F
        (𝟙 ((EnrichedFunctorCat.evaluation (V := V) (A := A) a).obj F))) :=
  GeneratorCells.original_free_counit_function a

end CoefficientContracts

end MathlibExtTest.EnrichedGeneratorCellsData
