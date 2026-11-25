/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ClosedMaps
public import MathlibExt.CategoryTheory.Enriched.GradedComponentActions

/-!
# Every ambient coefficient in the genuine Day closed correspondence

The original Day/Kan source maps act on all central grades. Composing their
full graded source correspondence with the genuine graded Kan adjunction and
the external tensor/end correspondence retains every ambient coefficient.
Both original scalar crossing maps and every complete output weight remain
in the projection formulas.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.Closed

open EnrichedFunctorCat

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I)

/-- Both actual Day/Kan source maps retain every whole central-graded transformation. -/
def gradedSourceEquiv (Γ : Center V) (F G Y : EnrichedFunctorCat V I) :
    GradedNatTrans Γ (tensorObject d F G).toEnrichedFunctor Y.toEnrichedFunctor ≃
      GradedNatTrans Γ
        (leftKanObject d.tensorEnrichedFunctor
          (LeftKanComparison.externalObject
            F.toEnrichedFunctor G.toEnrichedFunctor)).toEnrichedFunctor
        Y.toEnrichedFunctor where
  toFun := gradedPrecomp Γ
    (LeftKanComparison.fromKan d.tensorEnrichedFunctor F.toEnrichedFunctor G.toEnrichedFunctor)
  invFun := gradedPrecomp Γ
    (LeftKanComparison.toKan d.tensorEnrichedFunctor F.toEnrichedFunctor G.toEnrichedFunctor)
  left_inv t := by
    rw [← gradedPrecomp_comp, LeftKanComparison.toKan_fromKan]
    exact gradedPrecomp_id Γ t
  right_inv t := by
    rw [← gradedPrecomp_comp, LeftKanComparison.fromKan_toKan, gradedPrecomp_id]

/-- The complete Day closed Hom correspondence at every original ambient coefficient. -/
def gradedHomEquiv (M : V) (F G Y : EnrichedFunctorCat V I) :
    GradedNatTrans ((Center.ofBraided V).obj M)
      (tensorObject d F G).toEnrichedFunctor Y.toEnrichedFunctor ≃
    GradedNatTrans ((Center.ofBraided V).obj M) G.toEnrichedFunctor
      (rightObject d F Y).toEnrichedFunctor :=
  (gradedSourceEquiv d ((Center.ofBraided V).obj M) F G Y).trans
    ((leftKanGradedHomEquiv d.tensorEnrichedFunctor ((Center.ofBraided V).obj M)
      (LeftKanComparison.externalObject F.toEnrichedFunctor G.toEnrichedFunctor) Y).trans
        (ExternalTensorMappingEndAdjunction.gradedHomEquiv M F G (tensorRestriction d Y)))

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- The original Kan unit followed by its actual Day inverse is the original Day point. -/
@[reassoc]
theorem unit_fromKan_component (F G : EnrichedFunctorCat V I) (p : I × I) :
    leftKanUnitComponent d.tensorEnrichedFunctor
        (LeftKanComparison.externalObject F.toEnrichedFunctor G.toEnrichedFunctor) p ≫
        component (LeftKanComparison.fromKan d.tensorEnrichedFunctor
          F.toEnrichedFunctor G.toEnrichedFunctor) (p.1 ⊗ p.2) =
      Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor G.toEnrichedFunctor p := by
  have h := congrArg (fun t => component t p)
    (LeftKanComparison.unit_fromKan d.tensorEnrichedFunctor
      F.toEnrichedFunctor G.toEnrichedFunctor)
  rw [component_comp, leftKanUnit_component, restrictionMap_component] at h
  exact h.trans (Generators.transformation_component d.tensorEnrichedFunctor
    F.toEnrichedFunctor G.toEnrichedFunctor p)

/-- Every coefficient projection retains the original full Day point and scalar crossing. -/
theorem gradedHomEquiv_apply_π (M : V) (F G Y : EnrichedFunctorCat V I)
    (t : GradedNatTrans ((Center.ofBraided V).obj M)
      (tensorObject d F G).toEnrichedFunctor Y.toEnrichedFunctor) (c j : I) :
    GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M)
        (gradedHomEquiv d M F G Y t) c ≫ π d F Y c j =
      MonoidalClosed.curry
        ((ExternalTensorMappingEndAdjunction.scalarExternalComponentIso M
            (F.toEnrichedFunctor.obj j) (G.toEnrichedFunctor.obj c)).hom ≫
          (M ◁ Generators.point d.tensorEnrichedFunctor
            F.toEnrichedFunctor G.toEnrichedFunctor (j, c)) ≫
          GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M) t (j ⊗ c)) := by
  change GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M)
    (ExternalTensorMappingEndAdjunction.gradedHomEquiv M F G (tensorRestriction d Y)
      (leftKanGradedHomEquiv d.tensorEnrichedFunctor ((Center.ofBraided V).obj M)
        (LeftKanComparison.externalObject F.toEnrichedFunctor G.toEnrichedFunctor) Y
        (gradedPrecomp ((Center.ofBraided V).obj M)
          (LeftKanComparison.fromKan d.tensorEnrichedFunctor
            F.toEnrichedFunctor G.toEnrichedFunctor) t))) c ≫ _ = _
  rw [ExternalTensorMappingEndAdjunction.gradedHomEquiv_apply_π,
    leftKanGradedHomEquiv_gradeFirstComponent, gradeFirstComponent_gradedPrecomp]
  change MonoidalClosed.curry
    ((ExternalTensorMappingEndAdjunction.scalarExternalComponentIso M
      (F.toEnrichedFunctor.obj j) (G.toEnrichedFunctor.obj c)).hom ≫
      (M ◁ leftKanUnitComponent d.tensorEnrichedFunctor
        (LeftKanComparison.externalObject F.toEnrichedFunctor G.toEnrichedFunctor) (j, c)) ≫
      (M ◁ component (LeftKanComparison.fromKan d.tensorEnrichedFunctor
        F.toEnrichedFunctor G.toEnrichedFunctor) (j ⊗ c)) ≫
      GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M) t (j ⊗ c)) = _
  rw [← whiskerLeft_comp_assoc]
  exact congrArg (fun z => MonoidalClosed.curry
    ((ExternalTensorMappingEndAdjunction.scalarExternalComponentIso M
      (F.toEnrichedFunctor.obj j) (G.toEnrichedFunctor.obj c)).hom ≫ (M ◁ z) ≫
      GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M) t (j ⊗ c)))
    (unit_fromKan_component d F G (j, c))

/-- The full graded inverse retains every original output Hom weight, both coefficient
crossings and the actual original end projection evaluation. -/
theorem gradedHomEquiv_symm_gen (M : V) (F G Y : EnrichedFunctorCat V I)
    (h : GradedNatTrans ((Center.ofBraided V).obj M) G.toEnrichedFunctor
      (rightObject d F Y).toEnrichedFunctor) (k : I) (p : I × I) :
    (M ◁ EnrichedDayKernel.gen d.tensorEnrichedFunctor
        F.toEnrichedFunctor G.toEnrichedFunctor k p) ≫
        GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M)
          ((gradedHomEquiv d M F G Y).symm h) k =
      (α_ M ((p.1 ⊗ p.2) ⟶[V] k)
          (F.toEnrichedFunctor.obj p.1 ⊗ G.toEnrichedFunctor.obj p.2)).inv ≫
        ((β_ ((p.1 ⊗ p.2) ⟶[V] k) M).inv ▷
          (F.toEnrichedFunctor.obj p.1 ⊗ G.toEnrichedFunctor.obj p.2)) ≫
        (α_ ((p.1 ⊗ p.2) ⟶[V] k) M
          (F.toEnrichedFunctor.obj p.1 ⊗ G.toEnrichedFunctor.obj p.2)).hom ≫
        (((p.1 ⊗ p.2) ⟶[V] k) ◁
          ((ExternalTensorMappingEndAdjunction.scalarExternalComponentIso M
            (F.toEnrichedFunctor.obj p.1) (G.toEnrichedFunctor.obj p.2)).inv ≫
              MonoidalClosed.uncurry
                (GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M) h p.2 ≫
                  π d F Y p.2 p.1))) ≫
        (β_ ((p.1 ⊗ p.2) ⟶[V] k)
          (Y.toEnrichedFunctor.obj (p.1 ⊗ p.2))).hom ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (p.1 ⊗ p.2) k) := by
  let t := (ExternalTensorMappingEndAdjunction.gradedHomEquiv M F G
    (tensorRestriction d Y)).symm h
  let u := (leftKanGradedHomEquiv d.tensorEnrichedFunctor ((Center.ofBraided V).obj M)
    (LeftKanComparison.externalObject F.toEnrichedFunctor G.toEnrichedFunctor) Y).symm t
  change (M ◁ EnrichedDayKernel.gen d.tensorEnrichedFunctor
      F.toEnrichedFunctor G.toEnrichedFunctor k p) ≫
    GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M)
      (gradedPrecomp ((Center.ofBraided V).obj M)
        (LeftKanComparison.toKan d.tensorEnrichedFunctor
          F.toEnrichedFunctor G.toEnrichedFunctor) u) k = _
  rw [gradeFirstComponent_gradedPrecomp]
  change (M ◁ EnrichedDayKernel.gen d.tensorEnrichedFunctor
      F.toEnrichedFunctor G.toEnrichedFunctor k p) ≫
    (M ◁ component (LeftKanComparison.toKan d.tensorEnrichedFunctor
      F.toEnrichedFunctor G.toEnrichedFunctor) k) ≫
    GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M) u k = _
  rw [← whiskerLeft_comp_assoc, LeftKanComparison.gen_toKan]
  have hKan := leftKanGradedHomEquiv_symm_gradeFirstComponent_ι
    d.tensorEnrichedFunctor ((Center.ofBraided V).obj M)
    (LeftKanComparison.externalObject F.toEnrichedFunctor G.toEnrichedFunctor) Y t k p
  have hEnd := ExternalTensorMappingEndAdjunction.gradedHomEquiv_symm_gradeFirst
    M F G (tensorRestriction d Y) h p.1 p.2
  exact hKan.trans (congrArg (fun q =>
    (α_ M ((p.1 ⊗ p.2) ⟶[V] k)
      (F.toEnrichedFunctor.obj p.1 ⊗ G.toEnrichedFunctor.obj p.2)).inv ≫
      ((β_ ((p.1 ⊗ p.2) ⟶[V] k) M).inv ▷
        (F.toEnrichedFunctor.obj p.1 ⊗ G.toEnrichedFunctor.obj p.2)) ≫
      (α_ ((p.1 ⊗ p.2) ⟶[V] k) M
        (F.toEnrichedFunctor.obj p.1 ⊗ G.toEnrichedFunctor.obj p.2)).hom ≫
      (((p.1 ⊗ p.2) ⟶[V] k) ◁ q) ≫
      (β_ ((p.1 ⊗ p.2) ⟶[V] k) (Y.toEnrichedFunctor.obj (p.1 ⊗ p.2))).hom ≫
      MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (p.1 ⊗ p.2) k)) hEnd)

/-- All original ambient coefficient arrows commute with the complete Day Hom correspondence. -/
theorem gradedHomEquiv_regrade {M M' : V} (r : M' ⟶ M)
    (F G Y : EnrichedFunctorCat V I)
    (t : GradedNatTrans ((Center.ofBraided V).obj M)
      (tensorObject d F G).toEnrichedFunctor Y.toEnrichedFunctor) :
    gradedHomEquiv d M' F G Y (GradedNatTrans.regrade ((Center.ofBraided V).map r) t) =
      GradedNatTrans.regrade ((Center.ofBraided V).map r) (gradedHomEquiv d M F G Y t) := by
  change ExternalTensorMappingEndAdjunction.gradedHomEquiv M' F G (tensorRestriction d Y)
    (leftKanGradedHomEquiv d.tensorEnrichedFunctor ((Center.ofBraided V).obj M')
      (LeftKanComparison.externalObject F.toEnrichedFunctor G.toEnrichedFunctor) Y
      (gradedPrecomp ((Center.ofBraided V).obj M')
        (LeftKanComparison.fromKan d.tensorEnrichedFunctor
          F.toEnrichedFunctor G.toEnrichedFunctor)
        (GradedNatTrans.regrade ((Center.ofBraided V).map r) t))) = _
  rw [gradedPrecomp_regrade, leftKanGradedHomEquiv_regrade,
    ExternalTensorMappingEndAdjunction.gradedHomEquiv_regrade]
  rfl

/-- The tensor-unit coefficient retains exactly the actual ordinary Day transpose. -/
theorem gradedHomEquiv_unit (F G Y : EnrichedFunctorCat V I)
    (f : tensorObject d F G ⟶ Y) :
    gradedHomEquiv d (𝟙_ V) F G Y f = transpose d F G Y f := by
  apply GradedNatTrans.gradeFirstComponent_ext ((Center.ofBraided V).obj (𝟙_ V))
  intro c
  apply hom_ext d F Y c
  intro j
  rw [gradedHomEquiv_apply_π, gradeFirstUnit_component, gradeFirstUnit_component,
    Category.assoc, transpose_component_π, ← MonoidalClosed.curry_natural_left]
  apply congrArg MonoidalClosed.curry
  change (ExternalTensorMappingEndAdjunction.scalarExternalComponentIso (𝟙_ V)
    (F.toEnrichedFunctor.obj j) (G.toEnrichedFunctor.obj c)).hom ≫
      ((𝟙_ V) ◁ Generators.point d.tensorEnrichedFunctor
        F.toEnrichedFunctor G.toEnrichedFunctor (j, c)) ≫
      (λ_ ((tensorObject d F G).toEnrichedFunctor.obj (j ⊗ c))).hom ≫
      component f (j ⊗ c) =
    (F.toEnrichedFunctor.obj j ◁ (λ_ (G.toEnrichedFunctor.obj c)).hom) ≫
      Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor
        G.toEnrichedFunctor (j, c) ≫ component f (j ⊗ c)
  have hu := leftUnitor_naturality_assoc
    (Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor G.toEnrichedFunctor (j, c))
    (component f (j ⊗ c))
  have hs := ExternalTensorMappingEndAdjunction.scalarExternalComponentIso_unit
    (F.toEnrichedFunctor.obj j) (G.toEnrichedFunctor.obj c)
  exact (congrArg (fun q =>
    (ExternalTensorMappingEndAdjunction.scalarExternalComponentIso (𝟙_ V)
      (F.toEnrichedFunctor.obj j) (G.toEnrichedFunctor.obj c)).hom ≫ q) hu).trans
    ((Category.assoc
      (ExternalTensorMappingEndAdjunction.scalarExternalComponentIso (𝟙_ V)
        (F.toEnrichedFunctor.obj j) (G.toEnrichedFunctor.obj c)).hom
      (λ_ (F.toEnrichedFunctor.obj j ⊗ G.toEnrichedFunctor.obj c)).hom
      (Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor G.toEnrichedFunctor
        (j, c) ≫ component f (j ⊗ c))).symm.trans
      (congrArg (fun q => q ≫ Generators.point d.tensorEnrichedFunctor
        F.toEnrichedFunctor G.toEnrichedFunctor (j, c) ≫ component f (j ⊗ c)) hs))

/-- Every coefficient retains the entire original target-arrow naturality. -/
theorem gradedHomEquiv_naturality_right (M : V) (F G : EnrichedFunctorCat V I)
    {Y Y' : EnrichedFunctorCat V I} (q : Y ⟶ Y')
    (t : GradedNatTrans ((Center.ofBraided V).obj M)
      (tensorObject d F G).toEnrichedFunctor Y.toEnrichedFunctor) :
    gradedHomEquiv d M F G Y' (gradedPostcomp ((Center.ofBraided V).obj M) t q) =
      gradedPostcomp ((Center.ofBraided V).obj M) (gradedHomEquiv d M F G Y t)
        ((rightFunctor d F).map q) := by
  apply GradedNatTrans.gradeFirstComponent_ext ((Center.ofBraided V).obj M)
  intro c
  apply hom_ext d F Y' c
  intro j
  rw [gradedHomEquiv_apply_π, gradeFirstComponent_gradedPostcomp,
    gradeFirstComponent_gradedPostcomp, Category.assoc, rightMap_π,
    reassoc_of% (gradedHomEquiv_apply_π d M F G Y t c j),
    ← MonoidalClosed.curry_natural_right]
  simp only [Category.assoc]

/-- Every coefficient retains the complete original variable-input source transformation. -/
theorem gradedHomEquiv_naturality_left (M : V) (F : EnrichedFunctorCat V I)
    {G G' : EnrichedFunctorCat V I} (f : G' ⟶ G) (Y : EnrichedFunctorCat V I)
    (t : GradedNatTrans ((Center.ofBraided V).obj M)
      (tensorObject d F G).toEnrichedFunctor Y.toEnrichedFunctor) :
    gradedHomEquiv d M F G' Y
        (gradedPrecomp ((Center.ofBraided V).obj M) ((leftFunctor d F).map f) t) =
      gradedPrecomp ((Center.ofBraided V).obj M) f (gradedHomEquiv d M F G Y t) := by
  apply GradedNatTrans.gradeFirstComponent_ext ((Center.ofBraided V).obj M)
  intro c
  apply hom_ext d F Y c
  intro j
  let q := GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M) t (j ⊗ c)
  have hmap : component ((leftFunctor d F).map f) (j ⊗ c) =
      Input.mapAt d.tensorEnrichedFunctor (𝟙 F) f (j ⊗ c) :=
    Input.bifunctor_map_component d.tensorEnrichedFunctor (𝟙 F) f (j ⊗ c)
  have hp := Generators.point_input_natural d.tensorEnrichedFunctor (𝟙 F) f (j, c)
  change Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor
      G'.toEnrichedFunctor (j, c) ≫ Input.mapAt d.tensorEnrichedFunctor (𝟙 F) f (j ⊗ c) =
    (component (𝟙 F) j ⊗ₘ component f c) ≫
      Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor G.toEnrichedFunctor
        (j, c) at hp
  rw [component_id] at hp
  rw [gradedHomEquiv_apply_π, gradeFirstComponent_gradedPrecomp,
    gradeFirstComponent_gradedPrecomp, Category.assoc, gradedHomEquiv_apply_π,
    ← MonoidalClosed.curry_natural_left]
  change MonoidalClosed.curry
    ((ExternalTensorMappingEndAdjunction.scalarExternalComponentIso M
      (F.toEnrichedFunctor.obj j) (G'.toEnrichedFunctor.obj c)).hom ≫
      (M ◁ Generators.point d.tensorEnrichedFunctor
        F.toEnrichedFunctor G'.toEnrichedFunctor (j, c)) ≫
      (M ◁ component ((leftFunctor d F).map f) (j ⊗ c)) ≫ q) =
    MonoidalClosed.curry
      ((F.toEnrichedFunctor.obj j ◁ (M ◁ component f c)) ≫
        (ExternalTensorMappingEndAdjunction.scalarExternalComponentIso M
          (F.toEnrichedFunctor.obj j) (G.toEnrichedFunctor.obj c)).hom ≫
        (M ◁ Generators.point d.tensorEnrichedFunctor
          F.toEnrichedFunctor G.toEnrichedFunctor (j, c)) ≫ q)
  rw [hmap, ← whiskerLeft_comp_assoc, hp, whiskerLeft_comp_assoc]
  simpa only [Category.assoc, id_tensorHom, id_tensorHom_id] using congrArg
    (fun z => MonoidalClosed.curry
      (z ≫ (M ◁ Generators.point d.tensorEnrichedFunctor
        F.toEnrichedFunctor G.toEnrichedFunctor (j, c)) ≫ q))
    (ExternalTensorMappingEndAdjunction.scalarExternalComponentIso_naturality
      (𝟙 M) (𝟙 (F.toEnrichedFunctor.obj j)) (component f c)).symm

/-- The original complete Day input map on the fixed source, with its exact two carriers. -/
def weightMap {F F' : EnrichedFunctorCat V I} (p : F' ⟶ F) (G : EnrichedFunctorCat V I) :
    tensorObject d F' G ⟶ tensorObject d F G :=
  (Input.bifunctor d.tensorEnrichedFunctor).map (X := (F', G)) (Y := (F, G)) (p, 𝟙 G)

/-- Every coefficient retains the complete original contravariant weight transformation. -/
theorem gradedHomEquiv_naturality_source (M : V) {F F' : EnrichedFunctorCat V I}
    (p : F' ⟶ F) (G Y : EnrichedFunctorCat V I)
    (t : GradedNatTrans ((Center.ofBraided V).obj M)
      (tensorObject d F G).toEnrichedFunctor Y.toEnrichedFunctor) :
    gradedHomEquiv d M F' G Y
        (gradedPrecomp ((Center.ofBraided V).obj M) (weightMap d p G) t) =
      gradedPostcomp ((Center.ofBraided V).obj M) (gradedHomEquiv d M F G Y t)
        (pre d p Y) := by
  apply GradedNatTrans.gradeFirstComponent_ext ((Center.ofBraided V).obj M)
  intro c
  apply hom_ext d F' Y c
  intro j
  let q := GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj M) t (j ⊗ c)
  have hmap : component (weightMap d p G)
      (j ⊗ c) = Input.mapAt d.tensorEnrichedFunctor p (𝟙 G) (j ⊗ c) :=
    Input.bifunctor_map_component d.tensorEnrichedFunctor p (𝟙 G) (j ⊗ c)
  have hp := Generators.point_input_natural d.tensorEnrichedFunctor p (𝟙 G) (j, c)
  change Generators.point d.tensorEnrichedFunctor F'.toEnrichedFunctor
      G.toEnrichedFunctor (j, c) ≫ Input.mapAt d.tensorEnrichedFunctor p (𝟙 G) (j ⊗ c) =
    (component p j ⊗ₘ component (𝟙 G) c) ≫
      Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor G.toEnrichedFunctor
        (j, c) at hp
  rw [component_id] at hp
  have hn : (ExternalTensorMappingEndAdjunction.scalarExternalComponentIso M
      (F'.toEnrichedFunctor.obj j) (G.toEnrichedFunctor.obj c)).hom ≫
      (M ◁ (component p j ⊗ₘ 𝟙 (G.toEnrichedFunctor.obj c))) =
    (component p j ▷ (M ⊗ G.toEnrichedFunctor.obj c)) ≫
      (ExternalTensorMappingEndAdjunction.scalarExternalComponentIso M
        (F.toEnrichedFunctor.obj j) (G.toEnrichedFunctor.obj c)).hom := by
    simpa only [tensorHom_id, id_tensorHom, id_tensorHom_id, id_whiskerRight] using
      (ExternalTensorMappingEndAdjunction.scalarExternalComponentIso_naturality
        (𝟙 M) (component p j) (𝟙 (G.toEnrichedFunctor.obj c))).symm
  rw [gradedHomEquiv_apply_π, gradeFirstComponent_gradedPrecomp,
    gradeFirstComponent_gradedPostcomp, Category.assoc, pre_π,
    reassoc_of% (gradedHomEquiv_apply_π d M F G Y t c j)]
  change MonoidalClosed.curry
    ((ExternalTensorMappingEndAdjunction.scalarExternalComponentIso M
      (F'.toEnrichedFunctor.obj j) (G.toEnrichedFunctor.obj c)).hom ≫
      (M ◁ Generators.point d.tensorEnrichedFunctor
        F'.toEnrichedFunctor G.toEnrichedFunctor (j, c)) ≫
      (M ◁ component (weightMap d p G)
        (j ⊗ c)) ≫ q) =
    MonoidalClosed.curry
      ((ExternalTensorMappingEndAdjunction.scalarExternalComponentIso M
          (F.toEnrichedFunctor.obj j) (G.toEnrichedFunctor.obj c)).hom ≫
        (M ◁ Generators.point d.tensorEnrichedFunctor
          F.toEnrichedFunctor G.toEnrichedFunctor (j, c)) ≫ q) ≫
      (MonoidalClosed.pre (component p j)).app (Y.toEnrichedFunctor.obj (j ⊗ c))
  rw [hmap, ← whiskerLeft_comp_assoc, hp, whiskerLeft_comp_assoc]
  calc
    _ = MonoidalClosed.curry
        ((component p j ▷ (M ⊗ G.toEnrichedFunctor.obj c)) ≫
          (ExternalTensorMappingEndAdjunction.scalarExternalComponentIso M
            (F.toEnrichedFunctor.obj j) (G.toEnrichedFunctor.obj c)).hom ≫
          (M ◁ Generators.point d.tensorEnrichedFunctor
            F.toEnrichedFunctor G.toEnrichedFunctor (j, c)) ≫ q) := by
      simpa only [Category.assoc] using congrArg (fun z => MonoidalClosed.curry
        (z ≫ (M ◁ Generators.point d.tensorEnrichedFunctor
          F.toEnrichedFunctor G.toEnrichedFunctor (j, c)) ≫ q)) hn
    _ = _ := (MonoidalClosed.curry_pre_app (component p j)
      ((ExternalTensorMappingEndAdjunction.scalarExternalComponentIso M
        (F.toEnrichedFunctor.obj j) (G.toEnrichedFunctor.obj c)).hom ≫
        (M ◁ Generators.point d.tensorEnrichedFunctor
          F.toEnrichedFunctor G.toEnrichedFunctor (j, c)) ≫ q)).symm

/-- The whole coefficient correspondences are an actual natural isomorphism of the original
ambient presheaves, with no coefficient-point restriction. -/
def gradedPresheafIso (F G Y : EnrichedFunctorCat V I) :
    enrichedNatTransYoneda (tensorObject d F G).toEnrichedFunctor Y.toEnrichedFunctor ≅
      enrichedNatTransYoneda G.toEnrichedFunctor (rightObject d F Y).toEnrichedFunctor :=
  NatIso.ofComponents (fun M => (gradedHomEquiv d M.unop F G Y).toIso) (by
    intro M N r
    apply ConcreteCategory.ext_apply
    intro t
    exact gradedHomEquiv_regrade d r.unop F G Y t)

/-- The original presheaf forward map is precisely the whole coefficient transpose. -/
theorem gradedPresheafIso_hom_app (M : V) (F G Y : EnrichedFunctorCat V I)
    (t : GradedNatTrans ((Center.ofBraided V).obj M)
      (tensorObject d F G).toEnrichedFunctor Y.toEnrichedFunctor) :
    (gradedPresheafIso d F G Y).hom.app (Opposite.op M) t = gradedHomEquiv d M F G Y t := rfl

end CategoryTheory.EnrichedDayKernel.Closed
