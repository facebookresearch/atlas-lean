/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalHomotopyCategory
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ComponentUnionWeakRestriction

/-!
# Equivalence components of the original inner mapping spaces

Every original edge of a scalar source evaluates an inner mapping simplex in
the original arrow space. We select precisely those components for which all
these evaluations are intrinsic equivalences. The resulting component unions
retain both variances of the original enrichment. Monic source restrictions
are Kan fibrations, while genuine edge coverage gives an exact preimage
pullback. At the one-simplex the enriched Yoneda comparison restricts to the
original equivalence-arrow subcomplex.

Source: Rezk (2001), Sections 5.7 and 11.6–11.7.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen SimplicialSpace.Inner

namespace SimplicialSpace.EquivalenceMapping

variable {Z V W : SimplicialSpace.{u}} {A B C : SSet.{u}}

/-- Evaluation on the same original edge, followed by enriched Yoneda. -/
def edgeEvaluation (Z : SimplicialSpace.{u}) {A : SSet.{u}} (γ : Δ[1] ⟶ A) :
    (discreteSourceMapping Z).obj (op A) ⟶ Z.diagram _⦋1⦌ :=
  (discreteSourceMapping Z).map γ.op ≫ (discreteYonedaIso Z 1).hom

/-- Original precomposition retains every original edge evaluation. -/
@[reassoc]
theorem edgeEvaluation_source (Z : SimplicialSpace.{u}) (i : A ⟶ B) (γ : Δ[1] ⟶ A) :
    (discreteSourceMapping Z).map i.op ≫ edgeEvaluation Z γ =
      edgeEvaluation Z (γ ≫ i) := by
  simp only [edgeEvaluation, op_comp, Functor.map_comp, Category.assoc]

/-- Every original target arrow commutes with the original edge evaluation. -/
@[reassoc]
theorem edgeEvaluation_target (t : Z ⟶ V) (γ : Δ[1] ⟶ A) :
    (discreteSourceMappingMap t).app (op A) ≫ edgeEvaluation V γ =
      edgeEvaluation Z γ ≫ t.hom.app (op ⦋1⦌) := by
  unfold edgeEvaluation
  rw [← Category.assoc, ← (discreteSourceMappingMap t).naturality γ.op,
    Category.assoc, discreteYonedaIso_naturality_target]
  exact (Category.assoc _ _ _).symm

/-- The exact selector tests every original edge, without choosing a representative. -/
def components (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z) (A : SSet.{u}) :
    Set (SSet.π₀ ((discreteSourceMapping Z).obj (op A))) :=
  {c | ∀ γ : Δ[1] ⟶ A,
    SSet.mapπ₀ (edgeEvaluation Z γ) c ∈ SegalHomotopy.equivalenceComponents Z hZ}

/-- The literal component union of the original inner mapping space. -/
def subcomplex (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z) (A : SSet.{u}) :
    ((discreteSourceMapping Z).obj (op A)).Subcomplex :=
  SSet.componentUnion _ (components Z hZ A)

private theorem componentLabel_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    (n : SimplexCategoryᵒᵖ) (q : X.obj n) :
    SSet.mapπ₀ f (SSet.π₀.mk (X.map (SimplexCategory.const ⦋0⦌ n.unop 0).op q)) =
      SSet.π₀.mk (Y.map (SimplexCategory.const ⦋0⦌ n.unop 0).op (f.app n q)) := by
  rw [SSet.mapπ₀_mk]
  exact congrArg SSet.π₀.mk (f.naturality_apply _ q)

/-- Every original mapping simplex is selected exactly when all its edge evaluations are. -/
theorem mem_subcomplex (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z) (A : SSet.{u})
    (n : SimplexCategoryᵒᵖ) (q : ((discreteSourceMapping Z).obj (op A)).obj n) :
    q ∈ (subcomplex Z hZ A).obj n ↔
      ∀ γ : Δ[1] ⟶ A,
        (edgeEvaluation Z γ).app n q ∈ (SegalHomotopy.equivalenceSubcomplex Z hZ).obj n := by
  rw [subcomplex, SSet.mem_componentUnion]
  change (∀ γ : Δ[1] ⟶ A, _ ∈ SegalHomotopy.equivalenceComponents Z hZ) ↔ _
  constructor
  · intro h γ
    change (edgeEvaluation Z γ).app n q ∈
      (SSet.componentUnion (Z.diagram _⦋1⦌)
        (SegalHomotopy.equivalenceComponents Z hZ)).obj n
    rw [SSet.mem_componentUnion]
    exact (componentLabel_naturality (edgeEvaluation Z γ) n q) ▸ h γ
  · intro h γ
    have hγ := h γ
    change (edgeEvaluation Z γ).app n q ∈
      (SSet.componentUnion (Z.diagram _⦋1⦌)
        (SegalHomotopy.equivalenceComponents Z hZ)).obj n at hγ
    rw [SSet.mem_componentUnion] at hγ
    exact (componentLabel_naturality (edgeEvaluation Z γ) n q).symm ▸ hγ

/-- Any original inner vertex gives the same all-edge equivalence test. -/
theorem mem_subcomplex_vertex (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z) (A : SSet.{u})
    (n : SimplexCategoryᵒᵖ) (q : ((discreteSourceMapping Z).obj (op A)).obj n)
    (α : ⦋0⦌ ⟶ n.unop) :
    q ∈ (subcomplex Z hZ A).obj n ↔ ∀ γ : Δ[1] ⟶ A,
      SegalHomotopy.IsEquivalenceEdge Z hZ
        ((edgeEvaluation Z γ).app (op ⦋0⦌)
          (((discreteSourceMapping Z).obj (op A)).map α.op q)) := by
  rw [mem_subcomplex]
  constructor <;> intro h γ
  · have hγ := (SegalHomotopy.mem_equivalenceSubcomplex_iff_vertex Z hZ n _ α).mp (h γ)
    exact (edgeEvaluation Z γ).naturality_apply α.op q ▸ hγ
  · apply (SegalHomotopy.mem_equivalenceSubcomplex_iff_vertex Z hZ n _ α).mpr
    exact ((edgeEvaluation Z γ).naturality_apply α.op q).symm ▸ h γ

/-- Any original inner operator preserves exact selected-component membership. -/
theorem mem_subcomplex_operator (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z) (A : SSet.{u})
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (q : ((discreteSourceMapping Z).obj (op A)).obj n) :
    q ∈ (subcomplex Z hZ A).obj n ↔
      ((discreteSourceMapping Z).obj (op A)).map θ q ∈ (subcomplex Z hZ A).obj m := by
  rw [subcomplex, SSet.mem_componentUnion, SSet.mem_componentUnion]
  let X := (discreteSourceMapping Z).obj (op A)
  let c := SSet.π₀.mk (X.map (SimplexCategory.const ⦋0⦌ n.unop 0).op q)
  have hq : q ∈ (SSet.π₀.component c).obj n := rfl
  have hm := (SSet.π₀.component c).map θ hq
  change SSet.π₀.mk
    (X.map (SimplexCategory.const ⦋0⦌ m.unop 0).op (X.map θ q)) = c at hm
  rw [hm]

/-- Original source restriction on the literal selected unions, for every source arrow. -/
def restriction (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z) (i : A ⟶ B) :
    (subcomplex Z hZ B : SSet.{u}) ⟶ (subcomplex Z hZ A : SSet.{u}) :=
  SSet.Subcomplex.lift
    ((subcomplex Z hZ B).ι ≫ (discreteSourceMapping Z).map i.op) (by
      intro n q hq
      rcases hq with ⟨a, rfl⟩
      apply (mem_subcomplex Z hZ A n _).mpr
      intro γ
      change (edgeEvaluation Z γ).app n (((discreteSourceMapping Z).map i.op).app n a.val) ∈
        (SegalHomotopy.equivalenceSubcomplex Z hZ).obj n
      have h := congrArg (fun f => f.app n a.val) (edgeEvaluation_source Z i γ)
      change (edgeEvaluation Z γ).app n (((discreteSourceMapping Z).map i.op).app n a.val) =
        (edgeEvaluation Z (γ ≫ i)).app n a.val at h
      rw [h]
      exact (mem_subcomplex Z hZ B n a.val).mp a.property (γ ≫ i))

/-- Both literal inclusions keep exactly the original raw precomposition. -/
@[reassoc (attr := simp)]
theorem restriction_ι (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z) (i : A ⟶ B) :
    restriction Z hZ i ≫ (subcomplex Z hZ A).ι =
      (subcomplex Z hZ B).ι ≫ (discreteSourceMapping Z).map i.op :=
  SSet.Subcomplex.lift_ι _ _

/-- Every selected simplex retains its same original precomposition value. -/
@[simp]
theorem restriction_app_val (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z) (i : A ⟶ B)
    (n : SimplexCategoryᵒᵖ) (q : (subcomplex Z hZ B : SSet.{u}).obj n) :
    dsimp% ((restriction Z hZ i).app n q).val =
      ((discreteSourceMapping Z).map i.op).app n q.val := rfl

/-- Original identities induce identities on the selected mapping spaces. -/
theorem restriction_id (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z) (A : SSet.{u}) :
    restriction Z hZ (𝟙 A) = 𝟙 (subcomplex Z hZ A : SSet.{u}) := by
  apply (cancel_mono (subcomplex Z hZ A).ι).mp
  rw [restriction_ι, op_id, (discreteSourceMapping Z).map_id,
    Category.comp_id, Category.id_comp]

/-- Original source composites act in the original contravariant order. -/
theorem restriction_comp (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z)
    (i : A ⟶ B) (j : B ⟶ C) :
    restriction Z hZ (i ≫ j) = restriction Z hZ j ≫ restriction Z hZ i := by
  apply (cancel_mono (subcomplex Z hZ A).ι).mp
  simp only [restriction_ι, Category.assoc, restriction_ι_assoc,
    op_comp, Functor.map_comp]

/-- Target arrows restrict by the same original target action, without a fibration premise. -/
def targetMap (t : Z ⟶ V) (hZ : segalSpaces Z) (hV : segalSpaces V) (A : SSet.{u}) :
    (subcomplex Z hZ A : SSet.{u}) ⟶ (subcomplex V hV A : SSet.{u}) :=
  SSet.Subcomplex.lift
    ((subcomplex Z hZ A).ι ≫ (discreteSourceMappingMap t).app (op A)) (by
      intro n q hq
      rcases hq with ⟨a, rfl⟩
      apply (mem_subcomplex V hV A n _).mpr
      intro γ
      change (edgeEvaluation V γ).app n
        (((discreteSourceMappingMap t).app (op A)).app n a.val) ∈
          (SegalHomotopy.equivalenceSubcomplex V hV).obj n
      have h := congrArg (fun f => f.app n a.val) (edgeEvaluation_target t γ)
      change (edgeEvaluation V γ).app n
          (((discreteSourceMappingMap t).app (op A)).app n a.val) =
        (t.hom.app (op ⦋1⦌)).app n ((edgeEvaluation Z γ).app n a.val) at h
      rw [h]
      have he := (mem_subcomplex Z hZ A n a.val).mp a.property γ
      exact ((SegalHomotopy.equivalenceMap t hZ hV).app n
        ⟨(edgeEvaluation Z γ).app n a.val, he⟩).property)

/-- Both target inclusion legs retain the same original mapping-space target arrow. -/
@[reassoc (attr := simp)]
theorem targetMap_ι (t : Z ⟶ V) (hZ : segalSpaces Z) (hV : segalSpaces V) (A : SSet.{u}) :
    targetMap t hZ hV A ≫ (subcomplex V hV A).ι =
      (subcomplex Z hZ A).ι ≫ (discreteSourceMappingMap t).app (op A) :=
  SSet.Subcomplex.lift_ι _ _

/-- The target action preserves every original degreewise value. -/
@[simp]
theorem targetMap_app_val (t : Z ⟶ V) (hZ : segalSpaces Z) (hV : segalSpaces V) (A : SSet.{u})
    (n : SimplexCategoryᵒᵖ) (q : (subcomplex Z hZ A : SSet.{u}).obj n) :
    dsimp% ((targetMap t hZ hV A).app n q).val =
      ((discreteSourceMappingMap t).app (op A)).app n q.val := rfl

/-- Original target identities act identically on the selected unions. -/
theorem targetMap_id (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z) (A : SSet.{u}) :
    targetMap (𝟙 Z) hZ hZ A = 𝟙 (subcomplex Z hZ A : SSet.{u}) := by
  apply (cancel_mono (subcomplex Z hZ A).ι).mp
  rw [targetMap_ι, Category.id_comp]
  have h : (discreteSourceMappingMap (𝟙 Z)).app (op A) = 𝟙 _ :=
    (innerHomFunctor.obj
      (op (ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj A)))).map_id Z
  rw [h, Category.comp_id]

/-- Original target composites retain their original covariant order. -/
theorem targetMap_comp (t : Z ⟶ V) (s : V ⟶ W)
    (hZ : segalSpaces Z) (hV : segalSpaces V) (hW : segalSpaces W) (A : SSet.{u}) :
    targetMap (t ≫ s) hZ hW A = targetMap t hZ hV A ≫ targetMap s hV hW A := by
  apply (cancel_mono (subcomplex W hW A).ι).mp
  rw [targetMap_ι, Category.assoc, targetMap_ι, targetMap_ι_assoc]
  change (subcomplex Z hZ A).ι ≫
      ((innerHomFunctor.obj (op (ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj A)))).map
        (t ≫ s)) = _
  rw [Functor.map_comp]
  rfl

/-- Source and target changes commute on the same original mapping-space square. -/
theorem restriction_targetMap (t : Z ⟶ V) (hZ : segalSpaces Z) (hV : segalSpaces V)
    (i : A ⟶ B) :
    targetMap t hZ hV B ≫ restriction V hV i =
      restriction Z hZ i ≫ targetMap t hZ hV A := by
  apply (cancel_mono (subcomplex V hV A).ι).mp
  simp only [Category.assoc, restriction_ι, targetMap_ι,
    restriction_ι_assoc, targetMap_ι_assoc]
  exact congrArg (fun f => (subcomplex Z hZ B).ι ≫ f)
    ((discreteSourceMappingMap t).naturality i.op).symm

/-- Decorated source restriction keeps the whole original edge-evaluation square. -/
@[reassoc]
theorem restriction_evaluation (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z)
    (i : A ⟶ B) (γ : Δ[1] ⟶ A) :
    restriction Z hZ i ≫ (subcomplex Z hZ A).ι ≫ edgeEvaluation Z γ =
      (subcomplex Z hZ B).ι ≫ edgeEvaluation Z (γ ≫ i) := by
  rw [restriction_ι_assoc, edgeEvaluation_source]

/-- Decorated target change keeps the whole original edge-evaluation square. -/
@[reassoc]
theorem targetMap_evaluation (t : Z ⟶ V) (hZ : segalSpaces Z) (hV : segalSpaces V)
    (γ : Δ[1] ⟶ A) :
    targetMap t hZ hV A ≫ (subcomplex V hV A).ι ≫ edgeEvaluation V γ =
      (subcomplex Z hZ A).ι ≫ edgeEvaluation Z γ ≫ t.hom.app (op ⦋1⦌) := by
  rw [targetMap_ι_assoc, edgeEvaluation_target]

/-- The actual inner mapping space is Kan from the same named Reedy fibrancy. -/
theorem rawMapping_kan (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z) (A : SSet.{u}) :
    SSet.KanComplex ((discreteSourceMapping Z).obj (op A)) :=
  ReedyModel.innerHom_kanComplex
    (ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj A)) Z
    (ReedyModel.isCofibrant _) hZ.1

/-- Its literal selected component union is Kan. -/
theorem subcomplex_kan (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z) (A : SSet.{u}) :
    SSet.KanComplex (subcomplex Z hZ A : SSet.{u}) := by
  let : SSet.KanComplex ((discreteSourceMapping Z).obj (op A)) := rawMapping_kan Z hZ A
  exact SSet.componentUnionKanComplex _ _

/-- The original union inclusion is a genuine Kan fibration. -/
theorem inclusion_fibration (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z) (A : SSet.{u}) :
    Fibration (subcomplex Z hZ A).ι :=
  SSet.componentUnionInclusionKanFibration _ _

private theorem rawRestriction_fibration (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z)
    (i : A ⟶ B) [Mono i] : Fibration ((discreteSourceMapping Z).map i.op) := by
  let : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let : Mono (SSet.simplicialSpaceDiscrete.map i) := by
    rw [NatTrans.mono_iff_mono_app]
    intro m
    rw [NatTrans.mono_iff_mono_app]
    intro j
    change Mono (i.app m)
    have hi : Mono i := inferInstance
    rw [NatTrans.mono_iff_mono_app] at hi
    exact hi m
  let f := ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map i)
  have hcof : cofibrations SimplicialSpace.{u} f :=
    (HomotopicalAlgebra.cofibration_iff f).mp
      ((ReedyModel.cofibration_iff f).mpr inferInstance)
  exact (HomotopicalAlgebra.fibration_iff _).mpr
    (ReedyModel.inner_precomp_fibration f Z hcof hZ.1)

private theorem liftingProperty_cancel_mono {X Y T : SSet.{u}}
    (i : A ⟶ B) (p : X ⟶ Y) (j : Y ⟶ T) [Mono j]
    [HasLiftingProperty i (p ≫ j)] : HasLiftingProperty i p where
  sq_hasLift := fun {a b} sq => by
    have sq' : CommSq a i (p ≫ j) (b ≫ j) :=
      ⟨by rw [← Category.assoc, sq.w, Category.assoc]⟩
    exact CommSq.HasLift.mk'
      ⟨sq'.lift, sq'.fac_left, (cancel_mono j).mp (by
        simpa only [Category.assoc] using sq'.fac_right)⟩

/-- A monic original source gives a Kan fibration on the same decorated restriction. -/
theorem restriction_fibration (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z)
    (i : A ⟶ B) [Mono i] : Fibration (restriction Z hZ i) := by
  let : Fibration (subcomplex Z hZ B).ι := inclusion_fibration Z hZ B
  let : Fibration ((discreteSourceMapping Z).map i.op) := rawRestriction_fibration Z hZ i
  have hcomp : Fibration (restriction Z hZ i ≫ (subcomplex Z hZ A).ι) := by
    rw [restriction_ι]
    infer_instance
  rw [SSet.modelCategoryQuillen.fibration_iff] at hcomp ⊢
  intro X Y j hj
  let : HasLiftingProperty j (restriction Z hZ i ≫ (subcomplex Z hZ A).ι) := hcomp j hj
  exact liftingProperty_cancel_mono j (restriction Z hZ i) (subcomplex Z hZ A).ι

/-- Genuine edge coverage identifies the selector with the exact original component preimage. -/
theorem components_preimage_of_edgeCover (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z)
    (i : A ⟶ B) (hi : ∀ γ : Δ[1] ⟶ B, ∃ δ : Δ[1] ⟶ A, δ ≫ i = γ) :
    components Z hZ B = (SSet.mapπ₀ ((discreteSourceMapping Z).map i.op)) ⁻¹'
      components Z hZ A := by
  ext c
  constructor
  · intro h δ
    have hc := congrArg (fun f => SSet.mapπ₀ f c) (edgeEvaluation_source Z i δ)
    rw [SSet.mapπ₀_comp_apply] at hc
    exact hc.symm ▸ h (δ ≫ i)
  · intro h γ
    obtain ⟨δ, rfl⟩ := hi γ
    have hc := congrArg (fun f => SSet.mapπ₀ f c) (edgeEvaluation_source Z i δ)
    rw [SSet.mapπ₀_comp_apply] at hc
    exact hc ▸ h δ

/-- The same edge coverage gives the literal native subcomplex preimage. -/
theorem subcomplex_preimage_of_edgeCover (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z)
    (i : A ⟶ B) (hi : ∀ γ : Δ[1] ⟶ B, ∃ δ : Δ[1] ⟶ A, δ ≫ i = γ) :
    subcomplex Z hZ B = (subcomplex Z hZ A).preimage ((discreteSourceMapping Z).map i.op) := by
  unfold subcomplex
  rw [components_preimage_of_edgeCover Z hZ i hi, SSet.componentUnion_preimage]
  rfl

/-- Both original inclusions and the same restriction form the exact edge-covered pullback. -/
theorem restriction_isPullback_of_edgeCover (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z)
    (i : A ⟶ B) (hi : ∀ γ : Δ[1] ⟶ B, ∃ δ : Δ[1] ⟶ A, δ ≫ i = γ) :
    IsPullback (subcomplex Z hZ B).ι (restriction Z hZ i)
      ((discreteSourceMapping Z).map i.op) (subcomplex Z hZ A).ι := by
  have hAux (U : ((discreteSourceMapping Z).obj (op B)).Subcomplex)
      (hU : U = Subfunctor.preimage (subcomplex Z hZ A) ((discreteSourceMapping Z).map i.op))
      (hR : SSet.Subcomplex.range (U.ι ≫ (discreteSourceMapping Z).map i.op) ≤
        subcomplex Z hZ A) :
      IsPullback U.ι (SSet.Subcomplex.lift (U.ι ≫ (discreteSourceMapping Z).map i.op) hR)
        ((discreteSourceMapping Z).map i.op) (subcomplex Z hZ A).ι := by
    subst U
    exact Subfunctor.preimage_isPullback _ _
  exact hAux _ (subcomplex_preimage_of_edgeCover Z hZ i hi) _

/-- Every original one-simplex operator is retained by the actual enriched Yoneda map. -/
theorem edgeEvaluation_one_operator (Z : SimplicialSpace.{u}) (θ : ⦋1⦌ ⟶ ⦋1⦌) :
    edgeEvaluation Z (SSet.stdSimplex.map θ) =
      (discreteYonedaIso Z 1).hom ≫ Z.diagram.map θ.op :=
  discreteYonedaIso_naturality_index Z θ

/-- The original identity edge operator is exactly the enriched Yoneda map. -/
theorem edgeEvaluation_one_id (Z : SimplicialSpace.{u}) :
    edgeEvaluation Z (𝟙 (Δ[1] : SSet.{u})) = (discreteYonedaIso Z 1).hom := by
  rw [edgeEvaluation, op_id, (discreteSourceMapping Z).map_id, Category.id_comp]

/-- Both constant edge operators evaluate to the original identity degeneracy. -/
theorem edgeEvaluation_one_const (Z : SimplicialSpace.{u}) (a : Fin 2) :
    edgeEvaluation Z (SSet.stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ a)) =
      (discreteYonedaIso Z 1).hom ≫
        Z.diagram.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ a).op ≫
          Z.diagram.σ (0 : Fin 1) := by
  rw [edgeEvaluation_one_operator, SimplexCategory.const_fac_thru_zero, op_comp,
    Functor.map_comp]
  have hs : SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 = SimplexCategory.σ (0 : Fin 1) :=
    (SimplexCategory.eq_const_to_zero _).symm
  rw [hs]
  rfl

private theorem constant_mem_equivalenceSubcomplex (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z)
    (a : Fin 2) (n : SimplexCategoryᵒᵖ) (q : (Z.diagram _⦋1⦌).obj n) :
    (Z.diagram.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ a).op).app n q ∈
      (SegalHomotopy.equivalenceSubcomplex Z hZ).obj n := by
  rw [SimplexCategory.const_fac_thru_zero, op_comp, Functor.map_comp]
  have hs : SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 = SimplexCategory.σ (0 : Fin 1) :=
    (SimplexCategory.eq_const_to_zero _).symm
  rw [hs]
  exact ((SegalHomotopy.equivalenceIdentity Z hZ).app n
    ((Z.diagram.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ a).op).app n q)).property

/-- At the original one-simplex the all-edge test is exactly the intrinsic equivalence
subcomplex. -/
theorem mem_subcomplex_one (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z)
    (n : SimplexCategoryᵒᵖ) (q : ((discreteSourceMapping Z).obj (op (Δ[1] : SSet.{u}))).obj n) :
    q ∈ (subcomplex Z hZ Δ[1]).obj n ↔
      (discreteYonedaIso Z 1).hom.app n q ∈
        (SegalHomotopy.equivalenceSubcomplex Z hZ).obj n := by
  rw [mem_subcomplex]
  constructor
  · intro h
    simpa only [edgeEvaluation_one_id] using h (𝟙 (Δ[1] : SSet.{u}))
  · intro h γ
    obtain ⟨θ, rfl⟩ := SSet.stdSimplex.map_surjective γ
    rw [edgeEvaluation_one_operator]
    rcases SimplexCategory.eq_of_one_to_one θ with ⟨a, rfl⟩ | rfl
    · exact constant_mem_equivalenceSubcomplex Z hZ a n ((discreteYonedaIso Z 1).hom.app n q)
    · rw [op_id, Z.diagram.map_id]
      exact h

/-- The original enriched-Yoneda isomorphism restricts to the actual equivalence-arrow union. -/
def yonedaIsoOne (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z) :
    (subcomplex Z hZ Δ[1] : SSet.{u}) ≅ (SegalHomotopy.equivalenceSubcomplex Z hZ : SSet.{u}) := by
  let f := SSet.Subcomplex.lift
    ((subcomplex Z hZ Δ[1]).ι ≫ (discreteYonedaIso Z 1).hom) (by
      intro n q hq
      rcases hq with ⟨a, rfl⟩
      exact (mem_subcomplex_one Z hZ n a.val).mp a.property)
  let g := SSet.Subcomplex.lift
    ((SegalHomotopy.equivalenceSubcomplex Z hZ).ι ≫ (discreteYonedaIso Z 1).inv) (by
      intro n q hq
      rcases hq with ⟨a, rfl⟩
      apply (mem_subcomplex_one Z hZ n _).mpr
      change (discreteYonedaIso Z 1).hom.app n
        ((discreteYonedaIso Z 1).inv.app n a.val) ∈
          (SegalHomotopy.equivalenceSubcomplex Z hZ).obj n
      have h := congrArg (fun k => k.app n a.val) (discreteYonedaIso Z 1).inv_hom_id
      change (discreteYonedaIso Z 1).hom.app n
        ((discreteYonedaIso Z 1).inv.app n a.val) = a.val at h
      rw [h]
      exact a.property)
  have hf : f ≫ (SegalHomotopy.equivalenceSubcomplex Z hZ).ι =
      (subcomplex Z hZ Δ[1]).ι ≫ (discreteYonedaIso Z 1).hom :=
    SSet.Subcomplex.lift_ι _ _
  have hg : g ≫ (subcomplex Z hZ Δ[1]).ι =
      (SegalHomotopy.equivalenceSubcomplex Z hZ).ι ≫ (discreteYonedaIso Z 1).inv :=
    SSet.Subcomplex.lift_ι _ _
  refine ⟨f, g, ?_, ?_⟩
  · apply (cancel_mono (subcomplex Z hZ Δ[1]).ι).mp
    rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · apply (cancel_mono (SegalHomotopy.equivalenceSubcomplex Z hZ).ι).mp
    rw [Category.assoc, hf, ← Category.assoc, hg, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- The forward comparison preserves the original enriched-Yoneda map and inclusion. -/
@[reassoc (attr := simp)]
theorem yonedaIsoOne_hom_ι (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z) :
    (yonedaIsoOne Z hZ).hom ≫ (SegalHomotopy.equivalenceSubcomplex Z hZ).ι =
      (subcomplex Z hZ Δ[1]).ι ≫ (discreteYonedaIso Z 1).hom :=
  rfl

/-- The inverse comparison preserves the same original inverse enriched-Yoneda map. -/
@[reassoc (attr := simp)]
theorem yonedaIsoOne_inv_ι (Z : SimplicialSpace.{u}) (hZ : segalSpaces Z) :
    (yonedaIsoOne Z hZ).inv ≫ (subcomplex Z hZ Δ[1]).ι =
      (SegalHomotopy.equivalenceSubcomplex Z hZ).ι ≫ (discreteYonedaIso Z 1).inv :=
  rfl

/-- The forward restricted Yoneda map is natural for every original target arrow. -/
theorem yonedaIsoOne_naturality_target (t : Z ⟶ V) (hZ : segalSpaces Z) (hV : segalSpaces V) :
    targetMap t hZ hV Δ[1] ≫ (yonedaIsoOne V hV).hom =
      (yonedaIsoOne Z hZ).hom ≫ SegalHomotopy.equivalenceMap t hZ hV := by
  apply (cancel_mono (SegalHomotopy.equivalenceSubcomplex V hV).ι).mp
  simp only [Category.assoc, yonedaIsoOne_hom_ι, targetMap_ι_assoc,
    SegalHomotopy.equivalenceMap_ι, yonedaIsoOne_hom_ι_assoc]
  rw [discreteYonedaIso_naturality_target]

/-- The inverse restricted Yoneda map retains the other original target square. -/
theorem yonedaIsoOne_inv_naturality_target (t : Z ⟶ V)
    (hZ : segalSpaces Z) (hV : segalSpaces V) :
    SegalHomotopy.equivalenceMap t hZ hV ≫ (yonedaIsoOne V hV).inv =
      (yonedaIsoOne Z hZ).inv ≫ targetMap t hZ hV Δ[1] := by
  apply (cancel_mono (yonedaIsoOne V hV).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    yonedaIsoOne_naturality_target, Iso.inv_hom_id_assoc]

end SimplicialSpace.EquivalenceMapping
