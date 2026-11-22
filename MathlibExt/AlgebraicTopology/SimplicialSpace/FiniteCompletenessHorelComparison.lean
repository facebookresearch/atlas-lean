/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.FiniteCompletenessEquivalenceEvaluation
import MathlibExt.AlgebraicTopology.SimplicialSpace.FullEEquivalenceTrivialFibration
import MathlibExt.AlgebraicTopology.SimplicialSpace.FullEEquivalenceEvaluation
import MathlibExt.AlgebraicTopology.SimplicialSpace.FiniteCompletenessComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalSpaces
import MathlibExt.AlgebraicTopology.SimplicialSpace.WeakEquivalences

/-!
# The original finite/full completeness comparison

The finite central edge maps to the backward edge of the full walking
isomorphism. Both actual evaluations are trivial Kan fibrations at every
Reedy-fibrant Segal target, so the original restriction is weak. The exact
collapse and zero-section equations then compare the original locality tests
and their complete all-target weak classes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SimplicialSpace.Inner SSet.modelCategoryQuillen

namespace SimplicialSpace.FiniteCompletenessHorel

open FiniteCompletenessMapping SSet.Rezk.FiniteCompleteness

/-- Evaluation on the original backward E10 edge has the actual scalar trivial-fibration class. -/
theorem backwardEvaluation_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    trivialFibrations SSet.{u}
      (FullEEquivalence.evaluation W hW
        (SSet.yonedaEquiv.symm SSet.coherentIso.inv.edge)) := by
  have : IsIso (FullEEquivalence.involution.{u}) :=
    ⟨⟨FullEEquivalence.involution, FullEEquivalence.involution_comp_self,
      FullEEquivalence.involution_comp_self⟩⟩
  have : IsIso ((discreteSourceMapping W).map FullEEquivalence.involution.op) :=
    inferInstance
  have h := ((trivialFibrations SSet.{u}).cancel_left_of_respectsIso
    ((discreteSourceMapping W).map FullEEquivalence.involution.op)
    (FullEEquivalence.evaluation W hW SSet.coherentIso.forwardMap)).mpr
      (FullEEquivalence.forwardEvaluation_trivialFibration W hW)
  simpa only [FullEEquivalence.evaluation_precompose,
    FullEEquivalence.forwardMap_involution] using h

/-- The original finite restriction followed by central evaluation is the backward full-E factor. -/
@[reassoc]
theorem comparison_centralEvaluation (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    restriction W comparison ≫ centralEvaluation W hW =
      FullEEquivalence.evaluation W hW
        (SSet.yonedaEquiv.symm SSet.coherentIso.inv.edge) := by
  have hraw : restriction W comparison ≫ toCentral W =
      (discreteSourceMapping W).map FullEEquivalence.involution.op ≫
        EquivalenceMapping.edgeEvaluation W SSet.coherentIso.forwardMap := by
    rw [toCentral_restriction]
    exact FullEEquivalence.centralMap_evaluation W
  apply (cancel_mono (SegalHomotopy.equivalenceSubcomplex W hW).ι).mp
  change restriction W comparison ≫ toCentral W =
    EquivalenceMapping.edgeEvaluation W
      (SSet.yonedaEquiv.symm SSet.coherentIso.inv.edge)
  rw [hraw]
  rw [← FullEEquivalence.forwardMap_involution]
  exact EquivalenceMapping.edgeEvaluation_source W FullEEquivalence.involution
    SSet.coherentIso.forwardMap

/-- Both endpoints of the same original Map(j) are Kan, constructed from Reedy fibrancy. -/
theorem comparisonEndpoints_kanComplex (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.KanComplex (rawMapping W SSet.Rezk.walkingIsomorphism) ∧
      SSet.KanComplex (mapping W) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  exact ⟨ReedyModel.innerHom_kanComplex
      (ofSimplicialObject.obj SSet.Rezk.walkingIsomorphism) W
      (ReedyModel.isCofibrant _) hW.1,
    (mappingEndpoints_kanComplex W hW).1⟩

/-- The literal Map(j) is realization weak at every original Reedy-fibrant Segal target. -/
theorem comparison_realizationWeak (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.realizationWeakEquivalences (restriction W comparison) :=
  SSet.realizationWeakEquivalences.of_postcomp
    (restriction W comparison) (centralEvaluation W hW)
    (evaluation_realizationWeak W hW).1
    (by rw [comparison_centralEvaluation]; exact (backwardEvaluation_trivialFibration W hW).2)

/-- Native Kan weakness of the same original restriction retains every pointed homotopy map. -/
theorem comparison_W (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.KanComplex.W (restriction W comparison) := by
  let _ : SSet.KanComplex (rawMapping W SSet.Rezk.walkingIsomorphism) :=
    (comparisonEndpoints_kanComplex W hW).1
  let _ : SSet.KanComplex (mapping W) := (comparisonEndpoints_kanComplex W hW).2
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mpr
    (comparison_realizationWeak W hW)

/-- Every original represented parameter is evaluated after the same literal raw comparison. -/
@[reassoc]
theorem comparison_evaluation (W : SimplicialSpace.{u}) (n : ℕ)
    (γ : SSet.Rezk.representable n ⟶ K) :
    restriction W comparison ≫ restriction W γ ≫ (representableMappingIso W n).hom =
      restriction W (γ ≫ comparison) ≫ (representableMappingIso W n).hom := by
  rw [restriction_comp]
  exact (Category.assoc _ _ _).symm

/-- All original inner operators commute with the same comparison restriction. -/
theorem comparison_operator (W : SimplicialSpace.{u})
    {m n : SimplexCategoryᵒᵖ} (θ : m ⟶ n) :
    (rawMapping W SSet.Rezk.walkingIsomorphism).map θ ≫
      (restriction W comparison).app n =
        (restriction W comparison).app m ≫ (mapping W).map θ :=
  (restriction W comparison).naturality θ

/-- The whole original comparison square is natural in every actual target map. -/
@[reassoc]
theorem comparison_naturality_target {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    (rawMappingNat f).app (op SSet.Rezk.walkingIsomorphism) ≫ restriction V comparison =
      restriction W comparison ≫ mappingMap f :=
  restriction_naturality f comparison

/-- The original collapse and comparison reverse to the exact epsilon/j/kappa equation. -/
@[reassoc]
theorem restriction_epsilon_comparison (W : SimplicialSpace.{u}) :
    restriction W epsilon ≫ restriction W comparison = restriction W kappa := by
  rw [← restriction_comp, comparison_epsilon]

/-- The original selected-zero map is a strict section after the same full collapse. -/
@[reassoc]
theorem restriction_epsilon_section (W : SimplicialSpace.{u}) :
    restriction W epsilon ≫ restriction W SSet.Rezk.completenessMap =
      𝟙 (rawMapping W (SSet.Rezk.representable 0)) := by
  rw [← restriction_comp, completenessMap_epsilon]
  exact (mappingFunctor W).map_id _

/-- The finite constant map is the original kappa restriction after degree-zero Yoneda. -/
def finiteConstantMap (W : SimplicialSpace.{u}) : W.diagram _⦋0⦌ ⟶ mapping W :=
  (representableMappingIso W 0).inv ≫ restriction W kappa

/-- The full constant map followed by the same Map(j) is precisely the finite constant map. -/
@[reassoc]
theorem constantMap_comparison (W : SimplicialSpace.{u}) :
    FullEEquivalence.constantMap W ≫ restriction W comparison = finiteConstantMap W := by
  change ((representableMappingIso W 0).inv ≫ restriction W epsilon) ≫
    restriction W comparison = _
  rw [Category.assoc, restriction_epsilon_comparison]
  rfl

/-- Every original point of K evaluates its constant map to the actual identity on W zero. -/
@[reassoc]
theorem finiteConstantMap_point (W : SimplicialSpace.{u})
    (γ : SSet.Rezk.representable 0 ⟶ K) :
    finiteConstantMap W ≫ restriction W γ ≫ (representableMappingIso W 0).hom =
      𝟙 (W.diagram _⦋0⦌) := by
  have hγ : γ ≫ kappa = 𝟙 (SSet.Rezk.representable.{u} 0) := by
    ext m n q
    apply ULift.ext
    exact (SimplexCategory.eq_const_to_zero _).trans
      (SimplexCategory.eq_const_to_zero _).symm
  rw [finiteConstantMap, Category.assoc,
    ← Category.assoc (restriction W kappa) (restriction W γ), ← restriction_comp, hγ]
  change (representableMappingIso W 0).inv ≫
      (mappingFunctor W).map (𝟙 _) ≫ (representableMappingIso W 0).hom = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

/-- Every original inner operator retains the finite constant map. -/
theorem finiteConstantMap_operator (W : SimplicialSpace.{u})
    {m n : SimplexCategoryᵒᵖ} (θ : m ⟶ n) :
    (W.diagram _⦋0⦌).map θ ≫ (finiteConstantMap W).app n =
      (finiteConstantMap W).app m ≫ (mapping W).map θ :=
  (finiteConstantMap W).naturality θ

/-- The same original finite constant map is natural in every target morphism. -/
@[reassoc]
theorem finiteConstantMap_naturality_target {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    f.hom.app (op ⦋0⦌) ≫ finiteConstantMap V = finiteConstantMap W ≫ mappingMap f := by
  have h : f.hom.app (op ⦋0⦌) ≫ (representableMappingIso V 0).inv =
      (representableMappingIso W 0).inv ≫
        (rawMappingNat f).app (op (SSet.Rezk.representable 0)) := by
    apply (cancel_mono (representableMappingIso V 0).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      representableMappingIso_target, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [finiteConstantMap, ← Category.assoc, h, Category.assoc,
    restriction_naturality, ← Category.assoc]
  rfl

/-- Central evaluation of the actual finite constant map is the original intrinsic identity. -/
@[reassoc]
theorem finiteConstantMap_centralEvaluation (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    finiteConstantMap W ≫ centralEvaluation W hW = SegalHomotopy.equivalenceIdentity W hW := by
  have h := congrArg (fun f : W.diagram _⦋0⦌ ⟶ mapping W =>
    f ≫ centralEvaluation W hW) (constantMap_comparison W)
  change FullEEquivalence.constantMap W ≫
    (restriction W comparison ≫ centralEvaluation W hW) =
      finiteConstantMap W ≫ centralEvaluation W hW at h
  have h₂ := congrArg
    (fun f : rawMapping W SSet.Rezk.walkingIsomorphism ⟶
      (SegalHomotopy.equivalenceSubcomplex W hW : SSet.{u}) =>
        FullEEquivalence.constantMap W ≫ f)
    (comparison_centralEvaluation W hW)
  exact h.symm.trans (h₂.trans (FullEEquivalence.constant_evaluation W hW _))

/-- The original kappa and epsilon weak tests agree at every Segal target. -/
theorem kappa_iff_epsilon (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.realizationWeakEquivalences (restriction W kappa) ↔
      SSet.realizationWeakEquivalences (restriction W epsilon) := by
  rw [← restriction_epsilon_comparison]
  exact SSet.realizationWeakEquivalences.postcomp_iff _ _ (comparison_realizationWeak W hW)

/-- The original epsilon and selected-zero section weak tests agree, with both split equations. -/
theorem epsilon_iff_section (W : SimplicialSpace.{u}) :
    SSet.realizationWeakEquivalences (restriction W epsilon) ↔
      SSet.realizationWeakEquivalences (restriction W SSet.Rezk.completenessMap) := by
  have h : SSet.realizationWeakEquivalences
      (restriction W epsilon ≫ restriction W SSet.Rezk.completenessMap) := by
    rw [restriction_epsilon_section]
    exact SSet.realizationWeakEquivalences.id_mem _
  exact ⟨fun hε => SSet.realizationWeakEquivalences.of_precomp _ _ hε h,
    fun hσ => SSet.realizationWeakEquivalences.of_postcomp _ _ hσ h⟩

/-- Kappa tests the same original selected-zero completeness condition at Segal targets. -/
theorem kappa_iff_section (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.realizationWeakEquivalences (restriction W kappa) ↔
      SSet.realizationWeakEquivalences (restriction W SSet.Rezk.completenessMap) :=
  (kappa_iff_epsilon W hW).trans (epsilon_iff_section W)

/-- Degree-zero Yoneda retains the exact original epsilon weak test. -/
theorem constantMap_iff_epsilon (W : SimplicialSpace.{u}) :
    SSet.realizationWeakEquivalences (FullEEquivalence.constantMap W) ↔
      SSet.realizationWeakEquivalences (restriction W epsilon) := by
  change SSet.realizationWeakEquivalences
      ((representableMappingIso W 0).inv ≫ restriction W epsilon) ↔ _
  exact SSet.realizationWeakEquivalences.cancel_left_of_respectsIso _ _

/-- Degree-zero Yoneda retains the exact original kappa weak test. -/
theorem finiteConstantMap_iff_kappa (W : SimplicialSpace.{u}) :
    SSet.realizationWeakEquivalences (finiteConstantMap W) ↔
      SSet.realizationWeakEquivalences (restriction W kappa) :=
  SSet.realizationWeakEquivalences.cancel_left_of_respectsIso _ _

/-- The original zero-point evaluation retains the selected-zero section weak test. -/
theorem pointEvaluation_iff_section (W : SimplicialSpace.{u}) :
    SSet.realizationWeakEquivalences (FullEEquivalence.pointEvaluation W SSet.coherentIso.x₀) ↔
      SSet.realizationWeakEquivalences (restriction W SSet.Rezk.completenessMap) := by
  change SSet.realizationWeakEquivalences
      (restriction W SSet.Rezk.completenessMap ≫ (representableMappingIso W 0).hom) ↔ _
  exact SSet.realizationWeakEquivalences.cancel_right_of_respectsIso _ _

/-- Actual forward evaluation compares the intrinsic identity test to the full constant-map test. -/
theorem identity_iff_constantMap (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.realizationWeakEquivalences (SegalHomotopy.equivalenceIdentity W hW) ↔
      SSet.realizationWeakEquivalences (FullEEquivalence.constantMap W) := by
  have h : SSet.realizationWeakEquivalences
      (FullEEquivalence.evaluation W hW SSet.coherentIso.forwardMap) :=
    (FullEEquivalence.forwardEvaluation_trivialFibration W hW).2
  simpa only [FullEEquivalence.constant_evaluation] using
    SSet.realizationWeakEquivalences.postcomp_iff (FullEEquivalence.constantMap W)
      (FullEEquivalence.evaluation W hW SSet.coherentIso.forwardMap)
      h

/-- Every original finite/full/selected-section/intrinsic-identity completeness test agrees. -/
theorem completeness_tests_iff (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (SSet.realizationWeakEquivalences (restriction W kappa) ↔
      SSet.realizationWeakEquivalences (restriction W epsilon)) ∧
    (SSet.realizationWeakEquivalences (restriction W kappa) ↔
      SSet.realizationWeakEquivalences (restriction W SSet.Rezk.completenessMap)) ∧
    (SSet.realizationWeakEquivalences (restriction W kappa) ↔
      SSet.realizationWeakEquivalences (FullEEquivalence.constantMap W)) ∧
    (SSet.realizationWeakEquivalences (restriction W kappa) ↔
      SSet.realizationWeakEquivalences (SegalHomotopy.equivalenceIdentity W hW)) :=
  ⟨kappa_iff_epsilon W hW, kappa_iff_section W hW,
    (kappa_iff_epsilon W hW).trans (constantMap_iff_epsilon W).symm,
    ((kappa_iff_epsilon W hW).trans (constantMap_iff_epsilon W).symm).trans
      (identity_iff_constantMap W hW).symm⟩

/-- The original finite completeness predicate uses every Segal spine and the literal kappa map. -/
def finiteCompleteSegalSpaces : ObjectProperty SimplicialSpace.{u} :=
  fun W => segalSpaces W ∧ SSet.realizationWeakEquivalences (restriction W kappa)

/-- The full original CSS family and the finite predicate define exactly the same target class. -/
theorem completeSegalSpaces_iff_finiteComplete (W : SimplicialSpace.{u}) :
    completeSegalSpaces W ↔ finiteCompleteSegalSpaces W := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  constructor
  · rintro ⟨hRF, hlocal⟩
    have hW : segalSpaces W := ⟨hRF, fun n hn => hlocal (.inl ⟨n, hn⟩)⟩
    exact ⟨hW, (kappa_iff_section W hW).mpr (hlocal (.inr PUnit.unit))⟩
  · rintro ⟨hW, hκ⟩
    refine ⟨hW.1, ?_⟩
    rintro (n | x)
    · exact hW.2 n.1 n.2
    · exact (kappa_iff_section W hW).mp hκ

/-- Test the same original inner precomposition at every finite-complete Segal target. -/
def finiteWeakEquivalences : MorphismProperty SimplicialSpace.{u} :=
  fun {X Y} (f : X ⟶ Y) => ∀ W : SimplicialSpace.{u}, finiteCompleteSegalSpaces W →
    SSet.realizationWeakEquivalences ((innerHomFunctor.map f.op).app W)

/-- Both original all-target weak definitions agree on every original arrow without extra
hypotheses. -/
theorem finiteWeakEquivalences_eq_rezkWeakEquivalences :
    finiteWeakEquivalences.{u} = rezkWeakEquivalences.{u} := by
  funext X Y f
  apply propext
  exact ⟨fun h W hW => h W ((completeSegalSpaces_iff_finiteComplete W).mp hW),
    fun h W hW => h W ((completeSegalSpaces_iff_finiteComplete W).mpr hW)⟩

end SimplicialSpace.FiniteCompletenessHorel
