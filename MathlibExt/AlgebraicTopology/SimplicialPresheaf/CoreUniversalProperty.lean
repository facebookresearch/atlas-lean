/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.CoreDerivedAdjunction
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalDerivedComponents
import MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices

/-!
# The actual maps of the original-local core universal property

The natural weak cospan already compares the original derived mapping spaces
with every fixed scalar replacement convention. Its localized isomorphism
keeps those two maps. The actual zero projection sends a represented derived
map to the transferred representative of its ordinary evaluation adjunct.
The existing derived-component interpretation and Quillen Hom functions
identify the same adjunct in the original homotopy categories.

The total derived functors are constructed by the existing Quillen theorem.
Their comparison maps identify the groupoidal source and the zero core on
genuinely original-local-fibrant targets. No mapping-space universal property
or replacement comparison is supplied as a premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
  HomotopicalAlgebra MonoidalClosed Opposite
open SimplicialPresheaf.InjectiveKan SimplicialPresheaf.OriginalLocalDerived
open scoped MonoidalClosed Simplicial SSet.modelCategoryQuillen

namespace SimplicialPresheaf.CoreUniversalProperty

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]

/-- The actual end projection evaluates the same original map at the chosen site object. -/
theorem vertex_projection (A Z : SimplicialPresheaf.{u} D) (f : A ⟶ Z) (a : Dᵒᵖ) :
    (innerHomπ A Z a).app (op ⦋0⦌) (innerHomHomEquiv A Z f) =
      SSet.ihomVertexEquiv (A.obj a) (Z.obj a) (f.app a) := by
  let _ : MonoidalClosed SSet.{u} := FunctorToTypes.monoidalClosed
  let _ : EnrichedCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedCategorySelf SSet.{u}
  let _ : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
  let _ : Enriched.FunctorCategory.HasEnrichedHom SSet.{u} A Z :=
    SimplicialPresheaf.hasEnd (Enriched.FunctorCategory.diagram SSet.{u} A Z)
  have hp : Enriched.FunctorCategory.homEquiv (V := SSet.{u}) f ≫ innerHomπ A Z a =
      curry' (f.app a) :=
    Enriched.FunctorCategory.homEquiv_apply_π (V := SSet.{u}) f a
  exact congrArg (SSet.unitHomEquiv _) hp

variable {I : Type i} [Small.{u} I]

/-- The natural localized comparison has exactly the original weak-cospan triangle. -/
theorem mappingIso_triangle (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    (CoreUniversalMapping.mappingIso S hz e).hom ≫
        CoreUniversalMapping.scalarHoToCommon S z e =
      CoreUniversalMapping.originalHoToCommon S z e := by
  let _ : IsIso (CoreUniversalMapping.originalHoToCommon S z e) :=
    CoreUniversalMapping.originalHoToCommon_isIso S hz e
  let _ : IsIso (CoreUniversalMapping.scalarHoToCommon S z e) :=
    CoreUniversalMapping.scalarHoToCommon_isIso S hz e
  change (_ ≫ (asIso (CoreUniversalMapping.scalarHoToCommon S z e)).inv) ≫
      (asIso (CoreUniversalMapping.scalarHoToCommon S z e)).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Changing a fixed scalar convention preserves the same original universal mapping comparison. -/
theorem changeScalarConventions_triangle (S : I → Arrow (SimplicialPresheaf.{u} D))
    {z : D} (hz : IsTerminal z) (e e' : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    CoreUniversalMapping.mappingIso S hz e ≪≫
        CoreUniversalMapping.changeScalarConventions S hz e e' =
      CoreUniversalMapping.mappingIso S hz e' := by
  apply Iso.ext
  change (CoreUniversalMapping.mappingIso S hz e).hom ≫
      ((CoreUniversalMapping.mappingIso S hz e).inv ≫
        (CoreUniversalMapping.mappingIso S hz e').hom) = _
  exact Iso.hom_inv_id_assoc _ _

/-- A strict original map has its actual same-Q/same-R derived vertex. -/
def derivedPoint (S : I → Arrow (SimplicialPresheaf.{u} D)) (K : SSet.{u})
    (C : SimplicialPresheaf.{u} D)
    (f : (BaselineConstantCoreComparison.constantReplacement (D := D)).obj K ⟶ C) :
    (innerHom
      ((localQ S).obj ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K))
      ((localR S).obj C)).obj (op ⦋0⦌) :=
  innerHomHomEquiv _ _
    ((localQCounit S).app ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K) ≫
      f ≫ (localRUnit S).app C)

/-- The actual universal projection produces the transferred representative of the zero adjunct. -/
theorem comparison_derivedPoint (S : I → Arrow (SimplicialPresheaf.{u} D))
    (z : D) (K : SSet.{u}) (C : SimplicialPresheaf.{u} D)
    (f : (BaselineConstantCoreComparison.constantReplacement (D := D)).obj K ⟶ C) :
    (BaselineConstantCoreComparison.comparison S z K C).app (op ⦋0⦌)
        (derivedPoint S K C f) =
      SSet.ihomVertexEquiv ((TransferredCoreReplacements.qReplacement S z).obj K)
        ((TransferredCoreReplacements.rReplacement S z).obj C)
        ((TransferredCoreReplacements.qCounit S z).app K ≫
          ((BaselineConstantCoreComparison.unit (D := D)).app K).app (op z) ≫
          f.app (op z) ≫ (TransferredCoreReplacements.rUnit S z).app C) := by
  let η := (BaselineConstantCoreComparison.unit (D := D)).app K
  let G := (BaselineConstantCoreComparison.constantReplacement (D := D)).obj K
  let r := (localRUnit S).app C
  have hn : (localQ S).map η ≫ (localQCounit S).app G =
      (localQCounit S).app (ConstantEvaluation.constant.obj K) ≫ η :=
    (localQCounit S).naturality η
  have hc : (localQ S).map η ≫ ((localQCounit S).app G ≫ f ≫ r) =
      (localQCounit S).app (ConstantEvaluation.constant.obj K) ≫ η ≫ f ≫ r :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun h => h ≫ (f ≫ r)) hn).trans (Category.assoc _ _ _))
  change (innerHomπ ((localQ S).obj (ConstantEvaluation.constant.obj K))
      ((localR S).obj C) (op z)).app (op ⦋0⦌)
    ((innerHomPre ((localQ S).map η) ((localR S).obj C)).app (op ⦋0⦌)
      (innerHomHomEquiv ((localQ S).obj G) ((localR S).obj C)
        ((localQCounit S).app G ≫ f ≫ r))) = _
  rw [innerHomHomEquiv_precomp, hc, vertex_projection]
  rfl

/-- The actual derived vertex represents precisely the localized original strict map. -/
theorem derivedPoint_ho (S : I → Arrow (SimplicialPresheaf.{u} D))
    (K : SSet.{u}) (C : SimplicialPresheaf.{u} D)
    (f : (BaselineConstantCoreComparison.constantReplacement (D := D)).obj K ⟶ C) :
    let _ : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
    OriginalLocalDerivedComponents.localDerivedComponentHoEquiv S
        ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K) C
        (SSet.π₀.mk (derivedPoint S K C f)) =
      (CoreDerivedAdjunction.localHo S).map f := by
  let d := originalLocalSmithData S
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := d.model
  let H := (weakEquivalences (SimplicialPresheaf.{u} D)).Q
  let G := (BaselineConstantCoreComparison.constantReplacement (D := D)).obj K
  let q := (localQCounit S).app G
  let r := (localRUnit S).app C
  have hq : weakEquivalences (SimplicialPresheaf.{u} D) q := by
    change d.model.categoryWithWeakEquivalences.weakEquivalences q
    rw [d.weakEquivalences_eq]
    exact weakEquivalences_le_originalLocalEquivalences S q
      (localQCounit_baseTrivialFibration S G).2
  have hr : weakEquivalences (SimplicialPresheaf.{u} D) r := by
    change d.model.categoryWithWeakEquivalences.weakEquivalences r
    rw [d.weakEquivalences_eq]
    exact (localRUnit_localTrivialCofibration S C).2
  let _ : IsIso (H.map q) := Localization.inverts H _ q hq
  let _ : IsIso (H.map r) := Localization.inverts H _ r hr
  change OriginalLocalDerivedComponents.localDerivedComponentHoEquiv S G C
      (SSet.π₀.mk (innerHomHomEquiv _ _ (q ≫ f ≫ r))) = H.map f
  apply (cancel_epi (H.map q)).mp
  apply (cancel_mono (H.map r)).mp
  exact (Category.assoc _ _ _).trans
    ((OriginalLocalDerivedComponents.localDerivedComponentHoEquiv_mk S G C
      (q ≫ f ≫ r)).trans
      ((H.map_comp q (f ≫ r)).trans
        ((congrArg (fun h => H.map q ≫ h) (H.map_comp f r)).trans
          (Category.assoc _ _ _).symm)))

/-- The Ho function of the projected derived vertex is the same ordinary zero adjunct. -/
theorem derivedPoint_adjunct (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (K : SSet.{u}) (C : SimplicialPresheaf.{u} D)
    (hC : isOriginalLocalFibrant S C)
    (f : (BaselineConstantCoreComparison.constantReplacement (D := D)).obj K ⟶ C) :
    let _ : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
    CoreDerivedAdjunction.homEquiv S hz K C hC
      (OriginalLocalDerivedComponents.localDerivedComponentHoEquiv S
        ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K) C
        (SSet.π₀.mk (derivedPoint S K C f))) =
      CoreDerivedAdjunction.scalarHo.map
        (((BaselineConstantCoreComparison.unit (D := D)).app K).app (op z) ≫ f.app (op z)) := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
  exact (congrArg (CoreDerivedAdjunction.homEquiv S hz K C hC)
    (derivedPoint_ho S K C f)).trans (CoreDerivedAdjunction.homEquiv_map S hz K C hC f)

/-- The original zero core computes the total right derived functor on actual local-fibrant targets. -/
theorem rightComparison_isIso (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (C : SimplicialPresheaf.{u} D) (hC : isOriginalLocalFibrant S C) :
    let _ : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
    IsIso ((CoreDerivedAdjunction.derivedAdjunctionData S hz).rightComparison.app C) := by
  let d := originalLocalSmithData S
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := d.model
  let _ : (ConstantEvaluation.adjunction hz).IsQuillenAdjunction :=
    ConstantEvaluation.isQuillenAdjunction S hz
  let _ : IsFibrant C := (d.isFibrant_iff C).mpr hC
  let V := (weakEquivalences SSet.{u}).Q
  let Φ := FibrantObject.localizerMorphism (SimplicialPresheaf.{u} D)
  have hR : Φ.Derives (ConstantEvaluation.evaluation z ⋙ V) := by
    intro X Y f hf
    let _ : WeakEquivalence f.hom := by
      rw [← weakEquivalence_iff_of_objectProperty, weakEquivalence_iff]
      exact hf
    let _ : WeakEquivalence ((ConstantEvaluation.evaluation z).map f.hom) :=
      Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
        (adj := ConstantEvaluation.adjunction hz) f.hom
    change IsIso (V.map ((ConstantEvaluation.evaluation z).map f.hom))
    exact Localization.inverts V (weakEquivalences SSet.{u}) _
      ((weakEquivalence_iff _).mp inferInstance)
  let a := CoreDerivedAdjunction.derivedAdjunctionData S hz
  let _ : a.rightDerived.IsRightDerivedFunctor a.rightComparison
      (weakEquivalences (SimplicialPresheaf.{u} D)) := a.rightIsDerived
  exact hR.isIso_of_isRightDerivedFunctor a.rightComparison (FibrantObject.mk C)

/-- The original constant source computes the total left derived functor for every scalar. -/
theorem leftComparison_isIso (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (K : SSet.{u}) :
    let _ : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
    IsIso ((CoreDerivedAdjunction.derivedAdjunctionData S hz).leftComparison.app K) := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
  let _ : (ConstantEvaluation.adjunction hz).IsQuillenAdjunction :=
    ConstantEvaluation.isQuillenAdjunction S hz
  let H := (weakEquivalences (SimplicialPresheaf.{u} D)).Q
  let Φ := CofibrantObject.localizerMorphism SSet.{u}
  have hL : Φ.Derives (ConstantEvaluation.constant (D := D) ⋙ H) := by
    intro X Y f hf
    let _ : WeakEquivalence f.hom := by
      rw [← weakEquivalence_iff_of_objectProperty, weakEquivalence_iff]
      exact hf
    let _ : WeakEquivalence (ConstantEvaluation.constant.map f.hom) :=
      Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
        (adj := ConstantEvaluation.adjunction hz) f.hom
    change IsIso (H.map (ConstantEvaluation.constant.map f.hom))
    exact Localization.inverts H (weakEquivalences (SimplicialPresheaf.{u} D)) _
      ((weakEquivalence_iff _).mp inferInstance)
  let a := CoreDerivedAdjunction.derivedAdjunctionData S hz
  let _ : a.leftDerived.IsLeftDerivedFunctor a.leftComparison
      (weakEquivalences SSet.{u}) := a.leftIsDerived
  exact hL.isIso' a.leftComparison (CofibrantObject.mk K)

end SimplicialPresheaf.CoreUniversalProperty
