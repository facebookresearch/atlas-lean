/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ScalarKanClosedEmbedding
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationK
import MathlibExt.CategoryTheory.Enriched.PointwiseSizeInstances
import MathlibExt.Topology.Category.PointedCGWH.ClosedEmbeddingInstances

/-!
# Closed original native cell histories and their original source Hom

Pointwise closedness is stable under the actual coproduct, pushout and whole
continuous ordinal colimit diagrams, because the original evaluations create
those colimits. The original free-I source Hom is transported through its exact
free/evaluation adjunction and actual finite boundary carrier bound. The full K
source theorem remains at the original realized-generator cardinal and bottom.
-/

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v uD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra Topology
open scoped CGWH.modelCategory Cardinal

namespace HomotopicalAlgebra.EnrichedProjective.Native.ClosedSourceHom

open ScalarKanClosedEmbedding

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf

local instance pointedColimits : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := by
  let : HasColimitsOfSize.{v, v} CGWH.{u, v} := CGWH.instHasColimitsOfSize
  change HasColimitsOfSize.{v, v} (Under CGWH.point.{u, v})
  infer_instance

variable {D : Type uD} [EnrichedCategory PointedCGWH.{u, v} D]

private abbrev baseClosed : MorphismProperty PointedCGWH.{u, v} :=
  TopCat.closedEmbeddings.inverseImage (PointedCGWH.pointedToCGWH ⋙ CGWH.cgwhToTop)

instance evaluatedClosed_cobase (d : D) : (evaluatedClosed d).IsStableUnderCobaseChange where
  of_isPushout sq hf := (baseClosed.{u, v}).of_isPushout
    (sq.map (evaluation (V := PointedCGWH.{u, v}) d)) hf

instance evaluatedClosed_coproducts (d : D) : (evaluatedClosed d).IsStableUnderCoproducts.{v} where
  isStableUnderCoproductsOfShape T :=
    { condition := by
        intro F G cF cG hF hG a ha b hb
        let E := evaluation (V := PointedCGWH.{u, v}) d
        change baseClosed (E.map b)
        apply (inferInstance : baseClosed.IsStableUnderColimitsOfShape (Discrete T)).condition
          (F ⋙ E) (G ⋙ E) (E.mapCocone cF) (E.mapCocone cG)
          (isColimitOfPreserves E hF) (isColimitOfPreserves E hG) (Functor.whiskerRight a E)
          (fun t => ha t) (E.map b)
        intro t
        change E.map (cF.ι.app t) ≫ E.map b = E.map (a.app t) ≫ E.map (cG.ι.app t)
        rw [← E.map_comp, ← E.map_comp]
        exact E.congr_map (hb t) }

instance evaluatedClosed_transfinite (d : D) :
    (evaluatedClosed d).IsStableUnderTransfiniteComposition.{v} where
  isStableUnderTransfiniteCompositionOfShape T :=
    { le := by
        intro X Y f hf
        obtain ⟨c⟩ := hf
        let E := evaluation (V := PointedCGWH.{u, v}) d
        let : PreservesWellOrderContinuousOfShape T E :=
          { preservesColimitsOfShape := fun _ _ => by infer_instance }
        let t : (baseClosed.inverseImage E).TransfiniteCompositionOfShape T f := c
        let mapped : baseClosed.TransfiniteCompositionOfShape T (E.map f) := t.map
        exact baseClosed.transfiniteCompositionsOfShape_le T _ mapped.mem }

/-- The source class retains closedness at every original native evaluation. -/
def pointwiseClosed : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} D) :=
  fun _ _ f => ∀ d : D, evaluatedClosed d f

/-- Every member of the source class has the literal original component closed embedding. -/
theorem pointwiseClosed_iff {X Y : EnrichedFunctorCat PointedCGWH.{u, v} D} (f : X ⟶ Y) :
    pointwiseClosed f ↔ ∀ d : D, IsClosedEmbedding (ConcreteCategory.hom (component f d).right) := by
  exact forall_congr' (fun d => evaluatedClosed_iff f d)

instance pointwiseClosed_respectsIso : (pointwiseClosed (D := D)).RespectsIso := by
  apply RespectsIso.of_respects_arrow_iso
  intro a b e ha d
  exact evaluatedClosed_ofArrowIso e.symm d (ha d)

instance pointwiseClosed_cobase : (pointwiseClosed (D := D)).IsStableUnderCobaseChange where
  of_isPushout sq hf d := (evaluatedClosed d).of_isPushout sq (hf d)

instance pointwiseClosed_coproducts : (pointwiseClosed (D := D)).IsStableUnderCoproducts.{v} where
  isStableUnderCoproductsOfShape T :=
    { condition := by
        intro F G cF cG hF hG a ha b hb d
        exact (inferInstance : (evaluatedClosed d).IsStableUnderColimitsOfShape (Discrete T)).condition
          F G cF cG hF hG a (fun t => ha t d) b hb }

instance pointwiseClosed_transfinite : (pointwiseClosed (D := D)).IsStableUnderTransfiniteComposition.{v} where
  isStableUnderTransfiniteCompositionOfShape T :=
    { le := by
        intro X Y f hf d
        obtain ⟨c⟩ := hf
        exact (evaluatedClosed d).transfiniteCompositionsOfShape_le T _
          (c.ofLE (fun _ _ _ hf => hf d)).mem }

section OriginalSources

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

omit B in
/-- The actual original pointed boundary source retains its finite realization carrier bound. -/
theorem originalBoundarySource_mk_le {K L : PointedCGWH.{u, v}} (i : K ⟶ L)
    (hi : PointedCGWH.realizedBoundaryInclusions i) : #↥K.right ≤ Cardinal.continuum := by
  change (CGWH.realizedBoundaryInclusions.{u, v}.strictMap (Under.costar CGWH.point)) i at hi
  cases hi with
  | @map A B f hf =>
    unfold CGWH.realizedBoundaryInclusions at hf
    obtain ⟨n⟩ := hf
    exact OperatorStabilizationK.NativeK.finiteCostarOfFinite_mk_le (SSet.boundary.{v} n)

/-- Every actual original free-I source preserves the given whole closed chain at the same original rank. -/
theorem originalISource_preservesClosedColimit
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hf : OperatorStabilizationK.NativeK.levelI (I := I) f)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I)
    [E.IsWellOrderContinuous]
    (hE : ∀ {a b : realizedGeneratorCardinal.{v}.ord.ToType} (φ : a ⟶ b), pointwiseClosed (E.map φ)) :
    PreservesColimit E (coyoneda.obj (Opposite.op X)) := by
  let U : I → PointedCGWH.{u, v} ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I := fun a => Free.functor a
  obtain ⟨q, hq⟩ := (MorphismProperty.adjointFamilyGenerators_iff U
    PointedCGWH.realizedBoundaryInclusions f).mp hf
  let : PreservesColimit E (coyoneda.obj (Opposite.op (Free.object q.1 q.2.1.left))) :=
    PointedCGWH.EnrichedSource.free_preservesClosedColimit q.1 q.2.1.left
      (originalBoundarySource_mk_le q.2.1.hom q.2.2) E
      (fun a _ _ φ => (evaluatedClosed_iff _ a).mp (hE φ a))
  let e : X ≅ Free.object q.1 q.2.1.left := Arrow.leftFunc.mapIso (eqToIso hq)
  exact preservesColimit_of_natIso E (coyoneda.mapIso e.op)

/-- Every member of the full original K bank retains source Hom on the same original closed chain. -/
theorem originalJSource_preservesClosedColimit {L : Type}
    (s : OperatorStabilizationK.NativeStabilizationFamily.{u, v} I L)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hf : OperatorStabilizationK.NativeK.generators s f)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I)
    [E.IsWellOrderContinuous]
    (hE : ∀ {a b : realizedGeneratorCardinal.{v}.ord.ToType} (φ : a ⟶ b), pointwiseClosed (E.map φ)) :
    PreservesColimit E (coyoneda.obj (Opposite.op X)) :=
  OperatorStabilizationK.NativeK.generatorsSource_preservesClosedColimit s f hf E
    (fun a _ _ φ => (evaluatedClosed_iff _ a).mp (hE φ a))

end OriginalSources

end HomotopicalAlgebra.EnrichedProjective.Native.ClosedSourceHom
