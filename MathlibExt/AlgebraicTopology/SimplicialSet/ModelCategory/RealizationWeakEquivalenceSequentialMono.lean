/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence

import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWColimits
import
 MathlibExt.Topology.Category.TopCat.Colimits.TopCatSingularClosedSequentialPreserves
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyTransfiniteClosed
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Subcomplex

/-!
# Realization weak equivalences on sequential mono diagrams

A componentwise realization weak equivalence between two `ℕ`-indexed
diagrams induces a realization weak equivalence on their colimit objects when
every transition in both diagrams is a simplicial monomorphism.

Geometric realization preserves the two colimits because it is a left
adjoint.  The realized transition maps are closed T1 embeddings, so the
singular functor preserves these particular sequential colimits.  The result
then follows from filtered-colimit stability of `SSet.KanComplex.W`.

This is deliberately restricted to sequential mono diagrams.  It installs no
arbitrary filtered-colimit instance and makes no model-category or
left-properness claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MorphismProperty

universe v u

namespace SSet

/-- A componentwise realization weak equivalence between sequential mono
diagrams induces a realization weak equivalence on any compatible map between
their colimit objects. -/
theorem realizationWeakEquivalences.of_isColimit_nat_mono
    {F G : ℕ ⥤ SSet.{u}} (alpha : F ⟶ G)
    {cF : Cocone F} {cG : Cocone G}
    (hcF : IsColimit cF) (hcG : IsColimit cG)
    (phi : cF.pt ⟶ cG.pt)
    (hphi : ∀ n, cF.ι.app n ≫ phi = alpha.app n ≫ cG.ι.app n)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), Mono (F.map f))
    (hG : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), Mono (G.map f))
    (hAlpha : ∀ n, realizationWeakEquivalences (alpha.app n)) :
    realizationWeakEquivalences phi := by
  let R : SSet.{u} ⥤ SSet.{u} := SSet.toTop.{u} ⋙ TopCat.toSSet.{u}
  have hFclosed : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings ((F ⋙ SSet.toTop).map f) := by
    intro i j f
    change TopCat.closedT1Embeddings (SSet.toTop.map (F.map f))
    exact @SSet.closedT1Embeddings_toTop_map_of_mono
      (F.obj i) (F.obj j) (F.map f) (hF f)
  have hGclosed : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      TopCat.closedT1Embeddings ((G ⋙ SSet.toTop).map f) := by
    intro i j f
    change TopCat.closedT1Embeddings (SSet.toTop.map (G.map f))
    exact @SSet.closedT1Embeddings_toTop_map_of_mono
      (G.obj i) (G.obj j) (G.map f) (hG f)
  let _ : PreservesColimit (F ⋙ SSet.toTop) TopCat.toSSet :=
    TopCat.preservesColimit_toSSet_of_closedT1 hFclosed
  let _ : PreservesColimit (G ⋙ SSet.toTop) TopCat.toSSet :=
    TopCat.preservesColimit_toSSet_of_closedT1 hGclosed
  have hcFR : IsColimit (R.mapCocone cF) :=
    isColimitOfPreserves R hcF
  have hcGR : IsColimit (R.mapCocone cG) :=
    isColimitOfPreserves R hcG
  let alphaR : F ⋙ R ⟶ G ⋙ R := Functor.whiskerRight alpha R
  have hAlphaR : SSet.KanComplex.W.functorCategory ℕ alphaR := by
    intro n
    have hn := hAlpha n
    change SSet.KanComplex.W
      (TopCat.toSSet.map (SSet.toTop.map (alpha.app n))) at hn
    simpa only [alphaR, R, Functor.comp_map,
      Functor.whiskerRight_app] using hn
  have hphiR : ∀ n,
      (R.mapCocone cF).ι.app n ≫ R.map phi =
        alphaR.app n ≫ (R.mapCocone cG).ι.app n := by
    intro n
    change R.map (cF.ι.app n) ≫ R.map phi =
      R.map (alpha.app n) ≫ R.map (cG.ι.app n)
    rw [← R.map_comp, ← R.map_comp, hphi n]
  have hW : SSet.KanComplex.W (R.map phi) :=
    MorphismProperty.IsStableUnderColimitsOfShape.condition
      (W := SSet.KanComplex.W) (F ⋙ R) (G ⋙ R)
      (R.mapCocone cF) (R.mapCocone cG) hcFR hcGR alphaR hAlphaR
      (R.map phi) hphiR
  exact hW

/-- A transfinite composite of realization weak equivalences that are simplicial
monomorphisms is a realization weak equivalence. -/
theorem realizationWeakEquivalences.of_transfiniteComposition_mono
    {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : (realizationWeakEquivalences.{u} ⊓
      MorphismProperty.monomorphisms SSet.{u}).TransfiniteCompositionOfShape J f)
    [(SSet.KanComplex.W : MorphismProperty SSet.{u}).IsStableUnderTransfiniteCompositionOfShape J] :
    realizationWeakEquivalences f := by
  let _ : PreservesColimits SSet.toTop.{u} :=
    _root_.sSetTopAdj.leftAdjoint_preservesColimits
  let _ : PreservesWellOrderContinuousOfShape J SSet.toTop.{u} :=
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  have hf' :
      ((TopCat.weakHomotopyEquivalences.{u} ⊓
        TopCat.closedT1Embeddings.{u}).inverseImage SSet.toTop.{u}).TransfiniteCompositionOfShape
          J f :=
    hf.ofLE (by
      intro A B g hg
      exact ⟨hg.1, @SSet.closedT1Embeddings_toTop_map_of_mono A B g hg.2⟩)
  have hTop : (TopCat.weakHomotopyEquivalences.{u} ⊓
      TopCat.closedT1Embeddings.{u}).TransfiniteCompositionOfShape J
      (SSet.toTop.map f) := hf'.map
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map f)
  exact TopCat.weakHomotopyEquivalences.of_transfiniteComposition_closedT1 hTop

end SSet

end
