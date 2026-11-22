/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootBoundaryChartInverse
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeProperPositiveOperators
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeProperBoundaryFacePostSection

/-!
# Exact original coface coefficient readbacks of the whole native inverse

The actual proper coface operator reads the same full enriched inverse
section with original coherent base transport. Its original root
coefficient is the genuine marked lower coordinate map; every positive
coefficient retains the whole original positive section. These exact
original units recover the full coface source section coefficient maps.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The entire original proper coface operator reads the genuine full enriched inverse section and its unchanged
coherent base transport. -/
def nativeRootBoundaryInverseCofaceSection (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    coneDiagram n ⟶
      (enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ k).op σ)))).obj
        (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))) :=
  (coneProperBoundaryOperator (coneCofaceEmbedding k).toOrderHom (coneCofaceEmbedding_not_surjective k) ≫
    (enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap (coneCofaceEmbedding k).toOrderHom))).map
      (nativeRootBoundaryInverseSection B n σ)) ≫
      (eqToHom (nativeChartBase_restriction_comp B (SimplexCategory.δ k) σ)).app
        (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)))

/-- The genuine full native chart inverse followed by each original coface map has exactly its original whole
supported coface section and coherent base transport. -/
theorem nativeRootBoundaryInverseCofaceSection_homEquiv (B : SSet.{u}) (n : ℕ)
    (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    EnrichedLeftKan.universalHomEquiv
      (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ k).op σ))) (coneDiagram n)
      (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)))
      (nativeRootBoundaryCofaceMap B n σ k ≫ nativeRootBoundaryChartInverse B n σ) =
        nativeRootBoundaryInverseCofaceSection B n σ k := by
  let f := (coneCofaceEmbedding.{u} k).toOrderHom
  let r := enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap f))
  let a := coneProperBoundaryOperator f (coneCofaceEmbedding_not_surjective k)
  let t := (eqToHom (nativeChartBase_restriction_comp B (SimplexCategory.δ k) σ)).app
    (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)))
  exact (nativeProperBoundaryFace_post_section B (SimplexCategory.δ k) σ (coneCofaceEmbedding_not_surjective k)
    (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))) (nativeRootBoundaryChartInverse B n σ)).trans
      (congrArg (fun q => (a ≫ r.map q) ≫ t) (nativeRootBoundaryChartInverse_homEquiv B n σ))

/-- At the unchanged original root, every positive omitted coface reads precisely its same genuine native
lower-coface unit under the full inverse section. -/
theorem nativeRootBoundaryInverseCofaceSection_root (B : SSet.{u}) (n : ℕ)
    (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) (hk : 0 < k) :
    (nativeRootBoundaryInverseCofaceSection B n σ k).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} n))) =
      nativeLowerCofaceRootSection B σ k := by
  let S := nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))
  let a := nativeRootBoundaryInverseSection B n σ
  let γ := nativeRootBoundaryCoordinateInverse B n σ
  let h := coneCofaceEmbedding_root.{u} k hk
  let v := coneCofaceEmbedding k (⊥ : Vertex.{u} n)
  let x := op (SimplicialThickening.mk (⊥ : Vertex.{u} n))
  let p := coneProperBoundaryImage (coneCofaceEmbedding k).toOrderHom (coneCofaceEmbedding_not_surjective k) (⊥ :
    Vertex.{u} n)
  let t := ((eqToHom (nativeChartBase_restriction_comp B (SimplexCategory.δ k) σ)).app S).app x
  let s := eqToHom (nativeLowerCofaceRootTarget B σ k hk S)
  let w := eqToHom (congrArg (fun y : Vertex.{u} (n + 1) => S.obj
    ((EnrichedFunctor.opposite (simplexInto B σ)).obj (op (SimplicialThickening.mk y)))) h)
  let r := eqToHom (congrArg (fun y : Vertex.{u} (n + 1) => coneRootBoundaryMarked y) h)
  let u := fun y : Vertex.{u} (n + 1) => a.app (op (SimplicialThickening.mk y))
  let e := coneLowerRootFaceIso.{u} k hk
  let g := coneLowerRootFaceToBoundary.{u} k hk
  let c := nativeLowerCofaceRootSection B σ k
  have ht : t ≫ s = w := nativeLowerRootUnitTransport B σ k hk S
  have hu : u v ≫ w = r ≫ u (⊥ : Vertex.{u} (n + 1)) := eqToHom_naturality u h
  have hp : p ≫ r = e.hom ≫ g := (coneLowerRootFaceIso_boundary k hk).symm
  have hg : g ≫ γ = nativeLowerRootBoundaryInverse B σ k hk :=
    nativeRootBoundaryCoordinateInverse_leg B n σ (coneRootLowerIndex n k hk)
  have hc : e.hom ≫ nativeLowerRootBoundaryInverse B σ k hk = c ≫ s := nativeLowerRootBoundaryInverse_coface B σ k hk
  apply (cancel_mono s).mp
  have h₁ : (((p ≫ u v) ≫ t) ≫ s) = (p ≫ r) ≫ u (⊥ : Vertex.{u} (n + 1)) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun q => (p ≫ u v) ≫ q) ht).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun q => p ≫ q) hu).trans (Category.assoc _ _ _).symm)))
  have h₂ : (p ≫ r) ≫ u (⊥ : Vertex.{u} (n + 1)) = (e.hom ≫ g) ≫ γ :=
    (congrArg (fun q => q ≫ u (⊥ : Vertex.{u} (n + 1))) hp).trans
      (congrArg (fun q => (e.hom ≫ g) ≫ q) (nativeRootBoundaryInverseSection_root B n σ))
  have h₃ : (e.hom ≫ g) ≫ γ = c ≫ s :=
    (Category.assoc _ _ _).trans ((congrArg (fun q => e.hom ≫ q) hg).trans hc)
  exact h₁.trans (h₂.trans h₃)

/-- Every original positive coefficient of every original positive omitted coface retains the same full marked
source unit under the genuine whole inverse section. -/
theorem nativeRootBoundaryInverseCofaceSection_positive (B : SSet.{u}) (n : ℕ)
    (σ : B _⦋n + 2⦌) (k : Fin (n + 3)) (hk : 0 < k) (i : (Index.{u} (n + 1))ᵒᵖ)
    (hi : (⊥ : Vertex.{u} (n + 1)) < i.unop.as) :
    (nativeRootBoundaryInverseCofaceSection B (n + 1) σ k).app i =
      (EnrichedLeftKan.universalHomEquiv
        (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ k).op σ))) (coneDiagram (n + 1))
        (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2))) (nativeBoundaryCofaceChartMap B (n + 1) σ k)).app i := by
  let S := nativeSubcomplexChart B (n + 2) σ (boundary (n + 2))
  let a := nativeRootBoundaryInverseSection B (n + 1) σ
  let P := nativePositiveRootBoundarySection B σ
  let U := EnrichedLeftKan.universalHomEquiv
    (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ k).op σ))) (coneDiagram (n + 1)) S
      (nativeBoundaryCofaceChartMap B (n + 1) σ k)
  let v := coneCofaceEmbedding k i.unop.as
  let x := op (SimplicialThickening.mk v)
  let p := coneProperBoundaryImage (coneCofaceEmbedding k).toOrderHom (coneCofaceEmbedding_not_surjective k) i.unop.as
  let b := coneAfterCofaceCoefficient.{u} k hk i.unop.as
  let c := coneRootBoundaryAfterInclusion v
  let z := coneAfterInclusion i.unop.as (⊥ : Vertex.{u} (n + 1))
  let t := ((eqToHom (nativeChartBase_restriction_comp B (SimplexCategory.δ k) σ)).app S).app i
  have hz : (coneAfterAboveIso hi).hom = z := coneAfterAboveIso_hom hi
  have : IsIso z := hz ▸ (coneAfterAboveIso hi).isIso_hom
  have hp : z ≫ p = b ≫ c :=
    congrArg (fun q => q.app i) (coneProperBoundaryOperator_positive k hk)
  have hf : c ≫ a.app x = P.app x :=
    congrArg (fun q => q.app x) (nativeRootBoundaryInverseSection_positive B (n + 1) σ)
  have hu : (b ≫ P.app x) ≫ t = z ≫ U.app i :=
    congrArg (fun q => q.app i) (nativeCofacePositiveBoundaryOperator_unit B n σ k hk)
  apply (cancel_epi z).mp
  have h₁ : z ≫ ((p ≫ a.app x) ≫ t) = ((z ≫ p) ≫ a.app x) ≫ t :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ t) (Category.assoc _ _ _).symm)
  have h₂ : ((z ≫ p) ≫ a.app x) ≫ t = ((b ≫ c) ≫ a.app x) ≫ t :=
    congrArg (fun q => (q ≫ a.app x) ≫ t) hp
  have h₃ : ((b ≫ c) ≫ a.app x) ≫ t = (b ≫ P.app x) ≫ t :=
    (congrArg (fun q => q ≫ t) (Category.assoc _ _ _)).trans (congrArg (fun q => (b ≫ q) ≫ t) hf)
  exact h₁.trans (h₂.trans (h₃.trans hu))

end SSet.Marked
