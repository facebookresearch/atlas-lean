/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfterCofaceOperator
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfterPositiveHomDetection
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeCofacePositiveUnitTransport

/-!
# Whole original positive coface sections in the actual native source

The genuine whole positive-cone coface operator retains all original
path and scalar maps. Its actual boundary section agrees with the
unchanged native coface unit on every full positive coefficient, with
exact original base and vertex transports. The original tail left-Kan
comparison detects the whole marked enriched map, including the root.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The whole original positive-cone coface operator reads exactly the unchanged original coface native boundary
section through the same actual entire positive boundary inverse, including all original root/path/scalar
coefficients and genuine coherent base transport. -/
theorem nativeCofacePositiveBoundaryOperator_unit (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌)
    (k : Fin (n + 3)) (hk : 0 < k) :
    (coneAfterCofaceOperator k hk ≫
      (enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap (coneCofaceEmbedding k).toOrderHom))).map
        (nativePositiveRootBoundarySection B σ)) ≫
      (eqToHom (nativeChartBase_restriction_comp B (SimplexCategory.δ k) σ)).app
        (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2))) =
      coneAfterDiagramInclusion (⊥ : Vertex.{u} (n + 1)) ≫
        EnrichedLeftKan.universalHomEquiv
          (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ k).op σ)))
          (coneDiagram (n + 1)) (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2)))
          (nativeBoundaryCofaceChartMap B (n + 1) σ k) := by
  let S := nativeSubcomplexChart B (n + 2) σ (boundary (n + 2))
  let P := nativePositiveRootBoundarySection B σ
  let U := EnrichedLeftKan.universalHomEquiv
    (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ k).op σ)))
    (coneDiagram (n + 1)) S (nativeBoundaryCofaceChartMap B (n + 1) σ k)
  apply coneAfterDiagram_hom_ext_positive n
  intro i
  let ti := coneTailEmbedding n i
  let v := coneCofaceEmbedding k ti
  let w := coneTailEmbedding (n + 1) (coneCofaceEmbedding (k.pred (ne_of_gt hk)) i)
  let x := op (SimplicialThickening.mk ti)
  let a := coneAfterCofaceCoefficient.{u} k hk ti
  let b := coneAfterInclusion ti (⊥ : Vertex.{u} (n + 1))
  let c := U.app x
  let p := P.app (op (SimplicialThickening.mk v))
  let q := P.app (op (SimplicialThickening.mk w))
  let t := ((eqToHom (nativeChartBase_restriction_comp B (SimplexCategory.δ k) σ)).app S).app x
  let s := eqToHom (nativeCofacePositiveTarget B n σ k hk i)
  let hr := (coneTailCofaceVertex.{u} k hk i).symm
  let r := eqToHom (congrArg (fun z : Vertex.{u} (n + 2) => coneAfterWeight z (⊥ : Vertex.{u} (n + 2))) hr)
  let z := eqToHom (congrArg (fun y : Vertex.{u} (n + 2) => S.obj
    ((EnrichedFunctor.opposite (simplexInto B σ)).obj (op (SimplicialThickening.mk y)))) hr)
  let Φ := coneCofacePositiveCoefficient k hk i
  have ht : t ≫ s = z := nativeCofacePositiveUnitTransport B n σ k hk i
  have hp : p ≫ z = r ≫ q :=
    eqToHom_naturality (fun y : Vertex.{u} (n + 2) => P.app (op (SimplicialThickening.mk y))) hr
  have ha : a ≫ r = b ≫ Φ := coneAfterCofaceCoefficient_tail k hk i
  have hc : c ≫ s = Φ ≫ q := nativeCofacePositiveBoundarySection_unit B n σ k hk i
  change (a ≫ p) ≫ t = b ≫ c
  apply (cancel_mono s).mp
  have h₁ : ((a ≫ p) ≫ t) ≫ s = (a ≫ p) ≫ z :=
    (Category.assoc _ _ _).trans (congrArg (fun y => (a ≫ p) ≫ y) ht)
  have h₂ : (a ≫ p) ≫ z = (b ≫ Φ) ≫ q :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun y => a ≫ y) hp).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun y => y ≫ q) ha)))
  have h₃ : (b ≫ Φ) ≫ q = (b ≫ c) ≫ s :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun y => b ≫ y) hc.symm).trans (Category.assoc _ _ _).symm)
  exact h₁.trans (h₂.trans h₃)

end SSet.Marked
