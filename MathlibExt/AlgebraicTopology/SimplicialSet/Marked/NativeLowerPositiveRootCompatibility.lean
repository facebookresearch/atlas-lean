/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfterRootCoface
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeCofacePositiveBoundaryOperator
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeLowerLowerRootInverseGluing

/-!
# Genuine original lower and positive root inverse compatibility

The whole original positive-coface enriched equation retains its
original root unit and coherent base transport. Thus each complete
positive root cone inside an original lower face has the same actual
native source inverse as its original positive coface image. This is
an equality of entire marked root coefficient maps in the true source.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The unchanged lower inverse and genuine positive inverse agree on the entire original positive root cone inside
every original positive omitted coface, retaining the original full marked coface image and original root/base
transports. -/
theorem nativeLowerPositiveRootInverse_condition (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌)
    (k : Fin (n + 3)) (hk : 0 < k) :
    (coneAfterInclusion (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1)) ≫
      (coneLowerRootFaceIso k hk).hom) ≫ nativeLowerRootBoundaryInverse B σ k hk =
      coneAfterRootCofaceImage k hk ≫
        (nativePositiveRootBoundarySection B σ).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 2)))) := by
  let S := nativeSubcomplexChart B (n + 2) σ (boundary (n + 2))
  let P := nativePositiveRootBoundarySection B σ
  let x := op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))
  let h := coneCofaceEmbedding_root.{u} k hk
  let v := coneCofaceEmbedding k (⊥ : Vertex.{u} (n + 1))
  let a := coneAfterCofaceCoefficient.{u} k hk (⊥ : Vertex.{u} (n + 1))
  let b := coneAfterInclusion (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1))
  let c := nativeLowerCofaceRootSection B σ k
  let t := ((eqToHom (nativeChartBase_restriction_comp B (SimplexCategory.δ k) σ)).app S).app x
  let s := eqToHom (nativeLowerCofaceRootTarget B σ k hk S)
  let z := eqToHom (congrArg (fun y : Vertex.{u} (n + 2) => S.obj
    ((EnrichedFunctor.opposite (simplexInto B σ)).obj (op (SimplicialThickening.mk y)))) h)
  let r := eqToHom (congrArg (fun y : Vertex.{u} (n + 2) => coneAfterWeight y (⊥ : Vertex.{u} (n + 2))) h)
  let u := fun y : Vertex.{u} (n + 2) => P.app (op (SimplicialThickening.mk y))
  have ht : t ≫ s = z := nativeLowerRootUnitTransport B σ k hk S
  have hp : u v ≫ z = r ≫ u (⊥ : Vertex.{u} (n + 2)) := eqToHom_naturality u h
  have hw : (a ≫ u v) ≫ t = b ≫ c :=
    congrArg (fun f => f.app x) (nativeCofacePositiveBoundaryOperator_unit B n σ k hk)
  have hroot : (b ≫ c) ≫ s = (a ≫ r) ≫ u (⊥ : Vertex.{u} (n + 2)) :=
    (congrArg (fun f => f ≫ s) hw.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => (a ≫ u v) ≫ f) ht).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun f => a ≫ f) hp).trans (Category.assoc _ _ _).symm))))
  have hc : (coneLowerRootFaceIso k hk).hom ≫ nativeLowerRootBoundaryInverse B σ k hk = c ≫ s :=
    nativeLowerRootBoundaryInverse_coface B σ k hk
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => b ≫ f) hc).trans ((Category.assoc _ _ _).symm.trans hroot))

end SSet.Marked
