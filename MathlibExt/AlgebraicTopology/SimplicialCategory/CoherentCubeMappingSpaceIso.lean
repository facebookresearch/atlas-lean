/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCubeMappingNaturality
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFrameHom

/-!
# Genuine whole original mapping-space and cube Hom-complex isomorphism

Actual cube evaluation and construction form a whole simplicial
isomorphism, retaining every original scalar cell and individual fixed
endpoint. Under this isomorphism the original Hom comparison is exactly
the genuine maximum-induced frame comparison. No Kan or weak outcome
is assumed for these constructions or readbacks.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.CubeMappingSpace
open SimplicialEnrichment

/-- The genuine whole maximum-induced original scalar frame comparison. -/
def comparison (H : SSet.{u}) : H ⟶ FrameHom.complex RightCubeCosimplicial.diagram H :=
  (FrameHom.standardIso H).inv ≫ (FrameHom.functor H).map (NatTrans.op RightCubeMaximumNaturality.map)

/-- The actual original comparison reads each individual scalar simplex as the same whole
  maximum-precomposed original map. -/
theorem comparison_app (H : SSet.{u}) (n : ℕ) (a : H _⦋n⦌) :
    (comparison H).app (op ⦋n⦌) a = RightCubeMaximum.map n ≫ SSet.yonedaEquiv.symm a := rfl

variable {C : Carrier.{u}} (x y : C)

/-- The actual whole right-mapping-space isomorphism with the genuine original cube-to-Hom complex, with
  both simplicial inverses proved. -/
def iso : SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
    (HomSimplexEndpoints.vertex y) ≅
    FrameHom.complex RightCubeCosimplicial.diagram (x ⟶[SSet.{u}] y) :=
  NatIso.ofComponents (fun q => (CubeMappingEquivalence.equiv (n := q.unop.len) x y).toIso) (fun θ => by
    ext σ
    exact (CubeMappingNaturality.evaluate_naturality x y θ.unop σ).symm)

/-- The actual whole forward isomorphism is the original cube evaluation of the same supplied mapping simplex. -/
theorem iso_hom_app {n : ℕ}
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋n⦌) :
    (iso x y).hom.app (op ⦋n⦌) σ = FixedFrontMappingEvaluation.evaluate x y σ := rfl

/-- The actual whole inverse isomorphism constructs the same original cube Hom map at its given individual endpoints. -/
theorem iso_inv_app {n : ℕ} (f : RightCubeRelations.object.{u} n ⟶ (x ⟶[SSet.{u}] y)) :
    (iso x y).inv.app (op ⦋n⦌) f = CubeHomFamily.construct x y f := rfl

/-- Under the proved whole isomorphism, the original actual Hom-to-right-mapping comparison is exactly the
  genuine maximum-induced scalar comparison. -/
theorem original_comparison : HomMapping.map x y ≫ (iso x y).hom = comparison (x ⟶[SSet.{u}] y) := by
  ext q a
  induction q using Opposite.rec with
  | _ q =>
    induction q using SimplexCategory.rec with
    | _ n => exact FixedFrontMappingEvaluation.evaluate_constructed x y (SSet.yonedaEquiv.symm a)

end CategoryTheory.CoherentRealization.CubeMappingSpace
