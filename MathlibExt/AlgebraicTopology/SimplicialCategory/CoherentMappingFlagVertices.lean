/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightMappingSimplex

/-!
# Original finite flag vertices in coherent mapping simplices

The degreewise flag evaluation of a supplied original enriched simplex
uses its literal original interval paths. Each front vertex is read at
the same whole path, with both individual object equalities retained.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.MappingFlagVertices
open SimplicialEnrichment HomFlagEvaluation PathMaximumFlags PathLastMaximum RightMappingSimplex
variable {C : Carrier.{u}} {n : ℕ} (x y : C)

/-- The actual standard-simplex vertex of the supplied original front label. -/
def standardVertex (k : Fin (n + 1)) : (Δ[n] : SSet.{u}) _⦋0⦌ :=
  SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋n⦌ k)

/-- The whole flag map sends the supplied front vertex to its literal original interval flag. -/
theorem flag_vertex (k : Fin (n + 1)) :
    (flagMap.{u} (n := n)).app (op ⦋0⦌) (standardVertex k) = ComposableArrows.mk₀ (flag.{u} k) :=
  ComposableArrows.ext₀ rfl

/-- A supplied actual enriched simplex is evaluated at the same literal original flag and exact original
  object equalities. -/
theorem evaluate_vertex (σ : coherentSimplex.{u} ⦋n + 1⦌ ⟶ C)
    (hx : σ.obj (.mk (ULift.up (0 : Fin (n + 2)))) = x)
    (hy : σ.obj (.mk (ULift.up (Fin.last (n + 1)))) = y) (k : Fin (n + 1)) :
    (evaluate x y σ hx hy).app (op ⦋0⦌) (standardVertex k) =
      (EqualityTransport.hom hx hy).app (op ⦋0⦌)
        ((σ.map (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1))))).app (op ⦋0⦌)
          (ComposableArrows.mk₀ (flag.{u} k))) := by
  have h := flag_vertex.{u} k
  exact congrArg (fun p => (EqualityTransport.hom hx hy).app (op ⦋0⦌)
    ((σ.map (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1))))).app (op ⦋0⦌) p)) h

/-- The actual flag evaluation of a supplied right-mapping simplex, retaining the original individual source
  and target. -/
def readSimplex (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
    (HomSimplexEndpoints.vertex y)) _⦋n⦌) :
    (x ⟶[SSet.{u}] y) _⦋n⦌ :=
  SSet.yonedaEquiv (evaluate x y (toEnriched x y σ) (front_obj x y σ 0) (last_obj x y σ))

/-- The degreewise flag readback retains the same entire original Hom cell of the genuine comparison. -/
theorem readSimplex_map (τ : (x ⟶[SSet.{u}] y) _⦋n⦌) :
    readSimplex x y ((HomMapping.map x y).app (op ⦋n⦌) τ) = τ := by
  have hS : toEnriched x y ((HomMapping.map x y).app (op ⦋n⦌) τ) =
      HomSimplex.simplex x y (SSet.yonedaEquiv.symm τ) :=
    (congrArg (fun f => SSet.yonedaEquiv f) (HomMapping.map_readback x y τ)).trans
      (SSet.yonedaEquiv.apply_symm_apply _)
  let A : HomMappingCells.FixedSimplex x y (n := n) :=
    ⟨toEnriched x y ((HomMapping.map x y).app (op ⦋n⦌) τ), front_obj x y _ 0, last_obj x y _⟩
  have hA : A = HomMappingCells.construct x y τ := Subtype.ext hS
  have hR := congrArg (fun s => SSet.yonedaEquiv (HomMappingCells.read x y s)) hA
  exact hR.trans ((congrArg (fun f => SSet.yonedaEquiv f) (HomMappingCells.read_construct x y τ)).trans
    (SSet.yonedaEquiv.apply_symm_apply τ))

end CategoryTheory.CoherentRealization.MappingFlagVertices
