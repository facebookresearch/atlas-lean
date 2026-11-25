/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingZeroUnit
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Original maximally marked simplicial sets over the point

The original simplicial set is maximally marked and mapped to the same
original point. The original maps form a genuine functor into that marked
slice. Both original ordered-interval endpoints and their original
projection retain their literal maps and strict unit equations.
-/

noncomputable section
universe u
open CategoryTheory Limits
open scoped Simplicial

namespace SSet.Marked

/-- The original maximal marking and unique original point map form the actual marked slice functor. -/
def maximalPointFunctor : SSet.{u} ⥤ Over (max (Δ[0] : SSet.{u})) where
  obj K := Over.mk (toMax (X := max K) (SSet.stdSimplex.isTerminalObj₀.from K))
  map {K K'} f := Over.homMk (maximal.map f) (Hom.ext (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _))
  map_id K := by apply Over.OverMorphism.ext; exact CategoryTheory.Functor.map_id maximal K
  map_comp f g := by apply Over.OverMorphism.ext; exact CategoryTheory.Functor.map_comp maximal f g

/-- Each original ordered-interval endpoint is its actual maximally marked map over the original point. -/
def pointEndpoint (ε : Fin 2) : maximalPointFunctor.{u}.obj (Δ[0] : SSet.{u}) ⟶
    maximalPointFunctor.{u}.obj (Δ[1] : SSet.{u}) := maximalPointFunctor.map (SSet.stdSimplex.δ ε)

/-- The same whole original interval projection is the map back to the original point. -/
def pointIntervalProjection : maximalPointFunctor.{u}.obj (Δ[1] : SSet.{u}) ⟶
    maximalPointFunctor.{u}.obj (Δ[0] : SSet.{u}) := maximalPointFunctor.map (SSet.stdSimplex.σ (0 : Fin 1))

/-- Both original endpoints retain their strict original projection unit. -/
theorem pointEndpoint_projection (ε : Fin 2) : pointEndpoint.{u} ε ≫ pointIntervalProjection = 𝟙 _ := by
  change maximalPointFunctor.map (SSet.stdSimplex.δ ε) ≫ maximalPointFunctor.map (SSet.stdSimplex.σ (0 : Fin 1)) = _
  rw [← CategoryTheory.Functor.map_comp]
  have h : SSet.stdSimplex.δ ε ≫ SSet.stdSimplex.σ (0 : Fin 1) = 𝟙 (Δ[0] : SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h, CategoryTheory.Functor.map_id]

end SSet.Marked
