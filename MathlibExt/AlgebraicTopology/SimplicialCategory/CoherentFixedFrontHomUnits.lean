/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontInsertion
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentIntervalFaceCover
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomRetargetAlgebra
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomUnitsAndEmpty
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedEqualityTransport

/-!
# Actual unit Hom maps of the fixed-front realization

The entire original front of the distinguished simplex is constant. The
genuine outside-face Hom isomorphism therefore identifies every front
interval map with the structural source identity. The last diagonal is
the target identity by the original enriched functor law.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedFrontHomUnits
open SimplicialEnrichment FixedFrontCollapse FixedFrontInsertion HornHomFaces

/-- The genuine original coherent front inclusion. -/
abbrev front (n : ℕ) := coherentSimplexMap (SimplexCategory.δ (Fin.last (n + 1)))

/-- The front operator retains the literal original cast-successor vertex. -/
theorem front_vertex (n : ℕ) (i : Fin (n + 1)) :
    (front.{u} n).obj (SimplicialThickening.mk (ULift.up i)) =
      SimplicialThickening.mk (ULift.up i.castSucc) := by
  exact congrArg (fun j => SimplicialThickening.mk (ULift.up.{u} j)) (Fin.succAbove_last_apply i)

/-- Each genuine original coherent front Hom map is an isomorphism, including residual
height zero. -/
theorem front_isIso (n : ℕ) (i j : Fin (n + 1)) :
    IsIso ((front.{u} n).map (SimplicialThickening.mk (ULift.up i))
      (SimplicialThickening.mk (ULift.up j))) := by
  have h : (OrdinalFace.embedding (Fin.last (n + 1))) (ULift.up.{u} j) <
      ULift.up (Fin.last (n + 1)) := by
    change (Fin.last (n + 1)).succAbove j < Fin.last (n + 1)
    exact (Fin.succAbove_last_apply j) ▸ Fin.castSucc_lt_last j
  exact (IntervalFaceCover.outsideIso_operator (Fin.last (n + 1)) (ULift.up i) (ULift.up j)
    (Or.inr h)) ▸ (IntervalFaceCover.outsideIso (Fin.last (n + 1)) (ULift.up i) (ULift.up
      j) (Or.inr h)).isIso_hom

/-- Every whole original front interval map into realization is the actual structural source
identity after
  its exact endpoint transports. -/
theorem front_hom (n : ℕ) (i j : Fin (n + 1)) :
    retargetMap (functor.{u} n) (SimplicialThickening.mk (ULift.up i.castSucc))
      (SimplicialThickening.mk (ULift.up j.castSucc)) (front_obj n i) (front_obj n j) =
      toUnit _ ≫ eId SSet.{u} (C := realization (FixedFrontCollapse.object n)) (source n) := by
  let a : coherentSimplex.{u} ⦋n⦌ := SimplicialThickening.mk (ULift.up i)
  let b : coherentSimplex.{u} ⦋n⦌ := SimplicialThickening.mk (ULift.up j)
  let f : (a ⟶[SSet.{u}] b) ⟶
      (SimplicialThickening.mk (ULift.up.{u} i.castSucc) ⟶[SSet.{u}]
        SimplicialThickening.mk (ULift.up.{u} j.castSucc)) :=
    (front n).map a b ≫ eqToHom (congrArg₂
      (fun a b : coherentSimplex.{u} ⦋n + 1⦌ => a ⟶[SSet.{u}] b)
      (front_vertex n i) (front_vertex n j))
  let : IsIso ((front n).map a b) := front_isIso n i j
  let : IsIso f := IsIso.comp_isIso' (front_isIso n i j)
    (eqToIso (congrArg₂
      (fun a b : coherentSimplex.{u} ⦋n + 1⦌ => a ⟶[SSet.{u}] b)
      (front_vertex n i) (front_vertex n j))).isIso_hom
  apply (cancel_epi f).1
  have hr := HomRetargetAlgebra.restriction_reindex (front.{u} n) (functor n) a b
    (front_vertex n i) (front_vertex n j) (front_obj n i) (front_obj n j)
  have he := retargetMap_eq (front_functor.{u} n) a b
    ((congrArg (functor n).obj (front_vertex n i)).trans (front_obj n i))
    ((congrArg (functor n).obj (front_vertex n j)).trans (front_obj n j)) rfl rfl
  exact (Category.assoc ((front n).map a b) (eqToHom (congrArg₂
    (fun a b : coherentSimplex.{u} ⦋n + 1⦌ => a ⟶[SSet.{u}] b)
    (front_vertex n i) (front_vertex n j))) _).trans
    (hr.trans (he.trans (by ext q p; rfl)))

/-- The actual last diagonal Hom map is the structural target identity on every whole scalar
simplex. -/
theorem last_hom (n : ℕ) :
    retargetMap (functor.{u} n) (SimplicialThickening.mk (ULift.up (Fin.last (n + 1))))
      (SimplicialThickening.mk (ULift.up (Fin.last (n + 1)))) (last_obj n) (last_obj n) =
      toUnit _ ≫ eId SSet.{u} (C := realization (FixedFrontCollapse.object n)) (target n) := by
  let a : coherentSimplex.{u} ⦋n + 1⦌ := SimplicialThickening.mk (ULift.up (Fin.last (n + 1)))
  let : IsIso (eId SSet.{u} a) := HomUnitsAndEmpty.unit_isIso a.as
  apply (cancel_epi (eId SSet.{u} a)).1
  have h := EqualityTransport.identity_retarget (C := realization (FixedFrontCollapse.object n))
    a (last_obj n) ((functor n).map a a) ((functor n).map_id a)
  exact h.trans (by ext q p; rfl)

end CategoryTheory.CoherentRealization.FixedFrontHomUnits
