/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftPointedSimplex

/-!
# Both original pointed relation directions under universe lift

The same full original relation simplex lifts and lowers by the actual
scalar Hom dictionary. Every distinguished face and all other original
constant faces are retained at independent coefficient universes.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

/-- The same full original pointed relation simplex lifts,
retaining every original face equation. -/
def uliftPointedRelStruct {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
    {p q : X.PtSimplex n x} {i : Fin (n + 1)} (h : PtSimplex.RelStruct p q i) :
    PtSimplex.RelStruct (uliftPointedSimplexEquiv.{u,v} X n x p)
      (uliftPointedSimplexEquiv.{u,v} X n x q) i where
  map := uliftStandardHomEquiv.{u,v} X ⦋n + 1⦌ h.map
  δ_castSucc_map := (uliftStandardHomEquiv_precomp.{u,v} X _ h.map).symm.trans
    (congrArg (uliftStandardHomEquiv.{u,v} X ⦋n⦌) h.δ_castSucc_map)
  δ_succ_map := (uliftStandardHomEquiv_precomp.{u,v} X _ h.map).symm.trans
    (congrArg (uliftStandardHomEquiv.{u,v} X ⦋n⦌) h.δ_succ_map)
  δ_map_of_lt j hj := (uliftStandardHomEquiv_precomp.{u,v} X _ h.map).symm.trans
    ((congrArg (uliftStandardHomEquiv.{u,v} X ⦋n⦌) (h.δ_map_of_lt j hj)).trans
      (uliftStandardHomEquiv_const.{u,v} X n x))
  δ_map_of_gt j hj := (uliftStandardHomEquiv_precomp.{u,v} X _ h.map).symm.trans
    ((congrArg (uliftStandardHomEquiv.{u,v} X ⦋n⦌) (h.δ_map_of_gt j hj)).trans
      (uliftStandardHomEquiv_const.{u,v} X n x))

/-- Both full original pointed relation maps preserve exactly the original relation's existence. -/
theorem uliftPointedRelStruct_nonempty_iff {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
    (p q : X.PtSimplex n x) (i : Fin (n + 1)) :
    Nonempty (PtSimplex.RelStruct (uliftPointedSimplexEquiv.{u,v} X n x p)
      (uliftPointedSimplexEquiv.{u,v} X n x q) i) ↔ Nonempty (PtSimplex.RelStruct p q i) := by
  constructor
  · rintro ⟨h⟩
    refine ⟨{ map := (uliftStandardHomEquiv.{u,v} X ⦋n + 1⦌).symm h.map
              δ_castSucc_map := ?_
              δ_succ_map := ?_
              δ_map_of_lt := ?_
              δ_map_of_gt := ?_ }⟩
    · apply (uliftStandardHomEquiv.{u,v} X ⦋n⦌).injective
      exact (uliftStandardHomEquiv_precomp.{u,v} X (SimplexCategory.δ i.castSucc) _).trans
        ((congrArg (fun f => SSet.stdSimplex.δ i.castSucc ≫ f)
          (Equiv.apply_symm_apply (uliftStandardHomEquiv.{u,v} X ⦋n + 1⦌) h.map)).trans
            h.δ_castSucc_map)
    · apply (uliftStandardHomEquiv.{u,v} X ⦋n⦌).injective
      exact (uliftStandardHomEquiv_precomp.{u,v} X (SimplexCategory.δ i.succ) _).trans
        ((congrArg (fun f => SSet.stdSimplex.δ i.succ ≫ f)
          (Equiv.apply_symm_apply (uliftStandardHomEquiv.{u,v} X ⦋n + 1⦌) h.map)).trans
            h.δ_succ_map)
    · intro j hj
      apply (uliftStandardHomEquiv.{u,v} X ⦋n⦌).injective
      exact (uliftStandardHomEquiv_precomp.{u,v} X (SimplexCategory.δ j) _).trans
        ((congrArg (fun f => SSet.stdSimplex.δ j ≫ f)
          (Equiv.apply_symm_apply (uliftStandardHomEquiv.{u,v} X ⦋n + 1⦌) h.map)).trans
            ((h.δ_map_of_lt j hj).trans (uliftStandardHomEquiv_const.{u,v} X n x).symm))
    · intro j hj
      apply (uliftStandardHomEquiv.{u,v} X ⦋n⦌).injective
      exact (uliftStandardHomEquiv_precomp.{u,v} X (SimplexCategory.δ j) _).trans
        ((congrArg (fun f => SSet.stdSimplex.δ j ≫ f)
          (Equiv.apply_symm_apply (uliftStandardHomEquiv.{u,v} X ⦋n + 1⦌) h.map)).trans
            ((h.δ_map_of_gt j hj).trans (uliftStandardHomEquiv_const.{u,v} X n x).symm))
  · rintro ⟨h⟩
    exact ⟨uliftPointedRelStruct h⟩

end SSet
