/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteStageInvariant
import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteStageInductionGeometry

/-!
# Finite latching invariants by degree induction

Double induction on actual outer degree and degeneracy index.

Both fields of every actual finite stage invariant are derived. The only
external assertions are the original row sharpness and original sigma HC
conditions. No stage Sharp or incoming HC family is a supplied outcome.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkAllFiniteLatching
open SharpComparisonDraft RezkIncomingHC RezkFiniteStageInvariant RezkFiniteStageGeometry

/-- Every ORIGINAL finite latching stage is sharp and HC in its ambient row,
derived by the actual lower-degree/previous-index double induction. -/
theorem all_stage_sharp_and_incoming
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrow : ∀ n, Sharp (eta.app (op ⦋n⦌)))
    (hsigma : ∀ (n : ℕ) (r : Fin (n + 1)), WeakEquivalence
      (pullback.lift (X.σ r) (eta.app (op ⦋n⦌))
        (SimplicialObject.σ_naturality eta r) ≫
        comparison (eta.app (op ⦋n + 1⦌)) (Y.σ r))) :
    ∀ (n : ℕ) (r : Fin (n + 1)),
      Sharp (outerLatchingStageMap eta n r) ∧
        WeakEquivalence
          (pullback.lift (outerLatchingStage X n r).ι (outerLatchingStageMap eta n r)
            (outerLatchingStageMap_ι eta n r).symm ≫
            comparison (eta.app (op ⦋n + 1⦌)) (outerLatchingStage Y n r).ι) := by
  intro n
  induction n with
  | zero =>
      intro r
      have hr : r = 0 := by
        apply Fin.ext
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ r.isLt)
      subst r
      exact zero_stage_sharp_and_incoming eta 0 (hrow 0) (hsigma 0 0)
  | succ n lower =>
      intro r
      refine Fin.induction ?_ (fun r previous => ?_) r
      · exact zero_stage_sharp_and_incoming eta (n + 1) (hrow (n + 1)) (hsigma (n + 1) 0)
      · have overlapSharp : Sharp (outerLatchingStageSourceOverlapMap eta (n + 1) r.succ) :=
          (SharpCoproductClosure.sharp_arrowIso_iff (overlapArrowIso eta n r)).mpr (lower r).1
        have beforeSharp : Sharp (outerLatchingStageBeforeMap eta (n + 1) r.succ) :=
          (SharpCoproductClosure.sharp_arrowIso_iff (beforeArrowIso eta n r)).mpr previous.1
        have overlapHC := (source_succ_left_hc_iff_stage_incoming eta n r).mpr (lower r).2
        have beforeHC := (before_incoming_iff eta n r).mpr previous.2
        have stageSharp := stage_sharp_of_original_induction_inputs eta (n + 1) r.succ
          (hrow (n + 1)) (hrow ((n + 1) + 1)) beforeSharp overlapSharp
          (hsigma (n + 1) r.succ) overlapHC beforeHC
        have stageHC := stage_incoming_of_original_piece_invariants eta (n + 1) r.succ
          (hrow (n + 1)) (hrow ((n + 1) + 1))
          (hsigma (n + 1) r.succ) overlapHC beforeHC
        exact ⟨stageSharp, stageHC⟩

end SSet.RezkAllFiniteLatching
