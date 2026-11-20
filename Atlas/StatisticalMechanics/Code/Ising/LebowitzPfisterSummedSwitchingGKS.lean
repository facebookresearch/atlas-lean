/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaAggregateSwitching
import Code.Sharpness.Claim1IsingComplete
import Code.FrontierA.GrahamWeightedEq22Refinement










open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness
open StatMech.Sharpness.GhostCurrentRep
open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]




theorem lpCurrentSum_gks_second
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (A B : Finset V) :
    currentSum G beta J A * currentSum G beta J B <=
      currentSum G beta J (A ∆ B) * currentSum G beta J ∅ := by
  have hgks := gks_second_J G.edgeFinset (fun e => beta * J e) (fun _ => 0)
    (fun e _ => mul_nonneg hbeta (hJ e)) (fun _ => le_rfl) A B
  rw [← expectationJ_eq_expJ G beta J A,
    ← expectationJ_eq_expJ G beta J B,
    ← expectationJ_eq_expJ G beta J (A ∆ B)] at hgks
  rw [current_representation, current_representation,
    current_representation, div_mul_div_comm] at hgks
  have hZ : 0 < currentSum G beta J ∅ :=
    acr_currentSum_empty_pos G beta J
  rw [div_le_div_iff₀ (mul_pos hZ hZ) hZ] at hgks
  nlinarith



theorem lpCurrentSum_pair_gks_gap
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (A : Finset V) {u v : V} (huv : u ≠ v) :
    currentSum G beta J A * currentSum G beta J ∅ -
          currentSum G beta J (A ∆ {u, v}) *
            currentSum G beta J {u, v} =
        sourcePairDisconnSum G beta J A ∅ u v ∧
      0 <= currentSum G beta J A * currentSum G beta J ∅ -
          currentSum G beta J (A ∆ {u, v}) *
            currentSum G beta J {u, v} := by
  have heq := gcr_currentSum_ghostRep G beta J A huv
  refine ⟨heq, ?_⟩
  rw [heq]
  exact lpSourcePairDisconnSum_nonneg G beta J hbeta hJ A ∅ u v





theorem lpMatchingCurrentSkewPolynomial_nonpos_iff_centeredGram
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (left right : I -> V) (g0 g1 : V) (hg : g0 ≠ g1) :
    lpMatchingCurrentSkewPolynomial
        (lpMatchingCurrentA G beta J left right)
        (lpMatchingCurrentB G beta J left right g0 g1)
        (lpMatchingCurrentC G beta J g0 g1)
        (lpMatchingCurrentD G beta J left right)
        (lpMatchingCurrentE G beta J left right g0 g1)
        (lpMatchingCurrentZ G beta J) <= 0 ↔
      lpMatchingDisconnCenteredGram G beta J left right g0 g1 <= 0 := by
  rw [lpMatchingCurrentSkewPolynomial_eq_sum_fiveCurrentCoefficient,
    lpMatchingFiveCurrentCoefficient_sum_nonpos_iff_centeredGram
      G beta J left right g0 g1 hg]

end

end StatMech.Ising

namespace StatMech.FrontierA

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]





theorem grahamEq22_globalGKSDrops_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    {i j k l m : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (him : i ≠ m) (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    (0 <= currentSum G beta J {k, l} *
          grahamFirstRemainderMass G beta J i j k l m -
        currentSum G beta J ∅ *
          grahamFirstMixedRemainderMass G beta J i j k l m) ∧
      (0 <= (currentSum G beta J {i, m} * currentSum G beta J {j, m}) *
          grahamSecondRemainderMass G beta J i j k l m -
        currentSum G beta J ∅ ^ 2 *
          grahamSecondMixedRemainderMass G beta J i j k l m) := by
  exact ⟨grahamFirstGlobalGKSDrop_nonneg G beta J hbeta hJ hij hkl,
    grahamSecondGlobalGKSDrop_nonneg G beta J hbeta hJ
      hij hik hil him hjk hjl hjm hkl hkm hlm⟩

end

end StatMech.FrontierA
