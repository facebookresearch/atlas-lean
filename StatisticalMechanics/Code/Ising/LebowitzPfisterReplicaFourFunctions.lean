/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaCollisionResummation
import Code.Ising.LebowitzPfisterReplicaAggregateSwitching









open Finset
open scoped BigOperators symmDiff

namespace StatMech.Ising

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _

omit [DecidableEq I] in



theorem lpReplicaMatchingDisconn_le_of_offdiagFourFunctions
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hpoint : ∀ i j : I, i ≠ j ->
      let H := lpReplicaCurrentGraph G sites
      let Jr := lpReplicaCurrentCoupling J hf r
      let Si := lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
      let Sj := lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
      let T := lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1
      sourcePairDisconnSum H beta Jr ∅ ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        sourcePairDisconnSum H beta Jr (Si ∆ Sj ∆ T) ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <=
        sourcePairDisconnSum H beta Jr Si ∅
            lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
          sourcePairDisconnSum H beta Jr (Sj ∆ T) ∅
            lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 +
        sourcePairDisconnSum H beta Jr Sj ∅
            lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
          sourcePairDisconnSum H beta Jr (Si ∆ T) ∅
            lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    sourcePairDisconnSum H beta Jr ∅ ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        lpMatchingDisconnTwo H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <=
      2 * lpMatchingDisconnZero H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        lpMatchingDisconnOne H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  classical
  dsimp only
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  let dE := sourcePairDisconnSum H beta Jr ∅ ∅
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  let a : I -> Real := fun i => sourcePairDisconnSum H beta Jr
    (lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) ∅
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  let b : I -> Real := fun i => sourcePairDisconnSum H beta Jr
    (lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1) ∅
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  let c : I -> I -> Real := fun i j => sourcePairDisconnSum H beta Jr
    (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1) ∅
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  have hJr : ∀ e, 0 <= Jr e :=
    lpReplicaCurrentCoupling_nonneg J hf r hJ hhf hr
  have hab (i j : I) : dE * (if i = j then 0 else c i j) <=
      a i * b j + a j * b i := by
    by_cases hij : i = j
    · rw [if_pos hij, mul_zero]
      exact add_nonneg
        (mul_nonneg
          (lpSourcePairDisconnSum_nonneg H beta Jr hbeta hJr _ ∅ _ _)
          (lpSourcePairDisconnSum_nonneg H beta Jr hbeta hJr _ ∅ _ _))
        (mul_nonneg
          (lpSourcePairDisconnSum_nonneg H beta Jr hbeta hJr _ ∅ _ _)
          (lpSourcePairDisconnSum_nonneg H beta Jr hbeta hJr _ ∅ _ _))
    · rw [if_neg hij]
      simpa only [H, Jr, dE, a, b, c] using hpoint i j hij
  rw [lpMatchingDisconnTwo_eq_offDiag H beta Jr
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (by simp
      [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])]
  unfold lpMatchingDisconnTwoOffDiag lpMatchingDisconnZero lpMatchingDisconnOne
  change dE * (∑ i : I, ∑ j : I, if i = j then 0 else c i j) <=
    2 * (∑ i : I, a i) * ∑ j : I, b j
  calc
    dE * (∑ i : I, ∑ j : I, if i = j then 0 else c i j) =
        ∑ i : I, ∑ j : I, dE * (if i = j then 0 else c i j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ <= ∑ i : I, ∑ j : I, (a i * b j + a j * b i) := by
      exact Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => hab i j
    _ = 2 * (∑ i : I, a i) * ∑ j : I, b j := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul,
        ← Finset.mul_sum]
      ring

end

end StatMech.Ising
