/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaCutParity
import Code.Sharpness.DeltaBound










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

local instance (G : SimpleGraph V) (sites : I -> V)
    (u v : LPReplicaCurrentVertex V) :
    DecidablePred (fun n : Current (LPReplicaCurrentVertex V) =>
      CurrentConnected (lpReplicaCurrentGraph G sites) n u v) :=
  fun _ => Classical.propDecidable _


def lpReplicaCurrentEdgeFlux
    (G : SimpleGraph V) (sites : I -> V)
    (n : Current (LPReplicaCurrentVertex V)) :
    (lpReplicaCurrentGraph G sites).edgeFinset -> Nat :=
  fun e => n e.1

@[simp] theorem lpReplicaCurrentEdgeFlux_ofEdgeFun
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaCurrentEdgeFlux G sites
      (ofEdgeFun (lpReplicaCurrentGraph G sites) m) = m := by
  funext e
  unfold lpReplicaCurrentEdgeFlux ofEdgeFun
  rw [dif_pos e.2]



noncomputable def lpReplicaOffdiagSeamSelector
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) (i j : I) (hij : i ≠ j)
    (n : Current (LPReplicaCurrentVertex V)) : I :=
  let H := lpReplicaCurrentGraph G sites
  let m := lpReplicaCurrentEdgeFlux G sites n
  let A := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
    lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
    lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
  if h : StatMech.Sharpness.sources H (ofEdgeFun H m) = A then
    Classical.choose
      (lpReplicaCurrent_exists_positiveSeam_of_offdiagSource
        G sites hsite hij m h)
  else i



theorem lpReplicaOffdiagSeamSelector_positive
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hsrc : StatMech.Sharpness.sources (lpReplicaCurrentGraph G sites)
      (ofEdgeFun (lpReplicaCurrentGraph G sites) m) =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) :
    0 < (ofEdgeFun (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentSeamEdge sites
        (lpReplicaOffdiagSeamSelector G sites hsite i j hij
          (ofEdgeFun (lpReplicaCurrentGraph G sites) m))) := by
  unfold lpReplicaOffdiagSeamSelector
  simp only [lpReplicaCurrentEdgeFlux_ofEdgeFun]
  rw [dif_pos hsrc]
  exact Classical.choose_spec
    (lpReplicaCurrent_exists_positiveSeam_of_offdiagSource
      G sites hsite hij m hsrc)

theorem lpReplicaOffdiagSeamSelector_connected
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hsrc : StatMech.Sharpness.sources (lpReplicaCurrentGraph G sites)
      (ofEdgeFun (lpReplicaCurrentGraph G sites) m) =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) :
    CurrentConnected (lpReplicaCurrentGraph G sites)
      (ofEdgeFun (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentLeft sites
        (lpReplicaOffdiagSeamSelector G sites hsite i j hij
          (ofEdgeFun (lpReplicaCurrentGraph G sites) m)))
      (lpReplicaCurrentRight sites
        (lpReplicaOffdiagSeamSelector G sites hsite i j hij
          (ofEdgeFun (lpReplicaCurrentGraph G sites) m))) := by
  let k := lpReplicaOffdiagSeamSelector G sites hsite i j hij
    (ofEdgeFun (lpReplicaCurrentGraph G sites) m)
  have hk := lpReplicaOffdiagSeamSelector_positive
    G sites hsite hij m hsrc
  refine SimpleGraph.Adj.reachable ?_
  constructor
  · unfold lpReplicaCurrentLeft lpReplicaCurrentRight
    rw [lpReplicaCurrentGraph_adj_left_right_iff]
    exact ⟨k, rfl, rfl⟩
  · simpa only [k] using hk

set_option maxHeartbeats 1600000 in

theorem lp_gatedSourcePairSum_partition_fintype
    {W L : Type*} [Fintype W] [DecidableEq W]
    [Fintype L] [DecidableEq L]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (A B : Finset W) (P : Current W -> Prop) [DecidablePred P]
    (f : Current W -> L) :
    gatedSourcePairSum G beta J A B P =
      ∑ l : L, gatedSourcePairSum G beta J A B
        (fun n => f n = l ∧ P n) := by
  unfold gatedSourcePairSum
  rw [← Summable.tsum_finsetSum (s := (Finset.univ : Finset L))
    (f := fun l (pq : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) =>
      (if StatMech.Sharpness.sources G (ofEdgeFun G pq.1) = A
        then weight G beta J (ofEdgeFun G pq.1) else 0) *
      (if StatMech.Sharpness.sources G (ofEdgeFun G pq.2) = B
        then weight G beta J (ofEdgeFun G pq.2) else 0) *
      (if f (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) = l ∧
          P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) then 1 else 0))
    (fun l _ => summable_gatedSourcePairSummand G beta J A B
      (fun n => f n = l ∧ P n))]
  apply tsum_congr
  rintro ⟨p, q⟩
  let n := ofEdgeFun G (fun e => p e + q e)
  by_cases hp : StatMech.Sharpness.sources G (ofEdgeFun G p) = A <;>
    by_cases hq : StatMech.Sharpness.sources G (ofEdgeFun G q) = B <;>
    by_cases hP : P n <;> simp [n, hp, hq, hP]


noncomputable def lpReplicaOffdiagDisconnSlice
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) (i j : I) (hij : i ≠ j)
    (beta : Real) (J : Sym2 (LPReplicaCurrentVertex V) -> Real)
    (k : I) : Real :=
  let H := lpReplicaCurrentGraph G sites
  let A := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
    lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
    lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
  gatedSourcePairSum H beta J A ∅ (fun n =>
    (lpReplicaOffdiagSeamSelector G sites hsite i j hij n = k ∧
      ¬ CurrentConnected H n lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) ∧
    CurrentConnected H n
      (lpReplicaCurrentLeft sites k) (lpReplicaCurrentRight sites k))



theorem lpReplica_sourcePairDisconnSum_offdiag_eq_sum_slices
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (beta : Real) (J : Sym2 (LPReplicaCurrentVertex V) -> Real) :
    sourcePairDisconnSum (lpReplicaCurrentGraph G sites) beta J
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
        ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 =
      ∑ k : I, lpReplicaOffdiagDisconnSlice
        G sites hsite i j hij beta J k := by
  let H := lpReplicaCurrentGraph G sites
  let A := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
    lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
    lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
  let sel := lpReplicaOffdiagSeamSelector G sites hsite i j hij
  have hpart := lp_gatedSourcePairSum_partition_fintype H beta J A ∅
    (fun n => ¬ CurrentConnected H n
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) sel
  have hadd (k : I) :
      gatedSourcePairSum H beta J A ∅ (fun n =>
          sel n = k ∧ ¬ CurrentConnected H n
            lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) =
        gatedSourcePairSum H beta J A ∅ (fun n =>
          (sel n = k ∧ ¬ CurrentConnected H n
            lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) ∧
          CurrentConnected H n
            (lpReplicaCurrentLeft sites k)
            (lpReplicaCurrentRight sites k)) := by
    apply gatedSourcePairSum_congr_sources
    intro p q hp hq
    have htotal : StatMech.Sharpness.sources H
        (ofEdgeFun H (fun e => p e + q e)) = A := by
      rw [← ofEdgeFun_add,
        StatMech.Sharpness.sources_add H
          (ofEdgeFun H p) (ofEdgeFun H q), hp, hq]
      simp
    have hconn := lpReplicaOffdiagSeamSelector_connected
      G sites hsite hij (fun e => p e + q e) htotal
    constructor
    · intro h
      refine ⟨h, ?_⟩
      rw [← h.1]
      exact hconn
    · exact fun h => h.1
  change gatedSourcePairSum H beta J A ∅ (fun n =>
      ¬ CurrentConnected H n lpReplicaCurrentGhost0
        lpReplicaCurrentGhost1) = _
  rw [hpart]
  apply Finset.sum_congr rfl
  intro k _
  rw [hadd k]
  rfl



theorem lpReplica_sourcePairDisconnSum_offdiag_eq_sum_toggled
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (beta : Real) (J : Sym2 (LPReplicaCurrentVertex V) -> Real) :
    let H := lpReplicaCurrentGraph G sites
    let A := lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1
    sourcePairDisconnSum H beta J A ∅
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 =
      ∑ k : I, gatedSourcePairSum H beta J
        (A ∆ lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k)
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k)
        (fun n =>
          (lpReplicaOffdiagSeamSelector G sites hsite i j hij n = k ∧
            ¬ CurrentConnected H n
              lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) ∧
          CurrentConnected H n
            (lpReplicaCurrentLeft sites k)
            (lpReplicaCurrentRight sites k)) := by
  dsimp only
  rw [lpReplica_sourcePairDisconnSum_offdiag_eq_sum_slices
    G sites hsite hij beta J]
  apply Finset.sum_congr rfl
  intro k _
  unfold lpReplicaOffdiagDisconnSlice
  let P : Current (LPReplicaCurrentVertex V) -> Prop := fun n =>
    lpReplicaOffdiagSeamSelector G sites hsite i j hij n = k ∧
      ¬ CurrentConnected (lpReplicaCurrentGraph G sites) n
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  have htoggle := lpReplica_gatedSourcePairSum_toggle_seam
    G sites beta J
    (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1)
    ∅ k P
  simpa only [P, bot_symmDiff] using htoggle

end

end StatMech.Ising
