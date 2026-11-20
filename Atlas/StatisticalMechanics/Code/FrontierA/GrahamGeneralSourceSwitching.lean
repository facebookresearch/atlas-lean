/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Sharpness.Claim1IsingComplete










open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace GrahamGeneralSourceSwitching

open StatMech.Sharpness.FluxEdgeCopy

set_option maxHeartbeats 2000000 in

theorem edgecopy_sourcePair_shift_of_connected
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↑G.edgeFinset -> Nat) (A B : Finset V)
    {u v : V} (huv : u ≠ v)
    (hconn : RandomCurrent.connK (endsM G m)
      (Finset.univ : Finset (Copy G m)) u v) :
    (∑ K : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) K = A then (1 : Real) else 0) *
          (if RandomCurrent.sources (endsM G m)
              ((Finset.univ : Finset (Copy G m)) \ K) = B then 1 else 0)) =
      ∑ K : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) K = A ∆ {u, v}
          then (1 : Real) else 0) *
          (if RandomCurrent.sources (endsM G m)
              ((Finset.univ : Finset (Copy G m)) \ K) = B ∆ {u, v}
            then 1 else 0) := by
  let U : Finset (Copy G m) := Finset.univ
  obtain ⟨P, hPU, hPsrc⟩ := RandomCurrent.exists_conn_set
    (endsM G m) U hconn huv
  let shift : Finset (Copy G m) ≃ Finset (Copy G m) :=
    { toFun := fun K => K ∆ P
      invFun := fun K => K ∆ P
      left_inv := by
        intro K
        change (K ∆ P) ∆ P = K
        rw [symmDiff_assoc, symmDiff_self, symmDiff_bot]
      right_inv := by
        intro K
        change (K ∆ P) ∆ P = K
        rw [symmDiff_assoc, symmDiff_self, symmDiff_bot] }
  have hcompl (K : Finset (Copy G m)) :
      U \ (K ∆ P) = (U \ K) ∆ P := by
    ext x
    have hp : x ∈ P -> x ∈ U := fun hx => hPU hx
    simp only [Finset.mem_sdiff, Finset.mem_symmDiff]
    tauto
  have hpoint (K : Finset (Copy G m)) :
      ((if RandomCurrent.sources (endsM G m) K = A then (1 : Real) else 0) *
          (if RandomCurrent.sources (endsM G m) (U \ K) = B then 1 else 0)) =
        ((if RandomCurrent.sources (endsM G m) (shift K) = A ∆ {u, v}
            then (1 : Real) else 0) *
          (if RandomCurrent.sources (endsM G m) (U \ shift K) = B ∆ {u, v}
            then 1 else 0)) := by
    have hsrc1 : RandomCurrent.sources (endsM G m) (shift K) =
        RandomCurrent.sources (endsM G m) K ∆ {u, v} := by
      change RandomCurrent.sources (endsM G m) (K ∆ P) = _
      rw [RandomCurrent.sources_symmDiff, hPsrc]
    have hsrc2 : RandomCurrent.sources (endsM G m) (U \ shift K) =
        RandomCurrent.sources (endsM G m) (U \ K) ∆ {u, v} := by
      change RandomCurrent.sources (endsM G m) (U \ (K ∆ P)) = _
      rw [hcompl, RandomCurrent.sources_symmDiff, hPsrc]
    rw [hsrc1, hsrc2]
    have hiffA :
        RandomCurrent.sources (endsM G m) K ∆ {u, v} = A ∆ {u, v} ↔
          RandomCurrent.sources (endsM G m) K = A := by
      exact (symmDiff_left_injective ({u, v} : Finset V)).eq_iff
    have hiffB :
        RandomCurrent.sources (endsM G m) (U \ K) ∆ {u, v} = B ∆ {u, v} ↔
          RandomCurrent.sources (endsM G m) (U \ K) = B := by
      exact (symmDiff_left_injective ({u, v} : Finset V)).eq_iff
    simp only [hiffA, hiffB]
  calc
    (∑ K : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) K = A then (1 : Real) else 0) *
          (if RandomCurrent.sources (endsM G m) (U \ K) = B then 1 else 0)) =
      ∑ K : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) (shift K) = A ∆ {u, v}
          then (1 : Real) else 0) *
          (if RandomCurrent.sources (endsM G m) (U \ shift K) = B ∆ {u, v}
            then 1 else 0) := Finset.sum_congr rfl (fun K _ => hpoint K)
    _ = _ := by
      simpa only [U] using shift.sum_comp
        (fun K : Finset (Copy G m) =>
          (if RandomCurrent.sources (endsM G m) K = A ∆ {u, v}
            then (1 : Real) else 0) *
            (if RandomCurrent.sources (endsM G m)
                ((Finset.univ : Finset (Copy G m)) \ K) = B ∆ {u, v}
              then 1 else 0))

end GrahamGeneralSourceSwitching



theorem gatedSourcePairSum_shift_connected
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (A B : Finset V) {u v : V} (huv : u ≠ v)
    (P : Current V -> Prop) [DecidablePred P] :
    gatedSourcePairSum G beta J A B
        (fun n => P n ∧ CurrentConnected G n u v) =
      gatedSourcePairSum G beta J (A ∆ {u, v}) (B ∆ {u, v})
        (fun n => P n ∧ CurrentConnected G n u v) := by
  unfold gatedSourcePairSum
  rw [StatMech.Sharpness.FluxEdgeCopy.sourcePairSum_conv_factor G beta J A B
      (fun m => if P (ofEdgeFun G m) ∧
        CurrentConnected G (ofEdgeFun G m) u v then 1 else 0)
      (fun m => by
        by_cases hP : P (ofEdgeFun G m) <;>
          by_cases hC : CurrentConnected G (ofEdgeFun G m) u v <;>
          simp [hP, hC])]
  rw [StatMech.Sharpness.FluxEdgeCopy.sourcePairSum_conv_factor G beta J
      (A ∆ {u, v}) (B ∆ {u, v})
      (fun m => if P (ofEdgeFun G m) ∧
        CurrentConnected G (ofEdgeFun G m) u v then 1 else 0)
      (fun m => by
        by_cases hP : P (ofEdgeFun G m) <;>
          by_cases hC : CurrentConnected G (ofEdgeFun G m) u v <;>
          simp [hP, hC])]
  apply tsum_congr
  intro m
  rw [StatMech.Sharpness.FluxEdgeCopy.sourcePair_superposition_bridge
      G beta J A B m,
    StatMech.Sharpness.FluxEdgeCopy.sourcePair_superposition_bridge
      G beta J (A ∆ {u, v}) (B ∆ {u, v}) m]
  have hconn := StatMech.Sharpness.FluxEdgeCopy.connK_univ_iff G m u v
  by_cases hP : P (ofEdgeFun G m) <;>
    by_cases hC : CurrentConnected G (ofEdgeFun G m) u v
  · have hcopy : RandomCurrent.connK
        (StatMech.Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset
          (StatMech.Sharpness.FluxEdgeCopy.Copy G m)) u v := hconn.mpr hC
    rw [GrahamGeneralSourceSwitching.edgecopy_sourcePair_shift_of_connected
      G m A B huv hcopy]
  all_goals simp [hP, hC]

end StatMech.FrontierA
