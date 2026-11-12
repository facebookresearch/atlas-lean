/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.EdgeCopyEncoding
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.SwitchingCovariance

/-!
# Disconnection sums as switching gaps

The double-current disconnection sum with sources `A` and `∅` equals the sum over currents of the
switching gap times the weight.

## i. Overview

In the edge-copy encoding, subsets `S` with sources `A` and complement with sources `∅`, restricted
to `u ↮ v`, are counted by the switching gap `#{K : ∂K = A} - #{K : ∂K = A ∆ {u, v}}` (subtraction
form of the switching lemma).

## ii. Key results

- `edgecopy_disconnect_count_eq_switching_gap` : the count per current
- `sourcePairDisconnSum_eq_switching_gap` : the summed identity

## iii. Table of contents

- A. Switching gaps

## iv. References

- M. Aizenman, "Geometric analysis of φ⁴ fields and Ising models", Comm. Math. Phys. 86 (1982) 1–48
- H. Duminil-Copin, "Random currents expansion of the Ising model", lecture notes (2016),
  arXiv:1607.06933

-/

@[expose] public section

open Finset BigOperators
open scoped symmDiff


namespace StatMech
namespace Sharpness
namespace FluxEdgeCopy

open StatMech.Sharpness (ofEdgeFun weight)
open StatMech.Sharpness.RandomCurrent (switching_disconnect_card)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Switching gaps -/

open Classical in
lemma edgecopy_disconnect_count_eq_switching_gap
    (m : ↥G.edgeFinset → ℕ) (A : Finset V) (u v : V)
    (hnd : ∀ i ∈ (univ : Finset (Copy G m)), ¬ (endsM G m i).IsDiag)
    (hA : RandomCurrent.sources (endsM G m) univ = A) (huv : u ≠ v) :
    (∑ S : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
          * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
          * (if ¬ RandomCurrent.connK (endsM G m) univ u v then 1 else 0))
      = ((#((univ : Finset (Copy G m)).powerset.filter
            (fun K => RandomCurrent.sources (endsM G m) K = A)) : ℝ)
          - #((univ : Finset (Copy G m)).powerset.filter
            (fun K => RandomCurrent.sources (endsM G m) K = A ∆ {u, v}))) := by
  classical
  have hcompl : ∀ S : Finset (Copy G m),
      (RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V))
        ↔ (RandomCurrent.sources (endsM G m) S = A) := by
    intro S
    rw [show (univ \ S) = (univ : Finset (Copy G m)) ∆ S from by
      ext i; simp only [mem_sdiff, Finset.mem_symmDiff, mem_univ, true_and]; tauto,
      RandomCurrent.sources_symmDiff, hA]
    constructor
    · intro h
      exact (symmDiff_eq_bot.mp (by rw [← Finset.bot_eq_empty] at h; exact h)).symm
    · intro h; rw [h, symmDiff_self, Finset.bot_eq_empty]
  have hstep : ∀ S : Finset (Copy G m),
      (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
          * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
        = (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0) := by
    intro S
    by_cases h : RandomCurrent.sources (endsM G m) S = A
    · rw [ite_eq_left h, ite_eq_left ((hcompl S).mpr h), one_mul]
    · rw [ite_eq_right h, zero_mul]
  simp_rw [hstep]
  rw [← Finset.sum_mul]
  have hcount : (∑ S : Finset (Copy G m),
      (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0))
      = (#((univ : Finset (Copy G m)).powerset.filter
          (fun K => RandomCurrent.sources (endsM G m) K = A)) : ℝ) := by
    rw [Finset.sum_boole]; congr 2
  rw [hcount]
  have hsw := switching_disconnect_card (endsM G m) (univ : Finset (Copy G m)) hnd A hA huv
  by_cases hC : RandomCurrent.connK (endsM G m) univ u v
  · rw [ite_eq_right (not_not.mpr hC)] at hsw
    have hswR : ((#((univ : Finset (Copy G m)).powerset.filter
            (fun K => RandomCurrent.sources (endsM G m) K = A)) : ℝ)
          - #((univ : Finset (Copy G m)).powerset.filter
            (fun K => RandomCurrent.sources (endsM G m) K = A ∆ {u, v}))) = 0 := by
      have hz : ((#((univ : Finset (Copy G m)).powerset.filter
            (fun K => RandomCurrent.sources (endsM G m) K = A)) : ℤ)
          - #((univ : Finset (Copy G m)).powerset.filter
            (fun K => RandomCurrent.sources (endsM G m) K = A ∆ {u, v}))) = 0 := by omega
      exact_mod_cast hz
    rw [hswR]; simp [hC]
  · rw [ite_eq_left hC] at hsw
    have hcast : (#((univ : Finset (Copy G m)).powerset.filter
          (fun K => RandomCurrent.sources (endsM G m) K = A ∆ {u, v})) : ℝ) = 0 := by
      have hz : ((#((univ : Finset (Copy G m)).powerset.filter
            (fun K => RandomCurrent.sources (endsM G m) K = A ∆ {u, v})) : ℤ)) = 0 := by omega
      exact_mod_cast hz
    rw [hcast, sub_zero]; simp [hC]

set_option maxHeartbeats 800000 in
-- the proof elaborates large finite sums and `simp` calls over configurations
lemma sourcePairDisconnSum_eq_switching_gap (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (u v : V)
    (huv : u ≠ v) :
    sourcePairDisconnSum G β J A ∅ u v
      = ∑' m : ↥G.edgeFinset → ℕ,
          (if RandomCurrent.sources (endsM G m) univ = A then
            ((#((univ : Finset (Copy G m)).powerset.filter
                (fun K => RandomCurrent.sources (endsM G m) K = A)) : ℝ)
              - #((univ : Finset (Copy G m)).powerset.filter
                (fun K => RandomCurrent.sources (endsM G m) K = A ∆ {u, v})))
           else 0)
          * weight G β J (ofEdgeFun G m) := by
  rw [sourcePairDisconnSum_eq_edgecopy]
  refine tsum_congr (fun m => ?_)
  congr 1
  by_cases hAm : RandomCurrent.sources (endsM G m) univ = A
  · rw [ite_eq_left hAm,
      edgecopy_disconnect_count_eq_switching_gap G m A u v
        (fun i _ => endsM_not_isDiag G m i) hAm huv]
  · rw [ite_eq_right hAm]
    refine Finset.sum_eq_zero (fun S _ => ?_)
    by_cases hSA : RandomCurrent.sources (endsM G m) S = A
    · have hne : RandomCurrent.sources (endsM G m) (univ \ S) ≠ (∅ : Finset V) := by
        rw [show (univ \ S) = (univ : Finset (Copy G m)) ∆ S from by
          ext i; simp only [mem_sdiff, Finset.mem_symmDiff, mem_univ, true_and]; tauto,
          RandomCurrent.sources_symmDiff, hSA]
        intro h
        exact hAm (by
          have := symmDiff_eq_bot.mp (by rw [← Finset.bot_eq_empty] at h; exact h)
          exact this)
      rw [ite_eq_right hne, mul_zero, zero_mul]
    · rw [ite_eq_right hSA, zero_mul, zero_mul]

lemma sourcePairDisconnSum_eq_switching_gap_nonvacuous :
    sourcePairDisconnSum (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1)
        ({0, 1, 2} : Finset (Fin 3)) ∅ 0 2
      = ∑' m : ↥(⊤ : SimpleGraph (Fin 3)).edgeFinset → ℕ,
          (if RandomCurrent.sources (endsM (⊤ : SimpleGraph (Fin 3)) m) univ
                = ({0, 1, 2} : Finset (Fin 3)) then
            ((#((univ : Finset (Copy (⊤ : SimpleGraph (Fin 3)) m)).powerset.filter
                (fun K => RandomCurrent.sources (endsM (⊤ : SimpleGraph (Fin 3)) m) K
                  = ({0, 1, 2} : Finset (Fin 3)))) : ℝ)
              - #((univ : Finset (Copy (⊤ : SimpleGraph (Fin 3)) m)).powerset.filter
                (fun K => RandomCurrent.sources (endsM (⊤ : SimpleGraph (Fin 3)) m) K
                  = ({0, 1, 2} : Finset (Fin 3)) ∆ {0, 2})))
           else 0)
          * weight (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1)
              (ofEdgeFun (⊤ : SimpleGraph (Fin 3)) m) :=
  sourcePairDisconnSum_eq_switching_gap (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1)
    ({0, 1, 2} : Finset (Fin 3)) 0 2 (by decide)

end FluxEdgeCopy
end Sharpness
end StatMech
