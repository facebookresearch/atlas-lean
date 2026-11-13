/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Sharpness.SwitchingCovariance
import Code.Sharpness.TwoReplica

open Finset BigOperators SimpleGraph
open scoped symmDiff Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech
namespace Sharpness
namespace GhostCurrentRep

open StatMech.Sharpness (ofEdgeFun weight currentSum sourcePairSum)
open StatMech.Sharpness.FluxEdgeCopy (Copy endsM endsM_not_isDiag sourcePairDisconnSum
  sourcePairDisconnSum_eq_edgecopy sourcePairSum_eq_edgecopy)
open StatMech.Sharpness.RandomCurrent (switching_disconnect_card)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]







theorem gcr_pairCount_empty (m : ↥G.edgeFinset → ℕ) (A : Finset V) :
    (∑ S : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
          * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0))
      = (if RandomCurrent.sources (endsM G m) univ = A then (1 : ℝ) else 0)
        * (#((univ : Finset (Copy G m)).powerset.filter
            (fun K => RandomCurrent.sources (endsM G m) K = A)) : ℝ) := by
  classical
  
  have hcompl : ∀ S : Finset (Copy G m),
      (RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V))
        ↔ (RandomCurrent.sources (endsM G m) S = RandomCurrent.sources (endsM G m) univ) := by
    intro S
    rw [show (univ \ S) = (univ : Finset (Copy G m)) ∆ S from by
      ext i; simp only [mem_sdiff, Finset.mem_symmDiff, mem_univ, true_and]; tauto,
      RandomCurrent.sources_symmDiff]
    constructor
    · intro h
      have := symmDiff_eq_bot.mp (by rw [← Finset.bot_eq_empty] at h; exact h)
      exact this.symm
    · intro h; rw [h, symmDiff_self, Finset.bot_eq_empty]
  by_cases hAm : RandomCurrent.sources (endsM G m) univ = A
  · 
    rw [if_pos hAm, one_mul]
    have hstep : ∀ S : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
          = (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0) := by
      intro S
      by_cases h : RandomCurrent.sources (endsM G m) S = A
      · rw [if_pos h, if_pos ((hcompl S).mpr (by rw [h, hAm])), one_mul]
      · rw [if_neg h, zero_mul]
    simp_rw [hstep]
    rw [Finset.sum_boole]; congr 2
  · 
    rw [if_neg hAm, zero_mul]
    refine Finset.sum_eq_zero (fun S _ => ?_)
    by_cases hSA : RandomCurrent.sources (endsM G m) S = A
    · have hne : RandomCurrent.sources (endsM G m) (univ \ S) ≠ (∅ : Finset V) := by
        rw [Ne, hcompl S]
        intro h; exact hAm (by rw [← hSA, h])
      rw [if_neg hne, mul_zero]
    · rw [if_neg hSA, zero_mul]





theorem gcr_pairCount_pair (m : ↥G.edgeFinset → ℕ) (A : Finset V) (u v : V) :
    (∑ S : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) S = A ∆ {u, v} then (1 : ℝ) else 0)
          * (if RandomCurrent.sources (endsM G m) (univ \ S) = ({u, v} : Finset V) then 1 else 0))
      = (if RandomCurrent.sources (endsM G m) univ = A then (1 : ℝ) else 0)
        * (#((univ : Finset (Copy G m)).powerset.filter
            (fun K => RandomCurrent.sources (endsM G m) K = A ∆ {u, v})) : ℝ) := by
  classical
  
  have hcompl : ∀ S : Finset (Copy G m),
      (RandomCurrent.sources (endsM G m) (univ \ S) = ({u, v} : Finset V))
        ↔ (RandomCurrent.sources (endsM G m) S
              = RandomCurrent.sources (endsM G m) univ ∆ {u, v}) := by
    intro S
    rw [show (univ \ S) = (univ : Finset (Copy G m)) ∆ S from by
      ext i; simp only [mem_sdiff, Finset.mem_symmDiff, mem_univ, true_and]; tauto,
      RandomCurrent.sources_symmDiff]
    constructor
    · intro h
      
      have := congrArg (fun X => RandomCurrent.sources (endsM G m) univ ∆ X) h
      simp only at this
      rw [← symmDiff_assoc, symmDiff_self, bot_symmDiff] at this
      exact this
    · intro h
      rw [h, ← symmDiff_assoc, symmDiff_self, bot_symmDiff]
  by_cases hAm : RandomCurrent.sources (endsM G m) univ = A
  · rw [if_pos hAm, one_mul]
    have hstep : ∀ S : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) S = A ∆ {u, v} then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = ({u, v} : Finset V) then 1 else 0)
          = (if RandomCurrent.sources (endsM G m) S = A ∆ {u, v} then (1 : ℝ) else 0) := by
      intro S
      by_cases h : RandomCurrent.sources (endsM G m) S = A ∆ {u, v}
      · rw [if_pos h, if_pos ((hcompl S).mpr (by rw [h, hAm])), one_mul]
      · rw [if_neg h, zero_mul]
    simp_rw [hstep]
    rw [Finset.sum_boole]; congr 2
  · rw [if_neg hAm, zero_mul]
    refine Finset.sum_eq_zero (fun S _ => ?_)
    by_cases hSA : RandomCurrent.sources (endsM G m) S = A ∆ {u, v}
    · have hne : RandomCurrent.sources (endsM G m) (univ \ S) ≠ ({u, v} : Finset V) := by
        rw [Ne, hcompl S]
        intro h
        
        rw [hSA] at h
        
        have : A = RandomCurrent.sources (endsM G m) univ := by
          have h2 := congrArg (fun X => X ∆ ({u, v} : Finset V)) h
          simp only at h2
          rwa [symmDiff_symmDiff_cancel_right, symmDiff_symmDiff_cancel_right] at h2
        exact hAm this.symm
      rw [if_neg hne, mul_zero]
    · rw [if_neg hSA, zero_mul]






theorem gcr_pairCount_disconn (m : ↥G.edgeFinset → ℕ) (A : Finset V) (u v : V) :
    (∑ S : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
          * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
          * (if ¬ RandomCurrent.connK (endsM G m) univ u v then 1 else 0))
      = (if RandomCurrent.sources (endsM G m) univ = A then (1 : ℝ) else 0)
        * (if ¬ RandomCurrent.connK (endsM G m) univ u v then (1 : ℝ) else 0)
        * (#((univ : Finset (Copy G m)).powerset.filter
            (fun K => RandomCurrent.sources (endsM G m) K = A)) : ℝ) := by
  classical
  
  rw [show (∑ S : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
          * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
          * (if ¬ RandomCurrent.connK (endsM G m) univ u v then 1 else 0))
      = (∑ S : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
          * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0))
        * (if ¬ RandomCurrent.connK (endsM G m) univ u v then 1 else 0) from by
    rw [Finset.sum_mul]]
  rw [gcr_pairCount_empty G m A]
  ring







theorem gcr_superposition_switching_gap (m : ↥G.edgeFinset → ℕ) (A : Finset V) {u v : V}
    (huv : u ≠ v) :
    (∑ S : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
          * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0))
      - (∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = A ∆ {u, v} then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = ({u, v} : Finset V) then 1 else 0))
      = ∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
            * (if ¬ RandomCurrent.connK (endsM G m) univ u v then 1 else 0) := by
  classical
  rw [gcr_pairCount_empty G m A, gcr_pairCount_pair G m A u v, gcr_pairCount_disconn G m A u v]
  by_cases hAm : RandomCurrent.sources (endsM G m) univ = A
  · 
    rw [if_pos hAm, one_mul, one_mul, one_mul]
    
    have hsw := switching_disconnect_card (endsM G m) (univ : Finset (Copy G m))
      (fun i _ => endsM_not_isDiag G m i) A hAm huv
    have hswR : (#((univ : Finset (Copy G m)).powerset.filter
            (fun K => RandomCurrent.sources (endsM G m) K = A)) : ℝ)
          - #((univ : Finset (Copy G m)).powerset.filter
            (fun K => RandomCurrent.sources (endsM G m) K = A ∆ {u, v}))
        = (if ¬ RandomCurrent.connK (endsM G m) univ u v then
            (#((univ : Finset (Copy G m)).powerset.filter
              (fun K => RandomCurrent.sources (endsM G m) K = A)) : ℝ) else 0) := by
      by_cases hC : RandomCurrent.connK (endsM G m) univ u v
      · rw [if_neg (not_not.mpr hC)] at hsw
        rw [if_neg (not_not.mpr hC)]
        exact_mod_cast hsw
      · rw [if_pos hC] at hsw
        rw [if_pos hC]
        exact_mod_cast hsw
    rw [hswR]
    by_cases hC : RandomCurrent.connK (endsM G m) univ u v <;> simp [hC]
  · 
    rw [if_neg hAm, zero_mul, zero_mul, zero_mul, sub_zero, zero_mul]



open StatMech.Sharpness (pairEquivSigma summable_norm_currentSum_summand)







theorem gcr_summable_edgecopy (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      (∑ S : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
          * (if RandomCurrent.sources (endsM G m) (univ \ S) = B then 1 else 0))
      * weight G β J (ofEdgeFun G m)) := by
  classical
  set f : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if sources G (ofEdgeFun G p) = A then weight G β J (ofEdgeFun G p) else 0 with hf
  set g : (↥G.edgeFinset → ℕ) → ℝ :=
    fun q => if sources G (ofEdgeFun G q) = B then weight G β J (ofEdgeFun G q) else 0 with hg
  have hfg : Summable (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) => f z.1 * g z.2) :=
    summable_mul_of_summable_norm
      (summable_norm_currentSum_summand G β J A) (summable_norm_currentSum_summand G β J B)
  
  set F : (Σ m : (↥G.edgeFinset → ℕ), {p : ↥G.edgeFinset → ℕ // p ≤ m}) → ℝ :=
    fun s => f s.2.1 * g (fun e => s.1 e - s.2.1 e) with hF
  have hcomp : ∀ z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
      f z.1 * g z.2 = F (pairEquivSigma z) := by
    rintro ⟨p, q⟩
    simp only [hF, pairEquivSigma, Equiv.coe_fn_mk]
    have hsub : (fun e => (p e + q e) - p e) = q := by ext e; simp
    rw [hsub]
  have hsumF : Summable F := by
    rw [← (pairEquivSigma (E := ↥G.edgeFinset)).summable_iff]
    exact hfg.congr (fun z => hcomp z)
  
  have hsig := hsumF.sigma
  
  refine hsig.congr (fun m => ?_)
  rw [tsum_fintype]
  
  rw [show (∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m}, F ⟨m, K⟩)
        = ∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m},
            (if sources G (ofEdgeFun G K.1) = A then weight G β J (ofEdgeFun G K.1) else 0)
              * (if sources G (ofEdgeFun G (fun e => m e - K.1 e)) = B
                    then weight G β J (ofEdgeFun G (fun e => m e - K.1 e)) else 0)
      from rfl]
  exact FluxEdgeCopy.sourcePair_superposition_bridge G β J A B m



theorem gcr_summable_edgecopy_disconn (β : ℝ) (J : Sym2 V → ℝ) (hJnn : ∀ e, 0 ≤ J e)
    (hβ : 0 ≤ β) (A : Finset V) (u v : V) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      (∑ S : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
          * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
          * (if ¬ RandomCurrent.connK (endsM G m) univ u v then 1 else 0))
      * weight G β J (ofEdgeFun G m)) := by
  classical
  
  have hw : ∀ m : ↥G.edgeFinset → ℕ, 0 ≤ weight G β J (ofEdgeFun G m) := by
    intro m; unfold weight
    refine Finset.prod_nonneg (fun e _ => ?_)
    have hbJ : 0 ≤ β * J e := mul_nonneg hβ (hJnn e)
    positivity
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) (gcr_summable_edgecopy G β J A ∅)
  · 
    rw [gcr_pairCount_disconn G m A u v]
    have h1 : (0 : ℝ) ≤ (if RandomCurrent.sources (endsM G m) univ = A then (1 : ℝ) else 0) := by
      by_cases h : RandomCurrent.sources (endsM G m) univ = A <;> simp [h]
    have h2 : (0 : ℝ) ≤ (if ¬ RandomCurrent.connK (endsM G m) univ u v then (1 : ℝ) else 0) := by
      by_cases h : RandomCurrent.connK (endsM G m) univ u v <;> simp [h]
    have h3 : (0 : ℝ) ≤ (#((univ : Finset (Copy G m)).powerset.filter
        (fun K => RandomCurrent.sources (endsM G m) K = A)) : ℝ) := Nat.cast_nonneg _
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) (hw m)
  · 
    rw [gcr_pairCount_disconn G m A u v, gcr_pairCount_empty G m A]
    have h3 : (0 : ℝ) ≤ (#((univ : Finset (Copy G m)).powerset.filter
        (fun K => RandomCurrent.sources (endsM G m) K = A)) : ℝ) := Nat.cast_nonneg _
    by_cases hC : RandomCurrent.connK (endsM G m) univ u v
    · 
      rw [if_neg (not_not.mpr hC), mul_zero, zero_mul]
      by_cases hA : RandomCurrent.sources (endsM G m) univ = A
      · rw [if_pos hA, one_mul, zero_mul]; exact mul_nonneg h3 (hw m)
      · rw [if_neg hA, zero_mul, zero_mul, zero_mul]
    · rw [if_pos hC, mul_one]

















theorem gcr_sourcePairSum_switching_gap (β : ℝ) (J : Sym2 V → ℝ)
    (A : Finset V) {u v : V} (huv : u ≠ v) :
    sourcePairSum G β J A ∅ - sourcePairSum G β J (A ∆ {u, v}) {u, v}
      = sourcePairDisconnSum G β J A ∅ u v := by
  classical
  rw [sourcePairSum_eq_edgecopy G β J A ∅,
    sourcePairSum_eq_edgecopy G β J (A ∆ {u, v}) {u, v},
    sourcePairDisconnSum_eq_edgecopy G β J A ∅ u v]
  
  rw [← Summable.tsum_sub (gcr_summable_edgecopy G β J A ∅)
    (gcr_summable_edgecopy G β J (A ∆ {u, v}) {u, v})]
  refine tsum_congr (fun m => ?_)
  
  rw [← sub_mul]
  congr 1
  exact gcr_superposition_switching_gap G m A huv



open StatMech.Sharpness (sourcePairSum_eq_mul)
















theorem gcr_currentSum_ghostRep (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) {u v : V} (huv : u ≠ v) :
    currentSum G β J A * currentSum G β J ∅
        - currentSum G β J (A ∆ {u, v}) * currentSum G β J {u, v}
      = sourcePairDisconnSum G β J A ∅ u v := by
  rw [← sourcePairSum_eq_mul G β J A ∅, ← sourcePairSum_eq_mul G β J (A ∆ {u, v}) {u, v}]
  exact gcr_sourcePairSum_switching_gap G β J A huv

























theorem gcr_ghostCurrentRep (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) {u v : V} (huv : u ≠ v)
    (Z mom₃ mom₁ mom₂ : ℝ) (hZ : Z = currentSum G β J ∅) (hZne : Z ≠ 0)
    (hrep₃ : mom₃ = currentSum G β J A / Z)
    (hrep₁ : mom₁ = currentSum G β J (A ∆ {u, v}) / Z)
    (hrep₂ : mom₂ = currentSum G β J {u, v} / Z) :
    Z ^ 2 * (mom₃ - mom₁ * mom₂) = sourcePairDisconnSum G β J A ∅ u v := by
  rw [← gcr_currentSum_ghostRep G β J A huv]
  subst hrep₃ hrep₁ hrep₂ hZ
  field_simp








theorem gcr_sourcePairSum_switching_gap_nonvacuous :
    sourcePairSum (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1) ({0, 1, 2} : Finset (Fin 3)) ∅
        - sourcePairSum (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1)
            (({0, 1, 2} : Finset (Fin 3)) ∆ {0, 2}) {0, 2}
      = sourcePairDisconnSum (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1)
          ({0, 1, 2} : Finset (Fin 3)) ∅ 0 2 :=
  gcr_sourcePairSum_switching_gap (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1)
    ({0, 1, 2} : Finset (Fin 3)) (by decide)


theorem gcr_currentSum_ghostRep_nonvacuous :
    currentSum (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1) ({0, 1, 2} : Finset (Fin 3))
          * currentSum (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1) ∅
        - currentSum (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1)
            (({0, 1, 2} : Finset (Fin 3)) ∆ {0, 2})
          * currentSum (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1) {0, 2}
      = sourcePairDisconnSum (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1)
          ({0, 1, 2} : Finset (Fin 3)) ∅ 0 2 :=
  gcr_currentSum_ghostRep (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1)
    ({0, 1, 2} : Finset (Fin 3)) (by decide)

end GhostCurrentRep
end Sharpness
end StatMech
