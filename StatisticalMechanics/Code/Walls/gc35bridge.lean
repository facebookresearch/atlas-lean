/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Mathlib
import Code.Walls.gc34resummation
import Code.Walls.gc33witness
import Code.Sharpness.ClaimIsingFull
import Code.Sharpness.TwoReplica
import Code.Sharpness.CurrentRep

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.style.show false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]














noncomputable def gc35_splitEquiv (m₀ : ↥G.edgeFinset → ℕ) :
    {K : Sharpness.Current V // ∀ e, K e ≤ (Sharpness.ofEdgeFun G m₀) e}
      ≃ {p : ↥G.edgeFinset → ℕ // p ≤ m₀} where
  toFun K := ⟨fun i => K.1 i.1, fun i => by
    have := K.2 i.1
    unfold Sharpness.ofEdgeFun at this
    rw [dif_pos i.2] at this
    exact this⟩
  invFun p := ⟨Sharpness.ofEdgeFun G p.1, fun e => by
    unfold Sharpness.ofEdgeFun
    by_cases h : e ∈ G.edgeFinset
    · rw [dif_pos h, dif_pos h]; exact p.2 _
    · rw [dif_neg h, dif_neg h]⟩
  left_inv K := by
    apply Subtype.ext
    funext e
    show (Sharpness.ofEdgeFun G (fun i => K.1 i.1)) e = K.1 e
    unfold Sharpness.ofEdgeFun
    by_cases h : e ∈ G.edgeFinset
    · rw [dif_pos h]
    · rw [dif_neg h]
      have := K.2 e
      unfold Sharpness.ofEdgeFun at this
      rw [dif_neg h] at this
      omega
  right_inv p := by
    apply Subtype.ext
    funext i
    show (Sharpness.ofEdgeFun G p.1) i.1 = p.1 i
    unfold Sharpness.ofEdgeFun
    rw [dif_pos i.2]













theorem gc35_hnw_mass_eq_edgeFun_split (β : ℝ) (J : Sym2 V → ℝ) (m₀ : ↥G.edgeFinset → ℕ)
    (A : Finset V) :
    hnw_mass G β J (Sharpness.ofEdgeFun G m₀) A
      = ∑ p : {p : ↥G.edgeFinset → ℕ // p ≤ m₀},
          (if Sharpness.sources G (Sharpness.ofEdgeFun G p.1) = A
            then Sharpness.weight G β J (Sharpness.ofEdgeFun G p.1)
              * Sharpness.weight G β J (Sharpness.ofEdgeFun G (fun i => m₀ i - p.1 i))
            else 0) := by
  unfold hnw_mass splitWeightedSum
  refine Fintype.sum_equiv (gc35_splitEquiv G m₀) _ _ (fun K => ?_)
  have hK1 : K.1 = Sharpness.ofEdgeFun G ((gc35_splitEquiv G m₀) K).1 := by
    funext e
    show K.1 e = (Sharpness.ofEdgeFun G (fun i => K.1 i.1)) e
    unfold Sharpness.ofEdgeFun
    by_cases h : e ∈ G.edgeFinset
    · rw [dif_pos h]
    · rw [dif_neg h]
      have := K.2 e
      unfold Sharpness.ofEdgeFun at this
      rw [dif_neg h] at this
      omega
  have hcompl : (fun e => (Sharpness.ofEdgeFun G m₀) e - K.1 e)
      = Sharpness.ofEdgeFun G (fun i => m₀ i - ((gc35_splitEquiv G m₀) K).1 i) := by
    funext e
    unfold Sharpness.ofEdgeFun
    by_cases h : e ∈ G.edgeFinset
    · rw [dif_pos h, dif_pos h]
      rw [hK1]; unfold Sharpness.ofEdgeFun; rw [dif_pos h]
    · rw [dif_neg h, dif_neg h]
      have := K.2 e
      unfold Sharpness.ofEdgeFun at this
      rw [dif_neg h] at this
      omega
  rw [one_mul, hcompl]
  congr 1
  · rw [hK1]
  · congr 1
    rw [hK1]













theorem gc35_inner_second_constraint_automatic (β : ℝ) (J : Sym2 V → ℝ)
    (m₀ : ↥G.edgeFinset → ℕ) (A B : Finset V)
    (hm : Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = A ∆ B) :
    (∑ p : {p : ↥G.edgeFinset → ℕ // p ≤ m₀},
        (if Sharpness.sources G (Sharpness.ofEdgeFun G p.1) = A
          then Sharpness.weight G β J (Sharpness.ofEdgeFun G p.1)
            * Sharpness.weight G β J (Sharpness.ofEdgeFun G (fun i => m₀ i - p.1 i))
          else 0))
    = ∑ p : {p : ↥G.edgeFinset → ℕ // p ≤ m₀},
        ((if Sharpness.sources G (Sharpness.ofEdgeFun G p.1) = A
            then Sharpness.weight G β J (Sharpness.ofEdgeFun G p.1) else 0)
          * (if Sharpness.sources G (Sharpness.ofEdgeFun G (fun i => m₀ i - p.1 i)) = B
              then Sharpness.weight G β J (Sharpness.ofEdgeFun G (fun i => m₀ i - p.1 i)) else 0)) := by
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases hA : Sharpness.sources G (Sharpness.ofEdgeFun G p.1) = A
  · rw [if_pos hA, if_pos hA]
    have hcomp : Sharpness.sources G (Sharpness.ofEdgeFun G (fun i => m₀ i - p.1 i)) = B := by
      have hsplit := sources_ofEdgeFun_add G m₀ p.1 p.2
      rw [hm, hA] at hsplit
      have h2 := congrArg (fun X => A ∆ X) hsplit
      simpa [symmDiff_symmDiff_cancel_left] using h2.symm
    rw [if_pos hcomp]
  · rw [if_neg hA]; rw [if_neg hA, zero_mul]





theorem gc35_inner_zero_off_fibre (β : ℝ) (J : Sym2 V → ℝ)
    (m₀ : ↥G.edgeFinset → ℕ) (A B : Finset V)
    (hm : Sharpness.sources G (Sharpness.ofEdgeFun G m₀) ≠ A ∆ B) :
    (∑ p : {p : ↥G.edgeFinset → ℕ // p ≤ m₀},
        ((if Sharpness.sources G (Sharpness.ofEdgeFun G p.1) = A
            then Sharpness.weight G β J (Sharpness.ofEdgeFun G p.1) else 0)
          * (if Sharpness.sources G (Sharpness.ofEdgeFun G (fun i => m₀ i - p.1 i)) = B
              then Sharpness.weight G β J (Sharpness.ofEdgeFun G (fun i => m₀ i - p.1 i)) else 0))) = 0 := by
  refine Finset.sum_eq_zero (fun p _ => ?_)
  by_cases hA : Sharpness.sources G (Sharpness.ofEdgeFun G p.1) = A
  · by_cases hBc : Sharpness.sources G (Sharpness.ofEdgeFun G (fun i => m₀ i - p.1 i)) = B
    · exfalso
      apply hm
      have := sources_ofEdgeFun_add G m₀ p.1 p.2
      rw [hA, hBc] at this
      exact this
    · rw [if_neg hBc, mul_zero]
  · rw [if_neg hA, zero_mul]























theorem gc35_sourcePairSum_eq_tsum_native_mass (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) :
    Sharpness.sourcePairSum G β J A B
      = ∑' m₀ : ↥G.edgeFinset → ℕ,
          (if Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = A ∆ B
            then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) A else 0) := by
  rw [sourcePairSum_eq_superposition]
  refine tsum_congr (fun m₀ => ?_)
  by_cases hm : Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = A ∆ B
  · rw [if_pos hm, gc35_hnw_mass_eq_edgeFun_split G β J m₀ A,
      gc35_inner_second_constraint_automatic G β J m₀ A B hm]
  · rw [if_neg hm, gc35_inner_zero_off_fibre G β J m₀ A B hm]


















theorem gc35_native_mass_fibre_summand (β : ℝ) (J : Sym2 V → ℝ) (m₀ : ↥G.edgeFinset → ℕ)
    (A B : Finset V) (hm : Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = A ∆ B) :
    hnw_mass G β J (Sharpness.ofEdgeFun G m₀) A
      = ∑ p : {p : ↥G.edgeFinset → ℕ // p ≤ m₀},
          ((if Sharpness.sources G (Sharpness.ofEdgeFun G p.1) = A
              then Sharpness.weight G β J (Sharpness.ofEdgeFun G p.1) else 0)
            * (if Sharpness.sources G (Sharpness.ofEdgeFun G (fun i => m₀ i - p.1 i)) = B
                then Sharpness.weight G β J (Sharpness.ofEdgeFun G (fun i => m₀ i - p.1 i)) else 0)) := by
  rw [gc35_hnw_mass_eq_edgeFun_split G β J m₀ A,
    gc35_inner_second_constraint_automatic G β J m₀ A B hm]

















theorem gc35_gated_pairSum_eq_superposition (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (P : Sharpness.Current V → Prop) [DecidablePred P] :
    (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
        (if Sharpness.sources G (Sharpness.ofEdgeFun G pq.1) = A
            then Sharpness.weight G β J (Sharpness.ofEdgeFun G pq.1) else 0)
          * (if Sharpness.sources G (Sharpness.ofEdgeFun G pq.2) = B
              then Sharpness.weight G β J (Sharpness.ofEdgeFun G pq.2) else 0)
          * (if P (fun e => Sharpness.ofEdgeFun G pq.1 e + Sharpness.ofEdgeFun G pq.2 e)
              then 1 else 0))
      = ∑' m₀ : ↥G.edgeFinset → ℕ,
          (if P (Sharpness.ofEdgeFun G m₀) then 1 else 0) *
          ∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m₀},
            ((if Sharpness.sources G (Sharpness.ofEdgeFun G K.1) = A
                then Sharpness.weight G β J (Sharpness.ofEdgeFun G K.1) else 0)
              * (if Sharpness.sources G (Sharpness.ofEdgeFun G (fun e => m₀ e - K.1 e)) = B
                    then Sharpness.weight G β J (Sharpness.ofEdgeFun G (fun e => m₀ e - K.1 e)) else 0)) := by
  set f : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if Sharpness.sources G (Sharpness.ofEdgeFun G p) = A
      then Sharpness.weight G β J (Sharpness.ofEdgeFun G p) else 0 with hf
  set g : (↥G.edgeFinset → ℕ) → ℝ :=
    fun q => if Sharpness.sources G (Sharpness.ofEdgeFun G q) = B
      then Sharpness.weight G β J (Sharpness.ofEdgeFun G q) else 0 with hg
  have hfg : Summable (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
      f z.1 * g z.2
        * (if P (fun e => Sharpness.ofEdgeFun G z.1 e + Sharpness.ofEdgeFun G z.2 e)
            then (1:ℝ) else 0)) := by
    apply Summable.of_norm
    have hbase : Summable (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) => ‖f z.1 * g z.2‖) :=
      (summable_mul_of_summable_norm
        (summable_norm_currentSum_summand G β J A) (summable_norm_currentSum_summand G β J B)).norm
    refine hbase.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_)
    rw [norm_mul]
    calc ‖f z.1 * g z.2‖ * ‖(if P _ then (1:ℝ) else 0)‖
        ≤ ‖f z.1 * g z.2‖ * 1 := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          by_cases h : P (fun e => Sharpness.ofEdgeFun G z.1 e + Sharpness.ofEdgeFun G z.2 e) <;>
            simp [h]
      _ = ‖f z.1 * g z.2‖ := by ring
  set F : (Σ m : (↥G.edgeFinset → ℕ), {p : ↥G.edgeFinset → ℕ // p ≤ m}) → ℝ :=
    fun s => f s.2.1 * g (fun e => s.1 e - s.2.1 e)
      * (if P (Sharpness.ofEdgeFun G s.1) then 1 else 0) with hF
  have hcomp : ∀ z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
      f z.1 * g z.2
        * (if P (fun e => Sharpness.ofEdgeFun G z.1 e + Sharpness.ofEdgeFun G z.2 e) then (1:ℝ) else 0)
        = F (pairEquivSigma z) := by
    rintro ⟨p, q⟩
    simp only [hF, pairEquivSigma, Equiv.coe_fn_mk]
    have hsub : (fun e => (p e + q e) - p e) = q := by ext e; simp
    rw [hsub]
    congr 2
    rw [Sharpness.ofEdgeFun_add]
  have hsumF : Summable F := by
    rw [← (pairEquivSigma (E := ↥G.edgeFinset)).summable_iff]
    exact hfg.congr (fun z => hcomp z)
  rw [tsum_congr hcomp, (pairEquivSigma (E := ↥G.edgeFinset)).tsum_eq F,
    Summable.tsum_sigma hsumF]
  refine tsum_congr (fun m => ?_)
  rw [tsum_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun K _ => ?_)
  simp only [hF]
  ring












theorem gc35_gated_pairSum_eq_tsum_native_mass (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (P : Sharpness.Current V → Prop) [DecidablePred P] :
    (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
        (if Sharpness.sources G (Sharpness.ofEdgeFun G pq.1) = A
            then Sharpness.weight G β J (Sharpness.ofEdgeFun G pq.1) else 0)
          * (if Sharpness.sources G (Sharpness.ofEdgeFun G pq.2) = B
              then Sharpness.weight G β J (Sharpness.ofEdgeFun G pq.2) else 0)
          * (if P (fun e => Sharpness.ofEdgeFun G pq.1 e + Sharpness.ofEdgeFun G pq.2 e)
              then 1 else 0))
      = ∑' m₀ : ↥G.edgeFinset → ℕ,
          (if P (Sharpness.ofEdgeFun G m₀) ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = A ∆ B
            then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) A else 0) := by
  rw [gc35_gated_pairSum_eq_superposition G β J A B P]
  refine tsum_congr (fun m₀ => ?_)
  by_cases hm : Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = A ∆ B
  · by_cases hP : P (Sharpness.ofEdgeFun G m₀)
    · rw [if_pos hP, one_mul, if_pos ⟨hP, hm⟩,
        ← gc35_inner_second_constraint_automatic G β J m₀ A B hm,
        ← gc35_hnw_mass_eq_edgeFun_split G β J m₀ A]
    · rw [if_neg hP, zero_mul, if_neg (fun h => hP h.1)]
  · rw [if_neg (fun h : P (Sharpness.ofEdgeFun G m₀) ∧ _ => hm h.2)]
    rw [gc35_inner_zero_off_fibre G β J m₀ A B hm, mul_zero]































theorem gc35_native_resummation (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (g : V) (hg : g ∉ S)
    (zero x : V) (h0 : zero ∈ S) (hx : x ∈ S)
    (hZ : currentSum G β (couplingIn J S) ∅ ≠ 0) :
    (∑' m₀ : ↥G.edgeFinset → ℕ,
        (if notConnComp G (Sharpness.ofEdgeFun G m₀) g = S
              ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = ({zero, x} : Finset V)
          then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) {zero, x} else 0))
    = expectationJ G β (couplingIn J S) {zero, x}
      * (∑' m₀ : ↥G.edgeFinset → ℕ,
          (if notConnComp G (Sharpness.ofEdgeFun G m₀) g = S
                ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = (∅ : Finset V)
            then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) ∅ else 0)) := by
  classical
  have hL := gc35_gated_pairSum_eq_tsum_native_mass G β J {zero, x} ∅
    (fun m => notConnComp G m g = S)
  have hR := gc35_gated_pairSum_eq_tsum_native_mass G β J ∅ ∅
    (fun m => notConnComp G m g = S)
  rw [show ({zero, x} : Finset V) ∆ (∅ : Finset V) = {zero, x} from symmDiff_bot _] at hL
  rw [show (∅ : Finset V) ∆ (∅ : Finset V) = ∅ from symmDiff_self _] at hR
  rw [← hL, ← hR]
  exact claim2_ising G β J S g hg zero x h0 hx hZ





theorem gc35_native_resummation_factor_mem_Icc (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (S : Finset V) (zero x : V) :
    0 ≤ expectationJ G β (couplingIn J S) {zero, x}
      ∧ expectationJ G β (couplingIn J S) {zero, x} ≤ 1 :=
  gc34_resummation_factor_mem_Icc G β J hβ hJ S {zero, x}












theorem gc35_gc33_ma_ofEdgeFun :
    gc33_ma = Sharpness.ofEdgeFun gc33_G (fun i => gc33_ma i.1) := by
  funext e
  unfold Sharpness.ofEdgeFun
  by_cases h : e ∈ gc33_G.edgeFinset
  · rw [dif_pos h]
  · rw [dif_neg h]
    
    unfold gc33_ma
    have hdiag : e.IsDiag := by
      by_contra hnd
      exact h (by
        obtain ⟨⟨a, b⟩, hab⟩ := e.exists_rep
        subst hab
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        show gc33_G.Adj a b
        rw [Sym2.mk_isDiag_iff] at hnd
        exact hnd)
    
    rw [if_neg ?_]
    rintro (he | he | he) <;>
      · rw [he] at hdiag
        rw [Sym2.mk_isDiag_iff] at hdiag
        exact absurd hdiag (by decide)






theorem gc35_bridge_witness_mass_eq :
    hnw_mass gc33_G 1 gc33_J gc33_ma ∅
      = ∑ p : {p : ↥gc33_G.edgeFinset → ℕ // p ≤ (fun i => gc33_ma i.1)},
          (if Sharpness.sources gc33_G (Sharpness.ofEdgeFun gc33_G p.1) = (∅ : Finset (Fin 5))
            then Sharpness.weight gc33_G 1 gc33_J (Sharpness.ofEdgeFun gc33_G p.1)
              * Sharpness.weight gc33_G 1 gc33_J
                  (Sharpness.ofEdgeFun gc33_G (fun i => (fun j => gc33_ma j.1) i - p.1 i))
            else 0) := by
  conv_lhs => rw [gc35_gc33_ma_ofEdgeFun]
  exact gc35_hnw_mass_eq_edgeFun_split gc33_G 1 gc33_J (fun i => gc33_ma i.1) ∅





theorem gc35_bridge_witness_positive :
    0 < hnw_mass gc33_G 1 gc33_J gc33_ma ∅ :=
  gc33_mass_ma_pos


























theorem gc35_status (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V) (S : Finset V) (zero x : V) :
    Sharpness.sourcePairSum G β J A B
        = ∑' m₀ : ↥G.edgeFinset → ℕ,
            (if Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = A ∆ B
              then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) A else 0)
      ∧ (0 ≤ expectationJ G β (couplingIn J S) {zero, x}
          ∧ expectationJ G β (couplingIn J S) {zero, x} ≤ 1) := by
  exact ⟨gc35_sourcePairSum_eq_tsum_native_mass G β J A B,
    gc35_native_resummation_factor_mem_Icc G β J hβ hJ S zero x⟩

end StatMech.Walls
