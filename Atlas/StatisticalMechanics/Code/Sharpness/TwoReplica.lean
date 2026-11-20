/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Mathlib
import Code.Sharpness.RandomCurrent
import Code.Sharpness.CurrentRep
import Code.Sharpness.ClaimIsing

open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]












theorem weight_mul_eq (β : ℝ) (J : Sym2 V → ℝ) (n₁ n₂ : Current V) :
    weight G β J n₁ * weight G β J n₂
      = (∏ e ∈ G.edgeFinset, (Nat.choose (n₁ e + n₂ e) (n₁ e) : ℝ))
        * weight G β J (fun e => n₁ e + n₂ e) := by
  unfold weight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  set X := β * J e with hX
  set a := n₁ e
  set b := n₂ e
  have hnat : (a + b).choose a * (a.factorial * b.factorial) = (a + b).factorial := by
    have h := Nat.add_choose_mul_factorial_mul_factorial b a
    rw [Nat.add_comm b a] at h
    rw [← h]; ring
  have hfac : ((a + b).choose a : ℝ) * (a.factorial * b.factorial) = (a + b).factorial := by
    exact_mod_cast hnat
  have haf : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
  have hbf : (b.factorial : ℝ) ≠ 0 := by exact_mod_cast b.factorial_ne_zero
  have habf : ((a + b).factorial : ℝ) ≠ 0 := by exact_mod_cast (a + b).factorial_ne_zero
  rw [pow_add]
  field_simp
  rw [← hfac]
  ring






theorem ofEdgeFun_add (p q : ↥G.edgeFinset → ℕ) :
    (fun e => (ofEdgeFun G p) e + (ofEdgeFun G q) e) = ofEdgeFun G (fun i => p i + q i) := by
  ext e
  unfold ofEdgeFun
  by_cases h : e ∈ G.edgeFinset <;> simp [h]





theorem sources_ofEdgeFun_add (m K : ↥G.edgeFinset → ℕ) (hK : K ≤ m) :
    sources G (ofEdgeFun G m)
      = sources G (ofEdgeFun G K) ∆ sources G (ofEdgeFun G (fun e => m e - K e)) := by
  have hsplit : ofEdgeFun G m
      = fun e => (ofEdgeFun G K) e + (ofEdgeFun G (fun e => m e - K e)) e := by
    rw [ofEdgeFun_add]
    congr 1
    ext i
    exact (Nat.add_sub_cancel' (hK i)).symm
  rw [hsplit, sources_add]




noncomputable def wEdge (β : ℝ) (J : Sym2 V → ℝ) (e : Sym2 V) (k : ℕ) : ℝ :=
  (β * J e) ^ k / k.factorial



theorem summable_norm_wEdge (β : ℝ) (J : Sym2 V → ℝ) (e : Sym2 V) :
    Summable (fun k => ‖wEdge β J e k‖) := by
  unfold wEdge
  have h2 : Summable (fun k : ℕ => (|β * J e|) ^ k / k.factorial) := by
    have := NormedSpace.expSeries_summable' (𝕂 := ℝ) (|β * J e|)
    convert this using 2 with k; rw [smul_eq_mul, div_eq_inv_mul]
  refine h2.congr (fun k => ?_)
  rw [Real.norm_eq_abs, abs_div, abs_pow]
  congr 1
  exact (abs_of_nonneg (by positivity)).symm


theorem summable_norm_weight_ofEdgeFun (β : ℝ) (J : Sym2 V → ℝ) :
    Summable (fun m : ↥G.edgeFinset → ℕ => ‖weight G β J (ofEdgeFun G m)‖) := by
  have h := (prod_tsum_fubini (fun (e : Sym2 V) k => ‖wEdge β J e k‖)
    (fun e => summable_norm_wEdge β J e) (fun _ _ => norm_nonneg _) G.edgeFinset).1
  refine h.congr (fun m => ?_)
  rw [weight_ofEdgeFun, norm_prod]
  exact Finset.prod_congr rfl (fun e _ => rfl)



theorem summable_norm_currentSum_summand (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      ‖if sources G (ofEdgeFun G m) = A then weight G β J (ofEdgeFun G m) else 0‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (summable_norm_weight_ofEdgeFun G β J)
  by_cases h : sources G (ofEdgeFun G m) = A <;> simp [h]







def pairEquivSigma {E : Type*} :
    ((E → ℕ) × (E → ℕ)) ≃ Σ m : (E → ℕ), {p : E → ℕ // p ≤ m} where
  toFun pq := ⟨fun e => pq.1 e + pq.2 e, ⟨pq.1, fun e => Nat.le_add_right _ _⟩⟩
  invFun mp := (mp.2.1, fun e => mp.1 e - mp.2.1 e)
  left_inv := by rintro ⟨p, q⟩; ext e <;> simp
  right_inv := by
    rintro ⟨m, ⟨p, hp⟩⟩
    have hm : (fun e => p e + (m e - p e)) = m := by
      ext e; exact Nat.add_sub_cancel' (hp e)
    simp only
    exact Sigma.subtype_ext hm rfl



noncomputable instance instFintypeLe (m : ↥G.edgeFinset → ℕ) :
    Fintype {p : ↥G.edgeFinset → ℕ // p ≤ m} := by
  classical exact Fintype.ofFinite _









noncomputable def sourcePairSum (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) : ℝ :=
  ∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
    (if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0)
      * (if sources G (ofEdgeFun G pq.2) = B then weight G β J (ofEdgeFun G pq.2) else 0)






theorem sourcePairSum_eq_mul (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) :
    sourcePairSum G β J A B = currentSum G β J A * currentSum G β J B := by
  set f : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if sources G (ofEdgeFun G p) = A then weight G β J (ofEdgeFun G p) else 0 with hf
  set g : (↥G.edgeFinset → ℕ) → ℝ :=
    fun q => if sources G (ofEdgeFun G q) = B then weight G β J (ofEdgeFun G q) else 0 with hg
  have hsumf : Summable f := (summable_norm_currentSum_summand G β J A).of_norm
  have hsumg : Summable g := (summable_norm_currentSum_summand G β J B).of_norm
  have hfg : Summable (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) => f z.1 * g z.2) :=
    summable_mul_of_summable_norm
      (summable_norm_currentSum_summand G β J A) (summable_norm_currentSum_summand G β J B)
  show (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ), f pq.1 * g pq.2)
      = (∑' p, f p) * (∑' q, g q)
  rw [Summable.tsum_mul_tsum hsumf hsumg hfg]














theorem sourcePairSum_eq_superposition (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) :
    sourcePairSum G β J A B
      = ∑' m : ↥G.edgeFinset → ℕ,
          ∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m},
            (if sources G (ofEdgeFun G K.1) = A then weight G β J (ofEdgeFun G K.1) else 0)
              * (if sources G (ofEdgeFun G (fun e => m e - K.1 e)) = B
                    then weight G β J (ofEdgeFun G (fun e => m e - K.1 e)) else 0) := by
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
    rw [← (pairEquivSigma
      (E := ↥G.edgeFinset)).summable_iff]
    exact hfg.congr (fun z => hcomp z)
  
  unfold sourcePairSum
  rw [show (fun pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
        (if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0)
          * (if sources G (ofEdgeFun G pq.2) = B then weight G β J (ofEdgeFun G pq.2) else 0))
      = fun pq => f pq.1 * g pq.2 from rfl]
  rw [tsum_congr hcomp, (pairEquivSigma (E := ↥G.edgeFinset)).tsum_eq F,
    Summable.tsum_sigma hsumF]
  refine tsum_congr (fun m => ?_)
  rw [tsum_fintype]






theorem sourcePairSum_superposition_source (m K : ↥G.edgeFinset → ℕ) (hK : K ≤ m)
    {A B : Finset V} (hA : sources G (ofEdgeFun G K) = A)
    (hB : sources G (ofEdgeFun G (fun e => m e - K e)) = B) :
    sources G (ofEdgeFun G m) = A ∆ B := by
  rw [sources_ofEdgeFun_add G m K hK, hA, hB]












theorem weight_split_eq_binom (β : ℝ) (J : Sym2 V → ℝ)
    (m K : ↥G.edgeFinset → ℕ) (hK : K ≤ m) :
    weight G β J (ofEdgeFun G K) * weight G β J (ofEdgeFun G (fun e => m e - K e))
      = (∏ e ∈ G.edgeFinset,
          (Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K) e) : ℝ))
        * weight G β J (ofEdgeFun G m) := by
  have hsplit : ofEdgeFun G m
      = fun e => (ofEdgeFun G K) e + (ofEdgeFun G (fun e => m e - K e)) e := by
    rw [ofEdgeFun_add]
    congr 1
    ext i
    exact (Nat.add_sub_cancel' (hK i)).symm
  rw [weight_mul_eq G β J (ofEdgeFun G K) (ofEdgeFun G (fun e => m e - K e))]
  congr 1
  · refine Finset.prod_congr rfl (fun e he => ?_)
    have : (ofEdgeFun G m) e
        = (ofEdgeFun G K) e + (ofEdgeFun G (fun e => m e - K e)) e := by rw [hsplit]
    rw [this]
  · rw [← hsplit]

end Sharpness

end StatMech
