/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.ShermanLoop
import Code.Onsager.ShermanSplit
import Code.Onsager.ShermanLemma4
import Code.Onsager.ShermanLemma4Return
import Code.Onsager.ShermanFactor
import Code.Onsager.ShermanAssembly3






































































namespace StatMech.Onsager

open Matrix BigOperators Finset

set_option linter.unusedSectionVars false













theorem ons_edgeWeight_ofFn {E : Type*} (Λ : Matrix E E ℂ) (m : ℕ) (f : Fin (m + 1) → E) :
    ons_edgeWeight Λ (List.ofFn f) = ∏ i : Fin m, Λ (f i.castSucc) (f i.succ) := by
  induction m with
  | zero => simp [List.ofFn_succ]
  | succ m ih =>
      rw [List.ofFn_succ]
      set g : Fin (m + 1) → E := fun i => f i.succ with hg
      have hgcons : List.ofFn g = g 0 :: List.ofFn (fun i : Fin m => g i.succ) := by
        rw [List.ofFn_succ]
      rw [hgcons, ons_edgeWeight_cons_cons, ← hgcons, ih g, Fin.prod_univ_succ]
      simp only [hg, Fin.castSucc_zero, Fin.succ_castSucc]









theorem ons_snoc_succ {E : Type*} {n : ℕ} (v : Fin (n + 1) → E) (i : Fin (n + 1)) :
    (Fin.snoc v (v 0) : Fin (n + 2) → E) i.succ = v (i + 1) := by
  rcases eq_or_ne i (Fin.last n) with rfl | hne
  · rw [Fin.succ_last, Fin.snoc_last, Fin.last_add_one]
  · have hlt : i < Fin.last n := lt_of_le_of_ne (Fin.le_last i) hne
    have hval : (i + 1 : Fin (n + 1)).val = i.val + 1 := Fin.val_add_one_of_lt hlt
    have hcast : i.succ = (i + 1 : Fin (n + 1)).castSucc := by
      apply Fin.ext
      rw [Fin.val_succ, Fin.val_castSucc, hval]
    rw [hcast, Fin.snoc_castSucc]












theorem ons_loopWeight_eq_edgeWeight {E : Type*} [Fintype E] [DecidableEq E] (Λ : Matrix E E ℂ)
    {n : ℕ} (v : Fin (n + 1) → E) :
    ons_loopWeight Λ v = ons_edgeWeight Λ (List.ofFn v ++ [v 0]) := by
  have hlist : List.ofFn v ++ [v 0] = List.ofFn (Fin.snoc v (v 0) : Fin (n + 2) → E) := by
    rw [List.ofFn_succ' (Fin.snoc v (v 0) : Fin (n + 2) → E)]
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  rw [hlist, ons_edgeWeight_ofFn]
  unfold ons_loopWeight
  apply Finset.prod_congr rfl
  intro i _
  rw [Fin.snoc_castSucc, ons_snoc_succ]












theorem ons_loopWeight_eq_firstReturn_prod {E : Type*} [Fintype E] [DecidableEq E]
    (Λ : Matrix E E ℂ) {n : ℕ} (e : E) (v : Fin (n + 1) → E) :
    ons_loopWeight Λ v
      = ((ons_firstReturnSplit e (List.ofFn v ++ [v 0])).map (ons_edgeWeight Λ)).prod := by
  rw [ons_loopWeight_eq_edgeWeight]
  exact (ons_edgeWeight_firstReturnSplit Λ e _).symm












theorem ons_summable_bucketE_of_count {L : ℕ} [NeZero L] (x ω : ℂ) (e : ons_Dart L) {z : ℂ}
    (hz : ‖z‖ < 1) (hcount : ∀ n : ℕ, ons_bucketE L x ω e n = z ^ (n + 1)) :
    Summable (fun n : ℕ => ons_bucketE L x ω e n / ((n : ℂ) + 1)) := by
  have hfun : (fun n : ℕ => ons_bucketE L x ω e n / ((n : ℂ) + 1))
      = (fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1)) := by
    funext n; rw [hcount n]
  rw [hfun]
  exact (ons_hasSum_shifted_pow_div hz).summable












theorem ons_hlam {L : ℕ} [NeZero L] [Fact (2 < L)] (x ω : ℂ) (e : ons_Dart L) {z : ℂ}
    (hz : ‖z‖ < 1) (hcount : ∀ n : ℕ, ons_bucketE L x ω e n = z ^ (n + 1)) :
    ∃ lam : ℂ,
      Complex.exp (- ∑' n : ℕ, ons_bucketE L x ω e n / ((n : ℂ) + 1)) = 1 - lam := by
  refine ⟨z, ?_⟩
  have hcong : (∑' n : ℕ, ons_bucketE L x ω e n / ((n : ℂ) + 1))
      = ∑' k : ℕ, z ^ (k + 1) / ((k : ℂ) + 1) := by
    apply tsum_congr; intro n; rw [hcount n]
  rw [hcong]
  exact ons_lemma4_exp hz
















theorem ons_det_final_of_count {L : ℕ} [NeZero L] [Fact (2 < L)] (x ω : ℂ)
    (hω : ω ^ 2 = Complex.I) (e : ons_Dart L)
    (hspec : ∀ α ∈ (ons_KWmat L x ω).charpoly.roots, ‖α‖ < 1)
    {z : ℂ} (hz : ‖z‖ < 1) (hcount : ∀ n : ℕ, ons_bucketE L x ω e n = z ^ (n + 1))
    (hN : Summable (fun n : ℕ => ons_bucketN L x ω e n / ((n : ℂ) + 1))) :
    (1 - ons_KWmat L x ω).det
      = Complex.exp (- ∑' n : ℕ, ons_bucketN L x ω e n / ((n : ℂ) + 1)) * (1 - z) ^ 2 := by
  have hB := ons_summable_bucketE_of_count x ω e hz hcount
  have hlam : Complex.exp (- ∑' n : ℕ, ons_bucketE L x ω e n / ((n : ℂ) + 1)) = 1 - z := by
    have hcong : (∑' n : ℕ, ons_bucketE L x ω e n / ((n : ℂ) + 1))
        = ∑' k : ℕ, z ^ (k + 1) / ((k : ℂ) + 1) := by
      apply tsum_congr; intro n; rw [hcount n]
    rw [hcong]; exact ons_lemma4_exp hz
  exact ons_det_eq_A_mul_sq x ω hω e hspec hB hN z hlam

end StatMech.Onsager
