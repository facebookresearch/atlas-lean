/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import MathlibExt.Probability.Concentration.BoundedDifferences

@[expose] public section

/-! # BPP error amplification

Majority voting over `n` independent repetitions, each correct
with probability at least `2/3`, fails with probability at most
`exp (-n/18)`. This is roadmap package MOD-46 of the Atlas TCS
canon roadmap. The bound is McDiarmid's bounded-differences inequality
on finite product spaces (`mcdiarmid_product_general`) applied to the
number of `false` votes.

Source: Arora and Barak, Computational Complexity (2009),
Section 7.1.
-/

open Finset

namespace Cslib.Complexity.BPPAmplification

/-- Majority vote of a tuple of Boolean votes. -/
def majority {n : ℕ} (v : Fin n → Bool) : Bool :=
  decide (n / 2 < (Finset.univ.filter (fun i => v i = true)).card)

private theorem pmf_sum_bool (p : PMF Bool) : (p true).toReal + (p false).toReal = 1 := by
  have h1 : (∑' b : Bool, p b) = 1 := PMF.tsum_coe p
  rw [tsum_fintype] at h1
  have h2 : ((∑ b : Bool, p b).toReal) = (1 : ENNReal).toReal := by rw [h1]
  rw [ENNReal.toReal_sum (fun b _ => p.apply_ne_top b)] at h2
  rw [ENNReal.toReal_one] at h2
  rw [Fintype.sum_bool] at h2
  exact h2

private theorem card_true_eq (n : ℕ) (v : Fin n → Bool) :
    ((Finset.univ.filter (fun i => v i = true)).card : ℝ)
      = ∑ i : Fin n, (if v i = true then (1 : ℝ) else 0) := by
  have h : (Finset.univ.filter (fun i => v i = true)).card
      = ∑ i ∈ (Finset.univ : Finset (Fin n)), (if v i = true then 1 else 0) := by
    rw [Finset.card_filter]
  calc ((Finset.univ.filter (fun i => v i = true)).card : ℝ)
      = ((∑ i ∈ (Finset.univ : Finset (Fin n)), (if v i = true then 1 else 0)) : ℕ) := by rw [h]
    _ = ∑ i ∈ (Finset.univ : Finset (Fin n)), (if v i = true then (1 : ℝ) else 0) := by
        rw [Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
    _ = ∑ i : Fin n, (if v i = true then (1 : ℝ) else 0) := by rfl

private theorem bad_card_le (n : ℕ) (v : Fin n → Bool) (h : majority v = false) :
    ((Finset.univ.filter (fun i => v i = true)).card : ℝ) ≤ (n : ℝ) / 2 := by
  unfold majority at h
  have hneg : ¬ (n / 2 < (Finset.univ.filter (fun i => v i = true)).card) :=
    of_decide_eq_false h
  have h1 : (Finset.univ.filter (fun i => v i = true)).card ≤ n / 2 :=
    Nat.le_of_not_gt hneg
  have h2 : (n / 2 * 2) ≤ n := Nat.div_mul_le_self n 2
  have h3 : (((Finset.univ.filter (fun i => v i = true)).card : ℕ) : ℝ) ≤ ((n / 2 : ℕ) : ℝ) :=
    Nat.cast_le.mpr h1
  have h4 : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
    have h2r : ((n / 2 * 2 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr h2
    push_cast at h2r
    linarith
  linarith

/-- Under the product weights `∏ i, q (v i)` with `q true + q false = 1`, the coordinate `v j`
has law `q`. -/
private theorem sum_prod_mul_coord {n : ℕ} (q : Bool → ℝ) (hq : q true + q false = 1)
    (j : Fin n) (h : Bool → ℝ) :
    ∑ v : Fin n → Bool, (∏ i, q (v i)) * h (v j) = ∑ b, q b * h b := by
  classical
  have hfac : ∀ v : Fin n → Bool, (∏ i, q (v i)) * h (v j) =
      ∏ i, (if i = j then q (v i) * h (v i) else q (v i)) := by
    intro v
    have e : ∀ i, (if i = j then q (v i) * h (v i) else q (v i)) =
        q (v i) * (if i = j then h (v i) else 1) := fun i => by split_ifs <;> simp
    simp only [e, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  calc ∑ v : Fin n → Bool, (∏ i, q (v i)) * h (v j)
      = ∑ v : Fin n → Bool, ∏ i, (fun i b => if i = j then q b * h b else q b) i (v i) :=
        Finset.sum_congr rfl fun v _ => hfac v
    _ = ∏ i, ∑ b, (fun i b => if i = j then q b * h b else q b) i b :=
        (Fintype.prod_sum fun i b => if i = j then q b * h b else q b).symm
    _ = ∑ b, q b * h b := by
        have e : ∀ i, (∑ b, if i = j then q b * h b else q b) =
            if i = j then ∑ b, q b * h b else 1 := by
          intro i
          split_ifs
          · rfl
          · rw [Fintype.sum_bool]
            exact hq
        simp only [e, Finset.prod_ite_eq', Finset.mem_univ, ite_true]

/-- BPP error amplification (one-sided form, finite): independent
votes each equal to `true` with probability at least `2 / 3` under
a product law on tuples (weight of a tuple is the product of the
per-vote probabilities, here with a common bias lower bound given
through a single PMF `p` on `Bool` with `p true ≥ 2 / 3`): the
majority is wrong (`false`) with probability at most
`exp (-(n / 18))`. The tuple law is the product PMF
built by recursion on the tuple as a function `Fin n → Bool`
weighted by `∏ i, (p (v i)).toReal`.

The proof applies `mcdiarmid_product_general` to the number of `false`
votes: it has mean `n · P(false) ≤ n / 3`, a wrong majority puts it at
least `n / 2`, and one vote changes it by at most `1`, so the deviation
`n / 6` has weight at most `exp (-2 (n / 6) ^ 2 / n) = exp (-n / 18)`. -/
theorem bpp_majority_amplify {n : ℕ} (p : PMF Bool)
    (hp : (2 / 3 : ℝ) ≤ (p true).toReal) :
    (∑ v : Fin n → Bool, (∏ i, (p (v i)).toReal) *
      (if majority v = false then 1 else 0)) ≤ Real.exp (-(n / 18 : ℝ)) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [majority]
  have hp_sum : (p true).toReal + (p false).toReal = 1 := pmf_sum_bool p
  -- `f v` is the number of `false` votes.
  set f : (Fin n → Bool) → ℝ := fun v => ∑ i, if v i = false then (1 : ℝ) else 0 with hf_def
  -- Changing one vote changes `f` by at most `1`.
  have hbd : ∀ (i : Fin n) (x y : Fin n → Bool), (∀ j, j ≠ i → x j = y j) →
      |f x - f y| ≤ 1 := by
    intro i x y hxy
    have hsplit : f x - f y =
        (if x i = false then (1 : ℝ) else 0) - (if y i = false then 1 else 0) := by
      simp only [hf_def, ← Finset.sum_sub_distrib]
      exact Finset.sum_eq_single i (fun j _ hji => by simp [hxy j hji]) (by simp)
    rw [hsplit]
    split_ifs <;> norm_num
  -- The mean number of `false` votes is `n · P(false)`.
  have hmean : ∑ y : Fin n → Bool, (∏ i, (p (y i)).toReal) * f y = n * (p false).toReal := by
    simp only [hf_def, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hj : ∀ j : Fin n, ∑ y : Fin n → Bool,
        (∏ i, (p (y i)).toReal) * (if y j = false then (1 : ℝ) else 0) = (p false).toReal := by
      intro j
      refine (sum_prod_mul_coord (fun b => (p b).toReal) hp_sum j
        (fun b => if b = false then (1 : ℝ) else 0)).trans ?_
      simp
    simp only [hj]
    simp
  have ht : (0 : ℝ) < n / 6 := div_pos (Nat.cast_pos.mpr hn) (by norm_num)
  have hmc := mcdiarmid_product_general (α := fun _ : Fin n => Bool)
    (fun _ b => (p b).toReal) (fun _ _ => ENNReal.toReal_nonneg)
    (fun _ => by rw [Fintype.sum_bool]; exact hp_sum) f (fun _ => (1 : ℝ))
    (fun _ => zero_le_one) ((n : ℝ) / 6) ht hbd
  have hexp : Real.exp (-2 * ((n : ℝ) / 6) ^ 2 / ∑ _i : Fin n, (1 : ℝ) ^ 2) =
      Real.exp (-(n / 18 : ℝ)) := by
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    congr 1
    simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    rw [div_eq_iff hn']
    ring
  have hlhs : (∑ v : Fin n → Bool, (∏ i, (p (v i)).toReal) *
      (if majority v = false then 1 else 0)) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin n → Bool => majority v = false),
        ∏ i, (p (v i)).toReal := by
    rw [Finset.sum_filter]
    simp only [mul_ite, mul_one, mul_zero]
  rw [hlhs]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun v _ _ =>
    Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg) (hmc.trans_eq hexp)
  -- A wrong majority has at least `n / 2` false votes: `n / 6` above the mean.
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  have htrue : ∑ i, (if v i = true then (1 : ℝ) else 0) ≤ n / 2 := by
    rw [← card_true_eq]
    exact bad_card_le n v hv
  have hfv : f v = n - ∑ i, (if v i = true then (1 : ℝ) else 0) := by
    have e : ∀ i, (if v i = false then (1 : ℝ) else 0) = 1 - (if v i = true then 1 else 0) := by
      intro i
      cases v i <;> simp
    simp only [hf_def, e, Finset.sum_sub_distrib]
    simp
  have hpf : (n : ℝ) * (p false).toReal ≤ n * (1 / 3) :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n)
  rw [hmean, hfv]
  linarith

end Cslib.Complexity.BPPAmplification
