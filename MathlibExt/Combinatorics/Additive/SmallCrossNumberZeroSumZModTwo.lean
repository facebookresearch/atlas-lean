/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.SmallCrossNumberZeroSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.ZMod.Basic

/-!
# Good sequences in elementary abelian `2`-groups

A repeated entry guarantees a good subsequence. Counting injective sequences gives an upper
bound on the threshold when the labeled positions are sampled independently and uniformly.

## References

* Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in Abelian
  Groups*, INTEGERS 24 (2024), Article A93, pp. 1–12. Section 3.1 defines the uniform multiset
  model; Theorem 11 gives the corresponding threshold bound in that model.
-/

namespace MetaMathlibExt

open Finset Filter

/-- An equal pair gives a good subsequence: use a singleton for zero and the pair otherwise. -/
private lemma good_of_eq {d s : ℕ} {g : Fin s → Fin d → ZMod 2} {i j : Fin s}
    (hij : i ≠ j) (heq : g i = g j) : IsGoodSequence g := by
  classical
  by_cases hzero : g i = 0
  · exact ⟨{i}, singleton_nonempty _, by simp [hzero], by simp [hzero]⟩
  have htwo : 2 • g i = 0 := by
    ext k
    change (2 : ℕ) • g i k = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have horder : addOrderOf (g i) = 2 := addOrderOf_eq_prime htwo hzero
  refine ⟨{i, j}, by simp, ?_, ?_⟩
  · rw [sum_pair hij, ← heq, ← two_nsmul, htwo]
  · rw [sum_pair hij, ← heq, horder]
    norm_num

/-- At most a falling factorial of the sequences are bad, because all of them are injective. -/
private lemma bad_count_le (d s : ℕ) :
    {g : Fin s → Fin d → ZMod 2 | IsGoodSequence g}ᶜ.ncard ≤ (2 ^ d).descFactorial s := by
  classical
  let good : Set (Fin s → Fin d → ZMod 2) := {g | IsGoodSequence g}
  let toEmbedding (g : (goodᶜ : Set (Fin s → Fin d → ZMod 2))) : Fin s ↪ (Fin d → ZMod 2) :=
    ⟨g.1, fun _ _ heq => by
      by_contra hij
      exact g.2 (good_of_eq hij heq)⟩
  have hinj : Function.Injective toEmbedding := fun _ _ h =>
    Subtype.ext (congrArg Function.Embedding.toFun h)
  simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card (α := Fin s ↪ (Fin d → ZMod 2)),
    Fintype.card_embedding_eq, Fintype.card_fun, Fintype.card_fin, ZMod.card] using
    Nat.card_le_card_of_injective toEmbedding hinj

/-- The birthday bound from the product of the successive fractions of unused elements. -/
private lemma bad_prob_le_exp (d s : ℕ) (hs : 1 ≤ s) (hsm : s ≤ 2 ^ d) :
    1 - goodSequenceProb (Fin d → ZMod 2) s ≤
      Real.exp (-((s : ℝ) * (s - 1) / (2 * (2 : ℝ) ^ d))) := by
  let M : ℕ := 2 ^ d
  let m : ℝ := M
  let good : Set (Fin s → Fin d → ZMod 2) := {g | IsGoodSequence g}
  have hm : 0 < m := by dsimp [m, M]; positivity
  have hm_eq : m = (2 : ℝ) ^ d := by simp [m, M]
  have hcard : Nat.card (Fin d → ZMod 2) = M := by
    simp [Nat.card_eq_fintype_card, M, ZMod.card]
  have htotal : good.ncard + goodᶜ.ncard = M ^ s := by
    rw [Set.ncard_add_ncard_compl]
    simp [Nat.card_eq_fintype_card, M, ZMod.card]
  have hsum : (∑ i ∈ range s, (i : ℝ)) = (s : ℝ) * (s - 1) / 2 := by
    apply (eq_div_iff (by norm_num)).mpr
    have h := congrArg (fun n : ℕ => (n : ℝ)) (sum_range_id_mul_two s)
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_sub hs, Nat.cast_one, Nat.cast_ofNat] using h
  have hprod : ∏ _i ∈ range s, m = m ^ s := by simp
  rw [← hm_eq]
  calc
    1 - goodSequenceProb (Fin d → ZMod 2) s = (goodᶜ.ncard : ℝ) / m ^ s := by
      rw [goodSequenceProb, hcard]
      change 1 - (good.ncard : ℝ) / m ^ s = _
      rw [sub_eq_iff_eq_add, ← add_div, add_comm (goodᶜ.ncard : ℝ)]
      apply ((div_eq_one_iff_eq (pow_ne_zero _ hm.ne')).mpr ?_).symm
      simpa only [Nat.cast_add, Nat.cast_pow] using congrArg (fun n : ℕ => (n : ℝ)) htotal
    _ ≤ (M.descFactorial s : ℝ) / m ^ s := by
      gcongr
      exact bad_count_le d s
    _ = ∏ i ∈ range s, ((M - i : ℕ) : ℝ) / m := by
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod, prod_div_distrib, hprod]
    _ ≤ ∏ i ∈ range s, Real.exp (-((i : ℝ) / m)) := by
      apply prod_le_prod₀ (fun i _ => div_nonneg (Nat.cast_nonneg _) hm.le)
      intro i hi
      have hiM : i ≤ M := (mem_range.mp hi).le.trans hsm
      rw [Nat.cast_sub hiM, sub_div, show (M : ℝ) = m from rfl, div_self hm.ne']
      simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-((i : ℝ) / m))
    _ = _ := by
      rw [← Real.exp_sum, sum_neg_distrib, ← div_div]
      simp only [div_eq_mul_inv, ← sum_mul, hsum]

/-- A sample of length `2 ^ ⌊2d/3⌋` has good probability bounded away from zero. -/
private lemma eventually_good_prob_ge : ∀ᶠ d : ℕ in atTop,
    1 - Real.exp (-(1 / 2)) ≤ goodSequenceProb (Fin d → ZMod 2) (2 ^ (2 * d / 3)) := by
  filter_upwards [eventually_ge_atTop 9] with d hd
  let s : ℕ := 2 ^ (2 * d / 3)
  have hs : 2 ≤ s := by
    change 2 ^ 1 ≤ 2 ^ (2 * d / 3)
    gcongr
    omega
  have hsm : s ≤ 2 ^ d := by
    dsimp only [s]
    gcongr
    omega
  have hsq : 2 * 2 ^ d ≤ s ^ 2 := by
    rw [mul_comm, ← pow_succ, show s ^ 2 = 2 ^ ((2 * d / 3) * 2) by rw [pow_mul]]
    gcongr
    omega
  have hsq' : (2 : ℝ) * 2 ^ d ≤ (s : ℝ) ^ 2 := by exact_mod_cast hsq
  have hs' : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hprod : (2 : ℝ) ^ d ≤ (s : ℝ) * ((s : ℝ) - 1) := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ s by positivity) (sub_nonneg.mpr hs')]
  have he : -((s : ℝ) * (s - 1) / (2 * (2 : ℝ) ^ d)) ≤ -(1 / 2) := by
    rw [neg_le_neg_iff, le_div_iff₀ (by positivity)]
    linarith
  have := (bad_prob_le_exp d s (by omega) hsm).trans (Real.exp_le_exp.mpr he)
  linarith

private lemma two_pow_rpow_eq_exp (d : ℕ) (r : ℝ) :
    ((2 : ℝ) ^ d) ^ r = Real.exp ((Real.log 2 * r) * d) := by
  rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
  congr 1
  ring

/-- Sample only on the exceptional indices where the threshold exceeds `(2^d)^(3/4)`.
The samples there have length little-o of the threshold but a positive probability of success. -/
private lemma threshold_le_three_quarters {t : ℕ → ℝ}
    (ht : IsThresholdFunction (fun d s => goodSequenceProb (Fin d → ZMod 2) s) t) :
    ∀ᶠ d : ℕ in atTop, t d ≤ ((2 : ℝ) ^ d) ^ (3 / 4 : ℝ) := by
  let cutoff (d : ℕ) := ((2 : ℝ) ^ d) ^ (3 / 4 : ℝ)
  let f (d : ℕ) := if cutoff d < t d then 2 ^ (2 * d / 3) else 0
  have hsmall : (fun d : ℕ => ((2 : ℝ) ^ d) ^ (2 / 3 : ℝ)) =o[atTop] cutoff := by
    simp only [cutoff, two_pow_rpow_eq_exp, Real.isLittleO_exp_comp_exp_comp]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have heq (d : ℕ) : Real.log 2 * (3 / 4) * (d : ℝ) - Real.log 2 * (2 / 3) * d =
        (Real.log 2 / 12) * d := by ring
    simp only [heq]
    exact (tendsto_const_mul_atTop_of_pos (by positivity : 0 < Real.log 2 / 12)).mpr
      tendsto_natCast_atTop_atTop
  have hf : (fun d => (f d : ℝ)) =o[atTop] t := by
    apply Asymptotics.IsLittleO.of_bound
    intro c hc
    filter_upwards [hsmall.def hc] with d hd
    by_cases h : cutoff d < t d
    · have hfloor : ((2 * d / 3 : ℕ) : ℝ) ≤ 2 / 3 * (d : ℝ) := by
        have hh : (2 * d / 3) * 3 ≤ 2 * d := Nat.div_mul_le_self _ _
        have hh' : ((2 * d / 3 : ℕ) : ℝ) * 3 ≤ 2 * (d : ℝ) := by exact_mod_cast hh
        linarith
      have hpow : (2 : ℝ) ^ (2 * d / 3 : ℕ) ≤ ((2 : ℝ) ^ d) ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by simpa [mul_comm] using hfloor)
      have hcutoff : 0 ≤ cutoff d := by dsimp [cutoff]; positivity
      have htpos : 0 ≤ t d := hcutoff.trans h.le
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hcutoff] at hd
      simp only [f, ite_eq_left h, Nat.cast_pow, Nat.cast_ofNat, Real.norm_of_nonneg htpos]
      rw [Real.norm_of_nonneg (by positivity)]
      exact hpow.trans (hd.trans (mul_le_mul_of_nonneg_left h.le hc.le))
    · simpa only [f, ite_eq_right h, Nat.cast_zero, norm_zero] using
        mul_nonneg hc.le (norm_nonneg (t d))
  have hlim := (ht.2 f).2 hf
  have hpos : 0 < 1 - Real.exp (-(1 / 2)) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    norm_num
  filter_upwards [hlim.eventually_lt_const hpos, eventually_good_prob_ge] with d hlt hge
  change t d ≤ cutoff d
  by_contra! h
  exact (not_lt_of_ge hge) (by simpa only [f, ite_eq_left h] using hlt)

/-- **Threshold for good sequences in $\mathbb{Z}_2^d$.** Write $\lg = \log_2$. Let $t$ be a
threshold function, in $d$, for the probability that a uniformly sampled labeled sequence of $s$
elements of $\mathbb{Z}_2^d$ is good. The entries are independent uniform draws. Write $n = 2^d$.
Then for every $\varepsilon > 0$, $t(d) = O\left(n / (\lg \lg n)^{1-\varepsilon}\right)$
as $d \to \infty$.

The cited paper uses a different law: its Section 3.1 configuration model is uniform over
size-$s$ multisets, not over labeled sequences. Counting repeated entries gives the displayed
bound directly in the labeled model.

Source: Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in
Abelian Groups*, INTEGERS 24 (2024), Article A93, Theorem 11 (`integers-2024-A93-thm-11`),
for the corresponding bound in the configuration model. -/
public theorem zmod_two_pi_good_threshold_isBigO (ε : ℝ) (hε : 0 < ε) (t : ℕ → ℝ)
    (ht : IsThresholdFunction (fun d s => goodSequenceProb (Fin d → ZMod 2) s) t) :
    t =O[Filter.atTop]
      fun d : ℕ => (2 : ℝ) ^ d / Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ d)) ^ (1 - ε) := by
  have hb : (1 : ℝ) < 2 := by norm_num
  have hlog := Real.log_pos hb
  have hgrowth : ∀ᶠ d : ℕ in atTop, (d : ℝ) ≤ ((2 : ℝ) ^ d) ^ (1 / 4 : ℝ) := by
    have ho := isLittleO_pow_exp_pos_mul_atTop 1 (show 0 < Real.log 2 * (1 / 4) by positivity)
    have hc := ho.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
    filter_upwards [hc.def zero_lt_one] with d hd
    simpa only [Function.comp_apply, pow_one, one_mul, Real.norm_of_nonneg (Nat.cast_nonneg d),
      Real.norm_of_nonneg (Real.exp_nonneg _), two_pow_rpow_eq_exp] using hd
  apply Asymptotics.IsBigO.of_bound'
  filter_upwards [ht.1, threshold_le_three_quarters ht, hgrowth, eventually_ge_atTop 2]
    with d htpos htcut hgrow hd
  have hlogpow : Real.logb 2 ((2 : ℝ) ^ d) = d := by
    rw [Real.logb_pow, Real.logb_self_eq_one hb, mul_one]
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hlogd : 1 ≤ Real.logb 2 d := by
    rw [← Real.logb_self_eq_one hb]
    exact Real.logb_le_logb_of_le hb (by norm_num) hd'
  have hlogd_le : Real.logb 2 d ≤ d := calc
    Real.logb 2 d ≤ Real.logb 2 ((2 : ℝ) ^ d) :=
      Real.logb_le_logb_of_le hb (by linarith) (by exact_mod_cast d.lt_two_pow_self.le)
    _ = d := hlogpow
  have hdenom : 0 < Real.logb 2 d ^ (1 - ε) := Real.rpow_pos_of_pos (by linarith) _
  rw [hlogpow, Real.norm_of_nonneg htpos.le, Real.norm_of_nonneg (by positivity)]
  refine htcut.trans ((le_div_iff₀ hdenom).mpr ?_)
  calc
    _ ≤ ((2 : ℝ) ^ d) ^ (3 / 4 : ℝ) * ((2 : ℝ) ^ d) ^ (1 / 4 : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (((Real.rpow_le_self_of_one_le hlogd (by linarith)).trans hlogd_le).trans hgrow)
        (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity), show (3 / 4 + 1 / 4 : ℝ) = 1 by norm_num,
      Real.rpow_one]

end MetaMathlibExt
