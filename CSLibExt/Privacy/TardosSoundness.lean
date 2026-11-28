/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.FingerprintingCode
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Soundness of the Tardos accusation for a fixed bias vector

Tardos (2008), Theorem 1, bounds the probability that the linear accusation
rule accuses a fixed innocent user. Its proof (Section 3) conditions on the
column biases `p` and on the pirated word `y`, which the coalition produces
before the innocent user's codeword is drawn, and shows that the accusation
probability is below `ε` for every such `p` and `y`. This module proves that
conditioned statement for the codebook distribution `biasCodebookPMF p`: an
exponential-moment bound `tardosAccuses_prob_le` for arbitrary parameters, and
`tardos_soundness_fixed_bias` with Tardos's length `100 c² k`, threshold
`20 c k`, cutoff `1 / (300 c)` and exponent `1 / (10 c)`.

The source proof uses `e^u ≤ 1 + u + u²` for `u < 1.7` and asserts that the
scaled weights are below `1`; at `c = 1` the largest scaled weight is
`√299 / 10 > 1.7`. The inequality is proved here for `u ≤ 7 / 4`, which covers
every `c ≥ 1`. Only the lower cutoff `1 / (300 c) ≤ p j` is used. The
statement in which a pirate produces `y` from the coalition's rows, and the
union bound over innocent users of Tardos's Corollary 3, are not proved here.
-/

@[expose] public section

namespace CSLibExt.Privacy.Fingerprinting

open scoped ENNReal

/-! ### Moments of the Tardos weight -/

private theorem mul_sqrt_div_self {a b : ℝ} (ha : 0 ≤ a) :
    a * Real.sqrt (b / a) = Real.sqrt (a * b) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp
  · have h : a * b = a ^ 2 * (b / a) := by field_simp
    rw [h, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]

/-- The Tardos weight of a `Bernoulli(p)` bit has mean zero (Tardos 2008,
Section 2.1, remarks after the construction). -/
theorem tardosWeight_mean_eq_zero {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * tardosWeight p true + (1 - p) * tardosWeight p false = 0 := by
  rw [tardosWeight_true, tardosWeight_false, mul_neg, mul_sqrt_div_self hp0,
    mul_sqrt_div_self (sub_nonneg.mpr hp1), mul_comm (1 - p) p, add_neg_cancel]

/-- The Tardos weight of a `Bernoulli(p)` bit has second moment one for
`0 < p < 1` (Tardos 2008, Section 2.1, remarks after the construction). -/
theorem tardosWeight_sq_mean_eq_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    p * tardosWeight p true ^ 2 + (1 - p) * tardosWeight p false ^ 2 = 1 := by
  have h1 : 0 < 1 - p := sub_pos.mpr hp1
  rw [tardosWeight_true, tardosWeight_false, neg_sq, Real.sq_sqrt (div_nonneg h1.le hp0.le),
    Real.sq_sqrt (div_nonneg hp0.le h1.le)]
  field_simp
  ring

private theorem tardosWeight_sq_mean_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * tardosWeight p true ^ 2 + (1 - p) * tardosWeight p false ^ 2 ≤ 1 := by
  rcases hp0.eq_or_lt with rfl | hp0
  · simp
  rcases hp1.eq_or_lt with rfl | hp1
  · simp
  exact (tardosWeight_sq_mean_eq_one hp0 hp1).le

/-! ### Exponential moment of one column -/

private theorem exp_le_one_add_add_sq {x : ℝ} (hx : x ≤ 7 / 4) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  rcases le_or_gt x (-1) with h | h
  · have : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  rcases le_or_gt x 1 with h' | h'
  · have habs : |x| ≤ 1 := abs_le.mpr ⟨h.le, h'⟩
    have := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le habs)).2
    linarith
  · have hy0 : 0 ≤ x - 1 := by linarith
    have hy1 : x - 1 ≤ 1 := by linarith
    have h34 : 0 ≤ 3 / 4 - (x - 1) := by linarith
    have hb : Real.exp (x - 1) ≤
        1 + (x - 1) + (x - 1) ^ 2 / 2 + (x - 1) ^ 3 / 6 + (x - 1) ^ 4 * 5 / 96 := by
      have := Real.exp_bound' hy0 hy1 (n := 4) (by norm_num)
      convert this using 1
      norm_num [Finset.sum_range_succ, Nat.factorial]
    have he : Real.exp 1 ≤ 68 / 25 := by
      have := Real.exp_one_lt_d9
      norm_num at this ⊢
      linarith
    have hsplit : Real.exp x = Real.exp 1 * Real.exp (x - 1) := by
      rw [← Real.exp_add]
      ring_nf
    rw [hsplit]
    calc Real.exp 1 * Real.exp (x - 1) ≤ 68 / 25 * Real.exp (x - 1) := by
          gcongr
      _ ≤ 68 / 25 *
          (1 + (x - 1) + (x - 1) ^ 2 / 2 + (x - 1) ^ 3 / 6 + (x - 1) ^ 4 * 5 / 96) := by
          gcongr
      _ ≤ 1 + x + x ^ 2 := by
          nlinarith [mul_nonneg hy0 h34, mul_nonneg (mul_nonneg hy0 hy0) h34,
            mul_nonneg (mul_nonneg (mul_nonneg hy0 hy0) hy0) h34]

/-- One-column exponential moment of the Tardos weight, generalizing the
computation in Tardos 2008, Section 3 (proof of Theorem 1), where the constant
`α = 1 / (10 c)` is fixed before the moment is factored: here, for arbitrary
`p ≤ 1`, `0 ≤ α` with `α² ≤ 3 p`, `E[exp (α U)] ≤ 1 + α²` for the weight `U` of
a `Bernoulli(p)` bit. Tardos's constants `α = 1 / (10 c)` and `p ≥ 1 / (300 c)`
satisfy `α² ≤ 3 p` for `c ≥ 1`. -/
theorem tardosWeight_exp_mean_le {p α : ℝ} (hp1 : p ≤ 1) (hα : 0 ≤ α)
    (hαp : α ^ 2 ≤ 3 * p) :
    p * Real.exp (α * tardosWeight p true) + (1 - p) * Real.exp (α * tardosWeight p false) ≤
      1 + α ^ 2 := by
  rcases hα.eq_or_lt with rfl | hα
  · simp
  have hp0 : 0 < p := by nlinarith [sq_pos_of_pos hα]
  have h1p : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hwt : α * tardosWeight p true ≤ 7 / 4 := by
    have hsq : (α * tardosWeight p true) ^ 2 ≤ 3 := by
      rw [tardosWeight_true, mul_pow, Real.sq_sqrt (div_nonneg h1p hp0.le), ← mul_div_assoc,
        div_le_iff₀ hp0]
      nlinarith [sq_nonneg α]
    nlinarith
  have hwf : α * tardosWeight p false ≤ 7 / 4 := by
    rw [tardosWeight_false, mul_neg]
    have := mul_nonneg hα.le (Real.sqrt_nonneg (p / (1 - p)))
    linarith
  have h1 := exp_le_one_add_add_sq hwt
  have h2 := exp_le_one_add_add_sq hwf
  have hmean := tardosWeight_mean_eq_zero hp0.le hp1
  have hvar := tardosWeight_sq_mean_le_one hp0.le hp1
  calc p * Real.exp (α * tardosWeight p true) + (1 - p) * Real.exp (α * tardosWeight p false)
      ≤ p * (1 + α * tardosWeight p true + (α * tardosWeight p true) ^ 2) +
          (1 - p) * (1 + α * tardosWeight p false + (α * tardosWeight p false) ^ 2) := by
        gcongr
    _ = 1 + α * (p * tardosWeight p true + (1 - p) * tardosWeight p false) +
          α ^ 2 * (p * tardosWeight p true ^ 2 + (1 - p) * tardosWeight p false ^ 2) := by
        ring
    _ ≤ 1 + α ^ 2 := by
        rw [hmean, mul_zero, add_zero]
        nlinarith [sq_nonneg α]

/-! ### Exponential moment of the score -/

/-- Exponential moment of the Tardos score under `biasCodebookPMF p`: the rows
and columns are independent, so `E[exp (α S_i(y))]` is the product over the
columns `j` with `y j = true` of the one-column moments (Tardos 2008, Section 3,
proof of Theorem 1). -/
theorem sum_biasCodebookPMF_mul_exp_tardosScore {n d : ℕ} (p : Fin d → unitInterval) (α : ℝ)
    (y : Word d) (i : Fin n) :
    ∑ C : Codebook n d, (biasCodebookPMF p C).toReal *
        Real.exp (α * tardosScore (fun j => (p j : ℝ)) C y i) =
      ∏ j : Fin d, if y j then
        (p j : ℝ) * Real.exp (α * tardosWeight (p j) true) +
          (1 - (p j : ℝ)) * Real.exp (α * tardosWeight (p j) false)
      else 1 := by
  classical
  let f : Fin d → Bool → ℝ := fun j b => if b then (p j : ℝ) else 1 - (p j : ℝ)
  let g : Fin d → Bool → ℝ := fun j b =>
    Real.exp (α * (if y j then tardosWeight (p j) b else 0))
  have hrow : ∀ C : Codebook n d, (biasCodebookPMF p C).toReal *
      Real.exp (α * tardosScore (fun j => (p j : ℝ)) C y i) =
      ∏ i' : Fin n, ∏ j : Fin d, (f j (C i' j) * if i' = i then g j (C i' j) else 1) := by
    intro C
    have hm : (biasCodebookPMF p C).toReal = ∏ i' : Fin n, ∏ j : Fin d, f j (C i' j) := by
      rw [biasCodebookPMF_apply, ENNReal.toReal_prod]
      refine Finset.prod_congr rfl fun i' _ => ?_
      rw [ENNReal.toReal_prod]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [bernoulliMass, f]
      split_ifs
      · exact ENNReal.toReal_ofReal (p j).2.1
      · rw [unitInterval.coe_symm_eq]
        exact ENNReal.toReal_ofReal (sub_nonneg.mpr (p j).2.2)
    have he : Real.exp (α * tardosScore (fun j => (p j : ℝ)) C y i) =
        ∏ j : Fin d, g j (C i j) := by
      rw [tardosScore_def, Finset.mul_sum, Real.exp_sum]
    rw [hm, he]
    simp only [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [Finset.sum_congr rfl fun C _ => hrow C]
  rw [← Fintype.prod_sum (fun (i' : Fin n) (row : Word d) =>
    ∏ j : Fin d, (f j (row j) * if i' = i then g j (row j) else 1))]
  have hinner : ∀ i' : Fin n,
      ∑ row : Word d, ∏ j : Fin d, (f j (row j) * if i' = i then g j (row j) else 1) =
        ∏ j : Fin d, ((p j : ℝ) * (if i' = i then g j true else 1) +
          (1 - (p j : ℝ)) * (if i' = i then g j false else 1)) := by
    intro i'
    rw [← Fintype.prod_sum (fun (j : Fin d) (b : Bool) =>
      f j b * if i' = i then g j b else 1)]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fintype.sum_bool]
    simp [f]
  simp only [hinner]
  rw [Finset.prod_eq_single i]
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp only [ite_true, g]
    split_ifs <;> simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ### Accusation probability of a fixed user -/

/-- Exponential-moment bound on the probability that the Tardos rule accuses
user `i` on a fixed word `y` with threshold `Z`, when the codebook is drawn
from `biasCodebookPMF p`, `0 ≤ α` and every bias is at least `α² / 3`: the
probability is at most `(1 + α²) ^ m * exp (-α Z)`, where `m` counts the ones
of `y`. This generalizes the Markov step in Tardos 2008, Section 3 (proof of
Theorem 1), which fixes `α = 1 / (10 c)` before applying Markov's inequality. The word `y` does not depend on the codebook, which models an
innocent user whose row the pirates never see. -/
theorem tardosAccuses_prob_le {n d : ℕ} (p : Fin d → unitInterval) {α : ℝ} (hα : 0 ≤ α)
    (hαp : ∀ j, α ^ 2 ≤ 3 * (p j : ℝ)) (Z : ℝ) (y : Word d) (i : Fin n) :
    ((biasCodebookPMF (n := n) p).toOuterMeasure
        {C | TardosAccuses (fun j => (p j : ℝ)) Z C y i}).toReal ≤
      (1 + α ^ 2) ^ (Finset.univ.filter fun j => y j = true).card * Real.exp (-(α * Z)) := by
  classical
  set E : Set (Codebook n d) := {C | TardosAccuses (fun j => (p j : ℝ)) Z C y i} with hE
  have hfin : ∀ C ∈ (Finset.univ : Finset (Codebook n d)),
      E.indicator (biasCodebookPMF (n := n) p) C ≠ ⊤ := by
    intro C _
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      ((Set.indicator_le_self _ _ C).trans (PMF.coe_le_one _ C))
  rw [PMF.toOuterMeasure_apply_fintype, ENNReal.toReal_sum hfin]
  calc ∑ C, (E.indicator (biasCodebookPMF (n := n) p) C).toReal
      ≤ ∑ C, (biasCodebookPMF (n := n) p C).toReal *
          Real.exp (α * tardosScore (fun j => (p j : ℝ)) C y i) * Real.exp (-(α * Z)) := by
        refine Finset.sum_le_sum fun C _ => ?_
        have h0 : 0 ≤ (biasCodebookPMF (n := n) p C).toReal := ENNReal.toReal_nonneg
        by_cases hC : C ∈ E
        · rw [Set.indicator_of_mem hC]
          have hZ : Z < tardosScore (fun j => (p j : ℝ)) C y i := hC
          have h1 : 1 ≤ Real.exp (α * tardosScore (fun j => (p j : ℝ)) C y i) *
              Real.exp (-(α * Z)) := by
            rw [← Real.exp_add]
            apply Real.one_le_exp
            nlinarith
          calc (biasCodebookPMF (n := n) p C).toReal
              = (biasCodebookPMF (n := n) p C).toReal * 1 := (mul_one _).symm
            _ ≤ _ := by
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left h1 h0
        · rw [Set.indicator_of_notMem hC, ENNReal.toReal_zero]
          positivity
    _ = (∑ C, (biasCodebookPMF (n := n) p C).toReal *
          Real.exp (α * tardosScore (fun j => (p j : ℝ)) C y i)) * Real.exp (-(α * Z)) := by
        rw [Finset.sum_mul]
    _ = (∏ j : Fin d, if y j then
          (p j : ℝ) * Real.exp (α * tardosWeight (p j) true) +
            (1 - (p j : ℝ)) * Real.exp (α * tardosWeight (p j) false)
        else 1) * Real.exp (-(α * Z)) := by
        rw [sum_biasCodebookPMF_mul_exp_tardosScore]
    _ ≤ (1 + α ^ 2) ^ (Finset.univ.filter fun j => y j = true).card *
          Real.exp (-(α * Z)) := by
        gcongr ?_ * _
        rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
        calc ∏ j ∈ Finset.univ.filter (fun j => y j = true),
              ((p j : ℝ) * Real.exp (α * tardosWeight (p j) true) +
                (1 - (p j : ℝ)) * Real.exp (α * tardosWeight (p j) false))
            ≤ ∏ _j ∈ Finset.univ.filter (fun j => y j = true), (1 + α ^ 2) := by
              refine Finset.prod_le_prod₀ (fun j _ => ?_) (fun j _ => ?_)
              · exact add_nonneg (mul_nonneg (p j).2.1 (Real.exp_pos _).le)
                  (mul_nonneg (sub_nonneg.mpr (p j).2.2) (Real.exp_pos _).le)
              · exact tardosWeight_exp_mean_le (p j).2.2 hα (hαp j)
          _ = (1 + α ^ 2) ^ (Finset.univ.filter fun j => y j = true).card :=
              Finset.prod_const _

/-- Tardos (2008), Theorem 1, conditioned on the biases and the pirated word as
in its proof (Section 3): with integers `c ≥ 1` and `k` satisfying
`k ≥ log (1 / ε)` (Tardos takes the integer `k = ⌈log (1 / ε)⌉`), `0 < ε < 1`,
length `d = 100 c² k`, threshold
`Z = 20 c k` and every bias at least `1 / (300 c)`, the probability over
`biasCodebookPMF p` that the Tardos rule accuses user `i` on a fixed word `y`
is below `ε`. -/
theorem tardos_soundness_fixed_bias {n d c k : ℕ} (hc : 1 ≤ c) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) (hk : Real.log (1 / ε) ≤ k) (hd : d = 100 * c ^ 2 * k)
    (p : Fin d → unitInterval) (hp : ∀ j, 1 / (300 * c : ℝ) ≤ (p j : ℝ)) (y : Word d) (i : Fin n) :
    ((biasCodebookPMF (n := n) p).toOuterMeasure
        {C | TardosAccuses (fun j => (p j : ℝ)) (20 * c * k) C y i}).toReal < ε := by
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hc0 : (0 : ℝ) < c := by linarith
  set α : ℝ := 1 / (10 * c) with hαdef
  have hα0 : 0 < α := by positivity
  have hαt : α ^ 2 ≤ 3 * (1 / (300 * c : ℝ)) := by
    rw [hαdef, div_pow, one_pow, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hαp : ∀ j, α ^ 2 ≤ 3 * (p j : ℝ) := fun j => hαt.trans (by linarith [hp j])
  refine (tardosAccuses_prob_le p hα0.le hαp _ y i).trans_lt ?_
  have hlog : 0 < Real.log (1 / ε) :=
    Real.log_pos (by rw [one_div]; exact (one_lt_inv₀ hε0).mpr hε1)
  have hk0 : (0 : ℝ) < k := hlog.trans_le hk
  have hαZ : α * (20 * c * k) = 2 * k := by
    rw [hαdef]
    field_simp
    ring
  have hαd : α ^ 2 * d = k := by
    rw [hαdef, hd]
    push_cast
    field_simp
    norm_num
  have hexpk : Real.exp (-(k : ℝ)) ≤ ε := by
    have : -(k : ℝ) ≤ Real.log ε := by
      rw [one_div, Real.log_inv] at hk
      linarith
    calc Real.exp (-(k : ℝ)) ≤ Real.exp (Real.log ε) := Real.exp_le_exp.mpr this
      _ = ε := Real.exp_log hε0
  have hmd : (Finset.univ.filter fun j => y j = true).card ≤ d :=
    (Finset.card_filter_le _ _).trans (by simp)
  rw [hαZ]
  rcases Nat.eq_zero_or_pos (Finset.univ.filter fun j => y j = true).card with h0 | hpos
  · rw [h0, pow_zero, one_mul]
    calc Real.exp (-(2 * k : ℝ)) < Real.exp (-(k : ℝ)) := Real.exp_lt_exp.mpr (by linarith)
      _ ≤ ε := hexpk
  · have hlt : (1 + α ^ 2) ^ (Finset.univ.filter fun j => y j = true).card <
        Real.exp (α ^ 2 * d) := by
      calc (1 + α ^ 2) ^ (Finset.univ.filter fun j => y j = true).card
          < Real.exp (α ^ 2) ^ (Finset.univ.filter fun j => y j = true).card := by
            refine pow_lt_pow_left₀ ?_ (by positivity) hpos.ne'
            have := Real.add_one_lt_exp (x := α ^ 2) (by positivity)
            linarith
        _ = Real.exp (α ^ 2 * (Finset.univ.filter fun j => y j = true).card) := by
            rw [← Real.exp_nat_mul, mul_comm]
        _ ≤ Real.exp (α ^ 2 * d) := by
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmd) (by positivity)
    calc (1 + α ^ 2) ^ (Finset.univ.filter fun j => y j = true).card * Real.exp (-(2 * k : ℝ))
        < Real.exp (α ^ 2 * d) * Real.exp (-(2 * k : ℝ)) := by
          gcongr
      _ = Real.exp (-(k : ℝ)) := by
          rw [← Real.exp_add, hαd]
          ring_nf
      _ ≤ ε := hexpk

end CSLibExt.Privacy.Fingerprinting
