/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# The Luria–Delbrück distribution (Lea–Coulson model)

In the fluctuation test of Luria and Delbrück (1943), mutations to resistance occur during the
exponential growth of a bacterial culture, and the number of resistant cells in the final
culture is counted. In the model of Lea and Coulson (1949), cells divide at rate `1`, a
mutant clone founded `τ` time units before the end has a geometric size
`P(size = j) = e^{-τ} (1 - e^{-τ})^{j - 1}` (`j ≥ 1`, the Yule process), and, in the limit of a
large final population `N` with `m = μ N` expected mutations, the founding times of mutant
clones are the points of a Poisson process with intensity `m e^{-τ}` on `(0, ∞)`.

Consequently the number of mutant clones is Poisson(`m`), their founding times are
i.i.d. with density `e^{-τ}`, and each clone has the mixed size law

`P(size = j) = ∫₀^∞ e^{-τ} e^{-τ} (1 - e^{-τ})^{j-1} dτ = 1 / (j (j + 1))`
(`integral_cloneSize`, `cloneProb`).

The number of mutants is the compound-Poisson sum of `Poisson(m)` independent clone sizes; its
law is `ldPmf m` (the **Luria–Delbrück distribution** in the Lea–Coulson form).

## Main definitions

* `cloneProb j = 1 / (j (j + 1))` for `j ≥ 1` and `0` for `j = 0`.
* `convPow p k`: the `k`-fold convolution power of a sequence `p : ℕ → ℝ`.
* `ldPmf m n = ∑_{k ≤ n} e^{-m} m^k / k! · cloneProb^{*k}(n)`.

## Main results

* `integral_cloneSize`: the geometric clone size mixed over the founding-time density `e^{-τ}`
  is `1 / (j (j + 1))`.
* `hasSum_cloneProb`, `hasSum_cloneProb_mul_pow`: the clone law sums to `1`, and its generating
  function is `h(z) = 1 + (1 / z - 1) log (1 - z)` for `0 < z < 1`.
* `ldPmf_zero`, `p0_method`: `P(no mutants) = e^{-m}`, so `m = -log p₀` (the `p₀` method of
  Luria and Delbrück).
* `hasSum_ldPmf`: the Luria–Delbrück probabilities sum to `1` (for `m ≥ 0`).
* `hasSum_ldPmf_mul_pow`: the **Lea–Coulson generating function**
  `∑ₙ pₙ zⁿ = exp (m (1 / z - 1) log (1 - z)) = (1 - z)^{m (1 - z) / z}` for `0 < z < 1`.
* `ldPmf_recursion`: the **Ma–Sandri–Sarkar recursion**
  `pₙ = (m / n) ∑_{i < n} pᵢ / (n - i + 1)` for `n ≥ 1`.

The derivation of the Poisson founding process from a finite-`N` growth model (the limit
`N → ∞`) is not formalized; the model is stated at the limit, as in Lea–Coulson.

## References

* S. E. Luria, M. Delbrück, *Mutations of bacteria from virus sensitivity to virus
  resistance*, Genetics 28 (1943), 491–511.
* D. E. Lea, C. A. Coulson, *The distribution of the numbers of mutants in bacterial
  populations*, J. Genet. 49 (1949), 264–285.
* W. T. Ma, G. vH. Sandri, S. Sarkar, *Analysis of the Luria–Delbrück distribution using
  discrete convolution powers*, J. Appl. Probab. 29 (1992), 255–267.
* Q. Zheng, *Progress of a half century in the study of the Luria–Delbrück distribution*,
  Math. Biosci. 162 (1999), 1–32.
-/

@[expose] public section

open Finset Real MeasureTheory Set
open Filter

namespace MathlibExt.Biology.PopulationGenetics.LuriaDelbruck

/-- The **Lea–Coulson clone-size law** `P(size = j) = 1 / (j (j + 1))` for `j ≥ 1`
(`P(size = 0) = 0`). -/
noncomputable def cloneProb (j : ℕ) : ℝ :=
  if j = 0 then 0 else 1 / ((j : ℝ) * (j + 1))

/-- The `k`-fold convolution power of a sequence on `ℕ`: `p^{*0} = δ₀` and
`p^{*(k+1)}(n) = ∑_{i ≤ n} p(i) p^{*k}(n - i)`. -/
noncomputable def convPow (p : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n => ∑ i ∈ range (n + 1), p i * convPow p k (n - i)

/-- The **Luria–Delbrück probability** of `n` mutants with expected mutation number `m`: the
compound-Poisson law `∑_k e^{-m} m^k / k! · cloneProb^{*k}(n)`. Since clones have size at
least `1`, only `k ≤ n` contribute. -/
noncomputable def ldPmf (m : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1), exp (-m) * m ^ k / k.factorial * convPow cloneProb k n

/-- The clone-size generating function `h(z) = 1 + (1 / z - 1) log (1 - z)`. -/
noncomputable def clonePgf (z : ℝ) : ℝ :=
  1 + (1 / z - 1) * log (1 - z)

private theorem cloneProb_nonneg (j : ℕ) : 0 ≤ cloneProb j := by
  unfold cloneProb
  split_ifs <;> positivity

private theorem cloneProb_succ (j : ℕ) :
    cloneProb (j + 1) = 1 / (j + 1 : ℝ) - 1 / (j + 2 : ℝ) := by
  simp only [cloneProb, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
    Nat.cast_add, Nat.cast_one]
  have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (j : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

private theorem convPow_nonneg (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (k n : ℕ) :
    0 ≤ convPow p k n := by
  induction k generalizing n with
  | zero => simp only [convPow]; split_ifs <;> positivity
  | succ k ih =>
      exact sum_nonneg fun i _ => mul_nonneg (hp i) (ih (n - i))

private theorem convPow_support (p : ℕ → ℝ) (hp : p 0 = 0) (k n : ℕ)
    (hn : n < k) : convPow p k n = 0 := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
      apply sum_eq_zero
      intro i hi
      have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      by_cases h0 : i = 0
      · simp [h0, hp]
      · rw [ih (n - i) (by omega), mul_zero]

private theorem hasSum_convPow (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) {t : ℝ}
    (ht : HasSum p t) (k : ℕ) : HasSum (convPow p k) (t ^ k) := by
  induction k with
  | zero => simpa only [convPow, pow_zero] using (hasSum_ite_eq 0 (1 : ℝ))
  | succ k ih =>
      have hn : Summable (fun n => ‖convPow p k n‖) := by
        simpa only [Real.norm_of_nonneg (convPow_nonneg p hp k _)] using ih.summable
      have hp' : Summable (fun n => ‖p n‖) := by
        simpa only [Real.norm_of_nonneg (hp _)] using ht.summable
      simpa only [convPow, ht.tsum_eq, ih.tsum_eq, pow_succ'] using
        hasSum_sum_range_mul_of_summable_norm hp' hn

private theorem convPow_mul_pow (p : ℕ → ℝ) (z : ℝ) (k n : ℕ) :
    convPow (fun i => p i * z ^ i) k n = convPow p k n * z ^ n := by
  induction k generalizing n with
  | zero => simp only [convPow]; split_ifs <;> simp_all
  | succ k ih =>
      simp only [convPow, ih, sum_mul]
      apply sum_congr rfl
      intro i hi
      have h : i + (n - i) = n := by simp only [Finset.mem_range] at hi; omega
      rw [show z ^ n = z ^ i * z ^ (n - i) by rw [← pow_add, h]]
      ring

private theorem hasSum_compound (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hp0 : p 0 = 0)
    {t m : ℝ} (ht : HasSum p t) (hm : 0 ≤ m) :
    HasSum (fun n => ∑ k ∈ range (n + 1),
      exp (-m) * m ^ k / k.factorial * convPow p k n) (exp (-m) * exp (m * t)) := by
  let w : ℕ → ℝ := fun k => exp (-m) * m ^ k / k.factorial
  have hw (k : ℕ) : 0 ≤ w k := by dsimp [w]; positivity
  have hc (k : ℕ) : HasSum (fun n => w k * convPow p k n) (w k * t ^ k) :=
    (hasSum_convPow p hp ht k).mul_left (w k)
  have he : HasSum (fun k => w k * t ^ k) (exp (-m) * exp (m * t)) := by
    have hexp : HasSum (fun k => (m * t) ^ k / k.factorial) (exp (m * t)) := by
      simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (m * t)
    convert hexp.mul_left (exp (-m)) using 1
    ext k
    dsimp [w]
    rw [mul_pow]
    ring
  have hs : Summable (fun x : ℕ × ℕ => w x.1 * convPow p x.1 x.2) := by
    apply (summable_prod_of_nonneg (fun x =>
      mul_nonneg (hw x.1) (convPow_nonneg p hp x.1 x.2))).mpr
    refine ⟨fun k => (hc k).summable, ?_⟩
    simpa only [(hc _).tsum_eq] using he.summable
  have H : HasSum (fun x : ℕ × ℕ => w x.1 * convPow p x.1 x.2)
      (exp (-m) * exp (m * t)) := by
    have hu := hs.hasSum.prod_fiberwise hc
    exact hu.unique he ▸ hs.hasSum
  have H' : HasSum (fun n => ∑' k, w k * convPow p k n)
      (exp (-m) * exp (m * t)) := by
    apply HasSum.prod_fiberwise ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr H)
    intro n
    exact (hs.prod_symm.prod_factor n).hasSum
  convert H' using 1
  ext n
  apply (tsum_eq_sum (s := range (n + 1)) ?_).symm
  intro k hk
  rw [convPow_support p hp0 k n (by simp only [Finset.mem_range] at hk; omega), mul_zero]

/-- **Clone-size law from the founding-time density**: a clone founded `τ` before the end has
geometric size `e^{-τ} (1 - e^{-τ})^{j-1}`; mixing over the founding-time density `e^{-τ}` on
`(0, ∞)` gives `1 / (j (j + 1))` for `j ≥ 1`. -/
theorem integral_cloneSize {j : ℕ} (hj : 1 ≤ j) :
    ∫ τ in Ioi (0 : ℝ), exp (-τ) * (exp (-τ) * (1 - exp (-τ)) ^ (j - 1)) = cloneProb j := by
  have hj0 : j ≠ 0 := by omega
  have hjR : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj0
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have hpow : j - 1 + 1 = j := by omega
  let F : ℝ → ℝ := fun τ =>
    (1 - exp (-τ)) ^ j / j - (1 - exp (-τ)) ^ (j + 1) / (j + 1)
  have hd (τ : ℝ) : HasDerivAt F
      (exp (-τ) * (exp (-τ) * (1 - exp (-τ)) ^ (j - 1))) τ := by
    have hb : HasDerivAt (fun τ : ℝ => 1 - exp (-τ)) (exp (-τ)) τ := by
      simpa using ((hasDerivAt_id τ).neg.exp).const_sub 1
    convert ((hb.pow j).div_const (j : ℝ)).sub
      ((hb.pow (j + 1)).div_const (j + 1 : ℝ)) using 1
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    field_simp
    rw [show (1 - exp (-τ)) ^ j =
      (1 - exp (-τ)) ^ (j - 1) * (1 - exp (-τ)) by
        rw [← hpow, pow_succ]
        simp only [Nat.add_sub_cancel]]
    ring
  have hl : Tendsto F atTop (nhds (1 / (j : ℝ) - 1 / (j + 1 : ℝ))) := by
    have hb : Tendsto (fun τ : ℝ => 1 - exp (-τ)) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub Real.tendsto_exp_neg_atTop_nhds_zero
    simpa [F] using ((hb.pow j).div_const (j : ℝ)).sub
      ((hb.pow (j + 1)).div_const (j + 1 : ℝ))
  have hi := integral_Ioi_of_hasDerivAt_of_nonneg' (fun τ _ => hd τ)
    (fun τ hτ => mul_nonneg (exp_pos _).le (mul_nonneg (exp_pos _).le
      (pow_nonneg (by
        have h := exp_le_one_iff.mpr (neg_nonpos.mpr hτ.le)
        linarith) _))) hl
  rw [hi]
  simp [F, hj0, cloneProb]
  field_simp
  ring

/-- The clone-size law sums to `1`. -/
theorem hasSum_cloneProb : HasSum cloneProb 1 := by
  have hsum (N : ℕ) :
      ∑ i ∈ range N, cloneProb (i + 1) = 1 - 1 / (N + 1 : ℝ) := by
    induction N with
    | zero => norm_num
    | succ N ih =>
        rw [sum_range_succ, ih, cloneProb_succ]
        push_cast
        ring
  apply (hasSum_nat_add_iff' 1).mp
  simp only [sum_range_one, cloneProb, ↓reduceIte, sub_zero]
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun i => cloneProb_nonneg (i + 1)) 1).mpr
  simp_rw [hsum]
  simpa using (tendsto_const_nhds.sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

/-- **Clone-size generating function**: for `0 < z < 1`,
`∑ⱼ zʲ / (j (j + 1)) = 1 + (1 / z - 1) log (1 - z)`. -/
theorem hasSum_cloneProb_mul_pow {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasSum (fun j => cloneProb j * z ^ j) (clonePgf z) := by
  have hz : |z| < 1 := by rwa [abs_of_pos hz0]
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one hz
  have ht : HasSum (fun n : ℕ => z ^ n / (n + 1)) (-log (1 - z) / z) := by
    convert hs.div_const z using 1
    ext n
    rw [pow_succ]
    field_simp
  have hu : HasSum (fun n : ℕ => z ^ (n + 1) / (n + 2))
      (-log (1 - z) / z - 1) := by
    simpa only [Nat.cast_add, Nat.cast_one, sum_range_one, pow_zero, one_div_one,
      add_assoc, one_add_one_eq_two, Nat.cast_zero, zero_add] using (hasSum_nat_add_iff' 1).mpr ht
  apply (hasSum_nat_add_iff' 1).mp
  simp only [sum_range_one, show cloneProb 0 = 0 by simp [cloneProb], zero_mul, sub_zero]
  convert hs.sub hu using 1
  · ext n
    rw [cloneProb_succ]
    ring
  · unfold clonePgf
    ring

/-- **`p₀`**: the probability of no mutants is `e^{-m}`. -/
theorem ldPmf_zero (m : ℝ) : ldPmf m 0 = exp (-m) := by
  simp [ldPmf, convPow]

/-- **The `p₀` method** (Luria–Delbrück 1943): the expected number of mutations is recovered
from the proportion of cultures with no mutants, `m = -log p₀`. -/
theorem p0_method (m : ℝ) : m = -log (ldPmf m 0) := by
  rw [ldPmf_zero, log_exp, neg_neg]

/-- The Luria–Delbrück probabilities are nonnegative for `m ≥ 0`. -/
theorem ldPmf_nonneg {m : ℝ} (hm : 0 ≤ m) (n : ℕ) : 0 ≤ ldPmf m n := by
  unfold ldPmf
  apply sum_nonneg
  intro k hk
  exact mul_nonneg (div_nonneg (mul_nonneg (exp_pos _).le (pow_nonneg hm _))
    (Nat.cast_nonneg _)) (convPow_nonneg cloneProb cloneProb_nonneg k n)

/-- The Luria–Delbrück probabilities sum to `1` (for `m ≥ 0`). -/
theorem hasSum_ldPmf {m : ℝ} (hm : 0 ≤ m) : HasSum (ldPmf m) 1 := by
  convert hasSum_compound cloneProb cloneProb_nonneg (by simp [cloneProb])
    hasSum_cloneProb hm using 1
  · rfl
  rw [mul_one, ← exp_add, neg_add_cancel, exp_zero]

/-- **Lea–Coulson generating function**: for `m ≥ 0` and `0 < z < 1`,
`∑ₙ pₙ zⁿ = exp (m (h(z) - 1)) = exp (m (1 / z - 1) log (1 - z))`. -/
theorem hasSum_ldPmf_mul_pow {m : ℝ} (hm : 0 ≤ m) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasSum (fun n => ldPmf m n * z ^ n) (exp (m * ((1 / z - 1) * log (1 - z)))) := by
  have h := hasSum_compound (fun i => cloneProb i * z ^ i)
    (fun i => mul_nonneg (cloneProb_nonneg i) (pow_nonneg hz0.le i))
    (by simp [cloneProb]) (hasSum_cloneProb_mul_pow hz0 hz1) hm
  simp only [convPow_mul_pow, ← mul_assoc, ← sum_mul] at h
  convert h using 1
  · rfl
  rw [← exp_add]
  congr 1
  unfold clonePgf
  ring

/-- The Lea–Coulson generating function in power form:
`exp (m (1 / z - 1) log (1 - z)) = (1 - z)^{m (1 - z) / z}` for `z < 1`, `z ≠ 0`. -/
theorem exp_leaCoulson_eq_rpow (m : ℝ) {z : ℝ} (hz0 : z ≠ 0) (hz1 : z < 1) :
    exp (m * ((1 / z - 1) * log (1 - z))) = (1 - z) ^ (m * (1 - z) / z) := by
  rw [rpow_def_of_pos (by linarith)]
  congr 1
  field_simp

private theorem convPow_coeff (p : ℕ → ℝ) (k n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.mk p) ^ k) = convPow p k n := by
  induction k generalizing n with
  | zero => simp only [pow_zero, PowerSeries.coeff_one, convPow]
  | succ k ih =>
      rw [pow_succ', PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [PowerSeries.coeff_mk, ih, convPow]

private theorem cloneProb_weight (j : ℕ) :
    cloneProb (j + 1) * (j + 1 : ℝ) = 1 / (j + 2 : ℝ) := by
  rw [cloneProb_succ]
  have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (j : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

private theorem convPow_weight (k n : ℕ) :
    (n + 1 : ℝ) * convPow cloneProb (k + 1) (n + 1) =
      (k + 1 : ℝ) * ∑ i ∈ range (n + 1),
        convPow cloneProb k i / ((n + 1 : ℝ) - i + 1) := by
  have h := congrArg (PowerSeries.coeff n)
    (PowerSeries.derivative_pow (PowerSeries.mk cloneProb) (k + 1))
  rw [PowerSeries.coeff_derivative, convPow_coeff, mul_assoc,
    PowerSeries.coeff_natCast_mul, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [Nat.add_sub_cancel, convPow_coeff, PowerSeries.coeff_derivative,
    PowerSeries.coeff_mk, Nat.cast_add, Nat.cast_one, cloneProb_weight] at h
  rw [mul_comm] at h
  rw [h]
  congr 1
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [Nat.cast_sub hi']
  ring

/-- **Ma–Sandri–Sarkar recursion**: for `n ≥ 1`,
`pₙ = (m / n) ∑_{i < n} pᵢ / (n - i + 1)` (all real `m`). -/
theorem ldPmf_recursion (m : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ldPmf m n = m / n * ∑ i ∈ range n, ldPmf m i / ((n : ℝ) - i + 1) := by
  cases n with
  | zero => omega
  | succ n =>
      simp only [Nat.cast_add, Nat.cast_one]
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff (by positivity : (n : ℝ) + 1 ≠ 0)).mpr
      rw [mul_comm]
      let w : ℕ → ℝ := fun k => exp (-m) * m ^ k / k.factorial
      have hw (k : ℕ) : w (k + 1) * (k + 1 : ℝ) = m * w k := by
        dsimp [w]
        rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        have hk : (k : ℝ) + 1 ≠ 0 := by positivity
        have hf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
        field_simp
      have hzero : convPow cloneProb 0 (n + 1) = 0 := by simp [convPow]
      calc
        (n + 1 : ℝ) * ldPmf m (n + 1) =
            ∑ k ∈ range (n + 1), w (k + 1) *
              ((n + 1 : ℝ) * convPow cloneProb (k + 1) (n + 1)) := by
          unfold ldPmf
          rw [sum_range_succ']
          simp only [hzero, mul_zero, add_zero, mul_sum]
          apply sum_congr rfl
          intro k hk
          dsimp [w]
          ring
        _ = ∑ k ∈ range (n + 1), m * w k * ∑ i ∈ range (n + 1),
              convPow cloneProb k i / ((n + 1 : ℝ) - i + 1) := by
          apply sum_congr rfl
          intro k hk
          rw [convPow_weight, ← mul_assoc, hw]
        _ = m * ∑ i ∈ range (n + 1), ∑ k ∈ range (n + 1),
              w k * convPow cloneProb k i / ((n + 1 : ℝ) - i + 1) := by
          simp_rw [mul_sum]
          rw [sum_comm]
          apply sum_congr rfl
          intro i hi
          apply sum_congr rfl
          intro k hk
          ring
        _ = m * ∑ i ∈ range (n + 1), ldPmf m i / ((n + 1 : ℝ) - i + 1) := by
          congr 1
          apply sum_congr rfl
          intro i hi
          rw [← sum_div]
          congr 1
          change (∑ k ∈ range (n + 1), w k * convPow cloneProb k i) =
            ∑ k ∈ range (i + 1), w k * convPow cloneProb k i
          symm
          apply sum_subset (range_mono (by simp only [Finset.mem_range] at hi; omega))
          intro k hk hk'
          rw [convPow_support cloneProb (by simp [cloneProb]) k i
            (by simp only [Finset.mem_range] at hk'; omega), mul_zero]

end MathlibExt.Biology.PopulationGenetics.LuriaDelbruck
