/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.PoissonProcess
public import MathlibExt.Probability.BranchingProcess.LinearBirthDeath
public import MathlibExt.Probability.Distributions.NegativeBinomialSplitting
public import Mathlib.Probability.ProductMeasure
import MathlibExt.Probability.Distributions.NegativeBinomial
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.MeasurableSpace.NCard
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Probability.Independence.InfinitePi

/-!
# Negative binomial clone sizes under consecutive seeding

A primary tumour contains clones `i` of constant size. Cells of clone `i` arrive at a metastatic
site as a Poisson process of rate `λ_i`, starting at time `0` with an empty site, and each
arriving cell founds an independent linear birth–death process with division rate `b` and death
rate `d`, `b > d > 0`, the same for all clones (neutral diversity). With `k_i = λ_i / b`,
`ρ = 1 - d / b` and `r = b - d`, Heyde, Reiter, Naxerova and Nowak (2019, Eqs. [1] and [2])
show that the mean size of clone `i` is `ȳ_i(t) = (k_i / ρ) (e^{r t} - 1)`, the solution of
`ȳ_i' = r ȳ_i + λ_i`, `ȳ_i(0) = 0`, and that its size `y_i(t)` is negative binomial with shape
`k_i` and success probability `q(t) = ρ / (ρ + e^{r t} - 1) = k_i / (ȳ_i(t) + k_i)`, the same for
every clone; the clone sizes are independent.

**The model** (`IsClonalSeeding`). The arrivals of one clone are the arrival times of i.i.d.
exponential interarrival times, whose counting process `PoissonProcess.count` is a Poisson
process (`PoissonProcess.isPoissonProcess_count`). The clone size `cloneSize T X t` is the total
size at time `t` of the lineages founded by the cells that arrived in `[0, t]`. It depends on the
lineages only through their sizes at time `t`, so the model specifies these: given the arrival
times, they are independent, the lineage founded at time `s` having Kendall's law
`LinearBirthDeath.prob b d (t - s)` of a linear birth–death process started from one cell. The
model exists for every family of rates (`exists_isClonalSeeding`).

**The proof.** Conditioning on the first interarrival time gives the generating functional of the
arrivals: `E[1{N(t) = n} ∏_{j ≤ n} g(S_j)] = e^{-λ t} λ^n (∫_0^t g)^n / n!` for continuous
`g ≥ 0`. With `g(s)` the generating function of a lineage of age `t - s` (Kendall), this gives
`E z^{y(t)} = (q / (1 - (1 - q) z))^{λ / b}` (`IsClonalSeeding.lintegral_pow_cloneSize`), the
generating function of the negative binomial law; a law on `ℕ` is determined by its generating
function on `(0, 1)` (isolated zeros of analytic functions).

## Main definitions

* `successProb b d t`: `q(t) = ρ / (ρ + e^{r t} - 1)`.
* `meanSize lam b d t`: `ȳ(t) = (k / ρ) (e^{r t} - 1)`.
* `cloneSize T X t`: the clone size `y(t)`.
* `IsClonalSeeding P lam b d T X`: the seeding model of one clone.

## Main results

* `negBinomial_cloneSizes`: the mean, the negative binomial law and the independence of the clone
  sizes.
* `IsClonalSeeding.measureReal_cloneSize`: `P(y(t) = m) = NB(m; λ / b, q(t))`.
* `IsClonalSeeding.integral_cloneSize`: `E y(t) = ȳ(t)`.
* `IsClonalSeeding.lintegral_pow_cloneSize`: the generating function of `y(t)`.
* `hasDerivAt_meanSize`, `successProb_eq_div`: `ȳ' = r ȳ + λ` and `q = k / (ȳ + k)`.
* `iIndepFun_cloneSize`: clones with independent data have independent sizes.
* `exists_isClonalSeeding`: the model exists.

## References

* A. Heyde, J. G. Reiter, K. Naxerova and M. A. Nowak, *Consecutive seeding and transfer of
  genetic diversity in metastasis*, Proc. Natl. Acad. Sci. USA 116 (2019), 14129–14137,
  Eqs. [1] and [2].
* D. G. Kendall, *On the generalized "birth-and-death" process*, Ann. Math. Statist. 19 (1948),
  1–15.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal Nat

universe u

namespace MathlibExt.Biology.CancerGenomics.ConsecutiveSeeding

open MathlibExt.Probability ProbabilityTheory.PoissonProcess

/-! ### The generating function of a seeded lineage -/

/-- The denominator `b (1 - z) e^{(b - d) u} + b z - d` of the generating function of a
lineage of age `u` evaluated at `z`. -/
private noncomputable def lineageDenom (b d u z : ℝ) : ℝ :=
  b * (1 - z) * exp ((b - d) * u) + b * z - d

/-- The probability generating function `E z^{X(u)} = 1 - (b - d) e^{(b-d)u} (1 - z) / D` of
the size `X(u)` of a linear birth–death lineage of age `u` started from one cell, with
`D = lineageDenom b d u z`. -/
private noncomputable def lineagePGF (b d u z : ℝ) : ℝ :=
  1 - (b - d) * exp ((b - d) * u) * (1 - z) / lineageDenom b d u z

private lemma lineageDenom_pos {b d u z : ℝ} (hdb : d < b) (hb : 0 < b) (hu : 0 ≤ u) (hz1 : z ≤ 1) :
    0 < lineageDenom b d u z := by
  have hE : 1 ≤ exp ((b - d) * u) := one_le_exp (mul_nonneg (by linarith) hu)
  unfold lineageDenom
  have : b * (1 - z) * 1 ≤ b * (1 - z) * exp ((b - d) * u) :=
    mul_le_mul_of_nonneg_left hE (mul_nonneg hb.le (by linarith))
  nlinarith

/-- **Kendall's generating function.** For `0 ≤ d < b`, `u ≥ 0` and `0 ≤ z ≤ 1`, the law of a
linear birth–death lineage of age `u` started from one cell has generating function
`lineagePGF b d u z`. -/
private theorem hasSum_prob_mul_pow {b d u z : ℝ} (hd : 0 ≤ d) (hdb : d < b) (hu : 0 ≤ u)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    HasSum (fun m : ℕ ↦ LinearBirthDeath.prob b d u m * z ^ m) (lineagePGF b d u z) := by
  have hb : 0 < b := by linarith
  have hne : b ≠ d := ne_of_gt hdb
  set E := exp ((b - d) * u) with hE_def
  have hE : 1 ≤ E := one_le_exp (mul_nonneg (by linarith) hu)
  have hden : 0 < b * E - d := by nlinarith
  have hα : LinearBirthDeath.extinctionProb b d u = d * (E - 1) / (b * E - d) := by
    simp [LinearBirthDeath.extinctionProb, hne, hE_def]
  have hβ : LinearBirthDeath.geomRatio b d u = b * (E - 1) / (b * E - d) := by
    simp [LinearBirthDeath.geomRatio, hne, hE_def]
  set β := b * (E - 1) / (b * E - d) with hβ_def
  have hβ0 : 0 ≤ β := div_nonneg (mul_nonneg hb.le (by linarith)) hden.le
  have hβ1 : β < 1 := by
    rw [div_lt_one hden]
    linarith
  have hβz0 : 0 ≤ β * z := mul_nonneg hβ0 hz0
  have hβz1 : β * z < 1 := by nlinarith
  have hg := (hasSum_geometric_of_lt_one hβz0 hβz1).mul_left
    ((1 - d * (E - 1) / (b * E - d)) * (1 - β) * z)
  have hD := lineageDenom_pos hdb hb hu hz1 (d := d)
  refine (hasSum_nat_add_iff' 1).1 ?_
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one]
  convert hg using 1
  · funext n
    simp only [LinearBirthDeath.prob, hα, hβ]
    ring_nf
  · rw [show LinearBirthDeath.prob b d u 0 = d * (E - 1) / (b * E - d) from hα]
    unfold lineagePGF lineageDenom
    rw [← hE_def]
    have hDpos : 0 < b * (1 - z) * E + b * z - d := by
      unfold lineageDenom at hD
      rw [← hE_def] at hD
      exact hD
    rw [hβ_def]
    clear_value E β
    have hden' : b * E - d ≠ 0 := hden.ne'
    have hD' : b * (1 - z) * E + b * z - d ≠ 0 := hDpos.ne'
    have h1βz : 1 - b * (E - 1) / (b * E - d) * z ≠ 0 := by
      rw [div_mul_eq_mul_div, one_sub_div hden']
      refine div_ne_zero ?_ hden'
      intro h; apply hD'; linear_combination h
    have hD'' : b * E - b * E * z + b * z - d ≠ 0 := by
      intro h; apply hD'; linear_combination h
    have hD3 : E * b - E * b * z + b * z - d ≠ 0 := by
      intro h; apply hD'; linear_combination h
    have e1 : 1 - d * (E - 1) / (b * E - d) = (b - d) * E / (b * E - d) := by
      rw [one_sub_div hden']; congr 1; ring
    have e2 : 1 - b * (E - 1) / (b * E - d) = (b - d) / (b * E - d) := by
      rw [one_sub_div hden']; congr 1; ring
    have e3 : 1 - b * (E - 1) / (b * E - d) * z = (b * (1 - z) * E + b * z - d) / (b * E - d) := by
      rw [div_mul_eq_mul_div, one_sub_div hden']; congr 1; ring
    rw [e1, e2, e3]
    clear e1 e2 e3 h1βz hD'' hD3 hg
    generalize hC : b * E - d = C at *
    generalize hDD : b * (1 - z) * E + b * z - d = D at *
    field_simp
    subst hC hDD
    ring

/-- `1 - E z^{X(u)}` integrates in closed form: `∫_0^t (1 - lineagePGF b d u z) du =
log (lineageDenom b d t z / (b - d)) / b`. -/
private theorem integral_one_sub_lineagePGF {b d z t : ℝ} (hdb : d < b) (hb : 0 < b) (hz1 : z ≤ 1)
    (ht : 0 ≤ t) :
    ∫ u in (0 : ℝ)..t, (1 - lineagePGF b d u z) = log (lineageDenom b d t z / (b - d)) / b := by
  have hbd : 0 < b - d := by linarith
  have hderiv : ∀ u ∈ uIcc (0 : ℝ) t,
      HasDerivAt (fun u ↦ log (lineageDenom b d u z) / b) (1 - lineagePGF b d u z) u := by
    intro u hu
    rw [uIcc_of_le ht] at hu
    have hD := lineageDenom_pos hdb hb hu.1 hz1 (d := d)
    have hE : HasDerivAt (fun u ↦ lineageDenom b d u z)
        (b * (1 - z) * (exp ((b - d) * u) * (b - d))) u := by
      unfold lineageDenom
      have := ((hasDerivAt_id u).const_mul (b - d)).exp.const_mul (b * (1 - z))
      simpa [mul_comm, mul_left_comm, mul_assoc] using (this.add_const (b * z)).sub_const d
    convert (hE.log hD.ne').div_const b using 1
    unfold lineagePGF
    field_simp
    ring
  have hcont : ContinuousOn (fun u ↦ 1 - lineagePGF b d u z) (uIcc 0 t) := by
    intro u hu
    rw [uIcc_of_le ht] at hu
    have hD := lineageDenom_pos hdb hb hu.1 hz1 (d := d)
    have hD' : b * (1 - z) * exp ((b - d) * u) + b * z - d ≠ 0 := hD.ne'
    unfold lineagePGF lineageDenom
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := exact hD'))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have h0 : lineageDenom b d 0 z = b - d := by unfold lineageDenom; simp; ring
  rw [h0, log_div (lineageDenom_pos hdb hb ht hz1).ne' hbd.ne']
  ring

private lemma lineagePGF_nonneg {b d u z : ℝ} (hd : 0 ≤ d) (hdb : d < b) (hu : 0 ≤ u) (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) : 0 ≤ lineagePGF b d u z :=
  (hasSum_prob_mul_pow hd hdb hu hz0 hz1).nonneg fun m ↦
    mul_nonneg (LinearBirthDeath.prob_nonneg (by linarith) hd hu m) (pow_nonneg hz0 m)

/-- The generating function of a lineage founded at time `s`, evaluated at time `t` (age
`max (t - s) 0`), is continuous in `s`. -/
private lemma continuous_lineagePGF_age {b d z : ℝ} (hdb : d < b) (hb : 0 < b) (hz1 : z ≤ 1)
    (t : ℝ) :
    Continuous fun s ↦ lineagePGF b d (max (t - s) 0) z := by
  have hD : ∀ s : ℝ, b * (1 - z) * exp ((b - d) * max (t - s) 0) + b * z - d ≠ 0 := fun s ↦
    (lineageDenom_pos hdb hb (le_max_right _ _) hz1 (d := d)).ne'
  unfold lineagePGF lineageDenom
  fun_prop (disch := exact hD _)

private lemma measurable_prob (b d : ℝ) (k : ℕ) :
    Measurable fun u ↦ LinearBirthDeath.prob b d u k := by
  cases k with
  | zero =>
    simp only [LinearBirthDeath.prob, LinearBirthDeath.extinctionProb]
    split_ifs <;> fun_prop
  | succ k =>
    simp only [LinearBirthDeath.prob, LinearBirthDeath.extinctionProb,
      LinearBirthDeath.geomRatio]
    split_ifs <;> fun_prop

/-- `∏_j ∑_k f_j(k) = ∑_{m : Fin n → ℕ} ∏_j f_j(m_j)` in `ℝ≥0∞`. -/
private lemma tsum_prod_fin (n : ℕ) (f : Fin n → ℕ → ℝ≥0∞) :
    ∑' m : Fin n → ℕ, ∏ j, f j (m j) = ∏ j, ∑' k, f j k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) ↦ ℕ).tsum_eq, tsum_prod', Fin.prod_univ_succ]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    simp_rw [ENNReal.tsum_mul_left, ih (fun j ↦ f j.succ), ENNReal.tsum_mul_right]

/-! ### Negative binomial generating function and uniqueness -/

/-- The negative binomial success probability `q(t) = ρ / (ρ + e^{r t} - 1)` with
`ρ = 1 - d / b` and `r = b - d`. -/
noncomputable def successProb (b d t : ℝ) : ℝ :=
  (1 - d / b) / (1 - d / b + exp ((b - d) * t) - 1)

/-- The mean clone size `ȳ(t) = (k / ρ) (e^{r t} - 1)` with `k = lam / b`, `ρ = 1 - d / b` and
`r = b - d`. -/
noncomputable def meanSize (lam b d t : ℝ) : ℝ :=
  lam / b / (1 - d / b) * (exp ((b - d) * t) - 1)

private lemma successProb_pos {b d t : ℝ} (hdb : d < b) (hb : 0 < b) (ht : 0 ≤ t) :
    0 < successProb b d t := by
  have hρ : 0 < 1 - d / b := by rw [sub_pos, div_lt_one hb]; exact hdb
  have hE : 1 ≤ exp ((b - d) * t) := one_le_exp (mul_nonneg (by linarith) ht)
  unfold successProb
  apply div_pos hρ
  linarith

private lemma successProb_le_one {b d t : ℝ} (hdb : d < b) (hb : 0 < b) (ht : 0 ≤ t) :
    successProb b d t ≤ 1 := by
  have hρ : 0 < 1 - d / b := by rw [sub_pos, div_lt_one hb]; exact hdb
  have hE : 1 ≤ exp ((b - d) * t) := one_le_exp (mul_nonneg (by linarith) ht)
  unfold successProb
  rw [div_le_one (by linarith)]
  linarith

private lemma successProb_eq {b d t : ℝ} (hb : 0 < b) :
    successProb b d t = (b - d) / (b * exp ((b - d) * t) - d) := by
  unfold successProb
  have h1 : 1 - d / b = (b - d) / b := by rw [sub_div, div_self hb.ne']
  have h2 : 1 - d / b + exp ((b - d) * t) - 1 = (b * exp ((b - d) * t) - d) / b := by
    rw [sub_div, mul_div_cancel_left₀ _ hb.ne']
    ring
  rw [h2, h1, div_div_div_cancel_right₀ hb.ne']

private lemma meanSize_eq {lam b d t : ℝ} (hb : 0 < b) :
    meanSize lam b d t = lam / (b - d) * (exp ((b - d) * t) - 1) := by
  unfold meanSize
  have h1 : 1 - d / b = (b - d) / b := by rw [sub_div, div_self hb.ne']
  rw [h1, div_div_div_cancel_right₀ hb.ne']

private lemma successProb_div_eq {b d t z : ℝ} (hdb : d < b) (hb : 0 < b) (ht : 0 ≤ t)
    (hz1 : z ≤ 1) :
    successProb b d t / (1 - (1 - successProb b d t) * z) = (b - d) / lineageDenom b d t z := by
  have hE : 1 ≤ exp ((b - d) * t) := one_le_exp (mul_nonneg (by linarith) ht)
  have hD := lineageDenom_pos hdb hb ht hz1 (d := d)
  rw [successProb_eq hb]
  unfold lineageDenom at hD ⊢
  generalize exp ((b - d) * t) = E at *
  have hC : b * E - d ≠ 0 := by nlinarith
  generalize hD' : b * (1 - z) * E + b * z - d = D at *
  have h2 : 1 - (1 - (b - d) / (b * E - d)) * z = D / (b * E - d) := by
    rw [one_sub_div hC, div_mul_eq_mul_div, one_sub_div hC]
    congr 1
    rw [← hD']
    ring
  rw [h2, div_div_div_cancel_right₀ hC]

lemma successProb_eq_div {lam b d t : ℝ} (hdb : d < b) (hb : 0 < b) (hlam : 0 < lam)
    (ht : 0 ≤ t) : successProb b d t = lam / b / (meanSize lam b d t + lam / b) := by
  have hE : 1 ≤ exp ((b - d) * t) := one_le_exp (mul_nonneg (by linarith) ht)
  rw [successProb_eq hb, meanSize_eq hb]
  generalize exp ((b - d) * t) = E at *
  have hbd : b - d ≠ 0 := by linarith
  have hC : b * E - d ≠ 0 := by nlinarith
  have hsum : lam / (b - d) * (E - 1) + lam / b = lam * (b * E - d) / ((b - d) * b) := by
    field_simp
    ring
  rw [hsum, div_div_div_eq, div_eq_div_iff hC
    (mul_ne_zero hb.ne' (mul_ne_zero hlam.ne' hC))]
  ring

@[simp] lemma meanSize_zero (lam b d : ℝ) : meanSize lam b d 0 = 0 := by simp [meanSize]

/-- The mean clone size solves `ȳ' = (b - d) ȳ + lam`. -/
theorem hasDerivAt_meanSize {lam b d : ℝ} (hdb : d < b) (hb : 0 < b) (s : ℝ) :
    HasDerivAt (meanSize lam b d) ((b - d) * meanSize lam b d s + lam) s := by
  have hbd : b - d ≠ 0 := by linarith
  have he : meanSize lam b d = fun s ↦ lam / (b - d) * (exp ((b - d) * s) - 1) :=
    funext fun s ↦ meanSize_eq hb
  rw [he]
  have := (((hasDerivAt_id' s).const_mul (b - d)).exp.sub_const 1).const_mul (lam / (b - d))
  convert this using 1
  simp only [mul_one]
  field_simp
  ring

/-- **Generating function of the negative binomial law.** For `k > 0`, `0 < q ≤ 1` and
`0 ≤ z ≤ 1`, `∑_m NB(m; k, q) z^m = (q / (1 - (1 - q) z))^k`. -/
private theorem hasSum_negBinomialPMF_mul_pow {k q z : ℝ} (hk : 0 < k) (hq : 0 < q) (hq1 : q ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    HasSum (fun m : ℕ ↦ negBinomialPMF k q m * z ^ m) ((q / (1 - (1 - q) * z)) ^ k) := by
  set q' := 1 - (1 - q) * z with hq'
  have hq'0 : 0 < q' := by nlinarith
  have hq'1 : q' ≤ 1 := by nlinarith
  have h := (hasSum_negBinomialPMF hk hq'0 hq'1).mul_left ((q / q') ^ k)
  rw [mul_one] at h
  convert h using 1
  funext m
  unfold negBinomialPMF
  have h1q : 1 - q' = (1 - q) * z := by rw [hq']; ring
  rw [h1q, Real.div_rpow hq.le hq'0.le, mul_pow]
  field_simp

/-- **A law on `ℕ` is determined by its generating function on `(0, 1)`.** If two bounded
sequences have equal power series on `(0, 1)`, they are equal. -/
private theorem eq_of_tsum_mul_pow_eq {p q : ℕ → ℝ} (hp : ∀ m, |p m| ≤ 1) (hq : ∀ m, |q m| ≤ 1)
    (h : ∀ z ∈ Ioo (0 : ℝ) 1, ∑' m, p m * z ^ m = ∑' m, q m * z ^ m) : p = q := by
  set c : ℕ → ℝ := p - q with hc
  have hcb : ∀ n, ‖c n‖ ≤ 2 := fun n ↦ by
    simp only [hc, Pi.sub_apply, Real.norm_eq_abs]
    calc |p n - q n| ≤ |p n| + |q n| := abs_sub _ _
      _ ≤ 2 := by linarith [hp n, hq n]
  set F := FormalMultilinearSeries.ofScalars ℝ c with hF
  have hrad : ((1 / 2 : ℝ≥0) : ℝ≥0∞) ≤ F.radius := by
    refine F.le_radius_of_bound 2 fun n ↦ ?_
    rw [hF, FormalMultilinearSeries.ofScalars_norm]
    calc ‖c n‖ * (((1 / 2 : ℝ≥0)) : ℝ) ^ n ≤ 2 * 1 := by
          apply mul_le_mul (hcb n) _ (by positivity) (by norm_num)
          apply pow_le_one₀ (by positivity)
          norm_num
      _ = 2 := by ring
  have hpos : 0 < F.radius := lt_of_lt_of_le (by norm_num) hrad
  have hser := F.hasFPowerSeriesOnBall hpos
  have hsum : ∀ z ∈ Ioo (0 : ℝ) (1 / 2), F.sum z = 0 := by
    intro z hz
    have hz1 : z < 1 := by linarith [hz.2]
    have hsp : Summable fun m ↦ p m * z ^ m := by
      refine Summable.of_norm_bounded (g := fun m ↦ z ^ m)
        (summable_geometric_of_lt_one hz.1.le hz1) fun m ↦ ?_
      rw [norm_mul, norm_pow, Real.norm_of_nonneg hz.1.le, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (pow_nonneg hz.1.le m) (hp m)
    have hsq : Summable fun m ↦ q m * z ^ m := by
      refine Summable.of_norm_bounded (g := fun m ↦ z ^ m)
        (summable_geometric_of_lt_one hz.1.le hz1) fun m ↦ ?_
      rw [norm_mul, norm_pow, Real.norm_of_nonneg hz.1.le, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (pow_nonneg hz.1.le m) (hq m)
    have := FormalMultilinearSeries.ofScalars_sum_eq (E := ℝ) c z
    rw [FormalMultilinearSeries.ofScalarsSum] at this
    rw [hF, this]
    simp only [hc, Pi.sub_apply, smul_eq_mul, sub_mul]
    rw [hsp.tsum_sub hsq, h z ⟨hz.1, hz1⟩, sub_self]
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℝ), F.sum z = 0 := by
    have hev : ∀ᶠ z in 𝓝[>] (0 : ℝ), F.sum z = 0 := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with z hz
      exact hsum z hz
    exact hev.frequently.filter_mono (nhdsWithin_mono _ fun x hx ↦ ne_of_gt hx)
  have hzero := hser.analyticAt.frequently_zero_iff_eventually_zero.1 hfreq
  have hF0 : F = 0 := hser.hasFPowerSeriesAt.eq_zero_of_eventually hzero
  rw [hF, FormalMultilinearSeries.ofScalars_series_eq_zero] at hF0
  exact sub_eq_zero.1 hF0

private lemma negBinomialPMF_nonneg {k q : ℝ} (hk : 0 < k) (hq : 0 ≤ q) (hq1 : q ≤ 1) (m : ℕ) :
    0 ≤ negBinomialPMF k q m := by
  have := ascPochhammer_pos m k hk
  have h1 : 0 ≤ 1 - q := by linarith
  unfold negBinomialPMF
  positivity

private lemma intervalIntegrable_lineagePGF {b d z t : ℝ} (hdb : d < b) (hb : 0 < b) (hz1 : z ≤ 1)
    (ht : 0 ≤ t) : IntervalIntegrable (fun u ↦ lineagePGF b d u z) volume 0 t := by
  refine ContinuousOn.intervalIntegrable fun u hu ↦ ?_
  rw [uIcc_of_le ht] at hu
  have hD := lineageDenom_pos hdb hb hu.1 hz1 (d := d)
  have hD' : b * (1 - z) * exp ((b - d) * u) + b * z - d ≠ 0 := hD.ne'
  unfold lineagePGF lineageDenom
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := exact hD'))

/-- The closed form of the generating function of the clone size:
`e^{-lam t} e^{lam ∫_0^t G_{t-s}(z) ds} = (q / (1 - (1 - q) z))^{lam / b}` with
`q = successProb b d t`. -/
private theorem exp_mul_exp_integral_lineagePGF {b d z t : ℝ} (lam : ℝ) (hdb : d < b) (hb : 0 < b)
    (hz1 : z ≤ 1) (ht : 0 ≤ t) :
    exp (-(lam * t)) * exp (lam * ∫ s in (0 : ℝ)..t, lineagePGF b d (max (t - s) 0) z) =
      (successProb b d t / (1 - (1 - successProb b d t) * z)) ^ (lam / b) := by
  have hbd : 0 < b - d := by linarith
  have hD := lineageDenom_pos hdb hb ht hz1 (d := d)
  have h1 : ∫ s in (0 : ℝ)..t, lineagePGF b d (max (t - s) 0) z =
      ∫ u in (0 : ℝ)..t, lineagePGF b d u z := by
    rw [intervalIntegral.integral_congr (g := fun s ↦ lineagePGF b d (t - s) z) fun s hs ↦ by
      rw [uIcc_of_le ht] at hs
      simp only [max_eq_left (sub_nonneg.2 hs.2)]]
    rw [intervalIntegral.integral_comp_sub_left (fun u ↦ lineagePGF b d u z) t]
    simp
  have h2 : ∫ u in (0 : ℝ)..t, lineagePGF b d u z =
      t - log (lineageDenom b d t z / (b - d)) / b := by
    have := integral_one_sub_lineagePGF hdb hb hz1 ht (d := d)
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegrable_lineagePGF hdb hb hz1 ht), intervalIntegral.integral_const,
      smul_eq_mul, mul_one, sub_zero] at this
    linarith
  rw [h1, h2, ← exp_add, successProb_div_eq hdb hb ht hz1,
    Real.rpow_def_of_pos (div_pos hbd hD), log_div hbd.ne' hD.ne',
    log_div hD.ne' hbd.ne']
  congr 1
  field_simp
  ring

/-- The expectation of a function of an `ℕ`-valued random variable. -/
private lemma lintegral_comp_nat {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Y : Ω → ℕ}
    (hY : Measurable Y) (f : ℕ → ℝ≥0∞) :
    ∫⁻ ω, f (Y ω) ∂P = ∑' m, f m * P {ω | Y ω = m} := by
  rw [← lintegral_map (measurable_of_countable f) hY, lintegral_countable']
  refine tsum_congr fun m ↦ ?_
  rw [Measure.map_apply hY (measurableSet_singleton m)]
  rfl

/-! ### Arrival times of exponential interarrivals -/

/-- The partial sum `x 0 + ⋯ + x (n - 1)` of a sequence: the `n`-th arrival time of the
interarrival sequence `x`. -/
private def psum (x : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, x i

/-- `seqCons a y` prepends `a` to the sequence `y`. -/
private def seqCons (a : ℝ) (y : ℕ → ℝ) : ℕ → ℝ
  | 0 => a
  | i + 1 => y i

private lemma psum_seqCons_succ (a : ℝ) (y : ℕ → ℝ) (n : ℕ) :
    psum (seqCons a y) (n + 1) = a + psum y n := by
  rw [psum, Finset.sum_range_succ', add_comm]
  rfl

private lemma measurable_psum (n : ℕ) : Measurable fun x : ℕ → ℝ ↦ psum x n := by
  unfold psum
  fun_prop

private lemma measurable_seqCons : Measurable (fun p : ℝ × (ℕ → ℝ) ↦ seqCons p.1 p.2) := by
  rw [measurable_pi_iff]
  intro i
  cases i with
  | zero => exact measurable_fst
  | succ i => exact (measurable_pi_apply i).comp measurable_snd

/-- The i.i.d. product of rate-`r` exponential laws on sequences. -/
private noncomputable abbrev expSeq (r : ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ ↦ expMeasure r

private lemma map_seqCons_expSeq {r : ℝ} (hr : 0 < r) :
    ((expMeasure r).prod (expSeq r)).map (fun p ↦ seqCons p.1 p.2) = expSeq r := by
  have := isProbabilityMeasure_expMeasure hr
  refine Measure.eq_infinitePi _ fun s t ht ↦ ?_
  classical
  obtain ⟨N, hN⟩ : ∃ N, s ⊆ Finset.range (N + 1) :=
    ⟨s.sup id, fun i hi ↦ Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))⟩
  set t' : ℕ → Set ℝ := fun i ↦ if i ∈ s then t i else univ with ht'
  have hmt' : ∀ i, MeasurableSet (t' i) := by
    intro i
    simp only [ht']
    split_ifs
    exacts [ht i, .univ]
  have hpi : Set.pi (s : Set ℕ) t = Set.pi (Finset.range (N + 1) : Set ℕ) t' := by
    ext x
    simp only [Set.mem_pi, Finset.mem_coe, ht']
    constructor
    · intro h i _
      split_ifs with hi
      exacts [h i hi, trivial]
    · intro h i hi
      simpa [hi] using h i (hN hi)
  have hprod : ∏ i ∈ s, expMeasure r (t i) =
      ∏ i ∈ Finset.range (N + 1), expMeasure r (t' i) := by
    rw [← Finset.prod_subset hN]
    · exact Finset.prod_congr rfl fun i hi ↦ by simp [ht', hi]
    · intro i _ hi
      simp [ht', hi]
  rw [hpi, hprod, Measure.map_apply measurable_seqCons (MeasurableSet.pi
    (Finset.countable_toSet _) fun i _ ↦ hmt' i)]
  have hpre : (fun p : ℝ × (ℕ → ℝ) ↦ seqCons p.1 p.2) ⁻¹'
      Set.pi (Finset.range (N + 1) : Set ℕ) t' =
      t' 0 ×ˢ Set.pi (Finset.range N : Set ℕ) (fun i ↦ t' (i + 1)) := by
    ext ⟨a, y⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_range, Set.mem_Iio, Set.mem_prod]
    constructor
    · intro h
      exact ⟨h 0 (Nat.succ_pos N), fun i hi ↦ h (i + 1) (by omega)⟩
    · rintro ⟨h0, h⟩ i hi
      cases i with
      | zero => exact h0
      | succ i => exact h i (by omega)
  have : ∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ ↦ expMeasure r) i) := fun _ ↦ this
  rw [hpre, Measure.prod_prod, Measure.infinitePi_pi (μ := fun _ : ℕ ↦ expMeasure r)
    (mt := fun i _ ↦ hmt' (i + 1)), Finset.prod_range_succ', mul_comm]

private lemma expMeasure_Ioi {r : ℝ} (hr : 0 < r) {u : ℝ} (hu : 0 ≤ u) :
    expMeasure r (Ioi u) = ENNReal.ofReal (exp (-(r * u))) := by
  have := isProbabilityMeasure_expMeasure hr
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (exp_pos _).le]
  change (expMeasure r).real (Ioi u) = _
  have huniv : (expMeasure r).real univ = 1 := by simp [measureReal_def]
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, huniv,
    ← cdf_eq_real, cdf_expMeasure_eq hr, ite_eq_left hu]
  ring

private lemma ae_expSeq_nonneg {r : ℝ} (hr : 0 < r) : ∀ᵐ y ∂expSeq r, ∀ i, 0 ≤ y i := by
  have := isProbabilityMeasure_expMeasure hr
  rw [ae_all_iff]
  intro i
  have hm : (expSeq r).map (fun y ↦ y i) = expMeasure r :=
    Measure.infinitePi_map_eval (fun _ : ℕ ↦ expMeasure r) i
  have h0 : ∀ᵐ x ∂expMeasure r, 0 ≤ x := by
    rw [ae_iff]
    have heq : {a : ℝ | ¬0 ≤ a} = Iio 0 := by ext; simp
    rw [heq, expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
    exact lintegral_gammaPDF_of_nonpos le_rfl
  rw [← hm] at h0
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h0

private lemma integral_eq_sub_primitive {h : ℝ → ℝ} (hh : Continuous h) (x y : ℝ) :
    ∫ s in x..y, h s = (∫ s in (0 : ℝ)..y, h s) - ∫ s in (0 : ℝ)..x, h s :=
  (intervalIntegral.integral_interval_sub_left (hh.intervalIntegrable (μ := volume) 0 y)
    (hh.intervalIntegrable 0 x)).symm

private lemma continuous_primitive' {h : ℝ → ℝ} (hh : Continuous h) :
    Continuous fun x : ℝ ↦ ∫ s in (0 : ℝ)..x, h s :=
  continuous_iff_continuousAt.2 fun x ↦ (hh.integral_hasStrictDerivAt 0 x).hasDerivAt.continuousAt

/-- The calculus identity behind the Poisson counts:
`∫_0^t h(a + c) (∫_{a+c}^{a+t} h)^n dc = (∫_a^{a+t} h)^{n+1} / (n + 1)` for continuous `h`. -/
private lemma integral_mul_integral_pow {h : ℝ → ℝ} (hh : Continuous h) (a t : ℝ) (n : ℕ) :
    ∫ c in (0 : ℝ)..t, h (a + c) * (∫ s in (a + c)..(a + t), h s) ^ n =
      (∫ s in a..(a + t), h s) ^ (n + 1) / (n + 1) := by
  set H : ℝ → ℝ := fun x ↦ ∫ s in (0 : ℝ)..x, h s with hH
  have hint : ∀ x y : ℝ, ∫ s in x..y, h s = H y - H x := fun x y ↦
    (intervalIntegral.integral_interval_sub_left (hh.intervalIntegrable 0 y)
      (hh.intervalIntegrable 0 x)).symm
  simp_rw [hint]
  have hHd : ∀ x, HasDerivAt H (h x) x := fun x ↦
    (hh.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hderiv : ∀ c ∈ uIcc (0 : ℝ) t, HasDerivAt
      (fun c ↦ -(H (a + t) - H (a + c)) ^ (n + 1) / (n + 1))
      (h (a + c) * (H (a + t) - H (a + c)) ^ n) c := by
    intro c _
    have h1 : HasDerivAt (fun c ↦ H (a + c)) (h (a + c)) c := (hHd (a + c)).comp_const_add a c
    have h2 := ((h1.const_sub (H (a + t))).pow (n + 1)).neg.div_const ((n : ℝ) + 1)
    convert h2 using 1
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
  have hcont : Continuous fun c ↦ h (a + c) * (H (a + t) - H (a + c)) ^ n := by
    have : Continuous H := continuous_iff_continuousAt.2 fun x ↦ (hHd x).continuousAt
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp only [add_zero, sub_self, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, neg_zero, zero_div, zero_sub, neg_div, neg_neg]

/-- On the canonical space of interarrival sequences: on the event that exactly `n` arrivals
fall in `[0, t]`, the product of `h` over these arrival times shifted by `a`; zero off that
event. -/
private noncomputable def gapIntegrand (h : ℝ → ℝ) (n : ℕ) (a t : ℝ) (x : ℕ → ℝ) : ℝ≥0∞ :=
  {x : ℕ → ℝ | psum x n ≤ t ∧ t < psum x (n + 1)}.indicator
    (fun x ↦ ∏ j : Fin n, ENNReal.ofReal (h (a + psum x (j + 1)))) x

private lemma measurableSet_gap (n : ℕ) (t : ℝ) :
    MeasurableSet {x : ℕ → ℝ | psum x n ≤ t ∧ t < psum x (n + 1)} :=
  (measurableSet_le (measurable_psum n) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_psum (n + 1)))

private lemma measurable_gapIntegrand {h : ℝ → ℝ} (hh : Measurable h) (n : ℕ) (a t : ℝ) :
    Measurable (gapIntegrand h n a t) := by
  unfold gapIntegrand
  refine Measurable.indicator ?_ (measurableSet_gap n t)
  exact Finset.measurable_prod _ fun j _ ↦
    ENNReal.measurable_ofReal.comp (hh.comp (measurable_const.add (measurable_psum _)))

private lemma gapIntegrand_seqCons (h : ℝ → ℝ) (n : ℕ) (a t c : ℝ) (y : ℕ → ℝ) :
    gapIntegrand h (n + 1) a t (seqCons c y) =
      ENNReal.ofReal (h (a + c)) * gapIntegrand h n (a + c) (t - c) y := by
  unfold gapIntegrand
  have hmem : seqCons c y ∈ {x : ℕ → ℝ | psum x (n + 1) ≤ t ∧ t < psum x (n + 1 + 1)} ↔
      y ∈ {x : ℕ → ℝ | psum x n ≤ t - c ∧ t - c < psum x (n + 1)} := by
    simp only [mem_ofPred_eq, psum_seqCons_succ]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  by_cases hy : y ∈ {x : ℕ → ℝ | psum x n ≤ t - c ∧ t - c < psum x (n + 1)}
  · rw [indicator_of_mem (hmem.2 hy), indicator_of_mem hy, Fin.prod_univ_succ]
    congr 1
    · simp [psum, seqCons]
    · refine Finset.prod_congr rfl fun j _ ↦ ?_
      rw [show ((j.succ : Fin (n + 1)) : ℕ) + 1 = (j : ℕ) + 1 + 1 by simp, psum_seqCons_succ,
        add_assoc]
  · rw [indicator_of_notMem (fun h ↦ hy (hmem.1 h)), indicator_of_notMem hy, mul_zero]

/-- One step of the induction: integrating out the first interarrival time. -/
private lemma lintegral_expMeasure_step {r : ℝ} (hr : 0 < r) {h : ℝ → ℝ} (hh : Continuous h)
    (hh0 : ∀ s, 0 ≤ h s) (n : ℕ) (a t : ℝ) :
    ∫⁻ c, ENNReal.ofReal (h (a + c)) * ENNReal.ofReal (if 0 ≤ t - c then
        exp (-(r * (t - c))) * r ^ n * (∫ s in (a + c)..(a + c + (t - c)), h s) ^ n / n !
        else 0) ∂expMeasure r =
      ENNReal.ofReal (if 0 ≤ t then
        exp (-(r * t)) * r ^ (n + 1) * (∫ s in a..(a + t), h s) ^ (n + 1) / (n + 1)! else 0) := by
  set F : ℝ → ℝ := fun c ↦ r ^ (n + 1) * exp (-(r * t)) / n ! *
    (h (a + c) * (∫ s in (a + c)..(a + t), h s) ^ n) with hF
  have hpt : ∀ c, gammaPDF 1 r c * (ENNReal.ofReal (h (a + c)) * ENNReal.ofReal
      (if 0 ≤ t - c then exp (-(r * (t - c))) * r ^ n *
        (∫ s in (a + c)..(a + c + (t - c)), h s) ^ n / n ! else 0)) =
      (Icc 0 t).indicator (fun c ↦ ENNReal.ofReal (F c)) c := by
    intro c
    by_cases hc0 : 0 ≤ c
    · by_cases hct : c ≤ t
      · rw [indicator_of_mem (show c ∈ Icc 0 t from ⟨hc0, hct⟩)]
        change exponentialPDF r c * _ = _
        have htc : 0 ≤ t - c := by linarith
        rw [exponentialPDF_of_nonneg hc0, show a + c + (t - c) = a + t by ring]
        simp only [htc, ↓reduceIte]
        have hI : 0 ≤ ∫ s in (a + c)..(a + t), h s :=
          intervalIntegral.integral_nonneg (by linarith) fun s _ ↦ hh0 s
        rw [← ENNReal.ofReal_mul (hh0 _), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hF]
        have he : exp (-(r * c)) * exp (-(r * (t - c))) = exp (-(r * t)) := by
          rw [← exp_add]; congr 1; ring
        rw [← he]
        ring
      · have htc : ¬ 0 ≤ t - c := by linarith
        rw [indicator_of_notMem (show c ∉ Icc 0 t from fun h ↦ hct h.2)]
        simp [htc]
    · rw [gammaPDF_of_neg (lt_of_not_ge hc0), zero_mul,
        indicator_of_notMem (show c ∉ Icc 0 t from fun h ↦ hc0 h.1)]
  rw [expMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul _
    (by unfold gammaPDF; fun_prop) (by
      refine Measurable.mul (ENNReal.measurable_ofReal.comp (hh.measurable.comp
        (measurable_const.add measurable_id))) ?_
      refine ENNReal.measurable_ofReal.comp (Measurable.ite ?_ ?_ measurable_const)
      · exact measurableSet_le measurable_const (measurable_const.sub measurable_id)
      · have hc : Continuous fun c : ℝ ↦ ∫ s in (a + c)..(a + c + (t - c)), h s := by
          have he : (fun c : ℝ ↦ ∫ s in (a + c)..(a + c + (t - c)), h s) =
              fun c ↦ (∫ s in (0 : ℝ)..(a + t), h s) - ∫ s in (0 : ℝ)..(a + c), h s := by
            funext c
            rw [show a + c + (t - c) = a + t by ring, integral_eq_sub_primitive hh (a + c) (a + t)]
          rw [he]
          have hH := continuous_primitive' hh
          fun_prop
        exact (by fun_prop : Continuous fun c : ℝ ↦ exp (-(r * (t - c))) * r ^ n *
          (∫ s in (a + c)..(a + c + (t - c)), h s) ^ n / n !).measurable)]
  simp only [Pi.mul_apply]
  simp_rw [hpt]
  rw [lintegral_indicator measurableSet_Icc]
  have hHc := continuous_primitive' hh
  have hFc : Continuous F := by
    have he : F = fun c ↦ r ^ (n + 1) * exp (-(r * t)) / n ! * (h (a + c) *
        ((∫ s in (0 : ℝ)..(a + t), h s) - ∫ s in (0 : ℝ)..(a + c), h s) ^ n) := by
      funext c
      simp only [hF]
      rw [integral_eq_sub_primitive hh (a + c) (a + t)]
    rw [he]
    fun_prop
  split_ifs with ht
  · rw [← ofReal_integral_eq_lintegral_ofReal (hFc.integrableOn_Icc)]
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht, hF,
        intervalIntegral.integral_const_mul, integral_mul_integral_pow hh a t n]
      congr 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with c hc
      rw [hF]
      have hI : 0 ≤ ∫ s in (a + c)..(a + t), h s :=
        intervalIntegral.integral_nonneg (by linarith [hc.2]) fun s _ ↦ hh0 s
      have := hh0 (a + c)
      positivity
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge ht), Measure.restrict_empty, lintegral_zero_measure,
      ENNReal.ofReal_zero]

/-- **Arrival counts and the generating functional on the canonical space.** Under i.i.d.
rate-`r` exponential interarrivals, for a continuous `h ≥ 0`, `a ∈ ℝ` and `t ≥ 0`,
`E[1{exactly n arrivals in [0, t]} ∏_{j ≤ n} h(a + S_j)] =
e^{-r t} r^n (∫_a^{a+t} h)^n / n!`; for `t < 0` the event is empty. -/
private theorem lintegral_gapIntegrand {r : ℝ} (hr : 0 < r) {h : ℝ → ℝ} (hh : Continuous h)
    (hh0 : ∀ s, 0 ≤ h s) (n : ℕ) : ∀ a t : ℝ, ∫⁻ x, gapIntegrand h n a t x ∂expSeq r =
      ENNReal.ofReal (if 0 ≤ t then
        exp (-(r * t)) * r ^ n * (∫ s in a..(a + t), h s) ^ n / n ! else 0) := by
  have hP := isProbabilityMeasure_expMeasure hr
  have : ∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ ↦ expMeasure r) i) := fun _ ↦ hP
  induction n with
  | zero =>
    intro a t
    have hfun : gapIntegrand h 0 a t = {x : ℕ → ℝ | 0 ≤ t ∧ t < x 0}.indicator 1 := by
      funext x
      simp [gapIntegrand, psum, indicator]
    have hms : MeasurableSet {x : ℕ → ℝ | 0 ≤ t ∧ t < x 0} :=
      (MeasurableSet.const _).inter (measurableSet_lt measurable_const (measurable_pi_apply 0))
    rw [hfun, lintegral_indicator_one hms]
    split_ifs with ht
    · have hset : {x : ℕ → ℝ | 0 ≤ t ∧ t < x 0} = (fun x : ℕ → ℝ ↦ x 0) ⁻¹' Ioi t := by
        ext x; simp [ht]
      rw [hset, ← Measure.map_apply (measurable_pi_apply 0) measurableSet_Ioi,
        Measure.infinitePi_map_eval (fun _ : ℕ ↦ expMeasure r) 0, expMeasure_Ioi hr ht]
      simp
    · have hset : {x : ℕ → ℝ | 0 ≤ t ∧ t < x 0} = ∅ := by ext x; simp [ht]
      rw [hset, measure_empty, ENNReal.ofReal_zero]
  | succ n ih =>
    intro a t
    have hm : Measurable fun p : ℝ × (ℕ → ℝ) ↦ gapIntegrand h (n + 1) a t (seqCons p.1 p.2) :=
      (measurable_gapIntegrand hh.measurable _ _ _).comp measurable_seqCons
    rw [← map_seqCons_expSeq hr, lintegral_map (measurable_gapIntegrand hh.measurable _ _ _)
      measurable_seqCons, lintegral_prod _ hm.aemeasurable]
    simp_rw [gapIntegrand_seqCons]
    simp_rw [lintegral_const_mul _ (measurable_gapIntegrand hh.measurable _ _ _), ih]
    exact lintegral_expMeasure_step hr hh hh0 n a t

/-! ### The seeding model -/

section Model

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The **clone size** `y(t)`: the total size at time `t` of the lineages founded by the cells
that arrived in `[0, t]`, where `count T t ω` is the number of arrivals in `[0, t]` and
`X t j ω` is the size at time `t` of the lineage founded by the `(j + 1)`-th arriving cell. -/
noncomputable def cloneSize (T : ℕ → Ω → ℝ) (X : ℝ≥0 → ℕ → Ω → ℕ) (t : ℝ≥0) (ω : Ω) : ℕ :=
  ∑ j ∈ Finset.range (count T t ω), X t j ω

/-- **The seeding model of one clone.** Cells of the clone arrive at the metastatic site as a
Poisson process of rate `lam`, starting at time `0` with an empty site: the interarrival times
`T 0, T 1, …` are i.i.d. exponential of rate `lam`, so `count T` is a Poisson process of rate
`lam` (`PoissonProcess.isPoissonProcess_count`) and the `(j + 1)`-th cell arrives at
`arrivalTime T (j + 1)`. Each arriving cell founds an independent linear birth–death process
with division rate `b` and death rate `d`: given the arrival times, the sizes `X t j` at time
`t` of the lineages founded by the cells that arrived in `[0, t]` are independent, the `j`-th
with Kendall's law `LinearBirthDeath.prob b d (t - arrivalTime T (j + 1))` of a linear
birth–death process started from one cell and run for the age of the lineage. The clone size at
time `t` depends on the lineages only through these sizes. -/
structure IsClonalSeeding (P : Measure Ω) (lam : ℝ≥0) (b d : ℝ) (T : ℕ → Ω → ℝ)
    (X : ℝ≥0 → ℕ → Ω → ℕ) : Prop where
  /-- The interarrival times are measurable. -/
  measurable_interarrival : ∀ i, Measurable (T i)
  /-- The interarrival times are exponential of rate `lam`. -/
  hasLaw_interarrival : ∀ i, HasLaw (T i) (expMeasure lam) P
  /-- The interarrival times are independent. -/
  iIndepFun_interarrival : iIndepFun T P
  /-- The lineage sizes are measurable. -/
  measurable_lineage : ∀ t j, Measurable (X t j)
  /-- Given the arrival times, the sizes at time `t` of the lineages founded by the `n` cells
  that arrived in `[0, t]` are independent with Kendall's laws at the ages of the lineages. -/
  measure_lineage : ∀ (t : ℝ≥0) (n : ℕ) (A : Set (ℕ → ℝ)), MeasurableSet A →
    ∀ m : Fin n → ℕ,
      P {ω | (fun i ↦ T i ω) ∈ A ∧ count T t ω = n ∧ ∀ j : Fin n, X t j ω = m j} =
        ∫⁻ ω in {ω | (fun i ↦ T i ω) ∈ A ∧ count T t ω = n},
          ∏ j : Fin n, ENNReal.ofReal
            (LinearBirthDeath.prob b d (t - arrivalTime T (j + 1) ω) (m j)) ∂P

namespace IsClonalSeeding

variable {lam : ℝ≥0} {b d : ℝ} {T : ℕ → Ω → ℝ} {X : ℝ≥0 → ℕ → Ω → ℕ}

lemma isProbabilityMeasure (h : IsClonalSeeding P lam b d T X) (hlam : 0 < lam) :
    IsProbabilityMeasure P :=
  have := isProbabilityMeasure_expMeasure (NNReal.coe_pos.2 hlam)
  (h.hasLaw_interarrival 0).isProbabilityMeasure

private lemma measurable_seq (h : IsClonalSeeding P lam b d T X) : Measurable fun ω i ↦ T i ω :=
  measurable_pi_iff.2 h.measurable_interarrival

private lemma map_seq (h : IsClonalSeeding P lam b d T X) :
    P.map (fun ω i ↦ T i ω) = expSeq lam := by
  rw [h.iIndepFun_interarrival.map_fun_eq_infinitePi_map₀'
    fun i ↦ (h.hasLaw_interarrival i).aemeasurable]
  congr 1
  funext i
  exact (h.hasLaw_interarrival i).map_eq

private lemma ae_nonneg (h : IsClonalSeeding P lam b d T X) (hlam : 0 < lam) :
    ∀ᵐ ω ∂P, ∀ i, 0 ≤ T i ω := by
  have h0 := ae_expSeq_nonneg (NNReal.coe_pos.2 hlam)
  rw [← h.map_seq] at h0
  exact ae_of_ae_map h.measurable_seq.aemeasurable h0

private lemma measurable_count (h : IsClonalSeeding P lam b d T X) (t : ℝ≥0) :
    Measurable (count T t) := by
  unfold count
  refine measurable_ncard.comp (measurable_set_iff.2 fun n ↦ ?_)
  have hm : Measurable (arrivalTime T (n + 1)) := by
    unfold arrivalTime
    exact Finset.measurable_sum _ fun i _ ↦ h.measurable_interarrival i
  exact measurableSet_setOfPred.1 (measurableSet_le hm measurable_const)

end IsClonalSeeding

private lemma arrivalTime_eq_psum (T : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    arrivalTime T n ω = psum (fun i ↦ T i ω) n := rfl

private lemma count_eq_of_gap {T : ℕ → Ω → ℝ} {t : ℝ≥0} {ω : Ω} (hT : ∀ i, 0 ≤ T i ω) {k : ℕ}
    (hk : arrivalTime T k ω ≤ t ∧ t < arrivalTime T (k + 1) ω) : count T t ω = k := by
  have hm : Monotone fun n ↦ arrivalTime T n ω := by
    apply monotone_nat_of_le_succ
    intro n
    simp only [arrivalTime, Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hT n)
  have heq : {n : ℕ | arrivalTime T (n + 1) ω ≤ t} = Iio k := by
    ext n
    simp only [mem_ofPred_eq, mem_Iio]
    constructor
    · intro hn
      by_contra hnk
      have hle := hm (Nat.add_le_add_right (Nat.le_of_not_gt hnk) 1)
      linarith [hk.2]
    · intro hn
      exact (hm (by omega)).trans hk.1
  unfold count
  rw [heq, Set.ncard_Iio_nat]

namespace IsClonalSeeding

variable {lam : ℝ≥0} {b d : ℝ} {T : ℕ → Ω → ℝ} {X : ℝ≥0 → ℕ → Ω → ℕ}

private lemma measure_gap (h : IsClonalSeeding P lam b d T X) (hlam : 0 < lam) (t : ℝ≥0) (n : ℕ) :
    P {ω | arrivalTime T n ω ≤ t ∧ t < arrivalTime T (n + 1) ω} =
      ENNReal.ofReal (exp (-(lam * t)) * lam ^ n * t ^ n / n !) := by
  have hpre : {ω | arrivalTime T n ω ≤ t ∧ t < arrivalTime T (n + 1) ω} =
      (fun ω i ↦ T i ω) ⁻¹' {x : ℕ → ℝ | psum x n ≤ t ∧ t < psum x (n + 1)} := rfl
  rw [hpre, ← Measure.map_apply h.measurable_seq (measurableSet_gap n t), h.map_seq]
  have hg := lintegral_gapIntegrand (NNReal.coe_pos.2 hlam) (h := fun _ ↦ 1) continuous_const
    (fun _ ↦ zero_le_one) n 0 t
  simp only [gapIntegrand, ENNReal.ofReal_one, Finset.prod_const_one, zero_add,
    intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero, t.coe_nonneg,
    ↓reduceIte] at hg
  rw [← hg, lintegral_indicator (measurableSet_gap n t)]
  simp

private lemma count_ae_eq_gap (h : IsClonalSeeding P lam b d T X) (hlam : 0 < lam) (t : ℝ≥0)
    (n : ℕ) : {ω | arrivalTime T n ω ≤ t ∧ t < arrivalTime T (n + 1) ω} =ᵐ[P]
      {ω | count T t ω = n} := by
  have := h.isProbabilityMeasure hlam
  refine ae_eq_of_ae_subset_of_measure_ge ?_ ?_ ?_ (measure_ne_top _ _)
  · filter_upwards [h.ae_nonneg hlam] with ω hω hgap
    exact count_eq_of_gap hω hgap
  · rw [measure_gap h hlam, (hasLaw_count hlam h.hasLaw_interarrival
      h.iIndepFun_interarrival t).measure_eq (measurableSet_singleton n),
      show ({x : ℕ | x = n} : Set ℕ) = {n} from rfl, poissonMeasure_singleton]
    apply le_of_eq
    congr 1
    push_cast
    ring
  · have hpre : {ω | arrivalTime T n ω ≤ t ∧ t < arrivalTime T (n + 1) ω} =
        (fun ω i ↦ T i ω) ⁻¹' {x : ℕ → ℝ | psum x n ≤ t ∧ t < psum x (n + 1)} := rfl
    rw [hpre]
    exact (h.measurable_seq (measurableSet_gap n t)).nullMeasurableSet

/-- The generating functional of the arrivals: for continuous `g ≥ 0`,
`E[1{N(t) = n} ∏_{j ≤ n} g(S_j)] = e^{-lam t} lam^n (∫_0^t g)^n / n!`. -/
private theorem setLIntegral_count (h : IsClonalSeeding P lam b d T X) (hlam : 0 < lam) {g : ℝ → ℝ}
    (hg : Continuous g) (hg0 : ∀ s, 0 ≤ g s) (t : ℝ≥0) (n : ℕ) :
    ∫⁻ ω in {ω | count T t ω = n}, ∏ j : Fin n, ENNReal.ofReal (g (arrivalTime T (j + 1) ω)) ∂P =
      ENNReal.ofReal (exp (-(lam * t)) * lam ^ n * (∫ s in (0 : ℝ)..t, g s) ^ n / n !) := by
  rw [← Measure.restrict_congr_set (h.count_ae_eq_gap hlam t n)]
  have hpre : {ω | arrivalTime T n ω ≤ t ∧ t < arrivalTime T (n + 1) ω} =
      (fun ω i ↦ T i ω) ⁻¹' {x : ℕ → ℝ | psum x n ≤ t ∧ t < psum x (n + 1)} := rfl
  have hF : Measurable fun x : ℕ → ℝ ↦ ∏ j : Fin n, ENNReal.ofReal (g (psum x (j + 1))) :=
    Finset.measurable_prod _ fun j _ ↦
      ENNReal.measurable_ofReal.comp (hg.measurable.comp (measurable_psum _))
  rw [hpre, ← lintegral_indicator (h.measurable_seq (measurableSet_gap n t))]
  change ∫⁻ ω, ({x : ℕ → ℝ | psum x n ≤ t ∧ t < psum x (n + 1)}.indicator
    (fun x ↦ ∏ j : Fin n, ENNReal.ofReal (g (psum x (j + 1))))) (fun i ↦ T i ω) ∂P = _
  rw [← lintegral_map (hF.indicator (measurableSet_gap n t)) h.measurable_seq, h.map_seq]
  have := lintegral_gapIntegrand (NNReal.coe_pos.2 hlam) hg hg0 n 0 t
  simp only [gapIntegrand, zero_add, t.coe_nonneg, ↓reduceIte] at this
  exact this

/-- **The generating function of the clone size.** For `0 ≤ z ≤ 1`,
`E z^{y(t)} = exp(-lam t + lam ∫_0^t G_{t-s}(z) ds)`, where `G_u` is the generating function of
a lineage of age `u` (`lineagePGF`). -/
private theorem lintegral_ofReal_pow_cloneSize (h : IsClonalSeeding P lam b d T X) (hlam : 0 < lam)
    (hd : 0 ≤ d) (hdb : d < b) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (z ^ cloneSize T X t ω) ∂P =
      ENNReal.ofReal (exp (-(lam * t)) *
        exp (lam * ∫ s in (0 : ℝ)..t, lineagePGF b d (max (t - s) 0) z)) := by
  have hb : 0 < b := by linarith
  set g : ℝ → ℝ := fun s ↦ lineagePGF b d (max (t - s) 0) z with hg_def
  have hg0 : ∀ s, 0 ≤ g s := fun s ↦ lineagePGF_nonneg hd hdb (le_max_right _ _) hz0 hz1
  have hgc : Continuous g := continuous_lineagePGF_age hdb hb hz1 t
  set I := ∫ s in (0 : ℝ)..t, g s with hI
  have hn : ∀ n : ℕ, ∫⁻ ω in {ω | count T t ω = n}, ENNReal.ofReal (z ^ cloneSize T X t ω) ∂P =
      ENNReal.ofReal (exp (-(lam * t)) * lam ^ n * I ^ n / n !) := by
    intro n
    rw [← h.setLIntegral_count hlam hgc hg0 t n]
    set S := {ω | count T t ω = n} with hS_def
    have hS : MeasurableSet S := h.measurable_count t (measurableSet_singleton n)
    set V : Ω → (Fin n → ℕ) := fun ω j ↦ X t j ω with hV_def
    have hV : Measurable V := measurable_pi_iff.2 fun j ↦ h.measurable_lineage t j
    have h1 : ∫⁻ ω in S, ENNReal.ofReal (z ^ cloneSize T X t ω) ∂P =
        ∫⁻ ω in S, (fun m : Fin n → ℕ ↦ ENNReal.ofReal (z ^ ∑ j, m j)) (V ω) ∂P := by
      refine setLIntegral_congr_fun hS fun ω hω ↦ ?_
      have hω' : count T t ω = n := hω
      simp only [cloneSize, hω', hV_def, Fin.sum_univ_eq_sum_range (fun j ↦ X t j ω)]
    have hmap := lintegral_map (μ := P.restrict S)
      (measurable_of_countable (fun m : Fin n → ℕ ↦ ENNReal.ofReal (z ^ ∑ j, m j))) hV
    rw [h1, ← hmap, lintegral_countable']
    have h2 : ∀ m : Fin n → ℕ, (P.restrict S).map V {m} = ∫⁻ ω in S, ∏ j : Fin n,
        ENNReal.ofReal (LinearBirthDeath.prob b d (t - arrivalTime T (j + 1) ω) (m j)) ∂P := by
      intro m
      rw [Measure.map_apply hV (measurableSet_singleton _),
        Measure.restrict_apply (hV (measurableSet_singleton _))]
      have := h.measure_lineage t n univ MeasurableSet.univ m
      simp only [mem_univ, true_and] at this
      convert this using 2
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, hV_def, funext_iff, hS_def,
        mem_ofPred_eq]
      tauto
    simp_rw [h2]
    have hmeas : ∀ m : Fin n → ℕ, Measurable fun ω ↦ ∏ j : Fin n,
        ENNReal.ofReal (LinearBirthDeath.prob b d (t - arrivalTime T (j + 1) ω) (m j)) := by
      intro m
      refine Finset.measurable_prod _ fun j _ ↦ ENNReal.measurable_ofReal.comp ?_
      have hm : Measurable (arrivalTime T (j + 1)) := by
        unfold arrivalTime
        exact Finset.measurable_sum _ fun i _ ↦ h.measurable_interarrival i
      exact (measurable_prob b d (m j)).comp (measurable_const.sub hm)
    simp_rw [← lintegral_const_mul _ (hmeas _)]
    rw [← lintegral_tsum fun m ↦ ((hmeas m).const_mul _).aemeasurable]
    refine setLIntegral_congr_fun_ae hS ?_
    filter_upwards [Filter.EventuallyEqSet.mem_iff (h.count_ae_eq_gap hlam t n),
      h.ae_nonneg hlam] with ω hgap hnn hω
    have hgap' := hgap.2 hω
    have hage : ∀ j : Fin n, 0 ≤ (t : ℝ) - arrivalTime T (j + 1) ω := by
      intro j
      have hmono : arrivalTime T (j + 1) ω ≤ arrivalTime T n ω := by
        simp only [arrivalTime]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
          fun i _ _ ↦ hnn i
      linarith [hgap'.1]
    calc ∑' m : Fin n → ℕ, ENNReal.ofReal (z ^ ∑ j, m j) * ∏ j : Fin n,
          ENNReal.ofReal (LinearBirthDeath.prob b d (t - arrivalTime T (j + 1) ω) (m j))
        = ∑' m : Fin n → ℕ, ∏ j : Fin n, ENNReal.ofReal
            (LinearBirthDeath.prob b d (t - arrivalTime T (j + 1) ω) (m j) * z ^ m j) := by
          refine tsum_congr fun m ↦ ?_
          rw [← Finset.prod_pow_eq_pow_sum, ENNReal.ofReal_prod_of_nonneg
            fun j _ ↦ pow_nonneg hz0 _, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun j _ ↦ ?_
          rw [← ENNReal.ofReal_mul (pow_nonneg hz0 _), mul_comm]
      _ = ∏ j : Fin n, ∑' k : ℕ, ENNReal.ofReal
            (LinearBirthDeath.prob b d (t - arrivalTime T (j + 1) ω) k * z ^ k) :=
          tsum_prod_fin n fun j k ↦ ENNReal.ofReal
            (LinearBirthDeath.prob b d (t - arrivalTime T (j + 1) ω) k * z ^ k)
      _ = ∏ j : Fin n, ENNReal.ofReal (g (arrivalTime T (j + 1) ω)) := by
          refine Finset.prod_congr rfl fun j _ ↦ ?_
          have hs := hasSum_prob_mul_pow hd hdb (hage j) hz0 hz1
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ mul_nonneg
            (LinearBirthDeath.prob_nonneg hb.le hd (hage j) k) (pow_nonneg hz0 k)) hs.summable,
            hs.tsum_eq, hg_def]
          simp only [max_eq_left (hage j)]
  rw [← setLIntegral_univ, show (univ : Set Ω) = ⋃ n : ℕ, count T t ⁻¹' {n} by
      ext ω; simp,
    lintegral_iUnion (fun n ↦ h.measurable_count t (measurableSet_singleton n))
      (fun i j hij ↦ Set.disjoint_left.2 fun ω hi hj ↦ hij (hi.symm.trans hj))]
  have hn' : ∀ n : ℕ, ∫⁻ ω in count T t ⁻¹' {n}, ENNReal.ofReal (z ^ cloneSize T X t ω) ∂P =
      ENNReal.ofReal (exp (-(lam * t)) * lam ^ n * I ^ n / n !) := hn
  rw [tsum_congr hn']
  have hnn : ∀ n : ℕ, 0 ≤ exp (-(lam * t)) * lam ^ n * I ^ n / n ! := by
    have : 0 ≤ I := intervalIntegral.integral_nonneg t.coe_nonneg fun s _ ↦ hg0 s
    intro n
    positivity
  have hsum : HasSum (fun n : ℕ ↦ exp (-(lam * t)) * lam ^ n * I ^ n / n !)
      (exp (-(lam * t)) * exp (lam * I)) := by
    have := (NormedSpace.expSeries_div_hasSum_exp (lam * I : ℝ)).mul_left (exp (-(lam * t)))
    rw [← Real.exp_eq_exp_ℝ] at this
    convert this using 1
    funext n
    rw [mul_pow]
    ring
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable, hsum.tsum_eq]

/-- **The generating function of the clone size.** For `0 ≤ d < b`, `t ≥ 0` and `0 ≤ z ≤ 1`,
`E z^{y(t)} = (q / (1 - (1 - q) z))^{lam / b}` with `q = successProb b d t`: the generating
function of the negative binomial law with shape `lam / b` and success probability `q`
(Kendall 1948, for the birth–death–immigration process). -/
theorem lintegral_pow_cloneSize (h : IsClonalSeeding P lam b d T X) (hlam : 0 < lam)
    (hd : 0 ≤ d) (hdb : d < b) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (z ^ cloneSize T X t ω) ∂P = ENNReal.ofReal
      ((successProb b d t / (1 - (1 - successProb b d t) * z)) ^ ((lam : ℝ) / b)) := by
  rw [h.lintegral_ofReal_pow_cloneSize hlam hd hdb hz0 hz1 t,
    exp_mul_exp_integral_lineagePGF (lam : ℝ) hdb (by linarith) hz1 t.coe_nonneg]

lemma measurable_cloneSize (h : IsClonalSeeding P lam b d T X) (t : ℝ≥0) :
    Measurable (cloneSize T X t) := by
  have hf : Measurable fun p : ℕ × Ω ↦ ∑ j ∈ Finset.range p.1, X t j p.2 :=
    measurable_from_prod_countable_right fun n ↦
      (Finset.measurable_sum (Finset.range n) fun j _ ↦ h.measurable_lineage t j :)
  exact hf.comp ((h.measurable_count t).prodMk measurable_id)

/-- **The clone size is negative binomial** (Heyde, Reiter, Naxerova & Nowak 2019, Eq. [2]):
for `0 ≤ d < b` and `t ≥ 0`, `P(y(t) = m) = NB(m; lam / b, q(t))` with
`q(t) = ρ / (ρ + e^{(b-d) t} - 1)`, `ρ = 1 - d / b`. -/
theorem measureReal_cloneSize (h : IsClonalSeeding P lam b d T X) (hlam : 0 < lam)
    (hd : 0 ≤ d) (hdb : d < b) (t : ℝ≥0) (m : ℕ) :
    P.real {ω | cloneSize T X t ω = m} = negBinomialPMF (lam / b) (successProb b d t) m := by
  have hP := h.isProbabilityMeasure hlam
  have hb : 0 < b := by linarith
  have hk : 0 < (lam : ℝ) / b := div_pos (NNReal.coe_pos.2 hlam) hb
  have hq := successProb_pos hdb hb t.coe_nonneg
  have hq1 := successProb_le_one hdb hb t.coe_nonneg
  have hY := h.measurable_cloneSize t
  set p : ℕ → ℝ := fun m ↦ P.real {ω | cloneSize T X t ω = m} with hp
  set nb : ℕ → ℝ := negBinomialPMF (lam / b) (successProb b d t) with hnb
  suffices p = nb from congr_fun this m
  have hp0 : ∀ m, 0 ≤ p m := fun m ↦ measureReal_nonneg
  have hnb0 : ∀ m, 0 ≤ nb m := negBinomialPMF_nonneg hk hq.le hq1
  apply eq_of_tsum_mul_pow_eq
  · intro m
    rw [abs_of_nonneg (hp0 m)]
    exact measureReal_le_one
  · intro m
    rw [abs_of_nonneg (hnb0 m)]
    exact le_hasSum (hasSum_negBinomialPMF hk hq hq1) m fun j _ ↦ hnb0 j
  · intro z hz
    have hz0 := hz.1.le
    have hz1 := hz.2.le
    have hpgf := h.lintegral_ofReal_pow_cloneSize hlam hd hdb hz0 hz1 t
    rw [exp_mul_exp_integral_lineagePGF (lam : ℝ) hdb hb hz1 t.coe_nonneg,
      lintegral_comp_nat hY (fun m ↦ ENNReal.ofReal (z ^ m))] at hpgf
    have hnbsum := hasSum_negBinomialPMF_mul_pow hk hq hq1 hz0 hz1
    have hsp : Summable fun m ↦ p m * z ^ m := by
      refine Summable.of_norm_bounded (g := fun m ↦ z ^ m)
        (summable_geometric_of_lt_one hz0 hz.2) fun m ↦ ?_
      rw [norm_mul, norm_pow, Real.norm_of_nonneg hz0, Real.norm_of_nonneg (hp0 m)]
      exact mul_le_of_le_one_left (pow_nonneg hz0 m) measureReal_le_one
    have hl : ∑' m, ENNReal.ofReal (z ^ m) * P {ω | cloneSize T X t ω = m} =
        ENNReal.ofReal (∑' m, p m * z ^ m) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun m ↦ mul_nonneg (hp0 m) (pow_nonneg hz0 m)) hsp]
      refine tsum_congr fun m ↦ ?_
      rw [ENNReal.ofReal_mul (hp0 m), mul_comm, hp, ofReal_measureReal (measure_ne_top _ _)]
    rw [hl, ← hnbsum.tsum_eq] at hpgf
    exact (ENNReal.ofReal_eq_ofReal_iff
      (tsum_nonneg fun m ↦ mul_nonneg (hp0 m) (pow_nonneg hz0 m))
      (tsum_nonneg fun m ↦ mul_nonneg (hnb0 m) (pow_nonneg hz0 m))).1 hpgf

/-- **The mean clone size** (Heyde, Reiter, Naxerova & Nowak 2019, Eq. [1]): for `0 ≤ d < b`
and `t ≥ 0`, `y(t)` is integrable with `E y(t) = (k / ρ) (e^{(b-d) t} - 1)`, `k = lam / b`,
`ρ = 1 - d / b`. -/
theorem integral_cloneSize (h : IsClonalSeeding P lam b d T X) (hlam : 0 < lam) (hd : 0 ≤ d)
    (hdb : d < b) (t : ℝ≥0) :
    Integrable (fun ω ↦ (cloneSize T X t ω : ℝ)) P ∧
      ∫ ω, (cloneSize T X t ω : ℝ) ∂P = meanSize lam b d t := by
  have hP := h.isProbabilityMeasure hlam
  have hb : 0 < b := by linarith
  have hk : 0 < (lam : ℝ) / b := div_pos (NNReal.coe_pos.2 hlam) hb
  have hY := h.measurable_cloneSize t
  have hμ : 0 ≤ meanSize lam b d t := by
    rw [meanSize_eq hb]
    have : 1 ≤ exp ((b - d) * t) := one_le_exp (mul_nonneg (by linarith) t.coe_nonneg)
    have : 0 ≤ (lam : ℝ) / (b - d) := div_nonneg lam.coe_nonneg (by linarith)
    nlinarith
  have hlaw : ∀ m, P.real {ω | cloneSize T X t ω = m} =
      negBinomialReal (lam / b) (meanSize lam b d t) m := fun m ↦ by
    rw [h.measureReal_cloneSize hlam hd hdb t m, negBinomialReal_eq_negBinomialPMF hk hμ,
      successProb_eq_div hdb hb (NNReal.coe_pos.2 hlam) t.coe_nonneg, add_comm]
  have hsum := hasSum_mul_negBinomialReal hk hμ
  have hlin : ∫⁻ ω, ENNReal.ofReal (cloneSize T X t ω) ∂P =
      ENNReal.ofReal (meanSize lam b d t) := by
    rw [lintegral_comp_nat hY (fun m ↦ ENNReal.ofReal m), ← hsum.tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg (fun m ↦ mul_nonneg (Nat.cast_nonneg m)
        (negBinomialReal_nonneg hk hμ m)) hsum.summable]
    refine tsum_congr fun m ↦ ?_
    rw [← hlaw m, ENNReal.ofReal_mul (Nat.cast_nonneg m), ofReal_measureReal (measure_ne_top _ _)]
  have hm : AEStronglyMeasurable (fun ω ↦ (cloneSize T X t ω : ℝ)) P :=
    (measurable_of_countable (fun m : ℕ ↦ (m : ℝ))).comp hY |>.aestronglyMeasurable
  have h0 : 0 ≤ᵐ[P] fun ω ↦ (cloneSize T X t ω : ℝ) := ae_of_all _ fun ω ↦ Nat.cast_nonneg _
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal h0).2 (by rw [hlin]; exact ENNReal.ofReal_lt_top)⟩,
    ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae h0 hm, hlin, ENNReal.toReal_ofReal hμ]

end IsClonalSeeding

/-- The clone size at time `t` as a function of the clone's data: its interarrival sequence and
its lineage sizes. -/
private noncomputable def cloneSizeOf (t : ℝ≥0) (p : (ℕ → ℝ) × (ℝ≥0 → ℕ → ℕ)) : ℕ :=
  ∑ j ∈ Finset.range (count (fun n (x : ℕ → ℝ) ↦ x n) t p.1), p.2 t j

private lemma measurable_count_seq (t : ℝ≥0) : Measurable (count (fun n (x : ℕ → ℝ) ↦ x n) t) := by
  unfold count
  refine measurable_ncard.comp (measurable_set_iff.2 fun n ↦ ?_)
  have hm : Measurable (arrivalTime (fun n (x : ℕ → ℝ) ↦ x n) (n + 1)) := by
    unfold arrivalTime
    exact Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
  exact measurableSet_setOfPred.1 (measurableSet_le hm measurable_const)

private lemma measurable_cloneSizeOf (t : ℝ≥0) : Measurable (cloneSizeOf t) := by
  have hc := measurable_count_seq t
  have hf : Measurable fun q : ℕ × ((ℕ → ℝ) × (ℝ≥0 → ℕ → ℕ)) ↦
      ∑ j ∈ Finset.range q.1, q.2.2 t j :=
    measurable_from_prod_countable_right fun n ↦ (Finset.measurable_sum (Finset.range n)
      fun j _ ↦ (by fun_prop : Measurable fun p : (ℕ → ℝ) × (ℝ≥0 → ℕ → ℕ) ↦ p.2 t j) :)
  exact hf.comp ((hc.comp measurable_fst).prodMk measurable_id)

private lemma cloneSize_eq_cloneSizeOf (T : ℕ → Ω → ℝ) (X : ℝ≥0 → ℕ → Ω → ℕ) (t : ℝ≥0) (ω : Ω) :
    cloneSize T X t ω = cloneSizeOf t ((fun n ↦ T n ω), fun s j ↦ X s j ω) := rfl

/-- Clones whose data are independent have independent sizes. -/
theorem iIndepFun_cloneSize {ι : Type*} {T : ι → ℕ → Ω → ℝ} {X : ι → ℝ≥0 → ℕ → Ω → ℕ}
    (hind : iIndepFun (fun i ω ↦ ((fun n ↦ T i n ω), fun s j ↦ X i s j ω)) P) (t : ℝ≥0) :
    iIndepFun (fun i ↦ cloneSize (T i) (X i) t) P :=
  hind.comp (fun _ ↦ cloneSizeOf t) fun _ ↦ measurable_cloneSizeOf t

/-- **Negative binomial clone sizes under consecutive seeding** (Heyde, Reiter, Naxerova &
Nowak 2019, Eqs. [1] and [2]).

A primary tumour has clones `i : ι` of constant size. Cells of clone `i` arrive at a metastatic
site as a Poisson process of rate `lam i > 0`, starting at time `0` with an empty site, and each
arriving cell founds an independent linear birth–death process with division rate `b` and death
rate `d`, `b > d > 0`, the same for all clones (`IsClonalSeeding`, with interarrival times
`T i` and lineage sizes `X i`); the clones' data are independent. Write `k_i = lam i / b`,
`ρ = 1 - d / b` and `r = b - d`. Then:

* the mean clone size `ȳ_i(t) = (k_i / ρ) (e^{r t} - 1)` (`meanSize`) solves
  `ȳ_i' = r ȳ_i + lam i` with `ȳ_i(0) = 0`;
* for every `t ≥ 0`, the clone size `y_i(t)` (`cloneSize`) is integrable with mean `ȳ_i(t)`;
* `y_i(t)` is negative binomial with shape `k_i` and success probability
  `q(t) = ρ / (ρ + e^{r t} - 1)` (`successProb`), the same for every clone:
  `P(y_i(t) = m) = k_i^{(m)} / m! · q(t)^{k_i} (1 - q(t))^m = Γ(m + k_i) / (Γ(k_i) m!) ·
  q(t)^{k_i} (1 - q(t))^m` for every `m`;
* `q(t) = k_i / (ȳ_i(t) + k_i)`;
* the clone sizes `y_i(t)`, `i : ι`, are independent. -/
theorem negBinomial_cloneSizes {ι : Type*} {lam : ι → ℝ≥0} {b d : ℝ} {T : ι → ℕ → Ω → ℝ}
    {X : ι → ℝ≥0 → ℕ → Ω → ℕ} (hd : 0 < d) (hdb : d < b) (hlam : ∀ i, 0 < lam i)
    (h : ∀ i, IsClonalSeeding P (lam i) b d (T i) (X i))
    (hind : iIndepFun (fun i ω ↦ ((fun n ↦ T i n ω), fun s j ↦ X i s j ω)) P) :
    (∀ i, meanSize (lam i) b d 0 = 0 ∧
      ∀ s, HasDerivAt (meanSize (lam i) b d) ((b - d) * meanSize (lam i) b d s + lam i) s) ∧
    ∀ t : ℝ≥0,
      (∀ i, Integrable (fun ω ↦ (cloneSize (T i) (X i) t ω : ℝ)) P ∧
        ∫ ω, (cloneSize (T i) (X i) t ω : ℝ) ∂P = meanSize (lam i) b d t) ∧
      (∀ i m, P.real {ω | cloneSize (T i) (X i) t ω = m} =
        negBinomialPMF (lam i / b) (successProb b d t) m) ∧
      (∀ i, successProb b d t = lam i / b / (meanSize (lam i) b d t + lam i / b)) ∧
      iIndepFun (fun i ↦ cloneSize (T i) (X i) t) P := by
  have hb : 0 < b := by linarith
  refine ⟨fun i ↦ ⟨meanSize_zero _ _ _, hasDerivAt_meanSize hdb hb⟩, fun t ↦
    ⟨fun i ↦ (h i).integral_cloneSize (hlam i) hd.le hdb t,
      fun i m ↦ (h i).measureReal_cloneSize (hlam i) hd.le hdb t m,
      fun i ↦ successProb_eq_div hdb hb (NNReal.coe_pos.2 (hlam i)) t.coe_nonneg,
      iIndepFun_cloneSize hind t⟩⟩

/-! ### The model exists -/

/-- `P(X(a) < m)` for Kendall's law of a lineage of age `a`. -/
private noncomputable def kendallBelow (b d a : ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m, LinearBirthDeath.prob b d a i

/-- The quantile function of Kendall's law: the number of `k` with `P(X(a) ≤ k) < v`. For `v`
uniform on `(0, 1)` it has Kendall's law. -/
private noncomputable def kendallQuantile (b d a v : ℝ) : ℕ :=
  {k : ℕ | kendallBelow b d a (k + 1) < v}.ncard

private lemma measurable_kendallQuantile (b d : ℝ) :
    Measurable fun p : ℝ × ℝ ↦ kendallQuantile b d p.1 p.2 := by
  unfold kendallQuantile
  refine measurable_ncard.comp (measurable_set_iff.2 fun k ↦ ?_)
  have hm : Measurable fun p : ℝ × ℝ ↦ kendallBelow b d p.1 (k + 1) := by
    unfold kendallBelow
    exact Finset.measurable_sum _ fun i _ ↦ (measurable_prob b d i).comp measurable_fst
  exact measurableSet_setOfPred.1 (measurableSet_lt hm measurable_snd)

private lemma Measurable.kendallQuantile {α : Type*} {mα : MeasurableSpace α} (b d : ℝ)
    {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x ↦ kendallQuantile b d (f x) (g x) := by
  unfold ConsecutiveSeeding.kendallQuantile
  refine measurable_ncard.comp (measurable_set_iff.2 fun k ↦ ?_)
  have hm : Measurable fun x ↦ kendallBelow b d (f x) (k + 1) := by
    unfold kendallBelow
    exact Finset.measurable_sum _ fun i _ ↦ (measurable_prob b d i).comp hf
  exact measurableSet_setOfPred.1 (measurableSet_lt hm hg)

private lemma kendallBelow_mono {b d a : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (ha : 0 ≤ a) :
    Monotone (kendallBelow b d a) := by
  intro m n hmn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hmn)
    fun i _ _ ↦ LinearBirthDeath.prob_nonneg hb hd ha i

private lemma kendallBelow_le_one {b d a : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (ha : 0 ≤ a) (m : ℕ) :
    kendallBelow b d a m ≤ 1 :=
  sum_le_hasSum _ (fun i _ ↦ LinearBirthDeath.prob_nonneg hb hd ha i)
    (LinearBirthDeath.hasSum_prob hb hd ha)

private lemma kendallQuantile_eq_iff {b d a v : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (ha : 0 ≤ a)
    (hv0 : 0 < v) (hv1 : v < 1) (m : ℕ) :
    kendallQuantile b d a v = m ↔ kendallBelow b d a m < v ∧ v ≤ kendallBelow b d a (m + 1) := by
  have hmono := kendallBelow_mono hb hd ha
  set S := {k : ℕ | kendallBelow b d a (k + 1) < v} with hS
  have hfin : S.Finite := by
    have ht := (LinearBirthDeath.hasSum_prob hb hd ha).tendsto_sum_nat
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (ht.eventually (lt_mem_nhds hv1))
    refine (Set.finite_Iio N).subset fun k hk ↦ ?_
    by_contra hkN
    have := hN (k + 1) (by simp at hkN; omega)
    exact absurd hk (not_lt.2 this.le)
  have hdown : ∀ k ∈ S, ∀ k' ≤ k, k' ∈ S := fun k hk k' hk' ↦
    lt_of_le_of_lt (hmono (by omega)) hk
  have hIio : S = Iio S.ncard := by
    have hcard := Set.ncard_eq_toFinset_card S hfin
    ext k
    constructor
    · intro hk
      by_contra hkc
      simp only [mem_Iio, not_lt] at hkc
      have hsub : Iic k ⊆ S := fun k' hk' ↦ hdown k hk k' hk'
      have := Set.ncard_le_ncard hsub hfin
      rw [Set.ncard_eq_toFinset_card' (Iic k), Set.toFinset_Iic, Nat.card_Iic] at this
      omega
    · intro hk
      by_contra hkS
      have hsub : S ⊆ Iio k := fun k' hk' ↦ by
        by_contra h
        simp only [mem_Iio, not_lt] at h
        exact hkS (hdown k' hk' k h)
      have := Set.ncard_le_ncard hsub (Set.finite_Iio k)
      rw [Set.ncard_Iio_nat] at this
      simp only [mem_Iio] at hk
      omega
  unfold kendallQuantile
  rw [← hS]
  constructor
  · intro hm
    rw [hm] at hIio
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hpos
      · simp [kendallBelow, hv0]
      · have : m - 1 ∈ S := by rw [hIio]; simp; omega
        simpa [hS, Nat.sub_add_cancel hpos] using this
    · have : m ∉ S := by rw [hIio]; simp
      simpa [hS] using this
  · rintro ⟨h1, h2⟩
    have : S = Iio m := by
      ext k
      simp only [hS, mem_ofPred_eq, mem_Iio]
      constructor
      · intro hk
        by_contra hkm
        exact absurd (lt_of_le_of_lt (hmono (by omega)) hk) (not_lt.2 h2)
      · intro hk
        exact lt_of_le_of_lt (hmono (by omega)) h1
    rw [this, Set.ncard_Iio_nat]

/-- The uniform law on `(0, 1)`. -/
private noncomputable abbrev unifIoo : Measure ℝ := volume.restrict (Ioo 0 1)

private instance : IsProbabilityMeasure unifIoo := ⟨by simp [unifIoo]⟩

private lemma unifIoo_kendallQuantile {b d a : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (ha : 0 ≤ a) (m : ℕ) :
    unifIoo {v | kendallQuantile b d a v = m} =
      ENNReal.ofReal (LinearBirthDeath.prob b d a m) := by
  have hm : MeasurableSet {v : ℝ | kendallQuantile b d a v = m} :=
    (measurable_kendallQuantile b d).comp (measurable_const.prodMk measurable_id)
      (measurableSet_singleton m)
  rw [Measure.restrict_apply hm]
  have hx0 : 0 ≤ kendallBelow b d a m :=
    Finset.sum_nonneg fun i _ ↦ LinearBirthDeath.prob_nonneg hb hd ha i
  have hy1 := kendallBelow_le_one hb hd ha (m + 1)
  have hseq : {v : ℝ | kendallQuantile b d a v = m} ∩ Ioo 0 1 =
      Ioc (kendallBelow b d a m) (kendallBelow b d a (m + 1)) ∩ Ioo 0 1 := by
    ext v
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioc, mem_Ioo]
    constructor
    · rintro ⟨hq, hv⟩
      exact ⟨(kendallQuantile_eq_iff hb hd ha hv.1 hv.2 m).1 hq, hv⟩
    · rintro ⟨hq, hv⟩
      exact ⟨(kendallQuantile_eq_iff hb hd ha hv.1 hv.2 m).2 hq, hv⟩
  rw [hseq]
  have hdiff : kendallBelow b d a (m + 1) - kendallBelow b d a m =
      LinearBirthDeath.prob b d a m := by
    simp [kendallBelow, Finset.sum_range_succ]
  apply le_antisymm
  · calc volume (Ioc (kendallBelow b d a m) (kendallBelow b d a (m + 1)) ∩ Ioo 0 1)
        ≤ volume (Ioc (kendallBelow b d a m) (kendallBelow b d a (m + 1))) :=
          measure_mono inter_subset_left
      _ = _ := by rw [Real.volume_Ioc, hdiff]
  · calc ENNReal.ofReal (LinearBirthDeath.prob b d a m)
        = volume (Ioo (kendallBelow b d a m) (kendallBelow b d a (m + 1))) := by
          rw [Real.volume_Ioo, hdiff]
      _ ≤ _ := by
          refine measure_mono fun v hv ↦ ⟨⟨hv.1, hv.2.le⟩, ?_, ?_⟩
          · linarith [hv.1]
          · linarith [hv.2]

/-- Before the `n`-th arrival in `[0, t]` the arrival times are at most `t`. -/
private lemma psum_le_of_count_eq {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) {t : ℝ≥0} {n : ℕ}
    (hn : count (fun i (x : ℕ → ℝ) ↦ x i) t x = n) {j : ℕ} (hj : j < n) :
    psum x (j + 1) ≤ t := by
  by_contra hgt
  replace hgt := lt_of_not_ge hgt
  have hsub : {k : ℕ | arrivalTime (fun i (x : ℕ → ℝ) ↦ x i) (k + 1) x ≤ t} ⊆ Iio j := by
    intro k hk
    by_contra hkj
    simp only [mem_Iio, not_lt] at hkj
    have hmono : psum x (j + 1) ≤ psum x (k + 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
        fun i _ _ ↦ hx i
    exact absurd (lt_of_lt_of_le hgt hmono) (not_lt.2 hk)
  have := Set.ncard_le_ncard hsub (Set.finite_Iio j)
  rw [Set.ncard_Iio_nat] at this
  unfold count at hn
  omega

/-- A concrete probability space for the seeding model: i.i.d. exponential interarrival times
and i.i.d. uniform seeds on `(0, 1)`. -/
private noncomputable def seedingMeasure (lam : ℝ≥0) : Measure ((ℕ → ℝ) × (ℕ → ℝ)) :=
  (expSeq lam).prod (Measure.infinitePi fun _ : ℕ ↦ unifIoo)

/-- **The seeding model exists.** On `seedingMeasure lam`, with the `i`-th interarrival time the
`i`-th coordinate of the first sequence and the size at time `t` of the lineage founded by the
`(j + 1)`-th arriving cell given by the quantile function of Kendall's law at the lineage's age
applied to the `j`-th uniform seed, the hypotheses of `IsClonalSeeding` hold. -/
private theorem isClonalSeeding_seedingMeasure {lam : ℝ≥0} (hlam : 0 < lam) {b d : ℝ} (hb : 0 ≤ b)
    (hd : 0 ≤ d) :
    IsClonalSeeding (seedingMeasure lam) lam b d (fun i ω ↦ ω.1 i)
      (fun t j ω ↦ kendallQuantile b d (t - psum ω.1 (j + 1)) (ω.2 j)) := by
  have hr : 0 < (lam : ℝ) := NNReal.coe_pos.2 hlam
  have := isProbabilityMeasure_expMeasure hr
  have hU : ∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ ↦ unifIoo) i) := fun _ ↦ inferInstance
  have hE : ∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ ↦ expMeasure (lam : ℝ)) i) :=
    fun _ ↦ inferInstance
  have hfst : (seedingMeasure lam).map Prod.fst = expSeq lam := by
    rw [seedingMeasure, Measure.map_fst_prod, measure_univ, one_smul]
  have hlaw : ∀ i, (seedingMeasure lam).map (fun ω ↦ ω.1 i) = expMeasure lam := by
    intro i
    have h1 : (seedingMeasure lam).map (fun ω ↦ ω.1 i) =
        ((seedingMeasure lam).map Prod.fst).map (fun x : ℕ → ℝ ↦ x i) :=
      (Measure.map_map (measurable_pi_apply i) measurable_fst).symm
    rw [h1, hfst]
    exact Measure.infinitePi_map_eval (fun _ : ℕ ↦ expMeasure (lam : ℝ)) i
  have hQ : ∀ (t : ℝ≥0) (j : ℕ), Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) ↦
      kendallQuantile b d (t - psum ω.1 (j + 1)) (ω.2 j) := fun t j ↦ by
    have h0 : Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) ↦ psum ω.1 (j + 1) :=
      (measurable_psum (j + 1)).comp measurable_fst
    have h1 : Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) ↦ (t : ℝ) - psum ω.1 (j + 1) :=
      h0.const_sub (t : ℝ)
    have h2 : Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) ↦ ω.2 j :=
      (measurable_pi_apply j).comp measurable_snd
    exact Measurable.kendallQuantile b d h1 h2
  have hTm : ∀ i, Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) ↦ ω.1 i := fun i ↦
    (measurable_pi_apply i).comp measurable_fst
  have hTlaw : ∀ i, HasLaw (fun ω : (ℕ → ℝ) × (ℕ → ℝ) ↦ ω.1 i) (expMeasure lam)
      (seedingMeasure lam) := fun i ↦ ⟨(hTm i).aemeasurable, hlaw i⟩
  have hind : iIndepFun (fun i (ω : (ℕ → ℝ) × (ℕ → ℝ)) ↦ ω.1 i) (seedingMeasure lam) := by
    have : IsProbabilityMeasure (seedingMeasure lam) := by
      unfold seedingMeasure; infer_instance
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map hTm]
    simp_rw [hlaw]
    exact hfst
  refine ⟨hTm, hTlaw, hind, hQ, ?_⟩
  · intro t n A hA m
    set μ := expSeq lam
    set ν := Measure.infinitePi fun _ : ℕ ↦ unifIoo
    set B : Set (ℕ → ℝ) := A ∩ {x | count (fun i (x : ℕ → ℝ) ↦ x i) t x = n} with hB
    have hBm : MeasurableSet B := hA.inter (measurable_count_seq t (measurableSet_singleton n))
    set cyl : (ℕ → ℝ) → Set (ℕ → ℝ) := fun x ↦
      {u | ∀ j : Fin n, kendallQuantile b d (t - psum x (j + 1)) (u j) = m j} with hcyl
    have hset : {ω : (ℕ → ℝ) × (ℕ → ℝ) | (fun i ↦ ω.1 i) ∈ A ∧
        count (fun i ω ↦ ω.1 i) t ω = n ∧ ∀ j : Fin n,
          kendallQuantile b d (t - psum ω.1 (j + 1)) (ω.2 j) = m j} =
        {ω | ω.1 ∈ B ∧ ω.2 ∈ cyl ω.1} := by
      ext ω
      simp only [mem_ofPred_eq, hB, mem_inter_iff, hcyl, and_assoc]
      rfl
    have hsm : MeasurableSet {ω : (ℕ → ℝ) × (ℕ → ℝ) | ω.1 ∈ B ∧ ω.2 ∈ cyl ω.1} := by
      have h2 : {ω : (ℕ → ℝ) × (ℕ → ℝ) | ω.2 ∈ cyl ω.1} = ⋂ j : Fin n,
          {ω | kendallQuantile b d (t - psum ω.1 (j + 1)) (ω.2 j) = m j} := by
        ext ω
        simp [hcyl]
      have : {ω : (ℕ → ℝ) × (ℕ → ℝ) | ω.1 ∈ B ∧ ω.2 ∈ cyl ω.1} =
          Prod.fst ⁻¹' B ∩ {ω | ω.2 ∈ cyl ω.1} := rfl
      rw [this, h2]
      exact (hBm.preimage measurable_fst).inter
        (MeasurableSet.iInter fun j ↦ hQ t j (measurableSet_singleton _))
    rw [hset, seedingMeasure, Measure.prod_apply hsm]
    have hsec : ∀ x, ν (Prod.mk x ⁻¹' {ω | ω.1 ∈ B ∧ ω.2 ∈ cyl ω.1}) =
        B.indicator (fun x ↦ ν (cyl x)) x := by
      intro x
      by_cases hx : x ∈ B
      · rw [indicator_of_mem hx]
        congr 1
        ext u
        simp only [mem_preimage, mem_ofPred_eq]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨hx, h⟩⟩
      · rw [indicator_of_notMem hx]
        convert measure_empty (μ := ν)
        ext u
        simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun h ↦ absurd h hx
    change ∫⁻ x, ν (Prod.mk x ⁻¹' {ω | ω.1 ∈ B ∧ ω.2 ∈ cyl ω.1}) ∂μ = _
    simp_rw [hsec]
    -- the right-hand side as an integral over the interarrival sequences
    have hF : Measurable fun x : ℕ → ℝ ↦ ∏ j : Fin n,
        ENNReal.ofReal (LinearBirthDeath.prob b d (t - psum x (j + 1)) (m j)) :=
      Finset.measurable_prod _ fun j _ ↦ ENNReal.measurable_ofReal.comp
        ((measurable_prob b d _).comp (measurable_const.sub (measurable_psum _)))
    have hrhs : ∫⁻ ω in {ω : (ℕ → ℝ) × (ℕ → ℝ) | (fun i ↦ ω.1 i) ∈ A ∧
          count (fun i ω ↦ ω.1 i) t ω = n}, ∏ j : Fin n, ENNReal.ofReal
            (LinearBirthDeath.prob b d (t - arrivalTime (fun i ω ↦ ω.1 i) (j + 1) ω) (m j))
            ∂(seedingMeasure lam) =
        ∫⁻ x, B.indicator (fun x ↦ ∏ j : Fin n,
          ENNReal.ofReal (LinearBirthDeath.prob b d (t - psum x (j + 1)) (m j))) x ∂μ := by
      have hpre : {ω : (ℕ → ℝ) × (ℕ → ℝ) | (fun i ↦ ω.1 i) ∈ A ∧
          count (fun i ω ↦ ω.1 i) t ω = n} = Prod.fst ⁻¹' B := rfl
      rw [hpre, ← lintegral_indicator (hBm.preimage measurable_fst)]
      change ∫⁻ ω, B.indicator (fun x ↦ ∏ j : Fin n,
          ENNReal.ofReal (LinearBirthDeath.prob b d (t - psum x (j + 1)) (m j))) ω.1
            ∂(seedingMeasure lam) = _
      rw [← lintegral_map (hF.indicator hBm) measurable_fst, hfst]
    refine Eq.trans ?_ hrhs.symm
    refine lintegral_congr_ae ?_
    filter_upwards [ae_expSeq_nonneg hr] with x hx
    by_cases hxB : x ∈ B
    · rw [indicator_of_mem hxB, indicator_of_mem hxB]
      have hcount : count (fun i (x : ℕ → ℝ) ↦ x i) t x = n := hxB.2
      have hage : ∀ j : Fin n, 0 ≤ (t : ℝ) - psum x (j + 1) := fun j ↦
        sub_nonneg.2 (psum_le_of_count_eq hx hcount j.2)
      have hpi : cyl x = Set.pi (Finset.range n : Set ℕ) fun k ↦
          if h : k < n then {v | kendallQuantile b d (t - psum x (k + 1)) v = m ⟨k, h⟩}
          else univ := by
        ext u
        simp only [hcyl, mem_ofPred_eq, Set.mem_pi, Finset.coe_range, mem_Iio]
        constructor
        · intro hu k hk
          simp only [hk, ↓reduceDIte, mem_ofPred_eq]
          exact hu ⟨k, hk⟩
        · intro hu j
          have := hu j j.2
          simpa [j.2] using this
      rw [hpi, Measure.infinitePi_pi (μ := fun _ : ℕ ↦ unifIoo) (fun k _ ↦ by
        split_ifs
        · exact Measurable.kendallQuantile b d measurable_const measurable_id
            (measurableSet_singleton _)
        · exact MeasurableSet.univ)]
      rw [← Fin.prod_univ_eq_prod_range (fun k ↦ unifIoo (if h : k < n then
        {v | kendallQuantile b d (t - psum x (k + 1)) v = m ⟨k, h⟩} else univ)) n]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      simp only [j.2, ↓reduceDIte, Fin.eta]
      exact unifIoo_kendallQuantile hb hd (hage j) (m j)
    · rw [indicator_of_notMem hxB, indicator_of_notMem hxB]

/-- The seeding model pulls back along a measure-preserving map. -/
lemma IsClonalSeeding.comp {lam : ℝ≥0} {b d : ℝ} {T : ℕ → Ω → ℝ} {X : ℝ≥0 → ℕ → Ω → ℕ}
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} {f : Ω' → Ω}
    (hf : MeasurePreserving f P' P) (h : IsClonalSeeding P lam b d T X) (hlam : 0 < lam) :
    IsClonalSeeding P' lam b d (fun i ω' ↦ T i (f ω')) (fun t j ω' ↦ X t j (f ω')) := by
  have hTm : ∀ i, Measurable fun ω' ↦ T i (f ω') := fun i ↦
    (h.measurable_interarrival i).comp hf.measurable
  have hmap : ∀ i, P'.map (fun ω' ↦ T i (f ω')) = P.map (T i) := fun i ↦ by
    rw [show (fun ω' ↦ T i (f ω')) = T i ∘ f from rfl,
      ← Measure.map_map (h.measurable_interarrival i) hf.measurable, hf.map_eq]
  refine ⟨hTm, fun i ↦ ⟨(hTm i).aemeasurable, by
      rw [hmap i, (h.hasLaw_interarrival i).map_eq]⟩, ?_,
    fun t j ↦ (h.measurable_lineage t j).comp hf.measurable, ?_⟩
  · have := h.isProbabilityMeasure hlam
    have : IsProbabilityMeasure P' := ⟨by
      rw [← Set.preimage_univ (f := f), hf.measure_preimage MeasurableSet.univ.nullMeasurableSet,
        measure_univ]⟩
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map hTm]
    simp_rw [hmap]
    rw [show (fun ω' i ↦ T i (f ω')) = (fun ω i ↦ T i ω) ∘ f from rfl,
      ← Measure.map_map h.measurable_seq hf.measurable, hf.map_eq]
    exact (iIndepFun_iff_map_fun_eq_infinitePi_map h.measurable_interarrival).1
      h.iIndepFun_interarrival
  · intro t n A hA m
    have hc := h.measurable_count t
    have hS' : MeasurableSet {ω | (fun i ↦ T i ω) ∈ A ∧ count T t ω = n} :=
      (hA.preimage h.measurable_seq).inter (hc (measurableSet_singleton n))
    have hS : MeasurableSet {ω | (fun i ↦ T i ω) ∈ A ∧ count T t ω = n ∧
        ∀ j : Fin n, X t j ω = m j} := by
      have : {ω | (fun i ↦ T i ω) ∈ A ∧ count T t ω = n ∧ ∀ j : Fin n, X t j ω = m j} =
          {ω | (fun i ↦ T i ω) ∈ A ∧ count T t ω = n} ∩
            ⋂ j : Fin n, X t j ⁻¹' {m j} := by
        ext ω
        simp [and_assoc]
      rw [this]
      exact hS'.inter (MeasurableSet.iInter fun j ↦
        h.measurable_lineage t j (measurableSet_singleton _))
    have hg : Measurable fun ω ↦ ∏ j : Fin n, ENNReal.ofReal
        (LinearBirthDeath.prob b d (t - arrivalTime T (j + 1) ω) (m j)) := by
      refine Finset.measurable_prod _ fun j _ ↦ ENNReal.measurable_ofReal.comp
        ((measurable_prob b d _).comp ?_)
      have : Measurable (arrivalTime T (j + 1)) := by
        unfold arrivalTime
        exact Finset.measurable_sum _ fun i _ ↦ h.measurable_interarrival i
      exact this.const_sub _
    have e1 : {ω' | (fun i ↦ T i (f ω')) ∈ A ∧ count (fun i ω' ↦ T i (f ω')) t ω' = n ∧
        ∀ j : Fin n, X t j (f ω') = m j} =
        f ⁻¹' {ω | (fun i ↦ T i ω) ∈ A ∧ count T t ω = n ∧ ∀ j : Fin n, X t j ω = m j} := rfl
    have e2 : {ω' | (fun i ↦ T i (f ω')) ∈ A ∧ count (fun i ω' ↦ T i (f ω')) t ω' = n} =
        f ⁻¹' {ω | (fun i ↦ T i ω) ∈ A ∧ count T t ω = n} := rfl
    rw [e1, hf.measure_preimage hS.nullMeasurableSet, h.measure_lineage t n A hA m, e2]
    exact (hf.setLIntegral_comp_preimage hS' hg).symm

private lemma isProbabilityMeasure_seedingMeasure {lam : ℝ≥0} (hlam : 0 < lam) :
    IsProbabilityMeasure (seedingMeasure lam) := by
  have := isProbabilityMeasure_expMeasure (NNReal.coe_pos.2 hlam)
  have : ∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ ↦ expMeasure (lam : ℝ)) i) :=
    fun _ ↦ inferInstance
  unfold seedingMeasure
  infer_instance

/-- The data of one clone in the concrete model: its interarrival sequence and the sizes of its
lineages at every time. -/
private noncomputable def seedingData (b d : ℝ) (ω : (ℕ → ℝ) × (ℕ → ℝ)) :
    (ℕ → ℝ) × (ℝ≥0 → ℕ → ℕ) :=
  (ω.1, fun t j ↦ kendallQuantile b d (t - psum ω.1 (j + 1)) (ω.2 j))

private lemma measurable_seedingData (b d : ℝ) : Measurable (seedingData b d) := by
  refine measurable_fst.prodMk (measurable_pi_iff.2 fun t ↦ measurable_pi_iff.2 fun j ↦ ?_)
  have h0 : Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) ↦ psum ω.1 (j + 1) :=
    (measurable_psum (j + 1)).comp measurable_fst
  have h1 : Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) ↦ (t : ℝ) - psum ω.1 (j + 1) :=
    h0.const_sub (t : ℝ)
  have h2 : Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) ↦ ω.2 j :=
    (measurable_pi_apply j).comp measurable_snd
  exact Measurable.kendallQuantile b d h1 h2

/-- **The seeding model exists**, for any family of clones. For rates `lam i > 0` and
`b, d ≥ 0` there is a probability space carrying, for every clone `i`, interarrival times
`T i` and lineage sizes `X i` with `IsClonalSeeding P (lam i) b d (T i) (X i)`, the clones'
data being independent: the hypotheses of `negBinomial_cloneSizes` can be met. The space is a
product, over the clones, of i.i.d. exponential interarrival times and i.i.d. uniform seeds,
each lineage's size at time `t` being the quantile function of Kendall's law at the lineage's
age applied to its seed. -/
theorem exists_isClonalSeeding {ι : Type u} (lam : ι → ℝ≥0) (hlam : ∀ i, 0 < lam i) {b d : ℝ}
    (hb : 0 ≤ b) (hd : 0 ≤ d) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (T : ι → ℕ → Ω → ℝ)
      (X : ι → ℝ≥0 → ℕ → Ω → ℕ), IsProbabilityMeasure P ∧
      (∀ i, IsClonalSeeding P (lam i) b d (T i) (X i)) ∧
      iIndepFun (fun i ω ↦ ((fun n ↦ T i n ω), fun s j ↦ X i s j ω)) P := by
  have := fun i ↦ isProbabilityMeasure_seedingMeasure (hlam i)
  refine ⟨ι → (ℕ → ℝ) × (ℕ → ℝ), inferInstance, Measure.infinitePi fun i ↦ seedingMeasure (lam i),
    fun i n ω ↦ (ω i).1 n,
    fun i t j ω ↦ kendallQuantile b d (t - psum (ω i).1 (j + 1)) ((ω i).2 j), inferInstance,
    fun i ↦ ?_, ?_⟩
  · exact (isClonalSeeding_seedingMeasure (hlam i) hb hd).comp
      (measurePreserving_eval_infinitePi (fun i ↦ seedingMeasure (lam i)) i) (hlam i)
  · exact iIndepFun_infinitePi (X := fun _ ↦ seedingData b d) fun _ ↦ measurable_seedingData b d

end Model

end MathlibExt.Biology.CancerGenomics.ConsecutiveSeeding
