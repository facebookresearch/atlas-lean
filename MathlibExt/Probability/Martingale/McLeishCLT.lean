/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import MathlibExt.Probability.LindebergFeller

import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.CramerWold
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# McLeish's martingale central limit theorem

For a martingale difference array, convergence of the realized quadratic variation plus a
negligibility condition on the increments (McLeish's conditions, implied by the Lindeberg
condition) gives a Gaussian limit for the row sums and finite-dimensional convergence of the
partial-sum process. No independence is assumed.

## Setting

Row `n` is a sequence `X n k` whose partial sums `∑_{j<k} X n j` form a martingale for a
filtration `F n` (so `X n k` is `F n (k+1)`-measurable with `E[X n k | F n k] = 0`); the row sum
runs over `k < r n`. The martingale property is asked for every `k`; a finite row of
martingale differences is extended by zeros. McLeish's conditions:
* (a) `E[max_{k<r n} X n k²]` is eventually bounded (stated with `∫⁻`, never vacuous);
* (b) `max_{k<r n} |X n k| → 0` in probability;
* (c) `∑_{k<r n} X n k² → v` in probability (realized quadratic variation).

## Main results

* `tendstoInDistribution_martingale_mcLeish`: (a)–(c) imply `∑_{k<r n} X n k → N(0, v)` in
  distribution (McLeish 1974, Theorem 2.3).
* `tendstoInDistribution_martingale_lindeberg`: the same under square integrability, the
  Lindeberg condition `LindebergConditionTriangular` (rows of length `n`), and (c).
* `tendstoInDistribution_fdd_martingale_mcLeish`: finite-dimensional convergence of
  `S n s = ∑_{k < N n s} X n k` along any linearly ordered time axis, given quadratic-variation
  convergence `∑_{k < N n s} X n k² → A s` at each time, to any process with centered Gaussian
  finite-dimensional laws of covariance `A (min s u)`.
* `tendstoInDistribution_fdd_martingale_lindeberg`: its Lindeberg form.

## Proof

McLeish's argument. Stop each row once the realized quadratic variation exceeds `K = v + 1`;
the stopping is predictable, so the stopped increments `X'` are still martingale differences,
and the stopped and original rows agree outside an event of vanishing probability. For the
stopped row, the product `T' = ∏ (1 + i t X'_k)` has mean `1` (each factor is integrated against
a bounded predictable multiplier) and satisfies `‖T'‖² ≤ e^{t² K} (1 + t² max_k X_k²)`, which is
bounded in `L¹` by (a). The comparison `‖e^{iy} - (1 + iy) e^{-y²/2}‖ ≤ 2 |y|³` (`|y| ≤ 1`) and a
telescoping product estimate give
`e^{i t S'} = T' e^{-t² ∑ X'²/2} + O(|t|³ max|X| ∑ X'²)`; (b) and (c) make the error and
`e^{-t² ∑ X'²/2} - e^{-v t²/2}` small in probability, and the `L²` bound on `T'` (through
`ab ≤ λ a² + λ⁻¹ b²`) turns this into convergence of characteristic functions. Lévy's continuity
theorem (`TendstoInDistribution.of_tendsto_charFun`) concludes. The finite-dimensional statement
applies the one-dimensional theorem to the weighted arrays `a n k X n k`,
`a n k = ∑_{s ∈ I} c s 𝟙{k < N n s}`, and uses the Cramér–Wold device
(`TendstoInDistribution.of_inner`).

## Scope and what is not proved

* The quadratic-variation hypothesis is the realized `∑ X²` (McLeish). The conditional-variance
  form `∑ E[X n k² | F n k] → v` with the conditional Lindeberg condition (Brown 1971;
  McLeish 1974, Corollary (3.8)) is not proved.
* McLeish's (a) asks `sup_n E[max X²] < ∞`; here it is only required eventually, which is weaker.
  McLeish normalizes the limit variance to `1` (and `A t = t` in Theorem (3.2)); here `v ≥ 0` and
  `A` are arbitrary.
* The finite-dimensional theorems take the limit process `Z` as a hypothesis, specified by its
  Gaussian finite-dimensional laws (`hZ`); Brownian motion, or `W ∘ A`, is not constructed here.
* Tightness and the functional CLT in `D[0,1]` are not proved here; the finite-dimensional
  statement is the input `hfdd` of `tendstoInDistribution_skorokhod_of_tight_of_fdd` in
  `MathlibExt.Probability.Martingale.FunctionalCLT`.

## Sources

D. L. McLeish, *Dependent central limit theorems and invariance principles*, Ann. Probab. 2
(1974), no. 4, 620–628: Theorem (2.1) (the product argument), Theorem (2.3) (martingale
difference arrays), Theorem (3.2) (the finite-dimensional, Cramér–Wold part of its proof).
P. Hall and C. C. Heyde, *Martingale Limit Theory and Its Application*, Academic Press (1980),
§3.2.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped ENNReal NNReal

namespace MathlibExt.Probability.Martingale

noncomputable section

/-! ### Elementary estimates -/

/-- `‖1 + i y‖² = 1 + y²`. -/
private lemma norm_one_add_mul_I_sq (y : ℝ) :
    ‖(1 : ℂ) + (y : ℂ) * Complex.I‖ ^ 2 = 1 + y ^ 2 := by
  rw [Complex.sq_norm]
  have := Complex.normSq_add_mul_I 1 y
  simpa using this

/-- `‖(1 + i y) e^{-y²/2}‖ ≤ 1`, from `1 + y² ≤ e^{y²}`. -/
private lemma norm_one_add_mul_I_mul_exp_le (y : ℝ) :
    ‖((1 : ℂ) + (y : ℂ) * Complex.I) * ((Real.exp (-(y ^ 2 / 2)) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h1 : ‖(1 : ℂ) + (y : ℂ) * Complex.I‖ ^ 2 ≤ Real.exp (y ^ 2) := by
    rw [norm_one_add_mul_I_sq]; linarith [Real.add_one_le_exp (y ^ 2)]
  have h2 : Real.exp (-(y ^ 2 / 2)) ^ 2 * Real.exp (y ^ 2) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; simp; ring_nf
  have h3 : (‖(1 : ℂ) + (y : ℂ) * Complex.I‖ * Real.exp (-(y ^ 2 / 2))) ^ 2 ≤ 1 := by
    rw [mul_pow]
    calc _ ≤ Real.exp (y ^ 2) * Real.exp (-(y ^ 2 / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 1 := by rw [mul_comm, h2]
  have h4 : 0 ≤ ‖(1 : ℂ) + (y : ℂ) * Complex.I‖ * Real.exp (-(y ^ 2 / 2)) := by positivity
  nlinarith

/-- **Third-order comparison.** For `|y| ≤ 1`,
`‖e^{iy} - (1 + iy) e^{-y²/2}‖ ≤ 2 |y|³`: both sides agree with `1 + iy - y²/2` to second
order. -/
private lemma norm_exp_mul_I_sub_le (y : ℝ) (hy : |y| ≤ 1) :
    ‖Complex.exp ((y : ℂ) * Complex.I) -
        ((1 : ℂ) + (y : ℂ) * Complex.I) * ((Real.exp (-(y ^ 2 / 2)) : ℝ) : ℂ)‖ ≤
      2 * |y| ^ 3 := by
  have hxn : ‖(y : ℂ) * Complex.I‖ = |y| := by simp
  -- first piece: `e^{iy}` against its quadratic Taylor polynomial
  have hA : ‖Complex.exp ((y : ℂ) * Complex.I) - (1 + (y : ℂ) * Complex.I - (y : ℂ) ^ 2 / 2)‖
      ≤ |y| ^ 3 * (2 / 9) := by
    have h := Complex.exp_bound (x := (y : ℂ) * Complex.I) (by rw [hxn]; exact hy)
      (n := 3) (by norm_num)
    have hsum : ∑ m ∈ range 3, ((y : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) =
        1 + (y : ℂ) * Complex.I - (y : ℂ) ^ 2 / 2 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, mul_pow,
        Complex.I_sq]
      push_cast; ring
    rw [hsum, hxn] at h
    refine h.trans (le_of_eq ?_)
    norm_num
  -- second piece: `(1 + iy) e^{-y²/2}` against the same polynomial
  set a : ℝ := y ^ 2 / 2 with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : |(-a)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg ha0, ha]
    have : y ^ 2 ≤ 1 := by
      have := abs_le.1 hy; nlinarith
    linarith
  have hexp : |Real.exp (-a) - 1 - (-a)| ≤ a ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le ha1
    simpa using this
  have hy2 : y ^ 2 ≤ |y| := by
    rw [← sq_abs]; nlinarith [abs_nonneg y]
  have hB : ‖((1 : ℂ) + (y : ℂ) * Complex.I) * ((Real.exp (-a) : ℝ) : ℂ) -
      (1 + (y : ℂ) * Complex.I - (y : ℂ) ^ 2 / 2)‖ ≤ |y| ^ 3 := by
    have hid : ((1 : ℂ) + (y : ℂ) * Complex.I) * ((Real.exp (-a) : ℝ) : ℂ) -
        (1 + (y : ℂ) * Complex.I - (y : ℂ) ^ 2 / 2) =
        ((1 : ℂ) + (y : ℂ) * Complex.I) * ((Real.exp (-a) - 1 - (-a) : ℝ) : ℂ) -
          ((y ^ 3 / 2 : ℝ) : ℂ) * Complex.I := by
      simp only [ha]; push_cast; ring
    rw [hid]
    have hn1 : ‖(1 : ℂ) + (y : ℂ) * Complex.I‖ ≤ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [hxn]; simp only [norm_one]; linarith
    calc _ ≤ ‖((1 : ℂ) + (y : ℂ) * Complex.I) * ((Real.exp (-a) - 1 - (-a) : ℝ) : ℂ)‖ +
          ‖((y ^ 3 / 2 : ℝ) : ℂ) * Complex.I‖ := norm_sub_le _ _
      _ ≤ 2 * a ^ 2 + |y| ^ 3 / 2 := by
          gcongr
          · rw [norm_mul]
            refine mul_le_mul hn1 ?_ (norm_nonneg _) (by norm_num)
            rw [Complex.norm_real, Real.norm_eq_abs]; exact hexp
          · simp
      _ ≤ |y| ^ 3 := by
          rw [ha]
          have h4 : (y ^ 2) ^ 2 ≤ |y| ^ 3 := by
            have : (y ^ 2) ^ 2 = |y| ^ 4 := by rw [show |y| ^ 4 = (|y| ^ 2) ^ 2 by ring, sq_abs]
            rw [this]
            have h0 := abs_nonneg y
            have : |y| ^ 4 = |y| ^ 3 * |y| := by ring
            rw [this]; nlinarith [pow_nonneg h0 3]
          nlinarith
  calc _ ≤ ‖Complex.exp ((y : ℂ) * Complex.I) - (1 + (y : ℂ) * Complex.I - (y : ℂ) ^ 2 / 2)‖ +
        ‖((1 : ℂ) + (y : ℂ) * Complex.I) * ((Real.exp (-a) : ℝ) : ℂ) -
          (1 + (y : ℂ) * Complex.I - (y : ℂ) ^ 2 / 2)‖ := by
          rw [norm_sub_rev (((1 : ℂ) + (y : ℂ) * Complex.I) * ((Real.exp (-a) : ℝ) : ℂ))]
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ |y| ^ 3 * (2 / 9) + |y| ^ 3 := add_le_add hA hB
    _ ≤ 2 * |y| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg y) 3]

/-- Telescoping: for factors of norm at most `1`,
`‖∏ aₖ - ∏ bₖ‖ ≤ ∑ ‖aₖ - bₖ‖`. -/
private lemma norm_prod_sub_prod_le (m : ℕ) (a b : ℕ → ℂ)
    (ha : ∀ k < m, ‖a k‖ ≤ 1) (hb : ∀ k < m, ‖b k‖ ≤ 1) :
    ‖∏ k ∈ range m, a k - ∏ k ∈ range m, b k‖ ≤ ∑ k ∈ range m, ‖a k - b k‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, prod_range_succ, sum_range_succ]
    have hpb : ‖∏ k ∈ range m, b k‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
        fun k hk => hb k (by have := mem_range.1 hk; omega)
    have hid : (∏ k ∈ range m, a k) * a m - (∏ k ∈ range m, b k) * b m =
        (∏ k ∈ range m, a k - ∏ k ∈ range m, b k) * a m +
          (∏ k ∈ range m, b k) * (a m - b m) := by ring
    rw [hid]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      calc _ ≤ ‖∏ k ∈ range m, a k - ∏ k ∈ range m, b k‖ * 1 :=
            mul_le_mul_of_nonneg_left (ha m (by omega)) (norm_nonneg _)
        _ ≤ _ := by
            rw [mul_one]
            exact ih (fun k hk => ha k (by omega)) (fun k hk => hb k (by omega))
    · rw [norm_mul]
      calc _ ≤ 1 * ‖a m - b m‖ := mul_le_mul_of_nonneg_right hpb (norm_nonneg _)
        _ = _ := one_mul _

/-- For `0 ≤ x, y`, `|e^{-x} - e^{-y}| ≤ |x - y|`. -/
private lemma abs_exp_neg_sub_exp_neg_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  wlog hxy : x ≤ y generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x]; exact this hy hx (by linarith)
  have h1 : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.2 (by linarith)
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  have h2 : Real.exp (-y) = Real.exp (-x) * Real.exp (-(y - x)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 := Real.add_one_le_exp (-(y - x))
  have h4 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h5 : 0 < Real.exp (-x) := Real.exp_pos _
  rw [h2]
  nlinarith

/-- `a b ≤ c a² + c⁻¹ b²` in `ℝ≥0∞`, for `c ≠ 0, ∞`. -/
private lemma ennreal_mul_le_add (a b c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞) :
    a * b ≤ c * a ^ 2 + c⁻¹ * b ^ 2 := by
  rcases le_total (c * a) b with h | h
  · have ha : a ≤ c⁻¹ * b := by
      calc a = c⁻¹ * (c * a) := by rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
        _ ≤ c⁻¹ * b := by gcongr
    calc a * b ≤ c⁻¹ * b * b := by gcongr
      _ = c⁻¹ * b ^ 2 := by ring
      _ ≤ _ := le_add_self
  · calc a * b ≤ a * (c * a) := by gcongr
      _ = c * a ^ 2 := by ring
      _ ≤ _ := le_self_add

/-! ### McLeish's stopping of a martingale difference row -/

section Row

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- Prefix sum of squares `∑_{j < k} X_j²` of a row (the realized quadratic variation up to,
but excluding, index `k`). -/
private def qvPrefix (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ := ∑ j ∈ range k, X j ω ^ 2

/-- McLeish's stopped increments: `X_k` is kept while the realized quadratic variation strictly
before `k` is at most `K`, and replaced by `0` afterwards. The keep/stop decision is predictable
(it depends on `X_0, …, X_{k-1}` only). -/
private def stopX (X : ℕ → Ω → ℝ) (K : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if qvPrefix X k ω ≤ K then X k ω else 0

/-- McLeish's product `∏_{j < k} (1 + i t X'_j)` for the stopped increments `X'`. -/
private def stopProd (X : ℕ → Ω → ℝ) (K t : ℝ) (k : ℕ) (ω : Ω) : ℂ :=
  ∏ j ∈ range k, (1 + ((t * stopX X K j ω : ℝ) : ℂ) * Complex.I)

private lemma qvPrefix_mono (X : ℕ → Ω → ℝ) {j k : ℕ} (hjk : j ≤ k) (ω : Ω) :
    qvPrefix X j ω ≤ qvPrefix X k ω :=
  sum_le_sum_of_subset_of_nonneg (range_mono hjk) fun _ _ _ => sq_nonneg _

private lemma qvPrefix_succ (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    qvPrefix X (k + 1) ω = qvPrefix X k ω + X k ω ^ 2 := by
  simp [qvPrefix, sum_range_succ]

private lemma stopX_eq_of_qvPrefix_le (X : ℕ → Ω → ℝ) {K : ℝ} {m : ℕ} {ω : Ω}
    (h : qvPrefix X m ω ≤ K) {k : ℕ} (hk : k < m) : stopX X K k ω = X k ω := by
  simp only [stopX, (qvPrefix_mono X hk.le ω).trans h, ite_true]

private lemma sq_stopX_le (X : ℕ → Ω → ℝ) (K : ℝ) (k : ℕ) (ω : Ω) :
    stopX X K k ω ^ 2 ≤ X k ω ^ 2 := by
  unfold stopX; split_ifs <;> simp [sq_nonneg]

private lemma norm_stopProd_sq (X : ℕ → Ω → ℝ) (K t : ℝ) (k : ℕ) (ω : Ω) :
    ‖stopProd X K t k ω‖ ^ 2 = ∏ j ∈ range k, (1 + (t * stopX X K j ω) ^ 2) := by
  rw [stopProd, norm_prod, ← prod_pow]
  exact prod_congr rfl fun j _ => norm_one_add_mul_I_sq _

/-- **McLeish's product bound.** If `X_j² ≤ M` for `j < k` and `K, M ≥ 0`, the stopped product
satisfies `∏_{j<k} (1 + t² X'_j²) ≤ e^{t² K} (1 + t² M)`; before stopping it is even
`≤ e^{t² ∑_{j<k} X_j²}`. Only the single increment that crosses the level `K` escapes the
exponential bound, which is why one power of `M` appears. -/
private lemma stopProd_bound (X : ℕ → Ω → ℝ) {K M : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (t : ℝ)
    (ω : Ω) (k : ℕ) (hXM : ∀ j < k, X j ω ^ 2 ≤ M) :
    (qvPrefix X k ω ≤ K →
        ∏ j ∈ range k, (1 + (t * stopX X K j ω) ^ 2) ≤ Real.exp (t ^ 2 * qvPrefix X k ω)) ∧
      ∏ j ∈ range k, (1 + (t * stopX X K j ω) ^ 2) ≤ Real.exp (t ^ 2 * K) * (1 + t ^ 2 * M) := by
  induction k with
  | zero =>
    simp only [range_zero, prod_empty]
    refine ⟨fun _ => by simp [qvPrefix], ?_⟩
    have h1 : 1 ≤ Real.exp (t ^ 2 * K) := Real.one_le_exp (by positivity)
    have h2 : 1 ≤ 1 + t ^ 2 * M := by nlinarith [sq_nonneg t]
    nlinarith
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih fun j hj => hXM j (by omega)
    have hXk := hXM k (by omega)
    have hQ0 : 0 ≤ ∏ j ∈ range k, (1 + (t * stopX X K j ω) ^ 2) :=
      prod_nonneg fun _ _ => by positivity
    rw [prod_range_succ]
    by_cases hk : qvPrefix X k ω ≤ K
    · have hstop : stopX X K k ω = X k ω := by simp only [stopX, hk, ite_true]
      rw [hstop]
      have hb := ih1 hk
      have hfac : 0 ≤ 1 + (t * X k ω) ^ 2 := by positivity
      have hstep : (∏ j ∈ range k, (1 + (t * stopX X K j ω) ^ 2)) * (1 + (t * X k ω) ^ 2) ≤
          Real.exp (t ^ 2 * qvPrefix X k ω) * (1 + (t * X k ω) ^ 2) :=
        mul_le_mul_of_nonneg_right hb hfac
      refine ⟨fun _ => ?_, ?_⟩
      · refine hstep.trans ?_
        rw [qvPrefix_succ, show t ^ 2 * (qvPrefix X k ω + X k ω ^ 2) =
          t ^ 2 * qvPrefix X k ω + t ^ 2 * X k ω ^ 2 by ring, Real.exp_add]
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have := Real.add_one_le_exp (t ^ 2 * X k ω ^ 2)
        nlinarith
      · refine hstep.trans ?_
        refine mul_le_mul (Real.exp_le_exp.2 ?_) ?_ hfac (Real.exp_pos _).le
        · exact mul_le_mul_of_nonneg_left hk (sq_nonneg t)
        · rw [mul_pow]; nlinarith [sq_nonneg t]
    · have hstop : stopX X K k ω = 0 := by simp only [stopX, hk, ite_false]
      rw [hstop]
      simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
        mul_one]
      refine ⟨fun h => absurd ((qvPrefix_mono X (Nat.le_succ k) ω).trans h) hk, ih2⟩

/-- The stopped quadratic variation is at most `K + M`. -/
private lemma sum_sq_stopX_le (X : ℕ → Ω → ℝ) {K M : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M)
    (ω : Ω) (k : ℕ)
    (hXM : ∀ j < k, X j ω ^ 2 ≤ M) :
    ∑ j ∈ range k, stopX X K j ω ^ 2 ≤ qvPrefix X k ω ∧
      ∑ j ∈ range k, stopX X K j ω ^ 2 ≤ K + M := by
  induction k with
  | zero =>
    simp only [range_zero, sum_empty, qvPrefix, le_refl, true_and]
    linarith
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih fun j hj => hXM j (by omega)
    rw [sum_range_succ, qvPrefix_succ]
    by_cases hk : qvPrefix X k ω ≤ K
    · have hstop : stopX X K k ω = X k ω := by simp only [stopX, hk, ite_true]
      rw [hstop]
      exact ⟨by linarith, by linarith [hXM k (by omega)]⟩
    · have hstop : stopX X K k ω = 0 := by simp only [stopX, hk, ite_false]
      rw [hstop]
      exact ⟨by nlinarith [sq_nonneg (X k ω)], by simpa using ih2⟩

end Row

/-! ### Measurability and the mean of McLeish's product -/

section Expectation

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

variable {μ : Measure Ω} {F : Filtration ℕ m0} {X : ℕ → Ω → ℝ}

private lemma stronglyMeasurable_qvPrefix (hX : ∀ k, StronglyMeasurable[F (k + 1)] (X k))
    (k : ℕ) : StronglyMeasurable[F k] (qvPrefix X k) := by
  unfold qvPrefix
  refine Finset.stronglyMeasurable_fun_sum _ fun j hj => ?_
  have hjk : j + 1 ≤ k := mem_range.1 hj
  exact ((hX j).mono (F.mono hjk)).pow 2

private lemma measurableSet_qvPrefix_le (hX : ∀ k, StronglyMeasurable[F (k + 1)] (X k))
    (k : ℕ) (K : ℝ) : MeasurableSet[F k] {ω | qvPrefix X k ω ≤ K} :=
  (stronglyMeasurable_qvPrefix hX k).measurableSet_le stronglyMeasurable_const

private lemma stronglyMeasurable_stopX (hX : ∀ k, StronglyMeasurable[F (k + 1)] (X k))
    (K : ℝ) (k : ℕ) : StronglyMeasurable[F (k + 1)] (stopX X K k) := by
  unfold stopX
  exact StronglyMeasurable.ite (F.mono k.le_succ _ (measurableSet_qvPrefix_le hX k K)) (hX k)
    stronglyMeasurable_const

private lemma stronglyMeasurable_stopProd (hX : ∀ k, StronglyMeasurable[F (k + 1)] (X k))
    (K t : ℝ) (k : ℕ) : StronglyMeasurable[F k] (stopProd X K t k) := by
  unfold stopProd
  refine Finset.stronglyMeasurable_fun_prod _ fun j hj => ?_
  have hjk : j + 1 ≤ k := mem_range.1 hj
  have h1 : StronglyMeasurable[F k] fun ω => t * stopX X K j ω :=
    stronglyMeasurable_const.mul ((stronglyMeasurable_stopX hX K j).mono (F.mono hjk))
  exact stronglyMeasurable_const.add
    ((Complex.continuous_ofReal.comp_stronglyMeasurable h1).mul stronglyMeasurable_const)

private lemma norm_stopProd_le (X : ℕ → Ω → ℝ) {K M : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (t : ℝ)
    (ω : Ω) (k : ℕ) (hXM : ∀ j < k, X j ω ^ 2 ≤ M) :
    ‖stopProd X K t k ω‖ ≤ 1 + Real.exp (t ^ 2 * K) * (1 + t ^ 2 * M) := by
  have h1 := (stopProd_bound X hK hM t ω k hXM).2
  rw [← norm_stopProd_sq] at h1
  nlinarith [sq_nonneg (‖stopProd X K t k ω‖ - 1)]

/-- **McLeish's product has mean one.** For a martingale difference row (`X_k` is
`F_{k+1}`-measurable, integrable, with `E[X_k | F_k] = 0`) whose squares are dominated by an
integrable `M`, the stopped product satisfies `E[∏_{k<m} (1 + i t X'_k)] = 1`. The stopping
keeps every partial product bounded on the event where the next factor is still active, so each
step `E[P_k · i t X'_k] = 0` is a genuine conditional-expectation identity. -/
private lemma integral_stopProd [IsProbabilityMeasure μ]
    (hX : ∀ k, StronglyMeasurable[F (k + 1)] (X k)) (hint : ∀ k, Integrable (X k) μ)
    (hmd : ∀ k, μ[X k | F k] =ᵐ[μ] 0) {K : ℝ} (hK : 0 ≤ K) (t : ℝ) (m : ℕ) (Mx : Ω → ℝ)
    (hMx : Integrable Mx μ) (hMx0 : ∀ ω, 0 ≤ Mx ω) (hXM : ∀ ω, ∀ j < m, X j ω ^ 2 ≤ Mx ω) :
    ∫ ω, stopProd X K t m ω ∂μ = 1 := by
  have hPint : ∀ k ≤ m, Integrable (stopProd X K t k) μ := by
    intro k hk
    refine Integrable.mono' ((integrable_const 1).add
      (((integrable_const 1).add (hMx.const_mul (t ^ 2))).const_mul (Real.exp (t ^ 2 * K))))
      ((stronglyMeasurable_stopProd hX K t k).mono (F.le k)).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    exact norm_stopProd_le X hK (hMx0 ω) t ω k fun j hj => hXM ω j (by omega)
  suffices h : ∀ k ≤ m, ∫ ω, stopProd X K t k ω ∂μ = 1 from h m le_rfl
  intro k
  induction k with
  | zero => intro _; simp [stopProd]
  | succ k ih =>
    intro hk
    set g : Ω → ℂ := fun ω =>
      if qvPrefix X k ω ≤ K then (t : ℂ) * Complex.I * stopProd X K t k ω else 0 with hg
    have hsplit : stopProd X K t (k + 1) = fun ω => stopProd X K t k ω + (X k • g) ω := by
      funext ω
      change _ = stopProd X K t k ω + X k ω • g ω
      simp only [stopProd, prod_range_succ, hg, stopX]
      split_ifs
      · rw [Complex.real_smul]; push_cast; ring
      · simp
    have hgsm : StronglyMeasurable[F k] g :=
      StronglyMeasurable.ite (measurableSet_qvPrefix_le hX k K)
        (stronglyMeasurable_const.mul (stronglyMeasurable_stopProd hX K t k))
        stronglyMeasurable_const
    set C : ℝ := |t| * (1 + Real.exp (t ^ 2 * K)) with hC
    have hgbd : ∀ ω, ‖g ω‖ ≤ C := by
      intro ω
      simp only [hg]
      split_ifs with hq
      · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg t)
        have hXM' : ∀ j < k, X j ω ^ 2 ≤ Mx ω := fun j hj => hXM ω j (by omega)
        have h1 := (stopProd_bound X hK (hMx0 ω) t ω k hXM').1 hq
        rw [← norm_stopProd_sq] at h1
        have h2 : Real.exp (t ^ 2 * qvPrefix X k ω) ≤ Real.exp (t ^ 2 * K) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hq (sq_nonneg t))
        nlinarith [sq_nonneg (‖stopProd X K t k ω‖ - 1)]
      · simp only [norm_zero, hC]; positivity
    have hXg : Integrable (X k • g) μ := by
      refine Integrable.mono' ((hint k).norm.const_mul C)
        ((hint k).aestronglyMeasurable.smul (hgsm.mono (F.le k)).aestronglyMeasurable)
        (ae_of_all _ fun ω => ?_)
      change ‖X k ω • g ω‖ ≤ _
      rw [norm_smul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hgbd ω) (norm_nonneg _)
    have hzero : ∫ ω, (X k • g) ω ∂μ = 0 := by
      rw [← integral_condExp (F.le k)]
      have h1 := condExp_smul_of_aestronglyMeasurable_right (hint k) hXg
        hgsm.aestronglyMeasurable
      have h2 : (μ[X k | F k] • g) =ᵐ[μ] 0 := by
        filter_upwards [hmd k] with ω hω
        simp [hω]
      rw [integral_congr_ae (h1.trans h2)]
      simp
    rw [hsplit, integral_add (hPint k (by omega)) hXg, hzero, ih (by omega), add_zero]

/-- The event that every increment of the row is at most `ε` in absolute value. -/
private def smallSet (X : ℕ → Ω → ℝ) (m : ℕ) (ε : ℝ) : Set Ω :=
  {ω | ∀ k ∈ range m, |X k ω| ≤ ε}

private lemma abs_stopX_le (X : ℕ → Ω → ℝ) (K : ℝ) (k : ℕ) (ω : Ω) :
    |stopX X K k ω| ≤ |X k ω| := by
  unfold stopX; split_ifs <;> simp

/-- **Pointwise comparison with the Gaussian factor.** Writing `S'` for the stopped row sum,
`T'` for McLeish's product, and `c = e^{-v t²/2}`, the defect `e^{i t S'} - c T'` is bounded by
a cubic remainder, by the distance from `e^{-t² ∑ X'²/2}` to `c` times `‖T'‖`, and, off the
event that all increments are `≤ ε`, by `1 + ‖T'‖`. -/
private lemma norm_charTerm_sub_le (X : ℕ → Ω → ℝ) (K t v ε : ℝ) (m : ℕ) (ω : Ω)
    (hε0 : 0 ≤ ε) (hε : |t| * ε ≤ 1) (hv : 0 ≤ v) :
    ‖Complex.exp (((t * ∑ k ∈ range m, stopX X K k ω : ℝ) : ℂ) * Complex.I) -
        ((Real.exp (-(v * t ^ 2 / 2)) : ℝ) : ℂ) * stopProd X K t m ω‖ ≤
      2 * |t| ^ 3 * ε * ∑ k ∈ range m, stopX X K k ω ^ 2 +
      (|Real.exp (-(t ^ 2 / 2 * ∑ k ∈ range m, stopX X K k ω ^ 2)) -
          Real.exp (-(v * t ^ 2 / 2))| + (smallSet X m ε)ᶜ.indicator 1 ω) *
        ‖stopProd X K t m ω‖ +
      (smallSet X m ε)ᶜ.indicator 1 ω := by
  set T := stopProd X K t m ω with hT
  set r : ℝ := Real.exp (-(v * t ^ 2 / 2)) with hr
  set r' : ℝ := Real.exp (-(t ^ 2 / 2 * ∑ k ∈ range m, stopX X K k ω ^ 2)) with hr'
  have hr1 : r ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg t])
  have hr0 : 0 < r := Real.exp_pos _
  have hsq0 : 0 ≤ ∑ k ∈ range m, stopX X K k ω ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  by_cases hG : ω ∈ smallSet X m ε
  · have hnot : ω ∉ (smallSet X m ε)ᶜ := fun h => h hG
    rw [Set.indicator_of_notMem hnot]
    simp only [add_zero]
    set y : ℕ → ℝ := fun k => t * stopX X K k ω with hy
    have hyk : ∀ k ∈ range m, |y k| ≤ 1 ∧ |y k| ^ 3 ≤ |t| ^ 3 * ε * stopX X K k ω ^ 2 := by
      intro k hk
      have hXk : |stopX X K k ω| ≤ ε := (abs_stopX_le X K k ω).trans (hG k hk)
      have ht0 := abs_nonneg t
      have hs0 := abs_nonneg (stopX X K k ω)
      refine ⟨?_, ?_⟩
      · rw [hy, abs_mul]; exact (mul_le_mul_of_nonneg_left hXk ht0).trans hε
      · rw [hy, abs_mul, mul_pow, ← sq_abs (stopX X K k ω)]
        have : |stopX X K k ω| ^ 3 = |stopX X K k ω| * |stopX X K k ω| ^ 2 := by ring
        rw [this, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ht0 3)
        exact mul_le_mul_of_nonneg_right hXk (sq_nonneg _)
    have hA : Complex.exp (((t * ∑ k ∈ range m, stopX X K k ω : ℝ) : ℂ) * Complex.I) =
        ∏ k ∈ range m, Complex.exp (((y k : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_sum, mul_sum, Complex.ofReal_sum, sum_mul]
    have hB : ∏ k ∈ range m, ((1 : ℂ) + ((y k : ℝ) : ℂ) * Complex.I) *
        ((Real.exp (-(y k ^ 2 / 2)) : ℝ) : ℂ) = T * (r' : ℂ) := by
      rw [prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum, hT, stopProd, hr']
      congr 3
      rw [mul_sum, ← sum_neg_distrib]
      refine sum_congr rfl fun k _ => ?_
      rw [hy]; ring
    have hsplit : Complex.exp (((t * ∑ k ∈ range m, stopX X K k ω : ℝ) : ℂ) * Complex.I) -
        (r : ℂ) * T =
        (∏ k ∈ range m, Complex.exp (((y k : ℝ) : ℂ) * Complex.I) -
          ∏ k ∈ range m, ((1 : ℂ) + ((y k : ℝ) : ℂ) * Complex.I) *
            ((Real.exp (-(y k ^ 2 / 2)) : ℝ) : ℂ)) + ((r' - r : ℝ) : ℂ) * T := by
      rw [hA, hB]; push_cast; ring
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_prod_sub_prod_le m _ _ (fun k _ => by rw [Complex.norm_exp_ofReal_mul_I])
        (fun k _ => norm_one_add_mul_I_mul_exp_le _)).trans ?_
      rw [mul_sum]
      refine sum_le_sum fun k hk => ?_
      refine (norm_exp_mul_I_sub_le (y k) (hyk k hk).1).trans ?_
      have := (hyk k hk).2
      nlinarith
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  · have hin : ω ∈ (smallSet X m ε)ᶜ := hG
    rw [Set.indicator_of_mem hin]
    simp only [Pi.one_apply]
    have h1 : ‖Complex.exp (((t * ∑ k ∈ range m, stopX X K k ω : ℝ) : ℂ) * Complex.I) -
        (r : ℂ) * T‖ ≤ 1 + ‖T‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_exp_ofReal_mul_I, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr0]
      nlinarith [norm_nonneg T]
    have h2 : 0 ≤ 2 * |t| ^ 3 * ε * ∑ k ∈ range m, stopX X K k ω ^ 2 := by positivity
    nlinarith [abs_nonneg (r' - r), norm_nonneg T]

private lemma measurableSet_smallSet {X : ℕ → Ω → ℝ} (hX : ∀ k, StronglyMeasurable (X k))
    (m : ℕ) (ε : ℝ) : MeasurableSet (smallSet X m ε) := by
  have : smallSet X m ε = ⋂ k ∈ range m, {ω | |X k ω| ≤ ε} := by
    ext ω; simp [smallSet]
  rw [this]
  exact Finset.measurableSet_biInter _ fun k _ =>
    (hX k).norm.measurableSet_le stronglyMeasurable_const

/-- **Row estimate.** For one martingale difference row with dominating `Mx`, the
characteristic function of the stopped row sum at `t` is within an explicit error of
`e^{-v t²/2}`. The error has a cubic part (small when `ε` is small), an `L²` part `λ E‖T'‖²`,
and probabilities of the events where the increments are not all `≤ ε` or the stopped
quadratic variation's Gaussian factor is more than `η` away from `e^{-v t²/2}`. -/
private lemma row_bound [IsProbabilityMeasure μ]
    (hX : ∀ k, StronglyMeasurable[F (k + 1)] (X k)) (hint : ∀ k, Integrable (X k) μ)
    (hmd : ∀ k, μ[X k | F k] =ᵐ[μ] 0) {K : ℝ} (hK : 0 ≤ K) (t v ε η lam : ℝ) (hv : 0 ≤ v)
    (hε0 : 0 ≤ ε) (hε : |t| * ε ≤ 1) (hη : 0 ≤ η) (hlam : 0 < lam) (m : ℕ) (Mx : Ω → ℝ)
    (hMx : Integrable Mx μ) (hMx0 : ∀ ω, 0 ≤ Mx ω) (hXM : ∀ ω, ∀ j < m, X j ω ^ 2 ≤ Mx ω) :
    ‖∫ ω, Complex.exp (((t * ∑ k ∈ range m, stopX X K k ω : ℝ) : ℂ) * Complex.I) ∂μ -
        ((Real.exp (-(v * t ^ 2 / 2)) : ℝ) : ℂ)‖ ≤
      2 * |t| ^ 3 * ε * (K + ∫ ω, Mx ω ∂μ) +
        lam * (Real.exp (t ^ 2 * K) * (1 + t ^ 2 * ∫ ω, Mx ω ∂μ)) +
        lam⁻¹ * (2 * (η + μ.real {ω | η < |Real.exp (-(t ^ 2 / 2 *
            ∑ k ∈ range m, stopX X K k ω ^ 2)) - Real.exp (-(v * t ^ 2 / 2))|}) +
          2 * μ.real (smallSet X m ε)ᶜ) +
        μ.real (smallSet X m ε)ᶜ := by
  have hX0 : ∀ k, StronglyMeasurable (X k) := fun k => (hX k).mono (F.le _)
  set T : Ω → ℂ := stopProd X K t m with hT
  set Q : Ω → ℝ := fun ω => ∑ k ∈ range m, stopX X K k ω ^ 2 with hQ
  set r : ℝ := Real.exp (-(v * t ^ 2 / 2)) with hr
  set r' : Ω → ℝ := fun ω => Real.exp (-(t ^ 2 / 2 * Q ω)) with hr'
  set B : Set Ω := {ω | η < |r' ω - r|} with hB
  set G : Set Ω := smallSet X m ε with hG
  have hTsm : StronglyMeasurable T := (stronglyMeasurable_stopProd hX K t m).mono (F.le m)
  have hstopsm : ∀ k, StronglyMeasurable (stopX X K k) :=
    fun k => (stronglyMeasurable_stopX hX K k).mono (F.le _)
  have hQsm : StronglyMeasurable Q :=
    Finset.stronglyMeasurable_fun_sum _ fun k _ => (hstopsm k).pow 2
  have hr'sm : StronglyMeasurable r' :=
    Real.continuous_exp.comp_stronglyMeasurable (stronglyMeasurable_const.mul hQsm).neg
  have hBm : MeasurableSet B :=
    stronglyMeasurable_const.measurableSet_lt (hr'sm.sub stronglyMeasurable_const).norm
  have hGm : MeasurableSet Gᶜ := (measurableSet_smallSet hX0 m ε).compl
  -- integrability
  have hXM' : ∀ ω, ∀ j < m, X j ω ^ 2 ≤ Mx ω := hXM
  have hTint : Integrable T μ :=
    Integrable.mono' ((integrable_const 1).add
      (((integrable_const 1).add (hMx.const_mul (t ^ 2))).const_mul (Real.exp (t ^ 2 * K))))
      hTsm.aestronglyMeasurable
      (ae_of_all _ fun ω => norm_stopProd_le X hK (hMx0 ω) t ω m (hXM ω))
  have hT2int : Integrable (fun ω => ‖T ω‖ ^ 2) μ :=
    Integrable.mono' (((integrable_const 1).add (hMx.const_mul (t ^ 2))).const_mul
      (Real.exp (t ^ 2 * K))) (hTsm.norm.pow 2).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hT, norm_stopProd_sq]
        exact (stopProd_bound X hK (hMx0 ω) t ω m (hXM ω)).2)
  have hQint : Integrable Q μ :=
    Integrable.mono' ((integrable_const K).add hMx) hQsm.aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sum_nonneg fun _ _ => sq_nonneg _)]
        exact (sum_sq_stopX_le X hK (hMx0 ω) ω m (hXM ω)).2)
  have hEint : Integrable (fun ω =>
      Complex.exp (((t * ∑ k ∈ range m, stopX X K k ω : ℝ) : ℂ) * Complex.I)) μ := by
    refine Integrable.of_bound (C := 1) ?_ (ae_of_all _ fun ω => ?_)
    · refine (Complex.continuous_exp.comp_stronglyMeasurable ?_).aestronglyMeasurable
      exact (Complex.continuous_ofReal.comp_stronglyMeasurable (stronglyMeasurable_const.mul
        (Finset.stronglyMeasurable_fun_sum _ fun k _ => hstopsm k))).mul stronglyMeasurable_const
    · rw [Complex.norm_exp_ofReal_mul_I]
  -- reduce to the defect `e^{itS'} - r T'`
  have hmean := integral_stopProd hX hint hmd hK t m Mx hMx hMx0 hXM
  have hred : ∫ ω, Complex.exp (((t * ∑ k ∈ range m, stopX X K k ω : ℝ) : ℂ) * Complex.I) ∂μ -
      (r : ℂ) = ∫ ω, (Complex.exp (((t * ∑ k ∈ range m, stopX X K k ω : ℝ) : ℂ) * Complex.I) -
        (r : ℂ) * T ω) ∂μ := by
    rw [integral_sub hEint (hTint.const_mul _), integral_const_mul, hT, hmean, mul_one]
  rw [hred]
  refine (norm_integral_le_integral_norm _).trans ?_
  -- pointwise domination
  set H : Ω → ℝ := fun ω => 2 * |t| ^ 3 * ε * Q ω + lam * ‖T ω‖ ^ 2 +
    lam⁻¹ * (2 * (η + B.indicator 1 ω) + 2 * Gᶜ.indicator 1 ω) + Gᶜ.indicator 1 ω with hH
  have hpt : ∀ ω, ‖Complex.exp (((t * ∑ k ∈ range m, stopX X K k ω : ℝ) : ℂ) * Complex.I) -
      (r : ℂ) * T ω‖ ≤ H ω := by
    intro ω
    refine (norm_charTerm_sub_le X K t v ε m ω hε0 hε hv).trans ?_
    simp only [hH]
    set a := |r' ω - r| with ha
    set b := Gᶜ.indicator (1 : Ω → ℝ) ω with hb
    have hb01 : b = 0 ∨ b = 1 := by
      simp only [hb, Set.indicator, Pi.one_apply]; split_ifs <;> simp
    have ha0 : 0 ≤ a := abs_nonneg _
    have ha1 : a ≤ 1 := by
      have h1 : r' ω ≤ 1 := Real.exp_le_one_iff.2 (by
        have : 0 ≤ Q ω := sum_nonneg fun _ _ => sq_nonneg _
        nlinarith [sq_nonneg t])
      have h2 : r ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg t])
      have h3 := Real.exp_pos (-(t ^ 2 / 2 * Q ω))
      have h4 := Real.exp_pos (-(v * t ^ 2 / 2))
      rw [ha, abs_le]; constructor <;> linarith
    have haη : a ≤ η + B.indicator 1 ω := by
      by_cases hω : ω ∈ B
      · rw [Set.indicator_of_mem hω, Pi.one_apply]; linarith
      · rw [Set.indicator_of_notMem hω, add_zero]
        simpa [hB, ha] using hω
    have hTn := norm_nonneg (T ω)
    -- AM-GM: `w ‖T‖ ≤ λ ‖T‖² + λ⁻¹ w²`
    have hamgm : (a + b) * ‖T ω‖ ≤ lam * ‖T ω‖ ^ 2 + lam⁻¹ * (a + b) ^ 2 := by
      have hl : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hlam.ne'
      have hsq := sq_nonneg (lam * ‖T ω‖ - (a + b))
      have hli : 0 < lam⁻¹ := inv_pos.2 hlam
      have key : lam⁻¹ * (lam * ‖T ω‖ - (a + b)) ^ 2 =
          lam * ‖T ω‖ ^ 2 - 2 * (a + b) * ‖T ω‖ + lam⁻¹ * (a + b) ^ 2 := by
        field_simp; ring
      have hab : 0 ≤ (a + b) * ‖T ω‖ := mul_nonneg (by rcases hb01 with h | h <;> rw [h] <;>
        linarith) hTn
      nlinarith [mul_nonneg hli.le hsq]
    have hw2 : (a + b) ^ 2 ≤ 2 * (η + B.indicator 1 ω) + 2 * b := by
      rcases hb01 with h | h <;> rw [h] <;> nlinarith
    have hli : 0 ≤ lam⁻¹ := (inv_pos.2 hlam).le
    nlinarith [mul_le_mul_of_nonneg_left hw2 hli]
  have hHint : Integrable H μ :=
    ((((hQint.const_mul _).add (hT2int.const_mul _))).add
      ((((integrable_const η).add ((integrable_const (1 : ℝ)).indicator hBm)).const_mul 2).add
        (((integrable_const (1 : ℝ)).indicator hGm).const_mul 2) |>.const_mul _)).add
      ((integrable_const (1 : ℝ)).indicator hGm)
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hHint
    (ae_of_all _ hpt)).trans ?_
  have hIQ : ∫ ω, Q ω ∂μ ≤ K + ∫ ω, Mx ω ∂μ := by
    have h := integral_mono (g := fun ω => K + Mx ω) hQint ((integrable_const K).add hMx) fun ω =>
      (sum_sq_stopX_le X hK (hMx0 ω) ω m (hXM ω)).2
    rwa [integral_add (integrable_const K) hMx, integral_const, probReal_univ, one_smul] at h
  have hIT : ∫ ω, ‖T ω‖ ^ 2 ∂μ ≤ Real.exp (t ^ 2 * K) * (1 + t ^ 2 * ∫ ω, Mx ω ∂μ) := by
    have h := integral_mono (g := fun ω => Real.exp (t ^ 2 * K) * (1 + t ^ 2 * Mx ω)) hT2int
      (((integrable_const 1).add (hMx.const_mul (t ^ 2))).const_mul (Real.exp (t ^ 2 * K)))
      fun ω => by
        change ‖T ω‖ ^ 2 ≤ _
        rw [hT, norm_stopProd_sq]
        exact (stopProd_bound X hK (hMx0 ω) t ω m (hXM ω)).2
    rwa [integral_const_mul, integral_add (integrable_const 1) (hMx.const_mul _),
      integral_const_mul, integral_const, probReal_univ, one_smul] at h
  have hB1 : Integrable (B.indicator (1 : Ω → ℝ)) μ := (integrable_const 1).indicator hBm
  have hG1 : Integrable (Gᶜ.indicator (1 : Ω → ℝ)) μ := (integrable_const 1).indicator hGm
  have hIH : ∫ ω, H ω ∂μ = 2 * |t| ^ 3 * ε * ∫ ω, Q ω ∂μ + lam * ∫ ω, ‖T ω‖ ^ 2 ∂μ +
      lam⁻¹ * (2 * (η + μ.real B) + 2 * μ.real Gᶜ) + μ.real Gᶜ := by
    have i1 : Integrable (fun ω => 2 * |t| ^ 3 * ε * Q ω) μ := hQint.const_mul _
    have i2 : Integrable (fun ω => lam * ‖T ω‖ ^ 2) μ := hT2int.const_mul _
    have j0 : Integrable (fun ω => η + B.indicator 1 ω) μ := (integrable_const η).add hB1
    have j1 : Integrable (fun ω => 2 * (η + B.indicator 1 ω)) μ := j0.const_mul 2
    have j2 : Integrable (fun ω => 2 * Gᶜ.indicator (1 : Ω → ℝ) ω) μ := hG1.const_mul 2
    have j3 : Integrable (fun ω => 2 * (η + B.indicator 1 ω) + 2 * Gᶜ.indicator 1 ω) μ :=
      j1.add j2
    have i3 : Integrable
        (fun ω => lam⁻¹ * (2 * (η + B.indicator 1 ω) + 2 * Gᶜ.indicator 1 ω)) μ :=
      j3.const_mul _
    have i12 : Integrable (fun ω => 2 * |t| ^ 3 * ε * Q ω + lam * ‖T ω‖ ^ 2) μ := i1.add i2
    have i123 : Integrable (fun ω => 2 * |t| ^ 3 * ε * Q ω + lam * ‖T ω‖ ^ 2 +
        lam⁻¹ * (2 * (η + B.indicator 1 ω) + 2 * Gᶜ.indicator 1 ω)) μ := i12.add i3
    simp only [hH]
    rw [integral_add i123 hG1, integral_add i12 i3, integral_add i1 i2, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_add j1 j2, integral_const_mul,
      integral_const_mul, integral_add (integrable_const η) hB1, integral_const, probReal_univ,
      one_smul, integral_indicator_one hBm, integral_indicator_one hGm]
  rw [hIH]
  have ht3 : 0 ≤ 2 * |t| ^ 3 * ε := by positivity
  gcongr

end Expectation

end

/-! ### Martingale arrays -/

section Increments

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {F : Filtration ℕ m0}
  {X : ℕ → Ω → ℝ}

/-- Increments of a martingale `∑_{j<k} X_j` are martingale differences: `X_k` is
`F_{k+1}`-measurable, integrable, and `E[X_k | F_k] = 0`. -/
private lemma martingale_increment [IsFiniteMeasure μ]
    (h : Martingale (fun k ω => ∑ j ∈ range k, X j ω) F μ) (k : ℕ) :
    StronglyMeasurable[F (k + 1)] (X k) ∧ Integrable (X k) μ ∧ μ[X k | F k] =ᵐ[μ] 0 := by
  have hX : X k = (fun ω => ∑ j ∈ range (k + 1), X j ω) - fun ω => ∑ j ∈ range k, X j ω := by
    funext ω; simp [sum_range_succ]
  have hint : Integrable (X k) μ := by
    rw [hX]; exact (h.integrable (k + 1)).sub (h.integrable k)
  refine ⟨?_, hint, ?_⟩
  · rw [hX]
    exact (h.stronglyAdapted (k + 1)).sub ((h.stronglyAdapted k).mono (F.mono k.le_succ))
  · rw [hX]
    refine (condExp_sub (h.integrable (k + 1)) (h.integrable k) _).trans ?_
    have h1 := h.condExp_ae_eq k.le_succ
    have h2 : μ[fun ω => ∑ j ∈ range k, X j ω | F k] = fun ω => ∑ j ∈ range k, X j ω :=
      condExp_of_stronglyMeasurable (F.le k) (h.stronglyAdapted k) (h.integrable k)
    filter_upwards [h1] with ω hω
    simp [hω, h2]

end Increments

/-! ### Convergence in probability: finite linear combinations -/

section InMeasure

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

private lemma tendstoInMeasure_add {f f' : ℕ → Ω → ℝ} {g g' : Ω → ℝ}
    (hf : TendstoInMeasure μ f atTop g) (hf' : TendstoInMeasure μ f' atTop g') :
    TendstoInMeasure μ (fun n ω => f n ω + f' n ω) atTop (fun ω => g ω + g' ω) := by
  rw [tendstoInMeasure_iff_dist] at hf hf' ⊢
  intro ε hε
  have h := (hf (ε / 2) (by positivity)).add (hf' (ε / 2) (by positivity))
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    fun n => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Set.mem_union, Real.dist_eq] at hω ⊢
  by_contra hcon
  push Not at hcon
  have := abs_add_le (f n ω - g ω) (f' n ω - g' ω)
  rw [show f n ω - g ω + (f' n ω - g' ω) = f n ω + f' n ω - (g ω + g' ω) by ring] at this
  linarith [hcon.1, hcon.2]

private lemma tendstoInMeasure_const_mul {f : ℕ → Ω → ℝ} {g : Ω → ℝ} (w : ℝ)
    (hf : TendstoInMeasure μ f atTop g) :
    TendstoInMeasure μ (fun n ω => w * f n ω) atTop (fun ω => w * g ω) := by
  rw [tendstoInMeasure_iff_dist] at hf ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hf (ε / (|w| + 1)) (by positivity)) (fun _ => zero_le) fun n => measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω ⊢
  rw [← mul_sub, abs_mul] at hω
  rw [div_le_iff₀ (by positivity)]
  nlinarith [abs_nonneg (f n ω - g ω), abs_nonneg w]

private lemma tendstoInMeasure_sum {κ : Type*} (s : Finset κ) {f : κ → ℕ → Ω → ℝ}
    {g : κ → Ω → ℝ} (hf : ∀ i ∈ s, TendstoInMeasure μ (f i) atTop (g i)) :
    TendstoInMeasure μ (fun n ω => ∑ i ∈ s, f i n ω) atTop (fun ω => ∑ i ∈ s, g i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro ε hε
    have : ∀ n, {x : Ω | ε ≤ edist (∑ i ∈ (∅ : Finset κ), f i n x)
        (∑ i ∈ (∅ : Finset κ), g i x)} = ∅ := by
      intro n; ext; simp [hε.ne']
    simp only [this, measure_empty, tendsto_const_nhds]
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact tendstoInMeasure_add (hf a (mem_insert_self a s))
      (ih fun i hi => hf i (mem_insert_of_mem hi))

/-- A limit in probability of nonnegative random variables is nonnegative. -/
private lemma nonneg_of_tendstoInMeasure [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} {q : ℝ}
    (hf : TendstoInMeasure μ f atTop fun _ => q) (h0 : ∀ n ω, 0 ≤ f n ω) : 0 ≤ q := by
  by_contra hq
  push Not at hq
  have h := (tendstoInMeasure_iff_dist.1 hf) (-q) (by linarith)
  have huniv : ∀ n, {ω | -q ≤ dist (f n ω) q} = Set.univ := by
    intro n; ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, Real.dist_eq]
    rw [abs_of_nonneg (by linarith [h0 n ω])]; linarith [h0 n ω]
  simp only [huniv, measure_univ] at h
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

end InMeasure

/-! ### McLeish's theorem -/

section Main

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The pointwise maximum of the squared increments of a row, as a real number. -/
private lemma maxSq_facts (X : ℕ → Ω → ℝ) (m : ℕ) (hX : ∀ k, Measurable (X k)) :
    Measurable (fun ω => ⨆ k ∈ range m, ‖X k ω‖ₑ ^ 2) ∧
      (∀ ω, (⨆ k ∈ range m, ‖X k ω‖ₑ ^ 2) ≠ ∞) ∧
      ∀ ω, ∀ j < m, X j ω ^ 2 ≤ (⨆ k ∈ range m, ‖X k ω‖ₑ ^ 2).toReal := by
  have hfin : ∀ ω, (⨆ k ∈ range m, ‖X k ω‖ₑ ^ 2) ≠ ∞ := by
    intro ω
    refine ne_top_of_le_ne_top (b := ∑ k ∈ range m, ‖X k ω‖ₑ ^ 2) ?_ ?_
    · exact ENNReal.sum_ne_top.2 fun k _ => by simp
    · exact iSup₂_le fun k hk => single_le_sum (f := fun k => ‖X k ω‖ₑ ^ 2)
        (fun _ _ => zero_le) hk
  refine ⟨?_, hfin, fun ω j hj => ?_⟩
  · exact Measurable.biSup (↑(range m)) (Set.to_countable _)
      fun k _ => ((hX k).enorm).pow_const 2
  · have h1 : ‖X j ω‖ₑ ^ 2 ≤ ⨆ k ∈ range m, ‖X k ω‖ₑ ^ 2 :=
      le_iSup₂ (f := fun k (_ : k ∈ range m) => ‖X k ω‖ₑ ^ 2) j (mem_range.2 hj)
    have h2 := ENNReal.toReal_mono (hfin ω) h1
    refine le_of_eq_of_le ?_ h2
    rw [ENNReal.toReal_pow, toReal_enorm, Real.norm_eq_abs, sq_abs]


private lemma sum_stopX_eq (X : ℕ → Ω → ℝ) {K : ℝ} {m : ℕ} {ω : Ω} (h : qvPrefix X m ω ≤ K)
    (f : ℝ → ℝ) : ∑ k ∈ range m, f (stopX X K k ω) = ∑ k ∈ range m, f (X k ω) :=
  sum_congr rfl fun k hk => by rw [stopX_eq_of_qvPrefix_le X h (mem_range.1 hk)]

/-- Stopping changes the characteristic function by at most twice the probability that the
quadratic variation exceeds the stopping level. -/
private lemma norm_integral_exp_sub_stop_le [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, StronglyMeasurable (X k)) (K t : ℝ) (m : ℕ) :
    ‖∫ ω, Complex.exp (((t * ∑ k ∈ range m, X k ω : ℝ) : ℂ) * Complex.I) ∂μ -
        ∫ ω, Complex.exp (((t * ∑ k ∈ range m, stopX X K k ω : ℝ) : ℂ) * Complex.I) ∂μ‖ ≤
      2 * μ.real {ω | K < qvPrefix X m ω} := by
  have hqsm : StronglyMeasurable (qvPrefix X m) :=
    Finset.stronglyMeasurable_fun_sum _ fun k _ => (hX k).pow 2
  have hAm : MeasurableSet {ω | K < qvPrefix X m ω} :=
    stronglyMeasurable_const.measurableSet_lt hqsm
  have hstopsm : ∀ k, StronglyMeasurable (stopX X K k) := fun k => by
    unfold stopX
    exact StronglyMeasurable.ite
      ((Finset.stronglyMeasurable_fun_sum _ fun j _ => (hX j).pow 2).measurableSet_le
        stronglyMeasurable_const) (hX k) stronglyMeasurable_const
  have hexp : ∀ Y : ℕ → Ω → ℝ, (∀ k, StronglyMeasurable (Y k)) → Integrable (fun ω =>
      Complex.exp (((t * ∑ k ∈ range m, Y k ω : ℝ) : ℂ) * Complex.I)) μ := by
    intro Y hY
    refine Integrable.of_bound (C := 1) ?_ (ae_of_all _ fun ω => ?_)
    · refine (Complex.continuous_exp.comp_stronglyMeasurable ?_).aestronglyMeasurable
      exact (Complex.continuous_ofReal.comp_stronglyMeasurable (stronglyMeasurable_const.mul
        (Finset.stronglyMeasurable_fun_sum _ fun k _ => hY k))).mul stronglyMeasurable_const
    · rw [Complex.norm_exp_ofReal_mul_I]
  rw [← integral_sub (hexp X hX) (hexp _ hstopsm)]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hind : Integrable ({ω | K < qvPrefix X m ω}.indicator (fun _ => (2 : ℝ))) μ :=
    (integrable_const 2).indicator hAm
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hind
    (ae_of_all _ fun ω => ?_)).trans (le_of_eq ?_)
  · by_cases hω : ω ∈ {ω | K < qvPrefix X m ω}
    · rw [Set.indicator_of_mem hω]
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]; norm_num
    · rw [Set.indicator_of_notMem hω]
      have hq : qvPrefix X m ω ≤ K := not_lt.1 hω
      have := sum_stopX_eq X hq id
      simp only [id] at this
      simp [this]
  · rw [integral_indicator_const _ hAm, smul_eq_mul, mul_comm]

/-- Where the Gaussian factor of the stopped quadratic variation is far from
`e^{-v t²/2}`, either stopping occurred or the quadratic variation is far from `v`. -/
private lemma gaussFactor_subset (X : ℕ → Ω → ℝ) (K t v η : ℝ) (m : ℕ) (hv : 0 ≤ v) :
    {ω | η < |Real.exp (-(t ^ 2 / 2 * ∑ k ∈ range m, stopX X K k ω ^ 2)) -
        Real.exp (-(v * t ^ 2 / 2))|} ⊆
      {ω | K < qvPrefix X m ω} ∪ {ω | η / (t ^ 2 + 1) ≤ dist (qvPrefix X m ω) v} := by
  intro ω hω
  by_cases hq : qvPrefix X m ω ≤ K
  · right
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hsum : ∑ k ∈ range m, stopX X K k ω ^ 2 = qvPrefix X m ω := by
      have := sum_stopX_eq X hq (fun x => x ^ 2); simpa [qvPrefix] using this
    rw [hsum] at hω
    have hq0 : 0 ≤ qvPrefix X m ω := sum_nonneg fun _ _ => sq_nonneg _
    have h1 := abs_exp_neg_sub_exp_neg_le (x := t ^ 2 / 2 * qvPrefix X m ω)
      (y := v * t ^ 2 / 2) (by positivity) (by positivity)
    have h2 : |t ^ 2 / 2 * qvPrefix X m ω - v * t ^ 2 / 2| =
        t ^ 2 / 2 * |qvPrefix X m ω - v| := by
      rw [show t ^ 2 / 2 * qvPrefix X m ω - v * t ^ 2 / 2 = t ^ 2 / 2 * (qvPrefix X m ω - v)
        by ring, abs_mul, abs_of_nonneg (by positivity)]
    rw [Real.dist_eq, div_le_iff₀ (by positivity)]
    have h3 := abs_nonneg (qvPrefix X m ω - v)
    nlinarith [sq_nonneg t]
  · left; exact not_le.1 hq

/-- **McLeish's martingale central limit theorem** (McLeish 1974, Theorem 2.3).

Let `X n k` be a martingale difference array: for each row `n` the partial sums
`∑_{j<k} X n j` form a martingale with respect to a filtration `F n`. Consider row sums over
`k < r n`. Assume
* (a) the maximal squared increment is bounded in `L¹`: `E[max_{k<r n} X n k²] ≤ B < ∞`
  eventually (stated with lower Lebesgue integrals, so the hypothesis is never vacuous);
* (b) the maximal increment tends to `0` in probability;
* (c) the realized quadratic variation `∑_{k<r n} X n k²` tends to `v` in probability.

Then the row sums converge in distribution to `N(0, v)`. No independence and no conditional
variance assumption is made: the quadratic-variation hypothesis is on the realized squares.

Source: D. L. McLeish, *Dependent central limit theorems and invariance principles*,
Ann. Probab. 2 (1974) 620–628, Theorem (2.3), with the proof of Theorem (2.1). McLeish
normalizes `v = 1`; here `v ≥ 0` is arbitrary (`v = 0` gives convergence to `0`). -/
theorem tendstoInDistribution_martingale_mcLeish [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℝ) (F : ℕ → Filtration ℕ m0) (r : ℕ → ℕ)
    (hmart : ∀ n, Martingale (fun k ω => ∑ j ∈ range k, X n j ω) (F n) μ)
    (hL2 : ∃ B : ℝ≥0∞, B ≠ ∞ ∧
      ∀ᶠ n in atTop, ∫⁻ ω, ⨆ k ∈ range (r n), ‖X n k ω‖ₑ ^ 2 ∂μ ≤ B)
    (hmax : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ω | ∃ k ∈ range (r n), ε < |X n k ω|}) atTop (𝓝 0))
    (v : ℝ≥0)
    (hqv : TendstoInMeasure μ (fun n ω => ∑ k ∈ range (r n), X n k ω ^ 2) atTop
      (fun _ => (v : ℝ))) :
    TendstoInDistribution (fun n ω => ∑ k ∈ range (r n), X n k ω) atTop id (fun _ => μ)
      (gaussianReal 0 v) := by
  obtain ⟨B, hBtop, hB⟩ := hL2
  have hinc := fun n k => martingale_increment (hmart n) k
  have hXsm : ∀ n k, StronglyMeasurable (X n k) := fun n k => (hinc n k).1.mono ((F n).le _)
  have hSmeas : ∀ n, Measurable fun ω => ∑ k ∈ range (r n), X n k ω := fun n =>
    Finset.measurable_fun_sum _ fun k _ => (hXsm n k).measurable
  refine TendstoInDistribution.of_tendsto_charFun (fun n => (hSmeas n).aemeasurable)
    measurable_id.aemeasurable fun t => ?_
  have hlim : charFun ((gaussianReal 0 v).map id) t =
      ((Real.exp (-(v * t ^ 2 / 2)) : ℝ) : ℂ) := by
    rw [Measure.map_id, charFun_gaussianReal]
    push_cast; congr 1; ring
  have hchar : ∀ n, charFun (μ.map fun ω => ∑ k ∈ range (r n), X n k ω) t =
      ∫ ω, Complex.exp (((t * ∑ k ∈ range (r n), X n k ω : ℝ) : ℂ) * Complex.I) ∂μ := by
    intro n
    rw [charFun_apply_real, integral_map (hSmeas n).aemeasurable]
    · push_cast; rfl
    · exact (Complex.continuous_exp.comp ((continuous_const.mul
        Complex.continuous_ofReal).mul continuous_const)).aestronglyMeasurable
  rw [hlim]
  simp_rw [hchar]
  set c : ℂ := ((Real.exp (-(v * t ^ 2 / 2)) : ℝ) : ℂ) with hc
  set K : ℝ := (v : ℝ) + 1 with hK
  have hv0 : (0 : ℝ) ≤ v := v.2
  have hK0 : 0 ≤ K := by positivity
  set Bℝ : ℝ := B.toReal with hBℝ
  have hB0 : 0 ≤ Bℝ := ENNReal.toReal_nonneg
  set Mx : ℕ → Ω → ℝ := fun n ω => (⨆ k ∈ range (r n), ‖X n k ω‖ₑ ^ 2).toReal with hMx
  have hMxf := fun n => maxSq_facts (X n) (r n) (fun k => (hXsm n k).measurable)
  have hMx0 : ∀ n ω, 0 ≤ Mx n ω := fun _ _ => ENNReal.toReal_nonneg
  have hMxint : ∀ᶠ n in atTop, Integrable (Mx n) μ ∧ ∫ ω, Mx n ω ∂μ ≤ Bℝ := by
    filter_upwards [hB] with n hn
    have hne : ∫⁻ ω, ⨆ k ∈ range (r n), ‖X n k ω‖ₑ ^ 2 ∂μ ≠ ∞ := ne_top_of_le_ne_top hBtop hn
    refine ⟨integrable_toReal_of_lintegral_ne_top (hMxf n).1.aemeasurable hne, ?_⟩
    rw [integral_toReal (hMxf n).1.aemeasurable
      (ae_of_all _ fun ω => lt_top_iff_ne_top.2 ((hMxf n).2.1 ω))]
    exact ENNReal.toReal_mono hBtop hn
  -- convergence of probabilities, in real form
  have hprob : ∀ A : ℕ → Set Ω, Tendsto (fun n => μ (A n)) atTop (𝓝 0) →
      ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, μ.real (A n) ≤ τ := by
    intro A hA τ hτ
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hA
    simp only [ENNReal.toReal_zero] at h
    exact h.eventually (Iic_mem_nhds hτ)
  have hqv' := tendstoInMeasure_iff_dist.1 hqv
  have hqvP : ∀ η : ℝ, 0 < η → ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop,
      μ.real {ω | η ≤ dist (qvPrefix (X n) (r n) ω) v} ≤ τ := fun η hη τ hτ =>
    hprob _ (hqv' η hη) τ hτ
  have hstopP : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop,
      μ.real {ω | K < qvPrefix (X n) (r n) ω} ≤ τ := by
    intro τ hτ
    filter_upwards [hqvP 1 one_pos τ hτ] with n hn
    refine le_trans (measureReal_mono fun ω hω => ?_) hn
    simp only [Set.mem_ofPred_eq, Real.dist_eq, hK] at hω ⊢
    rw [abs_of_pos (by linarith)]; linarith
  rw [Metric.tendsto_nhds]
  intro δ hδ
  -- choice of the auxiliary parameters
  set A : ℝ := Real.exp (t ^ 2 * K) * (1 + t ^ 2 * Bℝ) with hA
  have hA0 : 0 < A := by positivity
  set lam : ℝ := δ / (6 * A) with hlam
  have hlam0 : 0 < lam := by positivity
  set ε : ℝ := min (1 / (|t| + 1)) (δ / (6 * (2 * |t| ^ 3 * (K + Bℝ) + 1))) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hεt : |t| * ε ≤ 1 := by
    have h1 : ε ≤ 1 / (|t| + 1) := min_le_left _ _
    have h2 : |t| * (1 / (|t| + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]; linarith
    exact (mul_le_mul_of_nonneg_left h1 (abs_nonneg t)).trans h2
  have hεc : 2 * |t| ^ 3 * ε * (K + Bℝ) ≤ δ / 6 := by
    have h1 : ε ≤ δ / (6 * (2 * |t| ^ 3 * (K + Bℝ) + 1)) := min_le_right _ _
    have hD : 0 ≤ 2 * |t| ^ 3 * (K + Bℝ) := by positivity
    calc 2 * |t| ^ 3 * ε * (K + Bℝ) = (2 * |t| ^ 3 * (K + Bℝ)) * ε := by ring
      _ ≤ (2 * |t| ^ 3 * (K + Bℝ)) * (δ / (6 * (2 * |t| ^ 3 * (K + Bℝ) + 1))) :=
          mul_le_mul_of_nonneg_left h1 hD
      _ ≤ δ / 6 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  set τ : ℝ := min (lam * δ / 24) (δ / 12) with hτ
  have hτ0 : 0 < τ := lt_min (by positivity) (by positivity)
  set η : ℝ := lam * δ / 24 with hη
  have hη0 : 0 < η := by positivity
  have hsmall := hprob _ (hmax ε hε0) τ hτ0
  have hgauss := hqvP (η / (t ^ 2 + 1)) (by positivity) τ hτ0
  filter_upwards [hMxint, hsmall, hgauss, hstopP τ hτ0] with n hMn hsn hgn hstn
  obtain ⟨hMint, hMle⟩ := hMn
  have hsmallEq : {ω | ∃ k ∈ range (r n), ε < |X n k ω|} = (smallSet (X n) (r n) ε)ᶜ := by
    ext ω; simp [smallSet]
  rw [hsmallEq] at hsn
  have hrow := row_bound (μ := μ) (F := F n) (X := X n) (fun k => (hinc n k).1)
    (fun k => (hinc n k).2.1) (fun k => (hinc n k).2.2) hK0 t v ε η lam hv0 hε0.le hεt hη0.le
    hlam0 (r n) (Mx n) hMint (hMx0 n) (hMxf n).2.2
  have hstop := norm_integral_exp_sub_stop_le (μ := μ) (X n) (hXsm n) K t (r n)
  have hBset := measureReal_mono (μ := μ) (gaussFactor_subset (X n) K t v η (r n) hv0)
  have hunion := measureReal_union_le (μ := μ) {ω | K < qvPrefix (X n) (r n) ω}
    {ω | η / (t ^ 2 + 1) ≤ dist (qvPrefix (X n) (r n) ω) v}
  set a := ∫ ω, Complex.exp (((t * ∑ k ∈ range (r n), X n k ω : ℝ) : ℂ) * Complex.I) ∂μ
  set a' := ∫ ω, Complex.exp (((t * ∑ k ∈ range (r n), stopX (X n) K k ω : ℝ) : ℂ) *
    Complex.I) ∂μ
  set p2 := μ.real (smallSet (X n) (r n) ε)ᶜ
  set p3 := μ.real {ω | K < qvPrefix (X n) (r n) ω}
  set pq := μ.real {ω | η / (t ^ 2 + 1) ≤ dist (qvPrefix (X n) (r n) ω) v}
  set pB := μ.real {ω | η < |Real.exp (-(t ^ 2 / 2 * ∑ k ∈ range (r n), stopX (X n) K k ω ^ 2)) -
        Real.exp (-(v * t ^ 2 / 2))|}
  set IM := ∫ ω, Mx n ω ∂μ
  have hτ1 : τ ≤ lam * δ / 24 := min_le_left _ _
  have hτ2 : τ ≤ δ / 12 := min_le_right _ _
  have hpB : pB ≤ 2 * τ := by linarith
  have hcub : 2 * |t| ^ 3 * ε * (K + IM) ≤ δ / 6 := by
    refine le_trans ?_ hεc
    have : 0 ≤ 2 * |t| ^ 3 * ε := by positivity
    nlinarith
  have hlamA : lam * (Real.exp (t ^ 2 * K) * (1 + t ^ 2 * IM)) ≤ δ / 6 := by
    have h1 : Real.exp (t ^ 2 * K) * (1 + t ^ 2 * IM) ≤ A := by
      rw [hA]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      nlinarith [sq_nonneg t]
    have h2 : lam * A = δ / 6 := by rw [hlam]; field_simp
    nlinarith
  have hinv : lam⁻¹ * (2 * (η + pB) + 2 * p2) ≤ δ / 3 := by
    have h1 : 2 * (η + pB) + 2 * p2 ≤ lam * δ / 3 := by rw [hη] at *; linarith
    have h2 : lam⁻¹ * (lam * δ / 3) = δ / 3 := by field_simp
    calc _ ≤ lam⁻¹ * (lam * δ / 3) :=
          mul_le_mul_of_nonneg_left h1 (inv_pos.2 hlam0).le
      _ = δ / 3 := h2
  rw [dist_eq_norm]
  have htri : ‖a - c‖ ≤ ‖a - a'‖ + ‖a' - c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  linarith

private lemma lindebergTerm_eq (Y : Ω → ℝ) (ε : ℝ) :
    (fun ω => Y ω ^ 2 * Set.indicator {ω' | ε < |Y ω'|} 1 ω) =
      {ω' | ε < |Y ω'|}.indicator fun ω => Y ω ^ 2 := by
  funext ω
  by_cases h : ω ∈ {ω' | ε < |Y ω'|} <;> simp [h]

/-- The Lindeberg condition (with square-integrable increments) implies McLeish's conditions
(a), an eventual `L¹` bound on the maximal squared increment, and (b), the maximal increment
tends to `0` in probability. -/
private lemma mcLeish_conditions_of_lindeberg [IsProbabilityMeasure μ] (X : ℕ → ℕ → Ω → ℝ)
    (hXm : ∀ n k, Measurable (X n k))
    (hint2 : ∀ n, ∀ k ∈ range n, Integrable (fun ω => X n k ω ^ 2) μ)
    (hL : LindebergConditionTriangular X μ) :
    (∃ B : ℝ≥0∞, B ≠ ∞ ∧
      ∀ᶠ n in atTop, ∫⁻ ω, ⨆ k ∈ range (id n), ‖X n k ω‖ₑ ^ 2 ∂μ ≤ B) ∧
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ω | ∃ k ∈ range (id n), ε < |X n k ω|}) atTop (𝓝 0)) := by
  have hLint : ∀ ε, ∀ n, ∀ k ∈ range n,
      Integrable (fun ω => X n k ω ^ 2 * Set.indicator {ω' | ε < |X n k ω'|} 1 ω) μ := by
    intro ε n k hk
    rw [lindebergTerm_eq]
    exact (hint2 n k hk).indicator
      (measurableSet_lt measurable_const (continuous_abs.measurable.comp (hXm n k)))
  have hLnn : ∀ ε n k ω, 0 ≤ X n k ω ^ 2 * Set.indicator {ω' | ε < |X n k ω'|} 1 ω := by
    intro ε n k ω
    exact mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  refine ⟨⟨2, by simp, ?_⟩, ?_⟩
  · -- (a) from the Lindeberg condition at level `1`
    filter_upwards [(hL 1 one_pos).eventually (Iic_mem_nhds one_pos)] with n hn
    have hpt : ∀ ω, (⨆ k ∈ range (id n), ‖X n k ω‖ₑ ^ 2) ≤ 1 + ∑ k ∈ range n,
        ENNReal.ofReal (X n k ω ^ 2 * Set.indicator {ω' | 1 < |X n k ω'|} 1 ω) := by
      intro ω
      refine iSup₂_le fun k hk => ?_
      have he : ‖X n k ω‖ₑ ^ 2 = ENNReal.ofReal (X n k ω ^ 2) := by
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      rw [he]
      by_cases h1 : 1 < |X n k ω|
      · have hind : X n k ω ^ 2 * Set.indicator {ω' | 1 < |X n k ω'|} 1 ω = X n k ω ^ 2 := by
          simp [Set.indicator_of_mem (show ω ∈ {ω' | 1 < |X n k ω'|} from h1)]
        refine le_add_left ?_
        refine le_trans (le_of_eq ?_) (single_le_sum (f := fun k => ENNReal.ofReal
          (X n k ω ^ 2 * Set.indicator {ω' | 1 < |X n k ω'|} 1 ω)) (fun _ _ => zero_le) hk)
        rw [hind]
      · refine le_add_right ?_
        rw [ENNReal.ofReal_le_one]
        have : X n k ω ^ 2 = |X n k ω| ^ 2 := (sq_abs _).symm
        rw [this]; nlinarith [abs_nonneg (X n k ω), not_lt.1 h1]
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    have hmeasL : ∀ k, Measurable fun ω =>
        ENNReal.ofReal (X n k ω ^ 2 * Set.indicator {ω' | 1 < |X n k ω'|} 1 ω) := by
      intro k
      refine ENNReal.measurable_ofReal.comp (((hXm n k).pow_const 2).mul ?_)
      exact measurable_one.indicator
        (measurableSet_lt measurable_const (continuous_abs.measurable.comp (hXm n k)))
    rw [lintegral_finsetSum _ fun k _ => hmeasL k]
    have hsum : ∑ k ∈ range n, ∫⁻ ω, ENNReal.ofReal
        (X n k ω ^ 2 * Set.indicator {ω' | 1 < |X n k ω'|} 1 ω) ∂μ =
        ENNReal.ofReal (∑ k ∈ range n,
          ∫ ω, X n k ω ^ 2 * Set.indicator {ω' | 1 < |X n k ω'|} 1 ω ∂μ) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun k _ => integral_nonneg fun ω => hLnn 1 n k ω]
      refine sum_congr rfl fun k hk => ?_
      rw [ofReal_integral_eq_lintegral_ofReal (hLint 1 n k hk)
        (ae_of_all _ fun ω => hLnn 1 n k ω)]
    rw [hsum, show (2 : ℝ≥0∞) = 1 + 1 by norm_num]
    gcongr
    exact ENNReal.ofReal_le_one.2 hn
  · -- (b) from the Lindeberg condition at level `ε`, by Chebyshev and a union bound
    intro ε hε
    have hbound : ∀ n, μ {ω | ∃ k ∈ range (id n), ε < |X n k ω|} ≤ ENNReal.ofReal
        ((ε ^ 2)⁻¹ * ∑ k ∈ range n,
          ∫ ω, X n k ω ^ 2 * Set.indicator {ω' | ε < |X n k ω'|} 1 ω ∂μ) := by
      intro n
      have hset : {ω | ∃ k ∈ range (id n), ε < |X n k ω|} =
          ⋃ k ∈ range n, {ω | ε < |X n k ω|} := by ext ω; simp
      rw [hset]
      refine (measure_biUnion_finset_le _ _).trans ?_
      rw [mul_sum, ENNReal.ofReal_sum_of_nonneg fun k _ =>
        mul_nonneg (by positivity) (integral_nonneg fun ω => hLnn ε n k ω)]
      refine sum_le_sum fun k hk => ?_
      have hcheb := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => hLnn ε n k ω)
        (hLint ε n k hk) (ε ^ 2)
      have hsub : {ω | ε < |X n k ω|} ⊆
          {ω | ε ^ 2 ≤ X n k ω ^ 2 * Set.indicator {ω' | ε < |X n k ω'|} 1 ω} := by
        intro ω hω
        simp only [Set.mem_ofPred_eq] at hω ⊢
        rw [Set.indicator_of_mem (show ω ∈ {ω' | ε < |X n k ω'|} from hω), Pi.one_apply,
          mul_one]
        have h2 : ε ^ 2 ≤ |X n k ω| ^ 2 := pow_le_pow_left₀ hε.le hω.le 2
        rwa [sq_abs] at h2
      have h1 : μ.real {ω | ε < |X n k ω|} ≤ (ε ^ 2)⁻¹ *
          ∫ ω, X n k ω ^ 2 * Set.indicator {ω' | ε < |X n k ω'|} 1 ω ∂μ := by
        rw [le_inv_mul_iff₀ (by positivity)]
        exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (by positivity)).trans hcheb
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal h1
    have hlim : Tendsto (fun n => ENNReal.ofReal ((ε ^ 2)⁻¹ * ∑ k ∈ range n,
        ∫ ω, X n k ω ^ 2 * Set.indicator {ω' | ε < |X n k ω'|} 1 ω ∂μ)) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal ((hL ε hε).const_mul (ε ^ 2)⁻¹)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) hbound


/-- **Martingale CLT under the Lindeberg condition.** For a martingale difference array (row `n`
has `n` increments, as in `LindebergConditionTriangular`) with square-integrable increments, if
the realized quadratic variation `∑_{k<n} X n k²` tends to `v` in probability and the Lindeberg
condition holds, the row sums converge in distribution to `N(0, v)`. The Lindeberg condition
implies McLeish's conditions (a) and (b), so this is a corollary of
`tendstoInDistribution_martingale_mcLeish`.

Source: McLeish (1974), remarks following Theorem (2.3), pp. 621–622 (the Lindeberg condition
implies (a) and (b)); compare P. Hall and C. C. Heyde, *Martingale Limit Theory and Its
Application* (1980), Theorem 3.2. -/
theorem tendstoInDistribution_martingale_lindeberg [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℝ) (F : ℕ → Filtration ℕ m0)
    (hmart : ∀ n, Martingale (fun k ω => ∑ j ∈ range k, X n j ω) (F n) μ)
    (hint2 : ∀ n, ∀ k ∈ range n, Integrable (fun ω => X n k ω ^ 2) μ)
    (hL : LindebergConditionTriangular X μ) (v : ℝ≥0)
    (hqv : TendstoInMeasure μ (fun n ω => ∑ k ∈ range n, X n k ω ^ 2) atTop
      (fun _ => (v : ℝ))) :
    TendstoInDistribution (fun n ω => ∑ k ∈ range n, X n k ω) atTop id (fun _ => μ)
      (gaussianReal 0 v) := by
  have hXm : ∀ n k, Measurable (X n k) := fun n k =>
    ((martingale_increment (hmart n) k).1.mono ((F n).le _)).measurable
  obtain ⟨ha, hb⟩ := mcLeish_conditions_of_lindeberg X hXm hint2 hL
  exact tendstoInDistribution_martingale_mcLeish X F id hmart ha hb v hqv

/-! ### Finite-dimensional convergence -/

/-- A martingale transform with deterministic coefficients is a martingale. -/
private lemma martingale_weighted [IsFiniteMeasure μ] {F : Filtration ℕ m0} {X : ℕ → Ω → ℝ}
    (h : Martingale (fun k ω => ∑ j ∈ range k, X j ω) F μ) (a : ℕ → ℝ) :
    Martingale (fun k ω => ∑ j ∈ range k, a j * X j ω) F μ := by
  have hinc := martingale_increment h
  refine martingale_of_condExp_sub_eq_zero_nat (fun k => ?_) (fun k => ?_) fun k => ?_
  · refine Finset.stronglyMeasurable_fun_sum _ fun j hj => ?_
    exact stronglyMeasurable_const.mul ((hinc j).1.mono (F.mono (mem_range.1 hj)))
  · exact integrable_finsetSum _ fun j _ => (hinc j).2.1.const_mul _
  · have hd : ((fun ω => ∑ j ∈ range (k + 1), a j * X j ω) -
        fun ω => ∑ j ∈ range k, a j * X j ω) = a k • X k := by
      funext ω; simp [sum_range_succ]
    rw [hd]
    filter_upwards [condExp_smul (a k) (X k) (F k), (hinc k).2.2] with ω h1 hω
    rw [h1]
    simp [hω]

/-- Indicator weights: summing over `k < N` equals summing the weighted terms over `k < r`
when `N ≤ r`. -/
private lemma sum_range_eq_sum_ite {N r : ℕ} (hNr : N ≤ r) (f : ℕ → ℝ) :
    ∑ k ∈ range N, f k = ∑ k ∈ range r, (if k < N then 1 else 0) * f k := by
  simp only [ite_mul, one_mul, zero_mul]
  rw [← sum_filter]
  congr 1
  ext k; simp only [mem_range, mem_filter]; omega

/-- **One linear combination.** Under McLeish's hypotheses for a time-indexed martingale
array, every finite linear combination `∑_s c_s S_n(s)` of the partial-sum process converges in
distribution to the corresponding combination of any process `Z` with the Gaussian
finite-dimensional laws of covariance `A (min s u)`. -/
private lemma tendstoInDistribution_linComb [IsProbabilityMeasure μ]
    {ι : Type*} [LinearOrder ι]
    (X : ℕ → ℕ → Ω → ℝ) (F : ℕ → Filtration ℕ m0) (r : ℕ → ℕ)
    (hmart : ∀ n, Martingale (fun k ω => ∑ j ∈ range k, X n j ω) (F n) μ)
    (hL2 : ∃ B : ℝ≥0∞, B ≠ ∞ ∧
      ∀ᶠ n in atTop, ∫⁻ ω, ⨆ k ∈ range (r n), ‖X n k ω‖ₑ ^ 2 ∂μ ≤ B)
    (hmax : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ω | ∃ k ∈ range (r n), ε < |X n k ω|}) atTop (𝓝 0))
    (N : ℕ → ι → ℕ) (hN : ∀ n, Monotone (N n)) (hNr : ∀ n s, N n s ≤ r n) (A : ι → ℝ)
    (hqv : ∀ s, TendstoInMeasure μ (fun n ω => ∑ k ∈ range (N n s), X n k ω ^ 2) atTop
      (fun _ => A s))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (Z : ι → Ω' → ℝ) (hZm : ∀ s, Measurable (Z s))
    (hZ : ∀ (I : Finset ι) (c : I → ℝ), P'.map (fun ω => ∑ s : I, c s * Z s ω) =
      gaussianReal 0 (∑ s : I, ∑ u : I, c s * c u * A (min (s : ι) u)).toNNReal)
    (I : Finset ι) (c : I → ℝ) :
    TendstoInDistribution (fun n ω => ∑ s : I, c s * ∑ k ∈ range (N n s), X n k ω) atTop
      (fun ω => ∑ s : I, c s * Z s ω) (fun _ => μ) P' := by
  obtain ⟨B, hBtop, hB⟩ := hL2
  set a : ℕ → ℕ → ℝ := fun n k => ∑ s : I, c s * (if k < N n s then 1 else 0) with ha
  set C : ℝ := ∑ s : I, |c s| with hC
  have hC0 : 0 ≤ C := sum_nonneg fun _ _ => abs_nonneg _
  have haC : ∀ n k, |a n k| ≤ C := by
    intro n k
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s _ => ?_)
    rw [abs_mul]
    split_ifs <;> simp
  set Y : ℕ → ℕ → Ω → ℝ := fun n k ω => a n k * X n k ω with hY
  have hsum : ∀ n ω, ∑ s : I, c s * ∑ k ∈ range (N n s), X n k ω =
      ∑ k ∈ range (r n), Y n k ω := by
    intro n ω
    simp_rw [sum_range_eq_sum_ite (hNr n _), mul_sum, hY, ha, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun k _ => sum_congr rfl fun s _ => by ring
  set q : ℝ := ∑ s : I, ∑ u : I, c s * c u * A (min (s : ι) u) with hq
  have hqvY : ∀ n ω, ∑ k ∈ range (r n), Y n k ω ^ 2 = ∑ s : I, ∑ u : I,
      c s * c u * ∑ k ∈ range (N n (min (s : ι) u)), X n k ω ^ 2 := by
    intro n ω
    have hind : ∀ k (s u : I), (if k < N n (min (s : ι) u) then (1 : ℝ) else 0) =
        (if k < N n s then 1 else 0) * (if k < N n u then 1 else 0) := by
      intro k s u
      rw [(hN n).map_min]
      by_cases h1 : k < N n s <;> by_cases h2 : k < N n u <;> simp [h1, h2]
    set G : ℕ → I → I → ℝ := fun k s u =>
      c s * c u * ((if k < N n (min (s : ι) u) then 1 else 0) * X n k ω ^ 2) with hG
    have hk : ∀ k, Y n k ω ^ 2 = ∑ s : I, ∑ u : I, G k s u := by
      intro k
      have h1 : Y n k ω ^ 2 = a n k * a n k * X n k ω ^ 2 := by simp only [hY]; ring
      rw [h1, ha, sum_mul_sum, sum_mul]
      refine sum_congr rfl fun s _ => ?_
      rw [sum_mul]
      refine sum_congr rfl fun u _ => ?_
      simp only [hG, hind]; ring
    calc ∑ k ∈ range (r n), Y n k ω ^ 2
        = ∑ k ∈ range (r n), ∑ s : I, ∑ u : I, G k s u := sum_congr rfl fun k _ => hk k
      _ = ∑ s : I, ∑ k ∈ range (r n), ∑ u : I, G k s u := sum_comm
      _ = ∑ s : I, ∑ u : I, ∑ k ∈ range (r n), G k s u :=
          sum_congr rfl fun s _ => sum_comm
      _ = _ := by
          refine sum_congr rfl fun s _ => sum_congr rfl fun u _ => ?_
          rw [sum_range_eq_sum_ite (hNr n _), mul_sum]
  have hqvY' : TendstoInMeasure μ (fun n ω => ∑ k ∈ range (r n), Y n k ω ^ 2) atTop
      (fun _ => q) := by
    have h := tendstoInMeasure_sum (μ := μ) (Finset.univ : Finset I) (fun s _ =>
      tendstoInMeasure_sum (Finset.univ : Finset I) fun u _ =>
        tendstoInMeasure_const_mul (c s * c u) (hqv (min (s : ι) u)))
    refine h.congr_left fun n => ae_of_all _ fun ω => (hqvY n ω).symm
  have hq0 : 0 ≤ q := nonneg_of_tendstoInMeasure hqvY' fun n ω =>
    sum_nonneg fun _ _ => sq_nonneg _
  have hqv' : TendstoInMeasure μ (fun n ω => ∑ k ∈ range (r n), Y n k ω ^ 2) atTop
      (fun _ => ((q.toNNReal : ℝ≥0) : ℝ)) := by
    rw [Real.coe_toNNReal _ hq0]; exact hqvY'
  have hmartY : ∀ n, Martingale (fun k ω => ∑ j ∈ range k, Y n j ω) (F n) μ :=
    fun n => martingale_weighted (hmart n) (a n)
  have hL2Y : ∃ B : ℝ≥0∞, B ≠ ∞ ∧
      ∀ᶠ n in atTop, ∫⁻ ω, ⨆ k ∈ range (r n), ‖Y n k ω‖ₑ ^ 2 ∂μ ≤ B := by
    refine ⟨ENNReal.ofReal (C ^ 2) * B, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBtop, ?_⟩
    filter_upwards [hB] with n hn
    have hpt : ∀ ω, (⨆ k ∈ range (r n), ‖Y n k ω‖ₑ ^ 2) ≤
        ENNReal.ofReal (C ^ 2) * ⨆ k ∈ range (r n), ‖X n k ω‖ₑ ^ 2 := by
      intro ω
      refine iSup₂_le fun k hk => ?_
      have h1 : ‖Y n k ω‖ₑ ^ 2 ≤ ENNReal.ofReal (C ^ 2) * ‖X n k ω‖ₑ ^ 2 := by
        simp only [hY]
        rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
          ← ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.ofReal_pow (abs_nonneg _),
          ← ENNReal.ofReal_mul (sq_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [abs_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (haC n k) 2)
          (sq_nonneg _)
      exact h1.trans (mul_le_mul_right
        (le_iSup₂ (f := fun k (_ : k ∈ range (r n)) => ‖X n k ω‖ₑ ^ 2) k hk) _)
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul_right hn _
  have hmaxY : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ω | ∃ k ∈ range (r n), ε < |Y n k ω|}) atTop (𝓝 0) := by
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hmax (ε / (C + 1)) (by positivity)) (fun _ => zero_le) fun n => measure_mono ?_
    rintro ω ⟨k, hk, hlt⟩
    refine ⟨k, hk, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    have h1 : |Y n k ω| ≤ C * |X n k ω| := by
      simp only [hY]; rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (haC n k) (abs_nonneg _)
    nlinarith [abs_nonneg (X n k ω)]
  have h1 := tendstoInDistribution_martingale_mcLeish Y F r hmartY hL2Y hmaxY q.toNNReal hqv'
  have hZc : AEMeasurable (fun ω => ∑ s : I, c s * Z s ω) P' :=
    (Finset.measurable_fun_sum (Finset.univ : Finset I) fun s _ =>
      (hZm (s : ι)).const_mul (c s)).aemeasurable
  have hlaw : (⟨P'.map (fun ω => ∑ s : I, c s * Z s ω), inferInstance⟩ :
      ProbabilityMeasure ℝ) = ⟨(gaussianReal 0 q.toNNReal).map id, inferInstance⟩ := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.coe_mk, Measure.map_id]
    exact hZ I c
  have hfun : (fun n ω => ∑ s : I, c s * ∑ k ∈ range (N n s), X n k ω) =
      fun n ω => ∑ k ∈ range (r n), Y n k ω := funext fun n => funext (hsum n)
  rw [hfun]
  refine ⟨h1.forall_aemeasurable, hZc, ?_⟩
  rw [hlaw]
  exact h1.tendsto

/-- **Finite-dimensional convergence for martingale arrays** (McLeish 1974, Theorem (3.2),
finite-dimensional part of the proof, with a general variance function `A` in place of `t`).

Let `X n k` be a martingale difference array satisfying McLeish's conditions (a) and (b) on the
rows `k < r n`, and let `S n s = ∑_{k < N n s} X n k` be the partial-sum process along a
time index `s ∈ ι` (any linear order), where `N n` is monotone with `N n s ≤ r n` (for example
`N n s = ⌊n s⌋` on `[0,1]` with `r n = n`). If for every time `s` the realized quadratic
variation `∑_{k < N n s} X n k²` tends to `A s` in probability, then for every finite set of
times `I` the vector `(S n s)_{s ∈ I}` converges in distribution to `(Z s)_{s ∈ I}`, for any
process `Z` whose finite-dimensional laws are centered Gaussian with covariance
`Cov(Z s, Z u) = A (min s u)` (stated through all linear combinations, `hZ`). With `A` the
identity on `[0,1]`, `Z` is a Brownian motion; in general `Z = W ∘ A`.

The proof is the Cramér–Wold device (Mathlib's `TendstoInDistribution.of_inner`) applied to
`tendstoInDistribution_martingale_mcLeish` for the weighted array
`a n k X n k`, `a n k = ∑_{s ∈ I} c s 𝟙{k < N n s}`, whose quadratic variation is
`∑_{s,u} c s c u ∑_{k < N n (min s u)} X n k²` by monotonicity of `N n`. -/
theorem tendstoInDistribution_fdd_martingale_mcLeish [IsProbabilityMeasure μ]
    {ι : Type*} [LinearOrder ι]
    (X : ℕ → ℕ → Ω → ℝ) (F : ℕ → Filtration ℕ m0) (r : ℕ → ℕ)
    (hmart : ∀ n, Martingale (fun k ω => ∑ j ∈ range k, X n j ω) (F n) μ)
    (hL2 : ∃ B : ℝ≥0∞, B ≠ ∞ ∧
      ∀ᶠ n in atTop, ∫⁻ ω, ⨆ k ∈ range (r n), ‖X n k ω‖ₑ ^ 2 ∂μ ≤ B)
    (hmax : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ω | ∃ k ∈ range (r n), ε < |X n k ω|}) atTop (𝓝 0))
    (N : ℕ → ι → ℕ) (hN : ∀ n, Monotone (N n)) (hNr : ∀ n s, N n s ≤ r n) (A : ι → ℝ)
    (hqv : ∀ s, TendstoInMeasure μ (fun n ω => ∑ k ∈ range (N n s), X n k ω ^ 2) atTop
      (fun _ => A s))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (Z : ι → Ω' → ℝ) (hZm : ∀ s, Measurable (Z s))
    (hZ : ∀ (I : Finset ι) (c : I → ℝ), P'.map (fun ω => ∑ s : I, c s * Z s ω) =
      gaussianReal 0 (∑ s : I, ∑ u : I, c s * c u * A (min (s : ι) u)).toNNReal)
    (I : Finset ι) :
    TendstoInDistribution (fun n ω => I.restrict fun s => ∑ k ∈ range (N n s), X n k ω) atTop
      (fun ω => I.restrict fun s => Z s ω) (fun _ => μ) P' := by
  have hXm : ∀ n k, Measurable (X n k) := fun n k =>
    ((martingale_increment (hmart n) k).1.mono ((F n).le _)).measurable
  set V : ℕ → Ω → EuclideanSpace ℝ I := fun n ω =>
    WithLp.toLp 2 (I.restrict fun s => ∑ k ∈ range (N n s), X n k ω) with hV
  set W : Ω' → EuclideanSpace ℝ I := fun ω => WithLp.toLp 2 (I.restrict fun s => Z s ω) with hW
  have hWm : Measurable W :=
    (WithLp.measurable_toLp 2 _).comp (Measurable.of_eval fun s : I => hZm (s : ι))
  have hVm : ∀ n, Measurable (V n) := fun n =>
    (WithLp.measurable_toLp 2 _).comp (Measurable.of_eval fun s : I =>
      Finset.measurable_fun_sum (range (N n (s : ι))) fun k _ => hXm n k)
  have hinner : ∀ (c : EuclideanSpace ℝ I) (v : I → ℝ),
      inner ℝ (WithLp.toLp 2 v : EuclideanSpace ℝ I) c = ∑ s : I, c s * v s := by
    intro c v
    rw [PiLp.inner_apply]
    refine sum_congr rfl fun s _ => ?_
    rw [PiLp.toLp_apply, Real.inner_apply, mul_comm]
  have hVW : TendstoInDistribution V atTop W (fun _ => μ) P' := by
    refine TendstoInDistribution.of_inner hWm.aemeasurable (fun n => (hVm n).aemeasurable)
      fun c => ?_
    have h := tendstoInDistribution_linComb X F r hmart hL2 hmax N hN hNr A hqv Z hZm hZ I
      (fun s => c s)
    refine h.congr (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
    · simp only [hV, hinner, Finset.restrict]
    · simp only [hW, hinner, Finset.restrict]
  have h := hVW.continuous_comp (PiLp.continuous_ofLp 2 _)
  simpa [hV, hW, Function.comp_def] using h

/-- **Finite-dimensional convergence under the Lindeberg condition.** The Lindeberg form of
`tendstoInDistribution_fdd_martingale_mcLeish`: rows of length `n`, square-integrable
increments, `LindebergConditionTriangular`, quadratic-variation convergence
`∑_{k < N n s} X n k² → A s` in probability at every time `s`, and `N n s ≤ n`. The
finite-dimensional distributions of `S n s = ∑_{k < N n s} X n k` converge to those of any
process `Z` with centered Gaussian finite-dimensional laws of covariance `A (min s u)`. -/
theorem tendstoInDistribution_fdd_martingale_lindeberg [IsProbabilityMeasure μ]
    {ι : Type*} [LinearOrder ι]
    (X : ℕ → ℕ → Ω → ℝ) (F : ℕ → Filtration ℕ m0)
    (hmart : ∀ n, Martingale (fun k ω => ∑ j ∈ range k, X n j ω) (F n) μ)
    (hint2 : ∀ n, ∀ k ∈ range n, Integrable (fun ω => X n k ω ^ 2) μ)
    (hL : LindebergConditionTriangular X μ)
    (N : ℕ → ι → ℕ) (hN : ∀ n, Monotone (N n)) (hNn : ∀ n s, N n s ≤ n) (A : ι → ℝ)
    (hqv : ∀ s, TendstoInMeasure μ (fun n ω => ∑ k ∈ range (N n s), X n k ω ^ 2) atTop
      (fun _ => A s))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (Z : ι → Ω' → ℝ) (hZm : ∀ s, Measurable (Z s))
    (hZ : ∀ (I : Finset ι) (c : I → ℝ), P'.map (fun ω => ∑ s : I, c s * Z s ω) =
      gaussianReal 0 (∑ s : I, ∑ u : I, c s * c u * A (min (s : ι) u)).toNNReal)
    (I : Finset ι) :
    TendstoInDistribution (fun n ω => I.restrict fun s => ∑ k ∈ range (N n s), X n k ω) atTop
      (fun ω => I.restrict fun s => Z s ω) (fun _ => μ) P' := by
  have hXm : ∀ n k, Measurable (X n k) := fun n k =>
    ((martingale_increment (hmart n) k).1.mono ((F n).le _)).measurable
  obtain ⟨ha, hb⟩ := mcLeish_conditions_of_lindeberg X hXm hint2 hL
  exact tendstoInDistribution_fdd_martingale_mcLeish X F id hmart ha hb N hN hNn A hqv Z hZm hZ I

end Main

end MathlibExt.Probability.Martingale
