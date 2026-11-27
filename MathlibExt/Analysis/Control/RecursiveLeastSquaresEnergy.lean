/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The one-step energy and log-determinant bounds, predictable martingale normalization, and
measurability and noise-moment arguments are adapted from Ahmad Rammal's
`MathlibExt/Analysis/Control/RecursiveLeastSquaresRegret.lean` at commit
`e8b0157bd888873d70c0e2a60e547ecf28bd0fb2` (https://github.com/facebookresearch/atlas-lean/pull/6727).
Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
Licensed under the license in this repository's LICENSE file.
-/

module

public import MathlibExt.Analysis.Control.RecursiveLeastSquares
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Process.Adapted
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Martingale.Convergence
import MathlibExt.MeasureTheory.Function.ConditionalExpectation.BestPredictor
import MathlibExt.Probability.MartingaleOrthogonality

/-!
# Shared stochastic energy estimate for recursive least squares

This is the single-sensor case of Theorem 3.1 of Xie, Zhang and Guo, *Convergence of a Distributed
Least Squares*, in the combined form of their Lemma 4.4, whose extra term vanishes for one sensor;
their Theorems 3.2 and 3.3 are derived from it. The information-weighted error drops by the weighted
prediction error at each step, up to a martingale cross term and a squared-noise term. Predictable
normalization lets half the weighted prediction error absorb the cross term; the log-determinant
bound controls the accumulated gains in the squared-noise term. Neither bounded leverage nor
unbounded cumulative regressor energy is needed.
-/

@[expose] public section

open Matrix MeasureTheory Filter
open scoped Topology ProbabilityTheory
namespace MathlibExt.Analysis.Control.RecursiveLeastSquares
section
private theorem energy_step {d : ℕ} {R P : Matrix (Fin d) (Fin d) ℝ}
    (hR : R.PosDef) (hRP : R * P = 1) (φ e : Fin d → ℝ) (w : ℝ) :
    let q := φ ⬝ᵥ (P *ᵥ φ)
    let u := φ ⬝ᵥ e
    let e' := e + ((w - u) / (1 + q)) • (P *ᵥ φ)
    e' ⬝ᵥ ((R + vecMulVec φ φ) *ᵥ e') =
      e ⬝ᵥ (R *ᵥ e) - u ^ 2 / (1 + q) + 2 * (u / (1 + q)) * w + q / (1 + q) * w ^ 2 := by
  dsimp only
  set x := P *ᵥ φ with hx_def
  set q := φ ⬝ᵥ x with hq_def
  set u := φ ⬝ᵥ e with hu_def
  have hx : R *ᵥ x = φ := by rw [hx_def, mulVec_mulVec, hRP, one_mulVec]
  have he : x ⬝ᵥ (R *ᵥ e) = u := by
    simpa only [star_trivial, hx, dotProduct_comm e φ, ← hu_def] using
      hR.isHermitian.star_dotProduct_mulVec_comm x e
  have hq : 0 ≤ q := by
    have hP : P = R⁻¹ := (inv_eq_right_inv hRP).symm
    simpa only [hq_def, hx_def, hP, star_trivial] using
      hR.inv.posSemidef.dotProduct_mulVec_nonneg φ
  have hden : 1 + q ≠ 0 := by positivity
  simp only [add_mulVec, mulVec_add, mulVec_smul, vecMulVec_mulVec, op_smul_eq_smul,
    dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, hx, he,
    dotProduct_comm e φ, dotProduct_comm x φ, ← hu_def, ← hq_def]
  field_simp
  ring

private theorem log_det_rlsInformation_le {d : ℕ} {P₀ : Matrix (Fin d) (Fin d) ℝ}
    (hP₀ : P₀.PosDef) : ∃ D : ℝ, ∀ (φ : ℕ → Fin d → ℝ) (t : ℕ),
    Real.log (rlsInformation P₀ φ t).det ≤
      D + d * Real.log (1 + ∑ k ∈ Finset.range t, φ k ⬝ᵥ φ k) := by
  let K := 1 + ∑ i : Fin d, ∑ j : Fin d, |P₀⁻¹ i j|
  have hK : 1 ≤ K := by
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => abs_nonneg _)
  refine ⟨Real.log ((d.factorial : ℝ) * K ^ d), fun φ t => ?_⟩
  let S := ∑ k ∈ Finset.range t, φ k ⬝ᵥ φ k
  have hsq (x : Fin d → ℝ) (i : Fin d) : x i ^ 2 ≤ x ⬝ᵥ x := by
    simpa only [dotProduct, pow_two] using
      (Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
        (Finset.mem_univ i))
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => by
    simpa only [star_trivial] using dotProduct_self_star_nonneg (φ k)
  have hentries (i j : Fin d) : |rlsInformation P₀ φ t i j| ≤ K * (1 + S) := by
    simp only [rlsInformation, Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply]
    have hinv : |P₀⁻¹ i j| ≤ K := by
      have hrow : |P₀⁻¹ i j| ≤ ∑ b : Fin d, |P₀⁻¹ i b| :=
        Finset.single_le_sum (fun b _ => abs_nonneg (P₀⁻¹ i b)) (Finset.mem_univ j)
      have hrows : (∑ b : Fin d, |P₀⁻¹ i b|) ≤ ∑ a : Fin d, ∑ b : Fin d, |P₀⁻¹ a b| :=
        Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => abs_nonneg (P₀⁻¹ a b))
          (Finset.mem_univ i)
      dsimp [K]
      linarith
    have hsum : |∑ k ∈ Finset.range t, φ k i * φ k j| ≤ S := by
      refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul]
      nlinarith [hsq (φ k) i, hsq (φ k) j, sq_nonneg (|φ k i| - |φ k j|),
        sq_abs (φ k i), sq_abs (φ k j)]
    exact (abs_add_le ..).trans ((add_le_add hinv hsum).trans (by nlinarith))
  have hdet := Matrix.det_le (abv := AbsoluteValue.abs) hentries
  simp only [AbsoluteValue.abs_apply, abs_of_pos (posDef_rlsInformation hP₀ φ t).det_pos,
    Fintype.card_fin, nsmul_eq_mul, mul_pow, ← mul_assoc] at hdet
  change Real.log (rlsInformation P₀ φ t).det ≤ _ + d * Real.log (1 + S)
  refine (Real.log_le_log (posDef_rlsInformation hP₀ φ t).det_pos hdet).trans_eq ?_
  rw [Real.log_mul (by have := Nat.factorial_pos d; positivity) (by positivity), Real.log_pow]

private def clock (a : ℕ → ℝ) (n : ℕ) : ℝ := 1 + ∑ k ∈ Finset.range n, a k

private theorem clock_succ (a : ℕ → ℝ) (k : ℕ) : clock a (k + 1) = clock a k + a k := by
  simp [clock, Finset.sum_range_succ, add_assoc]

private theorem clock_one_le {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (n : ℕ) : 1 ≤ clock a n :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => ha k)

private theorem clock_mono {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) : Monotone (clock a) :=
  monotone_nat_of_le_succ fun k => by rw [clock_succ]; exact le_add_of_nonneg_right (ha k)

/-- The right-endpoint sums of `x⁻ᵖ` on the intervals of the clock are bounded by its
integral on `[1, ∞)`. Intervals of zero length cause no problem. -/
private theorem clock_moment_budget {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) {p : ℝ} (hp : 1 < p)
    (n : ℕ) : ∑ k ∈ Finset.range n, a k / clock a (k + 1) ^ p ≤ (p - 1)⁻¹ := by
  have hclock k : 0 < clock a k := zero_lt_one.trans_le (clock_one_le ha k)
  have hstep k : a k / clock a (k + 1) ^ p ≤
      (clock a k ^ (1 - p) - clock a (k + 1) ^ (1 - p)) / (p - 1) := by
    have hab := clock_mono ha (Nat.le_succ k)
    have h0 : (0 : ℝ) ∉ Set.uIcc (clock a k) (clock a (k + 1)) := by
      rw [Set.uIcc_of_le hab]
      exact fun h => (hclock k).not_ge h.1
    have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
      (f := fun _ => clock a (k + 1) ^ (-p)) (g := fun x => x ^ (-p))
      intervalIntegrable_const (intervalIntegral.intervalIntegrable_rpow (Or.inr h0))
      (fun x hx => Real.rpow_le_rpow_of_nonpos (hclock k |>.trans_le hx.1) hx.2 (by linarith))
    rw [intervalIntegral.integral_const, integral_rpow (Or.inr ⟨by linarith, h0⟩),
      smul_eq_mul, Real.rpow_neg (hclock (k+1)).le] at h
    have hdiff : clock a (k + 1) - clock a k = a k := by rw [clock_succ]; ring
    have he : -p + 1 = -(p - 1) := by ring
    rw [he, hdiff, div_neg, ← neg_div, neg_sub] at h
    simpa only [div_eq_mul_inv, show -(p - 1) = 1 - p by ring] using h
  calc
    _ ≤ ∑ k ∈ Finset.range n,
        (clock a k ^ (1 - p) - clock a (k + 1) ^ (1 - p)) / (p - 1) :=
      Finset.sum_le_sum fun k _ => hstep k
    _ ≤ _ := by
      have hstart : clock a 0 = 1 := by simp [clock]
      rw [← Finset.sum_div, Finset.sum_range_sub', hstart, Real.one_rpow, ← one_div]
      exact div_le_div_of_nonneg_right
        (sub_le_self _ (Real.rpow_nonneg (hclock n).le _)) (by linarith)

/-- Abel summation: convergent normalized sums give an arbitrarily small coefficient of the
increasing normalizer, plus a constant that accounts for the initial segment. -/
private theorem eventually_abs_sum_le_of_tendsto {f x : ℕ → ℝ} (hf : Monotone f)
    (hfn : ∀ k, 0 ≤ f k) {L : ℝ}
    (h : Tendsto (fun n => ∑ k ∈ Finset.range n, x k) atTop (𝓝 L)) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, ∀ᶠ t in atTop,
      |∑ k ∈ Finset.range (t + 1), f k * x k| ≤ K + ε * f t := by
  let S (n : ℕ) := ∑ k ∈ Finset.range n, x k
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp h) (ε / 2) (by positivity))
  refine ⟨|∑ k ∈ Finset.range N, f k * x k| + (ε / 2) * f N, ?_⟩
  filter_upwards [eventually_ge_atTop N] with t ht
  have hsum := Finset.sum_Ico_by_parts f x (Nat.lt_succ_of_le ht)
  simp only [smul_eq_mul] at hsum
  change (∑ i ∈ Finset.Ico N (t + 1), f i * x i) =
    f t * S (t + 1) - f N * S N - ∑ i ∈ Finset.Ico N t, (f (i+1) - f i) * S (i+1) at hsum
  have htel : ∑ i ∈ Finset.Ico N t, (f (i+1) - f i) = f t - f N :=
    Finset.sum_Ico_sub (f := f) ht
  have hsum' : (∑ i ∈ Finset.Ico N (t+1), f i * x i) =
      f t * (S (t+1) - L) - f N * (S N - L) -
        ∑ i ∈ Finset.Ico N t, (f (i+1) - f i) * (S (i+1) - L) := by
    rw [hsum]
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, htel]
    ring
  have hlocal n (hn : N ≤ n) : |S n - L| ≤ ε / 2 :=
    le_of_lt (by simpa only [Real.dist_eq] using hN n hn)
  have hs : |∑ i ∈ Finset.Ico N t, (f (i+1) - f i) * (S (i+1) - L)| ≤
      (f t - f N) * (ε / 2) := by
    rw [← htel, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hf (Nat.le_succ i)))]
    exact mul_le_mul_of_nonneg_left (hlocal _ (by have := (Finset.mem_Ico.mp hi).1; omega))
      (sub_nonneg.mpr (hf (Nat.le_succ i)))
  have ht' : N ≤ t + 1 := by omega
  rw [← Finset.sum_range_add_sum_Ico _ ht']
  refine (abs_add_le ..).trans ?_
  have hr : |∑ k ∈ Finset.Ico N (t+1), f k * x k| ≤ (ε / 2) * f N + ε * f t := by
    rw [hsum']
    have h1 : |f t * (S (t+1) - L)| ≤ f t * (ε / 2) := by
      rw [abs_mul, abs_of_nonneg (hfn t)]
      exact mul_le_mul_of_nonneg_left (hlocal _ ht') (hfn t)
    have h2 : |f N * (S N - L)| ≤ f N * (ε / 2) := by
      rw [abs_mul, abs_of_nonneg (hfn N)]
      exact mul_le_mul_of_nonneg_left (hlocal _ le_rfl) (hfn N)
    have h3 := abs_sub (f t * (S (t+1) - L) - f N * (S N - L))
      (∑ i ∈ Finset.Ico N t, (f (i+1) - f i) * (S (i+1) - L))
    have h4 := abs_sub (f t * (S (t+1) - L)) (f N * (S N - L))
    linarith [mul_nonneg (hfn N) (show 0 ≤ ε / 2 by positivity)]
  linarith

end
section
variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m₀}
private theorem martingale_sum {X : ℕ → Ω → ℝ}
    (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) (hi : ∀ k, Integrable (X k) μ)
    (hc : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0) :
    Martingale (fun n ω => ∑ k ∈ Finset.range n, X k ω) ℱ μ := by
  have hs n : (fun ω => ∑ k ∈ Finset.range n, X k ω) = ∑ k ∈ Finset.range n, X k := by
    ext ω
    simp
  apply martingale_of_condExp_sub_eq_zero_nat
  · intro n
    change StronglyMeasurable[ℱ n] (fun ω => ∑ k ∈ Finset.range n, X k ω)
    rw [hs]
    exact Finset.stronglyMeasurable_sum _ fun k hk =>
      ((hX k).mono (ℱ.mono (Finset.mem_range.mp hk)) le_rfl).stronglyMeasurable
  · intro n
    exact integrable_finsetSum _ fun k _ => hi k
  · intro n
    convert hc n using 1
    congr 1
    ext ω
    simp [Finset.sum_range_succ]

private theorem ae_tendsto_sum_of_integral_norm_le {X : ℕ → Ω → ℝ}
    (hm : Martingale (fun n ω => ∑ k ∈ Finset.range n, X k ω) ℱ μ) {B : ℝ}
    (hB : ∀ n, (∫ ω, |∑ k ∈ Finset.range n, X k ω| ∂μ) ≤ B) :
    ∀ᵐ ω ∂μ, ∃ L : ℝ, Tendsto (fun n => ∑ k ∈ Finset.range n, X k ω) atTop (𝓝 L) := by
  have hnorm n : eLpNorm (fun ω => ∑ k ∈ Finset.range n, X k ω) 1 μ ≤ ENNReal.ofReal B := by
    rw [eLpNorm_one_eq_lintegral_eNorm (hm.integrable n).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_eNorm (hm.integrable n)]
    exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hB n)
  filter_upwards [hm.submartingale.ae_tendsto_limitProcess
    ((iSup_le hnorm).trans_lt ENNReal.ofReal_lt_top)] with ω hω
  exact ⟨_, hω⟩

private theorem ae_tendsto_sum_of_integral_sq_le {X : ℕ → Ω → ℝ}
    (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) (hi : ∀ k, MemLp (X k) 2 μ)
    (hc : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0) {B : ℝ}
    (hB : ∀ n, (∑ k ∈ Finset.range n, ∫ ω, (X k ω) ^ 2 ∂μ) ≤ B) :
    ∀ᵐ ω ∂μ, ∃ L : ℝ, Tendsto (fun n => ∑ k ∈ Finset.range n, X k ω) atTop (𝓝 L) := by
  let S n ω := ∑ k ∈ Finset.range n, X k ω
  have hm : Martingale S ℱ μ := martingale_sum hX (fun k => (hi k).integrable (by norm_num)) hc
  have hSi n : MemLp (S n) 2 μ := memLp_finsetSum (Finset.range n) (fun k _ => hi k)
  have heq (n : ℕ) : (∫ ω, (S n ω) ^ 2 ∂μ) = ∑ k ∈ Finset.range n, ∫ ω, (X k ω) ^ 2 ∂μ := by
    induction n with
    | zero => simp [S]
    | succ n ih =>
      have h := hm.integral_sub_sq_eq (Nat.le_succ n) (fun k => (hSi k).integrable_sq)
      simp only [S, Finset.sum_range_succ, add_sub_cancel_left] at h
      rw [Finset.sum_range_succ, ← ih]
      simpa [S, Finset.sum_range_succ] using (eq_sub_iff_add_eq.mp h).symm.trans (add_comm _ _)
  refine ae_tendsto_sum_of_integral_norm_le hm (B := 1 + B) fun n => ?_
  calc
    (∫ ω, |S n ω| ∂μ) ≤ ∫ ω, 1 + (S n ω) ^ 2 ∂μ := by
      apply integral_mono (hm.integrable n).abs ((integrable_const _).add ((hSi n).integrable_sq))
      intro ω
      change |S n ω| ≤ 1 + (S n ω) ^ 2
      nlinarith [sq_nonneg (|S n ω| - 1), sq_abs (S n ω)]
    _ ≤ 1 + B := by
      rw [integral_add (integrable_const _) ((hSi n).integrable_sq), heq]
      simpa using hB n

/-- Convergence of the centered increments when the integrated moments of order `p` are summable.
Clip at one: the clipped terms have summable second moments, and the discarded terms have
summable first moments. -/
private theorem ae_tendsto_sum_centered {X : ℕ → Ω → ℝ}
    (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) (hi : ∀ k, Integrable (X k) μ)
    {p B : ℝ} (hp₁ : 1 ≤ p) (hp₂ : p ≤ 2)
    (hpint : ∀ k, Integrable (fun ω => |X k ω| ^ p) μ)
    (hB : ∀ n, (∑ k ∈ Finset.range n, ∫ ω, |X k ω| ^ p ∂μ) ≤ B) :
    ∀ᵐ ω ∂μ, ∃ L : ℝ,
      Tendsto (fun n => ∑ k ∈ Finset.range n, (X k ω - μ[X k | ℱ k] ω)) atTop (𝓝 L) := by
  let Y k ω := if |X k ω| ≤ 1 then X k ω else 0
  let Z k ω := X k ω - Y k ω
  have hY k : Measurable[ℱ (k + 1)] (Y k) := by
    let : MeasurableSpace Ω := ℱ (k + 1)
    have hx : Measurable (X k) := hX k
    have habs : Measurable (fun ω => |X k ω|) := by
      simpa only [Real.norm_eq_abs] using hx.norm
    exact Measurable.ite (measurableSet_le habs measurable_const) hx measurable_const
  have hY₂ k ω : (Y k ω) ^ 2 ≤ |X k ω| ^ p := by
    by_cases h : |X k ω| ≤ 1
    · simp only [Y, ite_eq_left h, ← sq_abs (X k ω), ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg _) h (by linarith) (by simpa)
    · simp only [Y, ite_eq_right h, zero_pow (by decide : 2 ≠ 0)]
      positivity
  have hYlp k : MemLp (Y k) 2 μ := by
    have hm : AEStronglyMeasurable (Y k) μ := ((hY k).mono (ℱ.le _) le_rfl).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq hm).2 ((hpint k).mono' (hm.pow _) ?_)
    exact ae_of_all _ (fun ω => by
      change ‖Y k ω ^ 2‖ ≤ |X k ω| ^ p
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Y k ω))]
      exact hY₂ k ω)
  have hYi k := (hYlp k).integrable (show (1 : ENNReal) ≤ 2 by norm_num)
  have hZ k : Measurable[ℱ (k + 1)] (Z k) := (hX k).sub (hY k)
  have hZi k : Integrable (Z k) μ := (hi k).sub (hYi k)
  have hZ₁ k ω : |Z k ω| ≤ |X k ω| ^ p := by
    by_cases h : |X k ω| ≤ 1
    · simp only [Z, Y, ite_eq_left h, sub_self, abs_zero]
      positivity
    · simpa only [Z, Y, ite_eq_right h, sub_zero, Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le (not_le.mp h).le hp₁)
  let center (U : ℕ → Ω → ℝ) k := U k - μ[U k | ℱ k]
  have hcenter_meas {U : ℕ → Ω → ℝ} (hU : ∀ k, Measurable[ℱ (k + 1)] (U k)) k :
      Measurable[ℱ (k + 1)] (center U k) :=
    (hU k).sub (stronglyMeasurable_condExp.measurable.mono (ℱ.mono (Nat.le_succ k)) le_rfl)
  have hcenter_zero {U : ℕ → Ω → ℝ} (hU : ∀ k, Integrable (U k) μ) k :
      μ[center U k | ℱ k] =ᵐ[μ] 0 := by
    filter_upwards [condExp_sub (hU k) (integrable_condExp (f := U k) (m := ℱ k)) (ℱ k)] with ω hω
    simpa [center, condExp_of_stronglyMeasurable (ℱ.le k) stronglyMeasurable_condExp
      integrable_condExp] using hω
  have hYc k : MemLp (center Y k) 2 μ :=
    (hYlp k).sub ((hYlp k).condExp (m := ℱ k) (by norm_num))
  have hYint k : (∫ ω, (center Y k ω) ^ 2 ∂μ) ≤ ∫ ω, |X k ω| ^ p ∂μ := by
    have hv := integral_sq_sub_eq_integral_sq_sub_condExp_add (ℱ.le k)
      (g := (0 : Ω → ℝ)) (hYlp k) MemLp.zero stronglyMeasurable_zero
    simp only [Pi.zero_apply, sub_zero] at hv
    have hnon : 0 ≤ (∫ ω, (μ[Y k | ℱ k] ω) ^ 2 ∂μ) := integral_nonneg fun _ => sq_nonneg _
    exact (show (∫ ω, (center Y k ω) ^ 2 ∂μ) ≤ ∫ ω, (Y k ω) ^ 2 ∂μ by
      simp only [center, Pi.sub_apply]; linarith).trans
      (integral_mono (hYlp k).integrable_sq (hpint k) (hY₂ k))
  have hYconv := ae_tendsto_sum_of_integral_sq_le (hcenter_meas hY) hYc (hcenter_zero hYi)
    (fun n => (Finset.sum_le_sum fun k _ => hYint k).trans (hB n))
  have hZci k : Integrable (center Z k) μ := (hZi k).sub integrable_condExp
  have hZint k : (∫ ω, |center Z k ω| ∂μ) ≤ 2 * ∫ ω, |X k ω| ^ p ∂μ := by
    have hc := integral_abs_condExp_le (μ := μ) (m := ℱ k) (Z k)
    have hz : (∫ ω, |Z k ω| ∂μ) ≤ ∫ ω, |X k ω| ^ p ∂μ :=
      integral_mono (hZi k).abs (hpint k) (hZ₁ k)
    calc
      _ ≤ ∫ ω, |Z k ω| + |μ[Z k | ℱ k] ω| ∂μ :=
        integral_mono (hZci k).abs ((hZi k).abs.add integrable_condExp.abs) (fun ω => abs_sub ..)
      _ ≤ _ := by rw [integral_add (hZi k).abs integrable_condExp.abs]; linarith
  have hZbd n : (∫ ω, |∑ k ∈ Finset.range n, center Z k ω| ∂μ) ≤ 2 * B := by
    calc
      _ ≤ ∫ ω, ∑ k ∈ Finset.range n, |center Z k ω| ∂μ :=
        integral_mono ((integrable_finsetSum _ fun k _ => hZci k).abs)
          (integrable_finsetSum _ fun k _ => (hZci k).abs) (fun ω => Finset.abs_sum_le_sum_abs ..)
      _ ≤ _ := by
        rw [integral_finsetSum _ (fun k _ => (hZci k).abs)]
        refine (Finset.sum_le_sum fun k _ => hZint k).trans ?_
        rw [← Finset.mul_sum]
        gcongr
        exact hB n
  have hZconv := ae_tendsto_sum_of_integral_norm_le
    (martingale_sum (hcenter_meas hZ) hZci (hcenter_zero hZi)) hZbd
  have hsplit : ∀ᵐ ω ∂μ, ∀ k, center X k ω = center Y k ω + center Z k ω := by
    apply ae_all_iff.mpr
    intro k
    have heq : X k = Y k + Z k := by ext ω; simp [Z]
    filter_upwards [(condExp_congr_ae (ae_of_all μ (congrFun heq))).trans
      (condExp_add (hYi k) (hZi k) (ℱ k))] with ω hω
    change μ[X k | ℱ k] ω = _ at hω
    simp only [center, Pi.sub_apply, hω, Pi.add_apply, Z]
    ring
  filter_upwards [hYconv, hZconv, hsplit] with ω ⟨LY, hLY⟩ ⟨LZ, hLZ⟩ hs
  refine ⟨LY + LZ, ?_⟩
  change Tendsto (fun n => ∑ k ∈ Finset.range n, center X k ω) atTop (𝓝 (LY + LZ))
  simpa only [← Finset.sum_add_distrib, ← hs] using hLY.add hLZ

end

set_option maxHeartbeats 600000 in
-- The budget proof elaborates several integrability and conditional-expectation arguments.
/-- Localize at a deterministic bound on the conditional moments. The cutoff is at time `k`,
so predictability and conditional centering are preserved. For almost every path some integer
cutoff is inactive at every time. -/
private theorem ae_tendsto_normalized_sum {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀} {a v U : ℕ → Ω → ℝ}
    (ha : Adapted ℱ a) (hv : Adapted ℱ v) (hU : ∀ k, Measurable[ℱ (k + 1)] (U k))
    {p : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2) (hav : ∀ k ω, |v k ω| ^ p ≤ a k ω)
    (hiU : ∀ k, Integrable (U k) μ) (hi : ∀ k, Integrable (fun ω => |U k ω| ^ p) μ)
    (hm : ∃ C : Ω → ℝ, ∀ k, μ[fun ω => |U k ω| ^ p | ℱ k] ≤ᵐ[μ] C) :
    ∀ᵐ ω ∂μ, ∃ L : ℝ, Tendsto (fun n => ∑ k ∈ Finset.range n,
      v k ω * (U k ω - μ[U k | ℱ k] ω) / clock (a · ω) (k+1)) atTop (𝓝 L) := by
  let T k ω := clock (a · ω) (k+1)
  let H k ω := |U k ω| ^ p
  have ha₀ k ω : 0 ≤ a k ω := (Real.rpow_nonneg (abs_nonneg _) _).trans (hav k ω)
  have hT₁ k ω : 1 ≤ T k ω := clock_one_le (ha₀ · ω) _
  have hT₀ k ω : 0 < T k ω := zero_lt_one.trans_le (hT₁ k ω)
  have haT k ω : a k ω ≤ T k ω := by
    change a k ω ≤ clock (a · ω) (k+1)
    rw [clock_succ]
    have := clock_one_le (ha₀ · ω) k
    linarith
  have hT k : Measurable[ℱ k] (T k) := by
    let : MeasurableSpace Ω := ℱ k
    apply Measurable.const_add
    exact Finset.measurable_sum _ fun j hj =>
      (ha j).mono (ℱ.mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))) le_rfl
  let D (M : ℕ) k ω := if μ[H k | ℱ k] ω ≤ M then v k ω / T k ω else 0
  have hD M k : Measurable[ℱ k] (D M k) := by
    let : MeasurableSpace Ω := ℱ k
    exact Measurable.ite (measurableSet_le stronglyMeasurable_condExp.measurable measurable_const)
      ((hv k).div (hT k)) measurable_const
  have hDp M k ω : |D M k ω| ^ p ≤ a k ω / T k ω ^ p := by
    by_cases h : μ[H k | ℱ k] ω ≤ M
    · simp only [D, ite_eq_left h, abs_div, abs_of_pos (hT₀ k ω),
        Real.div_rpow (abs_nonneg _) (hT₀ k ω).le]
      exact div_le_div_of_nonneg_right (hav k ω) (Real.rpow_nonneg (hT₀ k ω).le _)
    · simp only [D, ite_eq_right h, abs_zero, Real.zero_rpow (by linarith : p ≠ 0)]
      exact div_nonneg (ha₀ k ω) (Real.rpow_nonneg (hT₀ k ω).le _)
  have ha_ratio k ω : a k ω / T k ω ^ p ≤ 1 := by
    rw [div_le_iff₀ (Real.rpow_pos_of_pos (hT₀ k ω) _), one_mul]
    refine (haT k ω).trans ?_
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (hT₁ k ω) hp.le
  have hDb M k ω : ‖D M k ω‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    by_contra! h
    have hh := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1) h (show 0 < p by linarith)
    rw [Real.one_rpow] at hh
    exact hh.not_ge ((hDp M k ω).trans (ha_ratio k ω))
  have hDp_meas M k : Measurable[ℱ k] (fun ω => |D M k ω| ^ p) := by
    let : MeasurableSpace Ω := ℱ k
    have hd : Measurable (D M k) := hD M k
    exact (Real.continuous_rpow_const (show 0 ≤ p by linarith)).measurable.comp
      (by simpa only [Real.norm_eq_abs] using hd.norm)
  let X (M : ℕ) k ω := D M k ω * U k ω
  have hX M k : Measurable[ℱ (k + 1)] (X M k) :=
    ((hD M k).mono (ℱ.mono (Nat.le_succ k)) le_rfl).mul (hU k)
  have hXi M k : Integrable (X M k) μ :=
    (hiU k).bdd_mul ((hD M k).mono (ℱ.le k) le_rfl).aestronglyMeasurable (ae_of_all μ (hDb M k))
  have hpow_eq M k : (fun ω => |X M k ω| ^ p) = fun ω => |D M k ω| ^ p * H k ω := by
    funext ω
    simp only [X, H, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  have hXpi M k : Integrable (fun ω => |X M k ω| ^ p) μ := by
    rw [hpow_eq]
    refine (hi k).bdd_mul (c := 1) ((hDp_meas M k).mono (ℱ.le k) le_rfl).aestronglyMeasurable ?_
    exact ae_of_all _ fun ω => by
      change ‖|D M k ω| ^ p‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact (hDp M k ω).trans (ha_ratio k ω)
  have hbudget M n : (∑ k ∈ Finset.range n, ∫ ω, |X M k ω| ^ p ∂μ) ≤ (M : ℝ) * (p-1)⁻¹ := by
    have hint k : Integrable (fun ω => |D M k ω| ^ p * μ[H k | ℱ k] ω) μ := by
      refine (integrable_condExp (f := H k) (m := ℱ k)).bdd_mul (c := 1)
        ((hDp_meas M k).mono (ℱ.le k) le_rfl).aestronglyMeasurable ?_
      exact ae_of_all _ fun ω => by
        change ‖|D M k ω| ^ p‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact (hDp M k ω).trans (ha_ratio k ω)
    have hpull k : (∫ ω, |X M k ω| ^ p ∂μ) = ∫ ω, |D M k ω| ^ p * μ[H k | ℱ k] ω ∂μ := by
      have hi' := hXpi M k
      rw [hpow_eq] at hi'
      rw [← integral_condExp (ℱ.le k), hpow_eq]
      exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left
        (hDp_meas M k).stronglyMeasurable hi' (hi k))
    simp only [hpull]
    rw [← integral_finsetSum _ (fun k _ => hint k)]
    have hc : (∫ _ : Ω, (M : ℝ) * (p-1)⁻¹ ∂μ) = (M : ℝ) * (p-1)⁻¹ := by simp
    rw [← hc]
    refine integral_mono (integrable_finsetSum _ fun k _ => hint k) (integrable_const _) fun ω => ?_
    change (∑ k ∈ Finset.range n, |D M k ω| ^ p * μ[H k | ℱ k] ω) ≤ _
    calc
      _ ≤ ∑ k ∈ Finset.range n, (M : ℝ) * (a k ω / T k ω ^ p) := by
        refine Finset.sum_le_sum fun k _ => ?_
        by_cases h : μ[H k | ℱ k] ω ≤ M
        · calc
            _ ≤ |D M k ω| ^ p * (M : ℝ) :=
              mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (abs_nonneg _) _)
            _ ≤ _ := by
              rw [mul_comm (M : ℝ)]
              exact mul_le_mul_of_nonneg_right (hDp M k ω) (Nat.cast_nonneg M)
        · simp only [D, ite_eq_right h, abs_zero, Real.zero_rpow (by linarith : p ≠ 0), zero_mul]
          exact mul_nonneg (by positivity) (div_nonneg (ha₀ k ω) (Real.rpow_nonneg (hT₀ k ω).le _))
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (clock_moment_budget (ha₀ · ω) hp n) (by positivity)
  have hconv := ae_all_iff.mpr fun M : ℕ =>
    ae_tendsto_sum_centered (hX M) (hXi M) hp.le hp₂ (hXpi M) (hbudget M)
  have hpull := ae_all_iff.mpr fun M : ℕ => ae_all_iff.mpr fun k =>
    condExp_mul_of_stronglyMeasurable_left (m := ℱ k) (hD M k).stronglyMeasurable
      (hXi M k) (hiU k)
  obtain ⟨C, hC⟩ := hm
  filter_upwards [hconv, hpull, ae_all_iff.mpr hC] with ω hconv hpull hC
  obtain ⟨M, hM⟩ := exists_nat_ge (C ω)
  obtain ⟨L, hL⟩ := hconv M
  refine ⟨L, hL.congr fun n => ?_⟩
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show μ[X M k | ℱ k] ω = D M k ω * μ[U k | ℱ k] ω from hpull M k]
  have hcut : μ[H k | ℱ k] ω ≤ M := (hC k).trans hM
  simp only [X, D, ite_eq_left hcut, T]
  ring

private theorem measurable_dot {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {f g : Ω → Fin d → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun ω => f ω ⬝ᵥ g ω) :=
  (continuous_fst.dotProduct continuous_snd).measurable.comp (hf.prodMk hg)

private theorem measurable_mulVec {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {P : Ω → Matrix (Fin d) (Fin d) ℝ} {f : Ω → Fin d → ℝ}
    (hP : Measurable P) (hf : Measurable f) : Measurable (fun ω => P ω *ᵥ f ω) :=
  (continuous_fst.matrix_mulVec continuous_snd).measurable.comp (hP.prodMk hf)

private theorem measurable_rlsStep {d : ℕ} :
    Measurable (fun x : (Fin d → ℝ) × ℝ × ((Fin d → ℝ) × Matrix (Fin d) (Fin d) ℝ) =>
      rlsStep x.1 x.2.1 x.2.2) := by
  let T := (Fin d → ℝ) × ℝ × ((Fin d → ℝ) × Matrix (Fin d) (Fin d) ℝ)
  have hφ : Continuous (fun x : T => x.1) := continuous_fst
  have hy : Continuous (fun x : T => x.2.1) := continuous_fst.comp continuous_snd
  have hθ : Continuous (fun x : T => x.2.2.1) :=
    continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hP : Continuous (fun x : T => x.2.2.2) :=
    continuous_snd.comp (continuous_snd.comp continuous_snd)
  have hx := hP.matrix_mulVec hφ
  have hq := (hφ.dotProduct hx).measurable.const_add 1
  have he := (hy.sub (hφ.dotProduct hθ)).measurable
  have hA := ((hP.matrix_mul (hφ.matrix_vecMulVec hφ)).matrix_mul hP).measurable
  have hQ := hq.inv.smul hA
  have hsub : Measurable (fun x : T => x.2.2.2 - (1 + x.1 ⬝ᵥ (x.2.2.2 *ᵥ x.1))⁻¹ •
      (x.2.2.2 * vecMulVec x.1 x.1 * x.2.2.2)) := by
    apply Measurable.of_eval_matrix
    intro i j
    exact (hP.measurable.eval_matrix (i := i) (j := j)).sub hQ.eval_matrix
  exact (hθ.measurable.add ((he.div hq).smul hx.measurable)).prodMk hsub

private theorem abs_rpow_le_one_add {s β : ℝ} (hs : 0 ≤ s) (hsβ : s ≤ β) (x : ℝ) :
    |x| ^ s ≤ 1 + |x| ^ β := by
  by_cases h : |x| ≤ 1
  · exact (Real.rpow_le_one (abs_nonneg _) h hs).trans (le_add_of_nonneg_right (by positivity))
  · exact (Real.rpow_le_rpow_of_exponent_le (not_le.mp h).le hsβ).trans
      (le_add_of_nonneg_left zero_le_one)

set_option maxHeartbeats 1200000 in
-- The proof combines the stochastic estimates with the matrix energy identity.
/-- **Joint stochastic energy and prediction-error bound for recursive least squares**

On a probability space with filtration $(\mathcal F_k)$, let the regressor $\varphi_k$ and the
noise $w_k$ be $\mathcal F_k$-measurable, and let $y_{k+1} = \varphi_k^\top \theta + w_{k+1}$
for fixed $\theta \in \mathbb R^d$. Assume $\mathbb E[w_{k+1} \mid \mathcal F_k] = 0$ and, for
some $\beta > 2$, assume $\mathbb E|w_{k+1}|^\beta < \infty$ for each $k$ and
$\sup_k \mathbb E[|w_{k+1}|^\beta \mid \mathcal F_k] < \infty$ almost surely.

Start recursive least squares at $(\theta_0,P_0)$ with $P_0$ positive definite, and write
$(\theta_k,P_k)$ for the state after $k$ updates. Set $e_k = \theta_k - \theta$,
$q_k = \varphi_k^\top P_k \varphi_k$, and $V_k = e_k^\top P_k^{-1} e_k$, where
$P_k^{-1} = P_0^{-1} + \sum_{j<k} \varphi_j \varphi_j^\top$ is the information matrix.
Almost surely there are finite nonnegative constants $C_0,C_1$ (depending on the path) such that
for all sufficiently large $t$,

$$
V_{t+1} + \tfrac12 \sum_{k=0}^t \frac{(\varphi_k^\top e_k)^2}{1+q_k}
\le C_0 + C_1 \log\!\left(1+\sum_{k=0}^t \|\varphi_k\|_2^2\right).
$$

This is the single-sensor case of Theorem 3.1 of Xie, Zhang and Guo, *Convergence of a
Distributed Least Squares*,
[doi:10.1109/TAC.2020.3047989](https://doi.org/10.1109/TAC.2020.3047989), which bounds the
weighted prediction-error sum and the information-weighted error each by $O(\log r_t)$, where
$r_t = \lambda_{\max}(P_0^{-1}) + \sum_{k=0}^t \|\varphi_k\|_2^2$, combined as in their
Lemma 4.4, whose extra term vanishes for one sensor. Unlike the source, this statement also
assumes $\mathbb E|w_{k+1}|^\beta < \infty$, combines the two parts with coefficient $\tfrac12$
on the sum, and writes $O(\log r_t)$ as $C_0 + C_1 \log(1 + \sum_{k=0}^t \|\varphi_k\|_2^2)$.
It requires neither bounded leverage nor divergence of the regressor energy. -/
theorem rls_energy_add_half_sum_le_log {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀) {d : ℕ}
    (θ : Fin d → ℝ) (φ : ℕ → Ω → Fin d → ℝ) (w y : ℕ → Ω → ℝ)
    (hφ : Adapted ℱ φ) (hw : Adapted ℱ w) {β : ℝ} (hβ : 2 < β)
    (hint : ∀ k, Integrable (fun ω => |w (k + 1) ω| ^ β) μ)
    (hmart : ∀ k, μ[w (k + 1) | ℱ k] =ᵐ[μ] 0)
    (hmom : ∃ C : Ω → ℝ, ∀ k, μ[fun ω => |w (k + 1) ω| ^ β | ℱ k] ≤ᵐ[μ] C)
    (hy : ∀ k ω, y (k + 1) ω = φ k ω ⬝ᵥ θ + w (k + 1) ω)
    (θ₀ : Fin d → ℝ) {P₀ : Matrix (Fin d) (Fin d) ℝ} (hP₀ : P₀.PosDef) :
    ∀ᵐ ω ∂μ,
      let state k := rls (φ · ω) (y · ω) θ₀ P₀ k
      let e k := (state k).1 - θ
      ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ∀ᶠ t in atTop,
        e (t + 1) ⬝ᵥ (rlsInformation P₀ (φ · ω) (t + 1) *ᵥ e (t + 1)) +
            (1 / 2) * ∑ k ∈ Finset.range (t + 1),
              (φ k ω ⬝ᵥ e k) ^ 2 / (1 + φ k ω ⬝ᵥ ((state k).2 *ᵥ φ k ω)) ≤
          C₀ + C₁ * Real.log (1 + ∑ k ∈ Finset.range (t + 1), φ k ω ⬝ᵥ φ k ω) := by
  let state k ω := rls (φ · ω) (y · ω) θ₀ P₀ k
  let err k ω := (state k ω).1 - θ
  let q k ω := φ k ω ⬝ᵥ ((state k ω).2 *ᵥ φ k ω)
  let u k ω := φ k ω ⬝ᵥ err k ω
  let a k ω := u k ω ^ 2 / (1 + q k ω)
  let c k ω := u k ω / (1 + q k ω)
  let g k ω := q k ω / (1 + q k ω)
  let W k := w (k+1)
  let Z k ω := W k ω ^ 2
  let R k ω := rlsInformation P₀ (φ · ω) k
  let V k ω := err k ω ⬝ᵥ (R k ω *ᵥ err k ω)
  have hR k ω : (R k ω).PosDef := posDef_rlsInformation hP₀ _ _
  have hP k ω : (state k ω).2 = (R k ω)⁻¹ := rls_snd_eq_inv hP₀ _ _ _ _
  have hq₀ k ω : 0 ≤ q k ω := by
    change 0 ≤ φ k ω ⬝ᵥ ((state k ω).2 *ᵥ φ k ω)
    rw [hP]
    simpa only [star_trivial] using (hR k ω).inv.posSemidef.dotProduct_mulVec_nonneg (φ k ω)
  have hden k ω : 0 < 1 + q k ω := by have := hq₀ k ω; positivity
  have ha₀ k ω : 0 ≤ a k ω := div_nonneg (sq_nonneg _) (hden k ω).le
  have hg₀ k ω : 0 ≤ g k ω := div_nonneg (hq₀ k ω) (hden k ω).le
  have hg₁ k ω : g k ω ≤ 1 := (div_le_one (hden k ω)).2 (by linarith)
  have hc₂ k ω : |c k ω| ^ (2 : ℝ) ≤ a k ω := by
    rw [Real.rpow_two, sq_abs]
    change (u k ω / (1 + q k ω)) ^ 2 ≤ u k ω ^ 2 / (1 + q k ω)
    rw [div_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (hden k ω)
      (by nlinarith [hq₀ k ω, sq_nonneg (q k ω)])
  have hstate : Adapted ℱ state := by
    intro k
    induction k with
    | zero => exact measurable_const
    | succ k ih =>
      let : MeasurableSpace Ω := ℱ (k+1)
      have hp : Measurable (φ k) := (hφ k).mono (ℱ.mono (Nat.le_succ k)) le_rfl
      have hs : Measurable (state k) := ih.mono (ℱ.mono (Nat.le_succ k)) le_rfl
      have ho : Measurable (y (k+1)) := by
        rw [show y (k+1) = _ from funext (hy k)]
        exact (measurable_dot hp measurable_const).add (hw (k+1))
      exact measurable_rlsStep.comp (hp.prodMk (ho.prodMk hs))
  have hq : Adapted ℱ q := by
    intro k
    let : MeasurableSpace Ω := ℱ k
    have hp : Measurable (φ k) := hφ k
    have hs : Measurable (state k) := hstate k
    exact measurable_dot hp (measurable_mulVec hs.snd hp)
  have hu : Adapted ℱ u := by
    intro k
    let : MeasurableSpace Ω := ℱ k
    have hp : Measurable (φ k) := hφ k
    have hs : Measurable (state k) := hstate k
    exact measurable_dot hp (hs.fst.sub measurable_const)
  have ha : Adapted ℱ a := fun k => (hu k).pow_const 2 |>.div ((hq k).const_add 1)
  have hc : Adapted ℱ c := fun k => (hu k).div ((hq k).const_add 1)
  have hg : Adapted ℱ g := fun k => (hq k).div ((hq k).const_add 1)
  have hZ k : Measurable[ℱ (k+1)] (Z k) := (hw (k+1)).pow_const 2
  have hw_dom k : Integrable (fun ω => 1 + |W k ω| ^ β) μ := (integrable_const _).add (hint k)
  have hlow_int {s : ℝ} (hs : 0 ≤ s) (hsβ : s ≤ β) k : Integrable (fun ω => |W k ω| ^ s) μ := by
    have hwk : Measurable (W k) := (hw (k+1)).mono (ℱ.le _) le_rfl
    apply (hw_dom k).mono'
      ((Real.continuous_rpow_const hs).measurable.comp
        (by simpa only [Real.norm_eq_abs] using hwk.norm)).aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      change ‖|W k ω| ^ s‖ ≤ 1 + |W k ω| ^ β
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact abs_rpow_le_one_add hs hsβ _
  have hWi k : Integrable (W k) μ := by
    have hm : Measurable (W k) := (hw (k+1)).mono (ℱ.le _) le_rfl
    apply (integrable_norm_iff hm.aestronglyMeasurable).mp
    simpa [Real.norm_eq_abs] using hlow_int (s := 1) (by norm_num) (by linarith) k
  have hZi k : Integrable (Z k) μ := by
    simpa only [Z, Real.rpow_two, sq_abs] using hlow_int (by norm_num : 0 ≤ (2 : ℝ)) hβ.le k
  obtain ⟨C, hC⟩ := hmom
  have hlow_bound {s : ℝ} (hs : 0 ≤ s) (hsβ : s ≤ β) k :
      μ[fun ω => |W k ω| ^ s | ℱ k] ≤ᵐ[μ] fun ω => 1 + C ω := by
    filter_upwards [condExp_mono (hlow_int hs hsβ k) (hw_dom k)
        (ae_of_all _ fun ω => abs_rpow_le_one_add hs hsβ (W k ω)),
      condExp_add (integrable_const (1 : ℝ)) (hint k) (ℱ k), hC k] with ω h1 h2 h3
    rw [condExp_const (ℱ.le k), Pi.add_apply] at h2
    exact h1.trans (h2.trans_le (add_le_add_right h3 1))
  let p : ℝ := min (β / 2) 2
  have hp : 1 < p := lt_min (by linarith) (by norm_num)
  have hp₂ : p ≤ 2 := min_le_right _ _
  have hpβ : 2 * p ≤ β := by have := min_le_left (β / 2) (2 : ℝ); linarith
  have hpow k : (fun ω => |Z k ω| ^ p) = fun ω => |W k ω| ^ (2 * p) := by
    funext ω
    change |W k ω ^ 2| ^ p = |W k ω| ^ (2 * p)
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs, ← Real.rpow_two,
      ← Real.rpow_mul (abs_nonneg _)]
  have hcross := ae_tendsto_normalized_sum ha hc (fun k => hw (k+1)) (by norm_num : 1 < (2 : ℝ))
    le_rfl hc₂ hWi (hlow_int (by norm_num) hβ.le)
    ⟨fun ω => 1 + C ω, hlow_bound (by norm_num) hβ.le⟩
  have hnoise := ae_tendsto_normalized_sum hg hg hZ hp hp₂
    (fun k ω => by
      simpa only [abs_of_nonneg (hg₀ k ω), Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge' (hg₀ k ω) (hg₁ k ω) zero_le_one hp.le))
    hZi (fun k => by rw [hpow]; exact hlow_int (by positivity) hpβ k)
    ⟨fun ω => 1 + C ω, fun k => by rw [hpow]; exact hlow_bound (by positivity) hpβ k⟩
  have hz_bound : ∀ᵐ ω ∂μ, ∀ k, μ[Z k | ℱ k] ω ≤ 1 + C ω := by
    apply ae_all_iff.mpr
    intro k
    change μ[Z k | ℱ k] ≤ᵐ[μ] (fun ω => 1 + C ω)
    simpa only [Z, Real.rpow_two, sq_abs] using hlow_bound (by norm_num) hβ.le k
  obtain ⟨D, hD⟩ := log_det_rlsInformation_le hP₀
  filter_upwards [hcross, hnoise, ae_all_iff.mpr hmart, hz_bound] with ω
    ⟨Lc, hLc⟩ ⟨Lg, hLg⟩ hzero hZbound
  have hLc' : Tendsto (fun n => ∑ k ∈ Finset.range n,
      c k ω * W k ω / clock (a · ω) (k+1)) atTop (𝓝 Lc) := by
    simpa only [W, hzero, Pi.zero_apply, sub_zero] using hLc
  obtain ⟨Kc, hKc⟩ := eventually_abs_sum_le_of_tendsto
    (fun i j hij => clock_mono (ha₀ · ω) (Nat.succ_le_succ hij))
    (fun k => zero_le_one.trans (clock_one_le (ha₀ · ω) _)) hLc' (by norm_num : 0 < (1/4 : ℝ))
  obtain ⟨Kg, hKg⟩ := eventually_abs_sum_le_of_tendsto
    (fun i j hij => clock_mono (hg₀ · ω) (Nat.succ_le_succ hij))
    (fun k => zero_le_one.trans (clock_one_le (hg₀ · ω) _)) hLg (by norm_num : 0 < (1 : ℝ))
  let L t := Real.log (1 + ∑ k ∈ Finset.range (t + 1), φ k ω ⬝ᵥ φ k ω)
  let G t := ∑ k ∈ Finset.range (t + 1), g k ω
  let M := max 0 (2 + C ω)
  let K := V 0 ω + 2 * Kc + 1/2 + Kg + 1
  let D' := D - Real.log P₀⁻¹.det
  have hM : 0 ≤ M := le_max_left _ _
  refine ⟨max 0 (K + M * D'), M * d, le_max_left _ _, mul_nonneg hM (Nat.cast_nonneg d), ?_⟩
  filter_upwards [hKc, hKg] with t hct hgt
  change V (t + 1) ω + (1 / 2) * (∑ k ∈ Finset.range (t + 1), a k ω) ≤
    max 0 (K + M * D') + M * d * L t
  have to_cancel (x T : ℝ) (h : 0 < T) : T * (x / T) = x := by field_simp
  have cancel_c k : clock (a · ω) (k+1) * (c k ω * W k ω / clock (a · ω) (k+1)) =
      c k ω * W k ω := to_cancel _ _ (zero_lt_one.trans_le (clock_one_le (ha₀ · ω) _))
  have cancel_g k : clock (g · ω) (k+1) *
      (g k ω * (Z k ω - μ[Z k | ℱ k] ω) / clock (g · ω) (k+1)) =
        g k ω * (Z k ω - μ[Z k | ℱ k] ω) :=
    to_cancel _ _ (zero_lt_one.trans_le (clock_one_le (hg₀ · ω) _))
  simp only [cancel_c] at hct
  simp only [cancel_g] at hgt
  simp only [clock] at hct
  simp only [clock, one_mul] at hgt
  have hnoise' : (∑ k ∈ Finset.range (t+1), g k ω * Z k ω) ≤ Kg + 1 + M * G t := by
    have hd := (le_abs_self _).trans hgt
    simp only [mul_sub, Finset.sum_sub_distrib] at hd
    have hE : (∑ k ∈ Finset.range (t+1), g k ω * μ[Z k | ℱ k] ω) ≤ (1 + C ω) * G t := by
      dsimp only [G]
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ => by
        rw [mul_comm (1 + C ω)]
        exact mul_le_mul_of_nonneg_left (hZbound k) (hg₀ k ω)
    have hMG : (2 + C ω) * G t ≤ M * G t :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Finset.sum_nonneg fun k _ => hg₀ k ω)
    dsimp only [G] at hMG hE ⊢
    linarith
  have hstep k : V (k+1) ω - V k ω = -a k ω + 2 * c k ω * W k ω + g k ω * Z k ω := by
    have hRP : R k ω * (state k ω).2 = 1 := by
      rw [hP, Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp (hR k ω).isUnit)]
    have herr : err (k+1) ω = err k ω + ((W k ω - u k ω) / (1+q k ω)) •
        ((state k ω).2 *ᵥ φ k ω) := by
      simp only [err, state, rls, rlsStep, hy, W, u, q, dotProduct_sub]
      have ht' : φ k ω ⬝ᵥ θ + w (k+1) ω - φ k ω ⬝ᵥ (rls (φ · ω) (y · ω) θ₀ P₀ k).1 =
        w (k+1) ω - (φ k ω ⬝ᵥ (rls (φ · ω) (y · ω) θ₀ P₀ k).1 - φ k ω ⬝ᵥ θ) := by ring
      rw [ht']
      abel
    have he := energy_step (hR k ω) hRP (φ k ω) (err k ω) (W k ω)
    change _ ⬝ᵥ _ = V k ω - a k ω + 2 * c k ω * W k ω + g k ω * Z k ω at he
    rw [← herr, ← rlsInformation_succ] at he
    change V (k+1) ω = _ at he
    linarith
  have hsum := Finset.sum_congr (s₁ := Finset.range (t+1)) rfl (fun k _ => hstep k)
  rw [Finset.sum_range_sub (fun k => V k ω), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib] at hsum
  have hsumc : (∑ k ∈ Finset.range (t+1), 2 * c k ω * W k ω) =
      2 * ∑ k ∈ Finset.range (t+1), c k ω * W k ω := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => mul_assoc ..
  rw [hsumc] at hsum
  have hG : G t ≤ D' + d * L t := by
    have hgd := sum_rls_gain_le_log_det hP₀ (φ · ω) (y · ω) θ₀ (t+1)
    have hd := hD (φ · ω) (t+1)
    change G t ≤ Real.log (R (t+1) ω).det - Real.log P₀⁻¹.det at hgd
    change Real.log (R (t+1) ω).det ≤ D + d * L t at hd
    dsimp only [D']
    linarith
  -- Keep the half of the weighted prediction term left after absorbing the cross term.
  have hjoint : V (t + 1) ω + (1 / 2) * (∑ k ∈ Finset.range (t + 1), a k ω) ≤ K + M * G t := by
    have hc' := (le_abs_self _).trans hct
    dsimp only [K]
    linarith only [hc', hsum, hnoise']
  calc
    _ ≤ K + M * G t := hjoint
    _ ≤ K + M * (D' + d * L t) := add_le_add_right (mul_le_mul_of_nonneg_left hG hM) K
    _ = (K + M * D') + M * d * L t := by ring
    _ ≤ _ := add_le_add_left (le_max_right 0 (K + M * D')) (M * d * L t)

end MathlibExt.Analysis.Control.RecursiveLeastSquares
