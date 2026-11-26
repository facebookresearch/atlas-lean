/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import MathlibExt.Analysis.SpecificLimits.PowerSeriesCoeffEqOfAgreeOnReciprocals

/-!
# Rényi–Vincze characterization of the exponential

An entire series with nonnegative coefficients satisfying either Rényi–Vincze integral identity
is a positive multiple of the exponential. The theorem `conjecture_refuted` proves this by
showing that the successive coefficient ratios satisfy $(n+1)a_{n+1}/a_n = 1$.
-/

/-! Source record `AMR-022-2032__2302032`. -/

/-!
# Hayman Research Problems in Function Theory, Problem 2.32 — Clause list

Stable identifiers: AMR-022-2032; Hayman - Research Problems in Function Theory (2018);
Problem 2.32; https://arxiv.org/abs/1809.07200; source labels 2.6 and 2.6'.

Every clause below appears in the formal proposition `conjecture`:

* C1: `f : Complex → Complex` (function domain).
* C2: `a : Nat → Real` (coefficient sequence domain).
* C3: `∀ n : Nat, 0 ≤ a n` (nonnegativity for n ≥ 0).
* C4: `∀ N : Nat, ∃ n : Nat, N ≤ n ∧ a n ≠ 0` (transcendental: infinitely many
  nonzero coefficients).
* C5: `∀ z : Complex, HasSum (fun n => ↑(a n) * z ^ n) (f z)` (global power-series representation).
* C6: `DifferentiableOn Complex f Set.univ` (entire).
* C7: `f` is no positive scalar multiple of `Complex.exp` (other than a
  rescaling of e^z).
* C8: integration domain `Set.Ici (0 : Real)` (closed at 0, i.e. [0,∞)).
* C9 (2.6): `∀ n : Nat, integral of ↑(a n * x ^ n) / f ↑x over Ici 0 equals 1`.
* C10 (2.6)': `∀ ρ : Real, 0 < ρ → ρ < 1 → integral of f ↑(ρ * x) / f ↑x over Ici 0
  equals 1 / (1 - ↑ρ)` with `ρ ∈ (0,1)` open.
* C11: `∃ f a, C3 ∧ C4 ∧ C5 ∧ C6 ∧ C7 ∧ (C9 ∨ C10)` with one shared `a`.

Mathlib grounding: `HasSum`, `DifferentiableOn`, `Complex.exp`, `Set.Ici`,
`MeasureTheory.volume` with set-restricted integral; `/` is Mathlib total field division.
-/

@[expose] public section

namespace MathlibExt.Analysis.HaymanProblem232Wanted

open scoped MeasureTheory

/-- **Hayman Problem 2.32: a non-exponential solution of the Rényi–Vincze conditions.** There
exist a function $f : \mathbb{C} \to \mathbb{C}$ and real numbers $a_0, a_1, a_2, \dots$ such that
$f$ is not the function $z \mapsto c\,e^z$ for any real $c > 0$; $a_n \ge 0$ for every $n$;
$a_n \ne 0$ for infinitely many $n$; for every $z \in \mathbb{C}$ the series
$\sum_{n \ge 0} a_n z^n$ has sum $f(z)$; $f$ is entire; and either
$\int_0^\infty a_n x^n / f(x)\,dx = 1$ for every $n \ge 0$ (condition (2.6)), or
$\int_0^\infty f(\rho x) / f(x)\,dx = 1/(1-\rho)$ for every real $\rho$ with $0 < \rho < 1$
(condition (2.6)').

Source: AMR-022-2032, Hayman - Research Problems in Function Theory (2018), Problem 2.32
(https://arxiv.org/abs/1809.07200, source labels 2.6 and 2.6', A. Renyi, St. Vincze). -/
def conjecture : Prop :=
  ∃ (f : Complex → Complex) (a : Nat → Real),
    (∀ c : ℝ, 0 < c → f ≠ fun z => (↑c : ℂ) * Complex.exp z) ∧
    (∀ n : Nat, 0 ≤ a n) ∧
    (∀ N : Nat, ∃ n : Nat, N ≤ n ∧ a n ≠ 0) ∧
    (∀ z : Complex, HasSum (fun n => (↑(a n) : Complex) * z ^ n) (f z)) ∧
    DifferentiableOn Complex f (Set.univ : Set Complex) ∧
    ((∀ n : Nat,
        ∫ x in Set.Ici (0 : Real), (↑(a n * x ^ n) : Complex) / f (↑x : Complex)
          ∂MeasureTheory.volume = (1 : Complex)) ∨
      (∀ ρ : Real, 0 < ρ → ρ < 1 →
        ∫ x in Set.Ici (0 : Real), f (↑(ρ * x) : Complex) / f (↑x : Complex)
          ∂MeasureTheory.volume = (1 : Complex) / (1 - (↑ρ : Complex))))

open Set Filter MeasureTheory
open scoped Topology
open SpecificLimits.PowerSeriesCoeffEqOfAgreeOnReciprocalsWanted

noncomputable section

private abbrev μ : Measure ℝ := volume.restrict (Ioi 0)

private structure SeriesData where
  a : ℕ → ℝ
  F : ℝ → ℝ
  nonneg : ∀ n, 0 ≤ a n
  cont : Continuous F
  series : ∀ x, HasSum (fun n => a n * x ^ n) (F x)
  pos : ∀ x, 0 < x → 0 < F x

private def SeriesData.p (s : SeriesData) (n : ℕ) (x : ℝ) := s.a n * x ^ n / s.F x

private theorem SeriesData.measurable_p (s : SeriesData) (n : ℕ) : Measurable (s.p n) := by
  unfold p
  have h := s.cont.measurable
  fun_prop

private theorem SeriesData.p_nonneg (s : SeriesData) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ s.p n x := div_nonneg (mul_nonneg (s.nonneg n) (pow_nonneg hx.le _)) (s.pos x hx).le

private theorem SeriesData.partition (s : SeriesData) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n => s.p n x) 1 := by
  simpa [SeriesData.p, (s.pos x hx).ne'] using (s.series x).div_const (s.F x)

-- Integrating the generating series for the normalized terms gives a geometric series.
private theorem SeriesData.moments_of_ratios (s : SeriesData)
    (h : ∀ r : ℝ, 0 < r → r < 1 → ∫ x, s.F (r * x) / s.F x ∂μ = 1 / (1 - r)) :
    ∀ n, ∫ x, s.p n x ∂μ = 1 := by
  let b (n : ℕ) := ∫ x, s.p n x ∂μ
  have hs (r : ℝ) (hr : 0 < r) (hr' : r < 1) :
      HasSum (fun n => b n * r ^ n) (1 / (1 - r)) := by
    let g (n : ℕ) (x : ℝ) := s.p n x * r ^ n
    have hpt (x : ℝ) : HasSum (fun n => g n x) (s.F (r * x) / s.F x) := by
      convert (s.series (r * x)).div_const (s.F x) using 1
      ext n
      simp only [g, SeriesData.p, mul_pow]
      ring
    have hI : Integrable (fun x => s.F (r * x) / s.F x) μ :=
      .of_integral_ne_zero <| by rw [h r hr hr']; positivity
    have hS := hasSum_integral_of_dominated_convergence (μ := μ) g
      (fun n => ((s.measurable_p n).mul measurable_const).aestronglyMeasurable)
      (fun n => (ae_restrict_mem measurableSet_Ioi).mono fun x hx => by
        change ‖s.p n x * r ^ n‖ ≤ s.p n x * r ^ n
        rw [Real.norm_of_nonneg (mul_nonneg (s.p_nonneg n hx) (pow_nonneg hr.le _))])
      (ae_of_all _ fun x => (hpt x).summable)
      (hI.congr (ae_of_all _ fun x => (hpt x).tsum_eq.symm))
      (ae_of_all _ hpt)
    simpa only [g, Pi.mul_apply, integral_mul_const, h r hr hr', b] using hS
  have hb (x : ℝ) (hx : |x| < 1) : Summable (fun k => b k * x ^ k) := by
    rcases eq_or_ne x 0 with rfl | hx'
    · apply summable_of_ne_finset_zero (s := {0})
      intro i hi
      simp_all
    · apply Summable.of_norm
      simpa only [norm_mul, norm_pow, Real.norm_eq_abs, abs_abs] using
        (hs |x| (abs_pos.mpr hx') hx).summable.norm
  apply coeff_eq_of_tsum_eq_on_inv_nat_add_two b (fun _ => 1) hb
  · intro x hx
    simpa using summable_geometric_of_abs_lt_one hx
  · intro n
    have h₀ : 0 < 1 / ((n : ℝ) + 2) := by positivity
    have h₁ : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    rw [(hs _ h₀ h₁).tsum_eq]
    simp only [one_mul]
    rw [tsum_geometric_of_lt_one h₀.le h₁, one_div]

private structure Balanced extends SeriesData where
  mass : ∀ n, ∫ x, toSeriesData.p n x ∂μ = 1

private theorem Balanced.integrable_p (s : Balanced) (n : ℕ) : Integrable (s.p n) μ :=
  .of_integral_ne_zero (by rw [s.mass]; norm_num)

private theorem Balanced.coeff_pos (s : Balanced) (n : ℕ) : 0 < s.a n := by
  refine lt_of_le_of_ne (s.nonneg n) fun h => ?_
  simpa [SeriesData.p, ← h] using s.mass n

private def Balanced.t (s : Balanced) (n : ℕ) := s.a n / s.a (n + 1)

private theorem Balanced.tpos (s : Balanced) (n : ℕ) : 0 < s.t n :=
  div_pos (s.coeff_pos _) (s.coeff_pos _)

private theorem Balanced.step (s : Balanced) (n : ℕ) (x : ℝ) :
    x * s.p n x = s.t n * s.p (n + 1) x := by
  dsimp only [SeriesData.p, Balanced.t]
  rw [pow_succ]
  field_simp [(s.coeff_pos (n + 1)).ne']

-- The variance of x under the probability density pₙ is tₙ (tₙ₊₁ - tₙ).
private theorem Balanced.monotone_t (s : Balanced) : Monotone s.t := by
  apply monotone_nat_of_le_succ
  intro n
  have h : 0 ≤ ∫ x, s.t n * s.t (n + 1) * s.p (n + 2) x -
      2 * s.t n * (s.t n * s.p (n + 1) x) + s.t n ^ 2 * s.p n x ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have h₁ := s.step n x
    have h₂ := s.step (n + 1) x
    calc
      0 ≤ (x - s.t n) ^ 2 * s.p n x := mul_nonneg (sq_nonneg _) (s.p_nonneg n hx)
      _ = _ := by linear_combination s.t n * h₂ + (x - 2 * s.t n) * h₁
  have i₁ := (s.integrable_p (n + 2)).const_mul (s.t n * s.t (n + 1))
  have i₂ := ((s.integrable_p (n + 1)).const_mul (s.t n)).const_mul (2 * s.t n)
  rw [integral_add (f := fun x => s.t n * s.t (n + 1) * s.p (n + 2) x -
    2 * s.t n * (s.t n * s.p (n + 1) x)) (i₁.sub i₂) ((s.integrable_p n).const_mul (s.t n ^ 2)),
    integral_sub i₁ i₂] at h
  simp only [integral_const_mul, s.mass, mul_one] at h
  exact le_of_not_gt fun hn => by nlinarith [mul_pos (s.tpos n) (sub_pos.mpr hn)]

-- Below q tₙ the terms from n onward decrease at least geometrically.
private theorem Balanced.tail (s : Balanced) {q x : ℝ} (hq : 0 < q) (hq' : q < 1)
    (hx : 0 < x) (n : ℕ) (h : x ≤ q * s.t n) :
    1 ≤ (∑ i ∈ Finset.range n, s.p i x) + (1 - q)⁻¹ * s.p n x := by
  have ht (k : ℕ) : s.p (n + k) x ≤ q ^ k * s.p n x := by
    induction k with
    | zero => simp
    | succ k ih =>
      have he := s.step (n + k) x
      have hx' := h.trans (mul_le_mul_of_nonneg_left (s.monotone_t (Nat.le_add_right n k)) hq.le)
      calc
        s.p (n + k + 1) x ≤ q * s.p (n + k) x := by
          apply le_of_mul_le_mul_left (a := s.t (n + k)) _ (s.tpos (n + k))
          rw [← he]
          nlinarith [mul_le_mul_of_nonneg_right hx' (s.p_nonneg (n + k) hx)]
        _ ≤ _ := by rw [pow_succ']; nlinarith [mul_le_mul_of_nonneg_left ih hq.le]
  have H := s.partition hx
  conv_lhs => rw [← H.tsum_eq, ← H.summable.sum_add_tsum_nat_add n]
  apply add_le_add_right
  have hs := ((hasSum_geometric_of_lt_one hq.le hq').mul_right (s.p n x))
  rw [← hs.tsum_eq]
  exact ((summable_nat_add_iff n).2 H.summable).tsum_le_tsum (fun k => by
    simpa only [add_comm] using ht k) hs.summable

-- Above tₙ / q the same comparison works backwards from n.
private theorem Balanced.head (s : Balanced) {q x : ℝ} (hq : 0 < q) (hq' : q < 1)
    (hx : 0 < x) (n : ℕ) (h : s.t n ≤ q * x) :
    ∑ i ∈ Finset.range (n + 1), s.p i x ≤ (1 - q)⁻¹ * s.p n x := by
  have hc : 0 ≤ (1 - q)⁻¹ := by positivity
  have he : (1 - q)⁻¹ * (1 - q) = 1 := inv_mul_cancel₀ (by linarith)
  induction n with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    nlinarith [mul_nonneg (mul_nonneg hc hq.le) (s.p_nonneg 0 hx), s.p_nonneg 0 hx,
      congrArg (· * s.p 0 x) he]
  | succ n ih =>
    have ih' := ih ((s.monotone_t (Nat.le_succ n)).trans h)
    have hstep : s.p n x ≤ q * s.p (n + 1) x := by
      apply le_of_mul_le_mul_left (a := x) _ hx
      rw [s.step]
      nlinarith [mul_le_mul_of_nonneg_right ((s.monotone_t (Nat.le_succ n)).trans h)
        (s.p_nonneg (n + 1) hx)]
    rw [Finset.sum_range_succ]
    nlinarith [mul_le_mul_of_nonneg_left hstep hc, congrArg (· * s.p (n + 1) x) he]

-- Integrate the two geometric bounds, using that each pₙ has mass one.
private theorem Balanced.bounds (s : Balanced) {q : ℝ} (hq : 0 < q) (hq' : q < 1) (n : ℕ) :
    q * s.t n ≤ n + (1 - q)⁻¹ ∧ (n : ℝ) + 1 ≤ s.t n / q + (1 - q)⁻¹ := by
  classical
  let cut (A : ℝ) := (Ioc 0 A).indicator (fun _ => (1 : ℝ))
  have cutInt (A : ℝ) : Integrable (cut A) μ :=
    (integrable_indicator_iff measurableSet_Ioc).2 <|
      (integrableOn_const (by simp : volume (Ioc 0 A) ≠ ⊤)).mono_measure Measure.restrict_le_self
  have cutMass (A : ℝ) (hA : 0 ≤ A) : ∫ x, cut A x ∂μ = A := by
    simp only [cut, integral_indicator measurableSet_Ioc, μ, Measure.restrict_restrict
      measurableSet_Ioc, inter_eq_left.mpr (Ioc_subset_Ioi_self), setIntegral_const,
      smul_eq_mul, mul_one, measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hA]
  let pref (m : ℕ) (x : ℝ) := ∑ i ∈ Finset.range m, s.p i x
  have prefInt (m : ℕ) : Integrable (pref m) μ := integrable_finsetSum _ fun i _ => s.integrable_p i
  have prefMass (m : ℕ) : ∫ x, pref m x ∂μ = m := by
    simp [pref, integral_finsetSum _ (fun i _ => s.integrable_p i), s.mass]
  have hC : 0 ≤ (1 - q)⁻¹ := by positivity
  constructor
  · have he : cut (q * s.t n) ≤ᵐ[μ] fun x => pref n x + (1 - q)⁻¹ * s.p n x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      by_cases hx' : x ≤ q * s.t n
      · simpa only [cut, indicator_of_mem (show x ∈ Ioc 0 (q * s.t n) from ⟨hx, hx'⟩)]
          using s.tail hq hq' hx n hx'
      · rw [show cut (q * s.t n) x = 0 from
          indicator_of_notMem (s := Ioc 0 _) (fun h => hx' h.2) _]
        exact add_nonneg (Finset.sum_nonneg fun i _ => s.p_nonneg i hx)
          (mul_nonneg hC (s.p_nonneg _ hx))
    have := integral_mono_ae (cutInt _) ((prefInt _).add ((s.integrable_p n).const_mul _)) he
    simp only [Pi.add_apply] at this
    rwa [cutMass _ (mul_pos hq (s.tpos n)).le,
      integral_add (prefInt n) ((s.integrable_p n).const_mul ((1 - q)⁻¹)),
      prefMass, integral_const_mul, s.mass, mul_one] at this
  · have he : pref (n + 1) ≤ᵐ[μ] fun x => cut (s.t n / q) x + (1 - q)⁻¹ * s.p n x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      by_cases hx' : x ≤ s.t n / q
      · rw [show cut (s.t n / q) x = 1 from indicator_of_mem (s := Ioc 0 _) ⟨hx, hx'⟩ _]
        exact (sum_le_hasSum (Finset.range _) (fun i _ => s.p_nonneg i hx) (s.partition hx)).trans
          (le_add_of_nonneg_right (mul_nonneg hC (s.p_nonneg _ hx)))
      · rw [show cut (s.t n / q) x = 0 from
          indicator_of_notMem (s := Ioc 0 _) (fun h => hx' h.2) _, zero_add]
        exact s.head hq hq' hx n (by linarith [(div_lt_iff₀ hq).mp (lt_of_not_ge hx')])
    have := integral_mono_ae (prefInt _) ((cutInt _).add ((s.integrable_p n).const_mul _)) he
    simpa only [Pi.add_apply, prefMass, Nat.cast_add_one,
      integral_add (cutInt _) ((s.integrable_p n).const_mul ((1 - q)⁻¹)),
      cutMass _ (div_pos (s.tpos _) hq).le, integral_const_mul, s.mass, mul_one] using this

private def Balanced.r (s : Balanced) (n : ℕ) := ((n : ℝ) + 1) / s.t n

private theorem Balanced.r_mul_coeff (s : Balanced) (n : ℕ) :
    s.r n * s.a n = ((n : ℝ) + 1) * s.a (n + 1) := by
  unfold r t
  field_simp [(s.coeff_pos n).ne', (s.coeff_pos (n + 1)).ne']

private theorem Balanced.tendsto_r (s : Balanced) : Tendsto s.r atTop (𝓝 1) := by
  have hzero (C : ℝ) : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_const_div_atTop_nhds_zero_nat C).comp (tendsto_add_atTop_nat 1)
  suffices h : Tendsto (fun n : ℕ => s.t n / ((n : ℝ) + 1)) atTop (𝓝 1) by
    change Tendsto (fun n : ℕ => ((n : ℝ) + 1) / s.t n) atTop (𝓝 1)
    simpa using h.inv₀ one_ne_zero
  apply tendsto_order.mpr
  constructor
  · intro l hl
    obtain ⟨q, hq, hq'⟩ := exists_between (max_lt hl zero_lt_one)
    have hpos := (le_max_right l 0).trans_lt hq
    let C := (1 - q)⁻¹
    have hlim : Tendsto (fun n : ℕ => q * (1 - C / ((n : ℝ) + 1))) atTop (𝓝 q) := by
      simpa using (tendsto_const_nhds (x := q)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).sub (hzero C))
    filter_upwards [hlim.eventually_const_lt ((le_max_left _ _).trans_lt hq)] with n hn
    have hd : 0 < (n : ℝ) + 1 := by positivity
    apply hn.trans_le
    rw [le_div_iff₀ hd]
    have H := (s.bounds hpos hq' n).2
    have H' := (le_div_iff₀ hpos).mp (show (n : ℝ) + 1 - (1 - q)⁻¹ ≤ s.t n / q by linarith)
    rw [mul_assoc, sub_mul, div_mul_cancel₀ _ hd.ne', one_mul, mul_comm]
    exact H'
  · intro u hu
    have hu₀ := zero_lt_one.trans hu
    obtain ⟨q, hq, hq'⟩ := exists_between (inv_lt_one_of_one_lt₀ hu)
    have hpos := (inv_pos.mpr hu₀).trans hq
    let C := (1 - q)⁻¹
    have hlim : Tendsto (fun n : ℕ => (1 + C / ((n : ℝ) + 1)) / q) atTop (𝓝 (1 / q)) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add (hzero C)).div_const q
    have hinv : 1 / q < u := by
      rw [div_lt_iff₀ hpos]
      simpa [mul_comm, one_div] using
        (div_lt_iff₀ hu₀).mp (show 1 / u < q by simpa only [one_div] using hq)
    filter_upwards [hlim.eventually_lt_const hinv] with n hn
    apply lt_of_le_of_lt _ hn
    have hd : 0 < (n : ℝ) + 1 := by positivity
    rw [le_div_iff₀ hpos]
    have H := (s.bounds hpos hq' n).1
    change q * s.t n ≤ ↑n + C at H
    field_simp [hd.ne']
    linarith

private theorem Balanced.deriv_series (s : Balanced) (B : ℝ) (hb : ∀ n, s.r n ≤ B)
    {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ s.F x ∧ HasSum (fun n => s.r n * s.p n x) (deriv s.F x / s.F x) := by
  let g (n : ℕ) (y : ℝ) := s.a (n + 1) * y ^ (n + 1)
  let d (n : ℕ) (y : ℝ) := s.r n * s.a n * y ^ n
  let u (n : ℕ) := B * (s.a n * (x + 1) ^ n)
  have hu : Summable u := (s.series (x + 1)).summable.mul_left B
  have hg (n : ℕ) (y : ℝ) : HasDerivAt (g n) (d n y) y := by
    convert (hasDerivAt_pow (n + 1) y).const_mul (s.a (n + 1)) using 1
    simp [d, s.r_mul_coeff]
    ring
  have hbound (n : ℕ) (y : ℝ) (hy : y ∈ Ioo 0 (x + 1)) : ‖d n y‖ ≤ u n := by
    have hr : 0 ≤ s.r n := div_nonneg (by positivity) (s.tpos _).le
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hr (s.nonneg _)) (pow_nonneg hy.1.le _))]
    dsimp only [u, d]
    rw [mul_assoc]
    exact mul_le_mul (hb n) (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hy.1.le hy.2.le n) (s.nonneg n))
      (mul_nonneg (s.nonneg n) (pow_nonneg hy.1.le n)) (hr.trans (hb n))
  have htail (y : ℝ) : HasSum (fun n => g n y) (s.F y - s.a 0) := by
    simpa [g] using (hasSum_nat_add_iff' 1).mpr (s.series y)
  have hx' : x ∈ Ioo 0 (x + 1) := ⟨hx, by linarith⟩
  have H := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => hg n y) hbound hx' (htail x).summable hx'
  have He : (fun y => ∑' n, g n y) = fun y => s.F y - s.a 0 := funext fun y => (htail y).tsum_eq
  rw [He] at H
  have HD : HasDerivAt s.F (∑' n, d n x) x := by simpa using H.add_const (s.a 0)
  refine ⟨HD.differentiableAt, ?_⟩
  rw [HD.deriv]
  convert ((Summable.of_norm_bounded hu (fun n => hbound n x hx')).hasSum.div_const (s.F x))
    using 1
  ext n
  dsimp [d, SeriesData.p]
  ring

private theorem Balanced.p_pos (s : Balanced) (n : ℕ) {x : ℝ} (hx : 0 < x) : 0 < s.p n x :=
  div_pos (mul_pos (s.coeff_pos n) (pow_pos hx n)) (s.pos x hx)

private theorem Balanced.p_le_one (s : Balanced) (n : ℕ) {x : ℝ} (hx : 0 < x) : s.p n x ≤ 1 :=
  le_hasSum (s.partition hx) n (fun i _ => s.p_nonneg i hx)

private theorem Balanced.tendsto_p (s : Balanced) (n : ℕ) : Tendsto (s.p n) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ ((tendsto_const_nhds (x := s.t n)).div_atTop tendsto_id)
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with x hx using s.p_nonneg n hx
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with x hx
    change s.p n x ≤ s.t n / x
    rw [le_div_iff₀ (show 0 < x from hx), mul_comm, s.step]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (s.p_le_one (n + 1) hx) (s.tpos n).le

-- Integrating the derivative of pₙ₊₁ gives the average of the logarithmic derivative.
private theorem Balanced.integral_logDeriv_mul_p (s : Balanced) (B : ℝ)
    (hb : ∀ n, s.r n ≤ B) (n : ℕ) :
    Integrable (fun x => logDeriv s.F x * s.p (n + 1) x) μ ∧
      ∫ x, logDeriv s.F x * s.p (n + 1) x ∂μ = s.r n := by
  have ht (x : ℝ) (hx : 0 < x) : 0 ≤ logDeriv s.F x ∧ logDeriv s.F x ≤ B := by
    have H := (s.deriv_series B hb hx).2
    constructor
    · exact H.nonneg (fun i => mul_nonneg (div_nonneg (by positivity) (s.tpos i).le)
        (s.p_nonneg i hx))
    · simpa only [logDeriv_apply, mul_one] using hasSum_le (fun i =>
        mul_le_mul_of_nonneg_right (hb i) (s.p_nonneg i hx)) H ((s.partition hx).mul_left B)
  have hi : Integrable (fun x => logDeriv s.F x * s.p (n + 1) x) μ := by
    refine ((s.integrable_p (n + 1)).const_mul B).mono' ?_ ?_
    · exact (((measurable_deriv s.F).div s.cont.measurable).mul
        (s.measurable_p (n + 1))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_of_nonneg (mul_nonneg (ht x hx).1 (s.p_nonneg _ hx))]
      exact mul_le_mul_of_nonneg_right (ht x hx).2 (s.p_nonneg _ hx)
  refine ⟨hi, ?_⟩
  have hf0 : s.F 0 = s.a 0 := by simpa [zero_pow_eq] using (s.series 0).tsum_eq.symm
  have hd (x : ℝ) (hx : x ∈ Ioi 0) :
      HasDerivAt (s.p (n + 1)) (s.r n * s.p n x - logDeriv s.F x * s.p (n + 1) x) x := by
    have H := (((hasDerivAt_pow (n + 1) x).const_mul (s.a (n + 1))).div
      (s.deriv_series B hb hx).1.hasDerivAt (s.pos x hx).ne')
    unfold SeriesData.p
    rw [logDeriv_apply]
    apply H.congr_deriv
    simp only [Nat.cast_add_one, Nat.add_one_sub_one]
    field_simp [(s.pos x hx).ne']
    linear_combination -x ^ n * s.F x * s.r_mul_coeff n
  have hcont : ContinuousAt (s.p (n + 1)) 0 := by
    unfold SeriesData.p
    apply ContinuousAt.div _ s.cont.continuousAt (hf0 ▸ (s.coeff_pos 0).ne')
    fun_prop
  have H := integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousWithinAt hd
    (((s.integrable_p n).const_mul (s.r n)).sub hi) (s.tendsto_p (n + 1))
  change (∫ x, s.r n * s.p n x - logDeriv s.F x * s.p (n + 1) x ∂μ) = 0 - s.p (n + 1) 0 at H
  rw [integral_sub ((s.integrable_p n).const_mul (s.r n)) hi,
    integral_const_mul, s.mass, mul_one] at H
  have h0 : s.p (n + 1) 0 = 0 := by simp [SeriesData.p]
  rw [h0, sub_zero] at H
  linarith

private theorem integral_strict {f g : ℝ → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (h : ∀ x, 0 < x → f x < g x) : ∫ x, f x ∂μ < ∫ x, g x ∂μ := by
  have hle := (ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))).mono
    (fun x hx => (h x hx).le)
  refine (integral_mono_ae hf hg hle).lt_of_ne fun he => ?_
  have heq := (integral_eq_iff_of_ae_le hf hg hle).mp he
  obtain ⟨x, hx, he'⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (show volume (Ioi (0 : ℝ)) ≠ 0 by simp) heq
  exact (h x hx).ne he'

-- A nonzero maximum deviation from 1 is attained. A strictly positive weighted average
-- cannot attain that extremum, since the deviations tend to zero.
private theorem Balanced.r_eq_one (s : Balanced) (i : ℕ) : s.r i = 1 := by
  by_contra hi
  let D (j : ℕ) := |s.r j - 1|
  have hD : Tendsto D atTop (𝓝 0) := by simpa [D] using (s.tendsto_r.sub_const 1).abs
  have hpos : 0 < D i := abs_pos.mpr (sub_ne_zero.mpr hi)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hD.eventually_lt_const hpos)
  let S := Finset.range (max i N + 1)
  have hiS : i ∈ S := Finset.mem_range.mpr (by omega)
  obtain ⟨m, hm, hmax⟩ := S.exists_max_image D ⟨i, hiS⟩
  have hall (k : ℕ) : D k ≤ D m := by
    by_cases hk : k ∈ S
    · exact hmax k hk
    · have hk' : ¬ k < max i N + 1 := fun h => hk (Finset.mem_range.mpr h)
      exact (hN k (by omega)).le.trans (hmax i hiS)
  have hstrict : D N < D m := (hN N le_rfl).trans_le (hall i)
  let b := 1 - D m
  let B := 1 + D m
  have hlo (k : ℕ) : b ≤ s.r k := by linarith [(abs_le.mp (hall k)).1]
  have hhi (k : ℕ) : s.r k ≤ B := by linarith [(abs_le.mp (hall k)).2]
  have hNlo : b < s.r N := by linarith [(abs_lt.mp hstrict).1]
  have hNhi : s.r N < B := by linarith [(abs_lt.mp hstrict).2]
  have hL (x : ℝ) (hx : 0 < x) : b < logDeriv s.F x ∧ logDeriv s.F x < B := by
    have H := (s.deriv_series B hhi hx).2
    constructor
    · simpa only [logDeriv_apply, mul_one] using hasSum_lt
        (fun k => mul_le_mul_of_nonneg_right (hlo k) (s.p_nonneg k hx))
        (mul_lt_mul_of_pos_right hNlo (s.p_pos N hx)) ((s.partition hx).mul_left b) H
    · simpa only [logDeriv_apply, mul_one] using hasSum_lt
        (fun k => mul_le_mul_of_nonneg_right (hhi k) (s.p_nonneg k hx))
        (mul_lt_mul_of_pos_right hNhi (s.p_pos N hx)) H ((s.partition hx).mul_left B)
  obtain ⟨hi', havg⟩ := s.integral_logDeriv_mul_p B hhi m
  have hl := integral_strict ((s.integrable_p (m + 1)).const_mul b) hi'
    (fun x hx => mul_lt_mul_of_pos_right (hL x hx).1 (s.p_pos _ hx))
  have hu := integral_strict hi' ((s.integrable_p (m + 1)).const_mul B)
    (fun x hx => mul_lt_mul_of_pos_right (hL x hx).2 (s.p_pos _ hx))
  rw [integral_const_mul, s.mass, mul_one, havg] at hl hu
  apply (lt_irrefl (D m))
  apply abs_lt.mpr
  constructor <;> linarith

/--
**No non-exponential solution of the Rényi–Vincze conditions.** There are no function
$f : \mathbb{C} \to \mathbb{C}$ and real numbers $a_0, a_1, a_2, \dots$ such that $f$ is not the
function $z \mapsto c\,e^z$ for any real $c > 0$; $a_n \ge 0$ for every $n$; $a_n \ne 0$ for
infinitely many $n$; for every $z \in \mathbb{C}$ the series $\sum_{n \ge 0} a_n z^n$ has sum
$f(z)$; $f$ is entire; and either $\int_0^\infty a_n x^n / f(x)\,dx = 1$ for every $n \ge 0$, or
$\int_0^\infty f(\rho x) / f(x)\,dx = 1/(1-\rho)$ for every real $\rho$ with $0 < \rho < 1$.

Miles and Williamson (J. London Math. Soc. (2) 33 (1986) 110-116) proved that a transcendental
entire $f$ with positive coefficients and $\int_0^\infty a_n x^n / f(x)\,dx = 1$ for all $n$ is
$c\,e^z$. The first integral condition forces every $a_n > 0$, and the second reduces to the
first.

Source: Antonio Greco and Andrea Loi, Radial balanced metrics on the unit disk,
arXiv:0803.3711 (2008), https://arxiv.org/abs/0803.3711. Moved from
`OpenConjectures/Analysis/HaymanProblem232`.
-/
public theorem conjecture_refuted : ¬ conjecture := by
  rintro ⟨f, a, hne, ha, hinf, hseries, hentire, hcond⟩
  let F (x : ℝ) := (f x).re
  have hF (x : ℝ) : HasSum (fun n => a n * x ^ n) (F x) := by
    simpa only [F, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
      using Complex.hasSum_re (hseries (x : ℂ))
  have hcoe (x : ℝ) : f (x : ℂ) = (F x : ℂ) := by
    apply (hseries _).unique
    simpa only [Complex.ofReal_mul, Complex.ofReal_pow] using Complex.hasSum_ofReal.mpr (hF x)
  let s : SeriesData := {
    a := a
    F := F
    nonneg := ha
    cont := Complex.continuous_re.comp
      ((differentiableOn_univ.mp hentire).continuous.comp Complex.continuous_ofReal)
    series := hF
    pos x hx := by
      obtain ⟨k, _, hk⟩ := hinf 0
      exact (mul_pos (lt_of_le_of_ne (ha k) (Ne.symm hk)) (pow_pos hx k)).trans_le
        (le_hasSum (hF x) k (fun j _ => mul_nonneg (ha j) (pow_nonneg hx.le j))) }
  have hm (n : ℕ) : ∫ x, s.p n x ∂μ = 1 := by
    rcases hcond with hm | hr
    · specialize hm n
      simp_rw [integral_Ici_eq_integral_Ioi, hcoe, ← Complex.ofReal_div, integral_complex_ofReal]
        at hm
      change ∫ x in Ioi 0, a n * x ^ n / F x = 1
      exact Complex.ofReal_injective (by simpa only [Complex.ofReal_one] using hm)
    · apply s.moments_of_ratios _ n
      intro r hr₀ hr₁
      specialize hr r hr₀ hr₁
      simp_rw [integral_Ici_eq_integral_Ioi, hcoe, ← Complex.ofReal_div, integral_complex_ofReal]
        at hr
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one] using hr
  let S : Balanced := ⟨s, hm⟩
  have hc (n : ℕ) : a n = a 0 / n.factorial := by
    induction n with
    | zero => simp
    | succ n ih =>
      have H := S.r_mul_coeff n
      rw [S.r_eq_one n, one_mul] at H
      change a n = ((n : ℝ) + 1) * a (n + 1) at H
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
      apply (eq_div_iff (by positivity)).mpr
      calc
        _ = a n * n.factorial := by rw [H]; ring
        _ = a 0 := (eq_div_iff (by positivity)).mp ih
  apply hne (a 0) (S.coeff_pos 0)
  funext z
  apply (hseries z).unique
  rw [Complex.exp_eq_exp_ℂ]
  convert (NormedSpace.expSeries_div_hasSum_exp z).mul_left (a 0 : ℂ) using 1
  ext n
  rw [hc n, Complex.ofReal_div]
  push_cast
  ring

end

end MathlibExt.Analysis.HaymanProblem232Wanted
