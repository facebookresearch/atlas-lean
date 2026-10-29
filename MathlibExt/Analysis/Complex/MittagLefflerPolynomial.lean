/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Mittag-Leffler's theorem on `ℂ` with polynomial corrections

Let `b ν` be distinct points of `ℂ` with `‖b ν‖ → ∞` and let `P ν` be polynomials.
`Complex.mittag_leffler` proves:

* some `f : ℂ → ℂ` is meromorphic on `ℂ`, analytic off `range b`, and has singular part
  `(P ν).eval (z - b ν)⁻¹` at each `b ν`;
* for suitable polynomials `p ν`, depending only on `b` and `P`, the functions of this kind are
  exactly those with `f z = g z + ∑ ν, ((P ν).eval (z - b ν)⁻¹ - (p ν).eval z)` for `z ∉ range b`,
  the series converging, with `g` entire.

`Complex.mittag_leffler_of_coeff_zero_eq_zero` is the textbook statement, in which the `P ν` have
no constant term; it follows from the general theorem, where a constant term is absorbed into `g`.

Values at the poles are junk in Lean, so "`f` has singular part `S` at `c`" is stated as
`f = S + φ` on a punctured neighbourhood of `c` with `φ` analytic at `c`, and the representation
is stated for `z ∉ range b`.

## Proof

Truncating the Cauchy power series of `z ↦ (P ν).eval (z - b ν)⁻¹` at `0` gives polynomials `p ν`
with `‖(P ν).eval (z - b ν)⁻¹ - (p ν).eval z‖ ≤ 2⁻¹ ^ ν` on `‖z‖ ≤ ‖b ν‖ / 4`. The corrected
series then converges everywhere, and after splitting off finitely many terms the Weierstrass
M-test (`Complex.differentiableOn_tsum_of_summable_norm`) shows that its sum `F` is analytic off
`range b` and that `F` minus the singular part at `b n` is analytic at `b n`. If `f` is of this
kind, `f - F` has only removable singularities, and filling them in with punctured limits gives
the entire function `g`. Conversely, `g + F` is of this kind.

## Relation to `MathlibExt.Analysis.Complex.MittagLeffler`

That module's `MathlibExt.Analysis.Complex.MittagLefflerWanted.mittag_leffler_of_isDiscrete`
proves existence only: for a closed discrete set `S` (possibly finite) and principal parts given
by `Finsupp` coefficients, with entire functions as correcting terms. The theorems here index the
poles by a sequence and add the classification of all solutions with polynomial corrections. On a
common instance (`S = range b`, the `P ν` without constant term) the two existence statements
agree, except that that theorem's `AnalyticAt` formulation also constrains the junk values
`f (b ν)`. Pinned Mathlib has no Mittag-Leffler theorem for meromorphic functions.

## Provenance

Rubric-guided revision of v1 ComplexVariables target 29 (`MittagLeffler.mittag_leffler` in
`v1/Atlas/ComplexVariables/code/Lecture17.lean` at commit
6191bf1ba03d204784385ef5be2472be88035b93), Lecture 17, Theorem 1 (Mittag-Leffler's theorem),
following Ahlfors, *Complex Analysis*. It fixes these defects of the archived formalization: its
existence part dropped "poles at just the points `b ν`" (analyticity off `range b`); its
representation part was conditional on an unasserted function with those poles and hid the
series behind an abstract witness, so neither the correcting polynomials nor the series appeared
in the statement; its distinct-points hypothesis was undocumented; and its singular-part
predicate constrained the junk value `f (b ν)`. The archived formalization and its original
license/provenance remain in `v1/` (the original license text is `v1/LICENSE`).
-/

set_option autoImplicit false

open Filter Polynomial Set Topology

namespace Complex

/-- `z ↦ P.eval (z - c)⁻¹` is analytic away from `c`. -/
private lemma analyticAt_eval_inv_sub (P : ℂ[X]) {c z : ℂ} (hz : z ≠ c) :
    AnalyticAt ℂ (fun w ↦ P.eval (w - c)⁻¹) z := by
  simpa [coe_aeval_eq_eval] using
    ((analyticAt_id.fun_sub analyticAt_const).fun_inv (sub_ne_zero.2 hz)).aeval_polynomial P

/-- `z ↦ P.eval (z - c)⁻¹` is meromorphic at `c`. -/
private lemma meromorphicAt_eval_inv_sub (P : ℂ[X]) (c : ℂ) :
    MeromorphicAt (fun w ↦ P.eval (w - c)⁻¹) c := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval_add] using hp.fun_add hq
  | monomial n a => simp only [eval_monomial]; fun_prop

/-- A Taylor polynomial at `0` of `z ↦ P.eval (z - c)⁻¹` approximates it within `ε` on
`‖z‖ ≤ ‖c‖ / 4`. -/
private lemma exists_polynomial_approx (P : ℂ[X]) {c : ℂ} (hc : c ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z : ℂ, ‖z‖ ≤ ‖c‖ / 4 → ‖P.eval (z - c)⁻¹ - p.eval z‖ ≤ ε := by
  have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
  obtain ⟨R, hR⟩ : ∃ R : NNReal, (R : ℝ) = ‖c‖ / 2 := ⟨⟨‖c‖ / 2, by positivity⟩, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : NNReal, (r : ℝ) = ‖c‖ / 3 := ⟨⟨‖c‖ / 3, by positivity⟩, rfl⟩
  have hf : HasFPowerSeriesOnBall (fun w ↦ P.eval (w - c)⁻¹)
      (cauchyPowerSeries (fun w ↦ P.eval (w - c)⁻¹) 0 R) 0 R := by
    refine DifferentiableOn.hasFPowerSeriesOnBall (fun w hw ↦ ?_)
      (by rw [← NNReal.coe_pos, hR]; positivity)
    refine (analyticAt_eval_inv_sub P ?_).differentiableAt.differentiableWithinAt
    rintro rfl
    rw [Metric.mem_closedBall, dist_zero_right, hR] at hw
    linarith
  have hrR : (r : ENNReal) < R := by
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, hr, hR]
    linarith
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.1 (hf.tendstoUniformlyOn hrR) ε hε).exists
  set q := cauchyPowerSeries (fun w ↦ P.eval (w - c)⁻¹) 0 R
  refine ⟨∑ k ∈ Finset.range N, C (q.coeff k) * X ^ k, fun z hz ↦ ?_⟩
  have hz' : z ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, hr]
    linarith
  have hq : q.partialSum N z = (∑ k ∈ Finset.range N, C (q.coeff k) * X ^ k).eval z := by
    simp only [FormalMultilinearSeries.partialSum, eval_finsetSum, eval_mul, eval_C, eval_pow,
      eval_X, FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
  have := hN z hz'
  simp only [dist_eq_norm, zero_add] at this
  rw [hq] at this
  exact this.le

/-- Polynomials `p ν` with `‖(P ν).eval (z - b ν)⁻¹ - (p ν).eval z‖ ≤ 2⁻¹ ^ ν` on
`‖z‖ ≤ ‖b ν‖ / 4`. -/
private lemma exists_polynomials_approx (b : ℕ → ℂ) (P : ℕ → ℂ[X]) :
    ∃ p : ℕ → ℂ[X], ∀ ν z, ‖z‖ ≤ ‖b ν‖ / 4 →
      ‖(P ν).eval (z - b ν)⁻¹ - (p ν).eval z‖ ≤ (2⁻¹ : ℝ) ^ ν := by
  have key : ∀ ν, ∃ p : ℂ[X], ∀ z : ℂ, ‖z‖ ≤ ‖b ν‖ / 4 →
      ‖(P ν).eval (z - b ν)⁻¹ - p.eval z‖ ≤ (2⁻¹ : ℝ) ^ ν := by
    intro ν
    rcases eq_or_ne (b ν) 0 with h | h
    · -- the only admissible point is `z = 0`; cancel the value there
      refine ⟨C ((P ν).eval 0), fun z hz ↦ ?_⟩
      obtain rfl : z = 0 := by simpa [h] using hz
      simp only [h, inv_zero, eval_C, sub_self, norm_zero]
      positivity
    · exact exists_polynomial_approx (P ν) h (by positivity)
  exact ⟨fun ν ↦ (key ν).choose, fun ν ↦ (key ν).choose_spec⟩

/-- Terms bounded by `2⁻¹ ^ ν` on `‖z‖ ≤ ‖b ν‖ / 4`, with `b ν → ∞`, are summable at every `z`. -/
private lemma summable_of_approx {b : ℕ → ℂ} {u : ℕ → ℂ → ℂ}
    (hb : Tendsto (fun ν ↦ ‖b ν‖) atTop atTop)
    (hu : ∀ ν z, ‖z‖ ≤ ‖b ν‖ / 4 → ‖u ν z‖ ≤ (2⁻¹ : ℝ) ^ ν) (z : ℂ) :
    Summable fun ν ↦ u ν z := by
  refine Summable.of_norm_bounded_eventually
    (summable_geometric_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num) (by norm_num)) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hb.eventually_ge_atTop (4 * ‖z‖)] with ν hν
  exact hu ν z (by linarith)

/-- Under the same bounds, if each `u ν` is analytic off `b ν`, then for all large `N` the tail
`z ↦ ∑' k, u (k + N) z` is analytic at a given point. -/
private lemma eventually_analyticAt_tsum_nat_add {b : ℕ → ℂ} {u : ℕ → ℂ → ℂ}
    (hb : Tendsto (fun ν ↦ ‖b ν‖) atTop atTop)
    (hu : ∀ ν z, ‖z‖ ≤ ‖b ν‖ / 4 → ‖u ν z‖ ≤ (2⁻¹ : ℝ) ^ ν)
    (hu_an : ∀ ν z, z ≠ b ν → AnalyticAt ℂ (u ν) z) (z₀ : ℂ) :
    ∀ᶠ N in atTop, AnalyticAt ℂ (fun z ↦ ∑' k, u (k + N) z) z₀ := by
  obtain ⟨R, hR0, hz₀R⟩ : ∃ R : ℝ, 0 < R ∧ ‖z₀‖ < R := ⟨‖z₀‖ + 1, by positivity, lt_add_one _⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hb.eventually_ge_atTop (4 * R))
  filter_upwards [eventually_ge_atTop N₀] with N hN
  -- on `ball 0 R` the tail terms satisfy the bound and have no poles
  have hfar : ∀ k, ∀ w ∈ Metric.ball (0 : ℂ) R, ‖w‖ < R ∧ 4 * R ≤ ‖b (k + N)‖ := fun k w hw ↦
    ⟨by simpa using hw, hN₀ (k + N) (by omega)⟩
  refine DifferentiableOn.analyticAt ?_ (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz₀R))
  refine differentiableOn_tsum_of_summable_norm
    ((summable_nat_add_iff N).2
      (summable_geometric_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num) (by norm_num)))
    (fun k w hw ↦ ?_) Metric.isOpen_ball
    (fun k w hw ↦ hu _ w (by linarith [(hfar k w hw).1, (hfar k w hw).2]))
  refine (hu_an _ w fun h ↦ ?_).differentiableAt.differentiableWithinAt
  obtain ⟨hw, hbw⟩ := hfar k w hw
  rw [← h] at hbw
  linarith

/-- Near any point, a sequence tending to `∞` meets no point other than that one. -/
private lemma eventually_notMem_range {b : ℕ → ℂ} (hb : Tendsto (fun ν ↦ ‖b ν‖) atTop atTop)
    (z₀ : ℂ) : ∀ᶠ z in 𝓝[≠] z₀, z ∉ range b := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hb.eventually_gt_atTop (‖z₀‖ + 1))
  have hnear : ∀ᶠ z in 𝓝[≠] z₀, ∀ ν ∈ Finset.range N, z ≠ b ν := by
    rw [eventually_all_finset]
    intro ν _
    rcases eq_or_ne (b ν) z₀ with h | h
    · rw [h]
      exact self_mem_nhdsWithin
    · exact eventually_ne_nhdsWithin h.symm
  have hball : ∀ᶠ z in 𝓝[≠] z₀, ‖z‖ < ‖z₀‖ + 1 := eventually_nhdsWithin_of_eventually_nhds
    (continuous_norm.continuousAt.eventually_lt continuousAt_const (lt_add_one _))
  filter_upwards [hnear, hball] with z hz hz'
  rintro ⟨ν, rfl⟩
  rcases lt_or_ge ν N with hν | hν
  · exact hz ν (Finset.mem_range.2 hν) rfl
  · linarith [hN ν hν]

/-- If `h = ψ` on a punctured neighbourhood of `z` and `ψ` is continuous at `z`, then the punctured
limit of `h` at `z` is `ψ z`. -/
private lemma limUnder_nhdsNE_eq {h ψ : ℂ → ℂ} {z : ℂ} (hψ : ContinuousAt ψ z)
    (hhψ : h =ᶠ[𝓝[≠] z] ψ) : limUnder (𝓝[≠] z) h = ψ z :=
  ((hψ.tendsto.mono_left nhdsWithin_le_nhds).congr' hhψ.symm).limUnder_eq

/-- Removable singularities: if near every point `h` agrees, off that point, with a function
analytic there, then `z ↦ limUnder (𝓝[≠] z) h` is entire. -/
private lemma differentiable_limUnder_nhdsNE {h : ℂ → ℂ}
    (hh : ∀ z₀, ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z₀ ∧ h =ᶠ[𝓝[≠] z₀] ψ) :
    Differentiable ℂ fun z ↦ limUnder (𝓝[≠] z) h := by
  intro z₀
  obtain ⟨ψ, hψ, hhψ⟩ := hh z₀
  refine (hψ.congr ?_).differentiableAt
  have hpunct : ∀ᶠ z in 𝓝 z₀, z ≠ z₀ → h =ᶠ[𝓝 z] ψ := by
    filter_upwards [(eventually_nhdsWithin_iff.1 hhψ).eventually_nhds] with z hz hne
    filter_upwards [hz, eventually_ne_nhds hne] with w hw hw' using hw hw'
  filter_upwards [hpunct, hψ.eventually_analyticAt] with z hz hzψ
  rcases eq_or_ne z z₀ with rfl | hne
  · exact (limUnder_nhdsNE_eq hψ.continuousAt hhψ).symm
  · exact (limUnder_nhdsNE_eq hzψ.continuousAt (nhdsWithin_le_nhds (hz hne))).symm

/-- **Mittag-Leffler's theorem.** Let `b ν` be distinct points of `ℂ` with `‖b ν‖ → ∞` and let
`P ν` be polynomials. Then

* some `f` is meromorphic on `ℂ`, analytic off `range b`, and has singular part
  `(P ν).eval (z - b ν)⁻¹` at each `b ν`, i.e. `f - (P ν).eval (· - b ν)⁻¹` is, on a punctured
  neighbourhood of `b ν`, a function analytic at `b ν`;
* for suitable polynomials `p ν` (depending only on `b` and `P`), the functions of this kind are
  exactly those with `f z = g z + ∑ ν, ((P ν).eval (z - b ν)⁻¹ - (p ν).eval z)` for `z ∉ range b`,
  the series converging, with `g` entire.

A constant term of `P ν` contributes nothing singular and is absorbed into `g`; the textbook
statement, for `P ν` without constant term, is `Complex.mittag_leffler_of_coeff_zero_eq_zero`. -/
public theorem mittag_leffler {b : ℕ → ℂ} (hb_inj : Function.Injective b)
    (hb : Tendsto (fun ν ↦ ‖b ν‖) atTop atTop) (P : ℕ → ℂ[X]) :
    (∃ f : ℂ → ℂ, Meromorphic f ∧ (∀ z ∉ range b, AnalyticAt ℂ f z) ∧
      ∀ ν, ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ (b ν) ∧
        ∀ᶠ z in 𝓝[≠] b ν, f z = (P ν).eval (z - b ν)⁻¹ + φ z) ∧
    ∃ p : ℕ → ℂ[X], ∀ f : ℂ → ℂ,
      (Meromorphic f ∧ (∀ z ∉ range b, AnalyticAt ℂ f z) ∧
        ∀ ν, ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ (b ν) ∧
          ∀ᶠ z in 𝓝[≠] b ν, f z = (P ν).eval (z - b ν)⁻¹ + φ z) ↔
      ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
        ∀ z ∉ range b, HasSum (fun ν ↦ (P ν).eval (z - b ν)⁻¹ - (p ν).eval z) (f z - g z) := by
  obtain ⟨p, hp⟩ := exists_polynomials_approx b P
  -- `s ν` is the prescribed singular part, `u ν` the corrected term, `F` the Mittag-Leffler series
  set s : ℕ → ℂ → ℂ := fun ν z ↦ (P ν).eval (z - b ν)⁻¹
  set u : ℕ → ℂ → ℂ := fun ν z ↦ s ν z - (p ν).eval z with hu
  have hu_an : ∀ ν z, z ≠ b ν → AnalyticAt ℂ (u ν) z := fun ν z hz ↦
    (analyticAt_eval_inv_sub (P ν) hz).fun_sub ((p ν).differentiable.analyticAt z)
  have hsum : ∀ z, Summable fun ν ↦ u ν z := summable_of_approx hb hp
  set F : ℂ → ℂ := fun z ↦ ∑' ν, u ν z with hF
  have hFsplit : ∀ N z, F z = ∑ ν ∈ Finset.range N, u ν z + ∑' k, u (k + N) z :=
    fun N z ↦ ((hsum z).sum_add_tsum_nat_add N).symm
  have hFan : ∀ z₀ ∉ range b, AnalyticAt ℂ F z₀ := by
    intro z₀ hz₀
    obtain ⟨N, hN⟩ := (eventually_analyticAt_tsum_nat_add hb hp hu_an z₀).exists
    refine AnalyticAt.congr ?_ (Eventually.of_forall fun z ↦ (hFsplit N z).symm)
    refine (Finset.analyticAt_fun_sum _ fun ν _ ↦ hu_an ν z₀ ?_).fun_add hN
    rintro rfl
    exact hz₀ ⟨ν, rfl⟩
  have hFsing : ∀ n, AnalyticAt ℂ (fun z ↦ F z - s n z) (b n) := by
    intro n
    obtain ⟨N, hN, hnN⟩ := ((eventually_analyticAt_tsum_nat_add hb hp hu_an (b n)).and
      (eventually_gt_atTop n)).exists
    have hn : n ∈ Finset.range N := Finset.mem_range.2 hnN
    refine AnalyticAt.congr (f := fun z ↦ ∑ ν ∈ (Finset.range N).erase n, u ν z - (p n).eval z +
      ∑' k, u (k + N) z) ?_ (Eventually.of_forall fun z ↦ ?_)
    · refine ((Finset.analyticAt_fun_sum _ fun ν hν ↦ hu_an ν (b n) fun h ↦ ?_).fun_sub
        ((p n).differentiable.analyticAt _)).fun_add hN
      exact Finset.ne_of_mem_erase hν (hb_inj h).symm
    · simp only [hFsplit N z, ← Finset.add_sum_erase _ _ hn, hu]
      ring
  have key : ∀ f : ℂ → ℂ,
      (Meromorphic f ∧ (∀ z ∉ range b, AnalyticAt ℂ f z) ∧
        ∀ ν, ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ (b ν) ∧ ∀ᶠ z in 𝓝[≠] b ν, f z = s ν z + φ z) ↔
      ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z ∉ range b, HasSum (fun ν ↦ u ν z) (f z - g z) := by
    intro f
    constructor
    · rintro ⟨-, hfan, hfsing⟩
      -- `f - F` has only removable singularities
      have hh : ∀ z₀, ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z₀ ∧ (fun z ↦ f z - F z) =ᶠ[𝓝[≠] z₀] ψ := by
        intro z₀
        by_cases hz₀ : z₀ ∈ range b
        · obtain ⟨n, rfl⟩ := hz₀
          obtain ⟨φ, hφ, hfφ⟩ := hfsing n
          refine ⟨fun z ↦ φ z - (F z - s n z), hφ.fun_sub (hFsing n), hfφ.mono fun z hz ↦ ?_⟩
          simp only [hz]
          ring
        · exact ⟨_, (hfan z₀ hz₀).fun_sub (hFan z₀ hz₀), EventuallyEq.rfl⟩
      refine ⟨fun z ↦ limUnder (𝓝[≠] z) fun w ↦ f w - F w, differentiable_limUnder_nhdsNE hh,
        fun z hz ↦ ?_⟩
      have hlim : limUnder (𝓝[≠] z) (fun w ↦ f w - F w) = f z - F z :=
        limUnder_nhdsNE_eq ((hfan z hz).fun_sub (hFan z hz)).continuousAt EventuallyEq.rfl
      simp only [hlim, sub_sub_cancel]
      exact (hsum z).hasSum
    · rintro ⟨g, hg, hfg⟩
      have hfF : ∀ z ∉ range b, f z = g z + F z := fun z hz ↦ by
        rw [hF]
        dsimp only
        rw [(hfg z hz).tsum_eq]
        ring
      have hfan : ∀ z ∉ range b, AnalyticAt ℂ f z := by
        intro z₀ hz₀
        refine ((hg.analyticAt z₀).fun_add (hFan z₀ hz₀)).congr ?_
        have hnear : ∀ᶠ z in 𝓝 z₀, z ∉ range b := by
          rw [← nhdsNE_sup_pure, eventually_sup, eventually_pure]
          exact ⟨eventually_notMem_range hb z₀, hz₀⟩
        filter_upwards [hnear] with z hz using (hfF z hz).symm
      have hfsing : ∀ ν, ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ (b ν) ∧
          ∀ᶠ z in 𝓝[≠] b ν, f z = s ν z + φ z := by
        intro n
        refine ⟨fun z ↦ g z + (F z - s n z), (hg.analyticAt _).fun_add (hFsing n), ?_⟩
        filter_upwards [eventually_notMem_range hb (b n)] with z hz
        rw [hfF z hz]
        ring
      refine ⟨fun z₀ ↦ ?_, hfan, hfsing⟩
      by_cases hz₀ : z₀ ∈ range b
      · obtain ⟨n, rfl⟩ := hz₀
        obtain ⟨φ, hφ, hfφ⟩ := hfsing n
        exact ((meromorphicAt_eval_inv_sub (P n) (b n)).fun_add hφ.meromorphicAt).congr
          (EventuallyEq.symm hfφ)
      · exact (hfan z₀ hz₀).meromorphicAt
  refine ⟨⟨F, (key F).2 ⟨0, differentiable_const 0, fun z _ ↦ ?_⟩⟩, p, key⟩
  rw [Pi.zero_apply, sub_zero]
  exact (hsum z).hasSum

/-- **Mittag-Leffler's theorem** as stated in the source (Ahlfors): `Complex.mittag_leffler` for
polynomials `P ν` without constant term.

The source assumes the `b ν` distinct without saying so (`hb_inj`). The hypothesis `_hP` is the
source's normalization making `P ν (1 / (z - b ν))` a genuine singular part; the theorem holds
without it (a constant term is absorbed into `g`), which is `Complex.mittag_leffler`. -/
public theorem mittag_leffler_of_coeff_zero_eq_zero {b : ℕ → ℂ} (hb_inj : Function.Injective b)
    (hb : Tendsto (fun ν ↦ ‖b ν‖) atTop atTop) (P : ℕ → ℂ[X])
    (_hP : ∀ ν, (P ν).coeff 0 = 0) :
    (∃ f : ℂ → ℂ, Meromorphic f ∧ (∀ z ∉ range b, AnalyticAt ℂ f z) ∧
      ∀ ν, ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ (b ν) ∧
        ∀ᶠ z in 𝓝[≠] b ν, f z = (P ν).eval (z - b ν)⁻¹ + φ z) ∧
    ∃ p : ℕ → ℂ[X], ∀ f : ℂ → ℂ,
      (Meromorphic f ∧ (∀ z ∉ range b, AnalyticAt ℂ f z) ∧
        ∀ ν, ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ (b ν) ∧
          ∀ᶠ z in 𝓝[≠] b ν, f z = (P ν).eval (z - b ν)⁻¹ + φ z) ↔
      ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
        ∀ z ∉ range b, HasSum (fun ν ↦ (P ν).eval (z - b ν)⁻¹ - (p ν).eval z) (f z - g z) :=
  mittag_leffler hb_inj hb P

end Complex
