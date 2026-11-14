/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch7PowerDifference
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Basic

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry9Bernoulligrowth

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

/-- uniform bound on `‖z ^ (r - 1)‖` for `z` in the half-plane `Re ≥ L`. -/
private theorem entry9_cpow_bound (z r : ℂ) (L c M : ℝ)
    (hL1 : 1 ≤ L) (hLz : L ≤ z.re) (hrec : r.re ≤ c) (hc0 : c ≤ 0)
    (hrM : ‖r‖ ≤ M) :
    ‖z ^ (r - 1)‖ ≤ Real.rpow L (c - 1) * Real.exp (Real.pi / 2 * M) := by
  have hre0 : 0 ≤ z.re := le_trans (by linarith) hLz
  have harg : |z.arg| ≤ Real.pi / 2 :=
    (Complex.abs_arg_le_pi_div_two_iff).mpr hre0
  have hIm : |(r - 1).im| ≤ M := by
    have h1 : (r - 1).im = r.im := by simp
    rw [h1]
    exact le_trans (Complex.abs_im_le_norm r) hrM
  have hne : z ≠ 0 := by
    intro h
    rw [h] at hLz
    simp at hLz
    linarith
  have hLpos : 0 < L := by linarith
  have hLnorm : L ≤ ‖z‖ := le_trans hLz (RCLike.re_le_norm z)
  have hre_r1 : (r - 1).re = r.re - 1 := by simp [Complex.sub_re]
  have step1 : ‖z ^ (r - 1)‖ ≤ ‖z‖ ^ (r - 1).re / Real.exp (z.arg * (r - 1).im) :=
    Complex.norm_cpow_le z (r - 1)
  have hexp : (1 : ℝ) / Real.exp (z.arg * (r - 1).im) ≤ Real.exp (Real.pi / 2 * M) := by
    have h1 : -(z.arg * (r - 1).im) ≤ Real.pi / 2 * M := by
      calc -(z.arg * (r - 1).im) ≤ |z.arg * (r - 1).im| := neg_le_abs _
        _ = |z.arg| * |(r - 1).im| := abs_mul _ _
        _ ≤ (Real.pi / 2) * M := by
            apply mul_le_mul harg hIm (abs_nonneg _) (by positivity)
        _ = Real.pi / 2 * M := by ring
    have h2 : (1 : ℝ) / Real.exp (z.arg * (r - 1).im) = Real.exp (-(z.arg * (r - 1).im)) := by
      rw [Real.exp_neg]; ring
    rw [h2]
    exact Real.exp_le_exp.mpr h1
  have hbase : (‖z‖ : ℝ) ^ (r - 1).re ≤ Real.rpow L (c - 1) := by
    have e1 : (‖z‖ : ℝ) ^ (r - 1).re ≤ L ^ (r - 1).re := by
      have hle : (r - 1).re ≤ 0 := by rw [hre_r1]; linarith
      exact Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < L) hLnorm hle
    have e2 : Real.rpow L (r - 1).re ≤ Real.rpow L (c - 1) := by
      apply Real.rpow_le_rpow_of_exponent_le hL1
      rw [hre_r1]
      linarith
    exact le_trans e1 e2
  calc ‖z ^ (r - 1)‖ ≤ ‖z‖ ^ (r - 1).re / Real.exp (z.arg * (r - 1).im) := step1
    _ = (‖z‖ ^ (r - 1).re) * (1 / Real.exp (z.arg * (r - 1).im)) := by ring
    _ ≤ Real.rpow L (c - 1) * Real.exp (Real.pi / 2 * M) := by
        apply mul_le_mul hbase hexp
        · apply div_nonneg (by norm_num) (le_of_lt (Real.exp_pos _))
        · exact Real.rpow_nonneg (le_of_lt hLpos) _

/-- uniform term bound from the mean value inequality on the half-plane. -/
private theorem entry9_term_bound (x r : ℂ) (J j : ℕ) (c M : ℝ)
    (hJ : ‖x‖ ≤ (J : ℝ)) (hjJ : J ≤ j) (hrec : r.re ≤ c) (hc0 : c ≤ 0)
    (hrM : ‖r‖ ≤ M) (hM0 : 0 ≤ M) :
    ‖((j + 1 : ℂ) ^ r - (((j + 1 : ℂ) + x) ^ r))‖ ≤
      M * ‖x‖ * Real.exp (Real.pi / 2 * M) * Real.rpow ((j : ℝ) + 1 - ‖x‖) (c - 1) := by
  set L : ℝ := (j : ℝ) + 1 - ‖x‖ with hLdef
  have hjJ' : (J : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjJ
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  have ha_re : ((j + 1 : ℂ)).re = (j : ℝ) + 1 := by
    simp [Complex.add_re, Complex.one_re, Complex.natCast_re]
  have hb_re : (((j + 1 : ℂ) + x)).re = (j : ℝ) + 1 + x.re := by
    simp [Complex.add_re, Complex.one_re, Complex.natCast_re]
  have hxlow : -‖x‖ ≤ x.re := neg_le_of_abs_le (abs_re_le_norm x)
  have ha_mem : ((j + 1 : ℂ)) ∈ ({c_ : ℂ | L ≤ c_.re} : Set ℂ) := by
    change L ≤ ((j + 1 : ℂ)).re
    rw [ha_re]; rw [hLdef]; linarith [norm_nonneg x]
  have hb_mem : (((j + 1 : ℂ) + x)) ∈ ({c_ : ℂ | L ≤ c_.re} : Set ℂ) := by
    change L ≤ ((((j + 1 : ℂ) + x))).re
    rw [hb_re]; rw [hLdef]; linarith
  have hconv : Convex ℝ ({c_ : ℂ | L ≤ c_.re} : Set ℂ) := convex_halfSpace_re_ge L
  have hdiff : ∀ z ∈ ({c_ : ℂ | L ≤ c_.re} : Set ℂ), DifferentiableAt ℂ (fun w : ℂ => w ^ r) z := by
    intro z hz
    have hzle : L ≤ z.re := hz
    have hzslit : z ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      linarith
    exact (Complex.hasStrictDerivAt_cpow_const hzslit).hasDerivAt.differentiableAt
  have hderiv : ∀ z ∈ ({c_ : ℂ | L ≤ c_.re} : Set ℂ),
      ‖deriv (fun w : ℂ => w ^ r) z‖ ≤ M * (Real.rpow L (c - 1) * Real.exp (Real.pi / 2 * M)) := by
    intro z hz
    have hzle : L ≤ z.re := hz
    have hzslit : z ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      linarith
    rw [Complex.deriv_cpow_const hzslit]
    calc ‖r * z ^ (r - 1)‖ = ‖r‖ * ‖z ^ (r - 1)‖ := norm_mul _ _
      _ ≤ M * (Real.rpow L (c - 1) * Real.exp (Real.pi / 2 * M)) := by
          apply mul_le_mul hrM (entry9_cpow_bound z r L c M hL1 hzle hrec hc0 hrM)
            (norm_nonneg _) hM0
  have hmvi := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hderiv hconv hb_mem ha_mem
  have hsub : ((((j + 1 : ℂ))) - (((j + 1 : ℂ) + x))) = -x := by ring
  rw [hsub, norm_neg] at hmvi
  calc ‖((j + 1 : ℂ) ^ r - (((j + 1 : ℂ) + x) ^ r))‖
        ≤ (M * (Real.rpow L (c - 1) * Real.exp (Real.pi / 2 * M))) * ‖x‖ := hmvi
    _ = M * ‖x‖ * Real.exp (Real.pi / 2 * M) * Real.rpow ((j : ℝ) + 1 - ‖x‖) (c - 1) := by
        rw [hLdef]; ring

/-- summability of the shifted real power series with exponent below `-1`. -/
private theorem entry9_majorant_summable (a c : ℝ) (ha : 1 ≤ a) (hc : c < 0) :
    Summable (fun n : ℕ => Real.rpow ((n : ℝ) + a) (c - 1)) := by
  have hs : (1 : ℝ) < 1 - c := by linarith
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / (|((n : ℝ) + a)| ^ (1 - c))) :=
    (Real.summable_one_div_nat_add_rpow a (1 - c)).mpr hs
  have heq : (fun n : ℕ => Real.rpow ((n : ℝ) + a) (c - 1)) =
      (fun n : ℕ => (1 : ℝ) / (|((n : ℝ) + a)| ^ (1 - c))) := by
    funext n
    have hpos : (0 : ℝ) < (n : ℝ) + a := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have habs : |((n : ℝ) + a)| = ((n : ℝ) + a) := abs_of_pos hpos
    have h1 : (c - 1 : ℝ) = -((1 : ℝ) - c) := by ring
    calc Real.rpow ((n : ℝ) + a) (c - 1)
        = Real.rpow ((n : ℝ) + a) (-((1 : ℝ) - c)) := by rw [← h1]
      _ = (Real.rpow ((n : ℝ) + a) (1 - c))⁻¹ := Real.rpow_neg (le_of_lt hpos) _
      _ = 1 / (|((n : ℝ) + a)| ^ (1 - c)) := by rw [habs, ← one_div]; rfl
  rw [heq]
  exact hsum

/-- each power-difference term is entire in `r` (bases are nonzero). -/
private theorem entry9_term_differentiable (x : ℂ) (hx : chapter7Admissible x) (j : ℕ) :
    Differentiable ℂ (fun r : ℂ => chapter7PowerDifferenceTerm r x j) := by
  have hb1 : ((j + 1 : ℂ)) ≠ 0 := by
    intro h
    have hre : ((j + 1 : ℂ)).re = (j : ℝ) + 1 := by
      simp [Complex.add_re, Complex.one_re, Complex.natCast_re]
    rw [h] at hre
    simp at hre
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hb2 : (((j + 1 : ℂ) + x)) ≠ 0 := hx j
  intro w
  have e1 : DifferentiableAt ℂ (fun r : ℂ => ((j + 1 : ℂ) ^ r)) w :=
    (differentiableAt_id).const_cpow (Or.inl hb1)
  have e2 : DifferentiableAt ℂ (fun r : ℂ => ((((j + 1 : ℂ) + x) ^ r))) w :=
    (differentiableAt_id).const_cpow (Or.inl hb2)
  have e := e1.sub e2
  have heq : (fun r : ℂ => chapter7PowerDifferenceTerm r x j) =
      (fun r : ℂ => ((j + 1 : ℂ) ^ r - (((j + 1 : ℂ) + x) ^ r))) := rfl
  rw [heq]
  exact e

/-- summability at a fixed `r` with `Re r < 0`, by comparison past `J`. -/
private theorem entry9_summable (x : ℂ) (_hx : chapter7Admissible x) (r : ℂ) (hr : r.re < 0) :
    Summable (chapter7PowerDifferenceTerm r x) := by
  obtain ⟨J, hJ⟩ := exists_nat_ge ‖x‖
  have hc0 : r.re ≤ 0 := le_of_lt hr
  have ha1 : (1 : ℝ) ≤ (J : ℝ) + 1 - ‖x‖ := by linarith
  set a : ℝ := (J : ℝ) + 1 - ‖x‖ with hadef
  set C : ℝ := ‖r‖ * ‖x‖ * Real.exp (Real.pi / 2 * ‖r‖) with hCdef
  have hbase : Summable (fun n : ℕ => Real.rpow ((n : ℝ) + a) (r.re - 1)) :=
    entry9_majorant_summable a r.re ha1 hr
  have hmajor : Summable (fun n : ℕ => C * Real.rpow ((n : ℝ) + a) (r.re - 1)) :=
    hbase.mul_left C
  have htail : Summable (fun n : ℕ => chapter7PowerDifferenceTerm r x (n + J)) := by
    apply Summable.of_norm_bounded hmajor
    intro n
    have hjJ : J ≤ n + J := Nat.le_add_left J n
    have hb := entry9_term_bound x r J (n + J) r.re ‖r‖ hJ hjJ le_rfl hc0 le_rfl (norm_nonneg r)
    have hL : ((((n + J : ℕ)) : ℝ) + 1 - ‖x‖) = (n : ℝ) + a := by
      push_cast
      rw [hadef]
      ring
    have hgoal_eq : chapter7PowerDifferenceTerm r x (n + J) =
        ((↑(n + J) + 1) ^ r - (↑(n + J) + 1 + x) ^ r) := rfl
    rw [hgoal_eq] at ⊢
    rw [hCdef] at ⊢
    rw [hL] at hb
    exact hb
  exact (summable_nat_add_iff J).mp htail

/-- **Convergence and holomorphy of the power-difference series.** Let $x$ be an admissible
complex number. For every complex $r$ with $\operatorname{Re} r < 0$ the series
$\sum_{j \ge 0} \bigl((j + 1)^r - (j + 1 + x)^r\bigr)$ (principal powers) is summable, and its
sum $\varphi_r(x)$ is a holomorphic function of $r$ on the half-plane $\operatorname{Re} r < 0$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7, Entry 9.
-/
theorem ramanujan_part1_ch7_entry9_bernoulligrowth
    (x : ℂ) (hx : chapter7Admissible x) :
    (∀ r : ℂ, r.re < 0 → Summable (chapter7PowerDifferenceTerm r x)) ∧
      DifferentiableOn ℂ (fun r : ℂ => chapter7PowerDifferenceSum r x)
        {r : ℂ | r.re < 0} := by
  have hsumm : ∀ r : ℂ, r.re < 0 → Summable (chapter7PowerDifferenceTerm r x) :=
    fun r hr => entry9_summable x hx r hr
  refine ⟨hsumm, ?_⟩
  intro r0 hr0
  have hr0neg : r0.re < 0 := hr0
  -- radius and uniform parameters
  set R : ℝ := -r0.re / 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  set c : ℝ := r0.re / 2 with hcdef
  have hcneg : c < 0 := by rw [hcdef]; linarith
  have hc0 : c ≤ 0 := le_of_lt hcneg
  set M : ℝ := ‖r0‖ + R with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; linarith [norm_nonneg r0, hRpos]
  obtain ⟨J, hJ⟩ := exists_nat_ge ‖x‖
  have ha1 : (1 : ℝ) ≤ (J : ℝ) + 1 - ‖x‖ := by linarith
  set a : ℝ := (J : ℝ) + 1 - ‖x‖ with hadef
  set C : ℝ := M * ‖x‖ * Real.exp (Real.pi / 2 * M) with hCdef
  set B : Set ℂ := Metric.ball r0 R with hBdef
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hr0B : r0 ∈ B := Metric.mem_ball_self hRpos
  have hBnhds : B ∈ nhds r0 := hBopen.mem_nhds hr0B
  -- every point of the ball satisfies the uniform bounds
  have hball_re : ∀ w ∈ B, w.re ≤ c := by
    intro w hw
    have hdist : dist w r0 < R := Metric.mem_ball.mp hw
    rw [dist_eq_norm] at hdist
    have h1 : (w - r0).re ≤ ‖w - r0‖ := Complex.re_le_norm _
    have h2 : (w - r0).re = w.re - r0.re := by simp [Complex.sub_re]
    rw [h2] at h1
    rw [hcdef]
    linarith
  have hball_norm : ∀ w ∈ B, ‖w‖ ≤ M := by
    intro w hw
    have hdist : dist w r0 < R := Metric.mem_ball.mp hw
    rw [dist_eq_norm] at hdist
    have h1 : ‖w‖ - ‖r0‖ ≤ ‖w - r0‖ := norm_sub_norm_le w r0
    rw [hMdef]
    linarith
  have hball_neg : ∀ w ∈ B, w.re < 0 := by
    intro w hw
    have hle := hball_re w hw
    linarith
  -- uniform majorant
  have hbase : Summable (fun n : ℕ => Real.rpow ((n : ℝ) + a) (c - 1)) :=
    entry9_majorant_summable a c ha1 hcneg
  have hmajor : Summable (fun n : ℕ => C * Real.rpow ((n : ℝ) + a) (c - 1)) :=
    hbase.mul_left C
  -- tail functions
  have hFdiff : ∀ n : ℕ, DifferentiableOn ℂ (fun w => chapter7PowerDifferenceTerm w x (n + J))
      B := by
    intro n
    exact (entry9_term_differentiable x hx (n + J)).differentiableOn
  have hFbound : ∀ n : ℕ, ∀ w ∈ B,
      ‖chapter7PowerDifferenceTerm w x (n + J)‖ ≤ C * Real.rpow ((n : ℝ) + a) (c - 1) := by
    intro n w hw
    have hjJ : J ≤ n + J := Nat.le_add_left J n
    have hb := entry9_term_bound x w J (n + J) c M hJ hjJ (hball_re w hw) hc0
      (hball_norm w hw) hM0
    have hL : ((((n + J : ℕ)) : ℝ) + 1 - ‖x‖) = (n : ℝ) + a := by
      push_cast
      rw [hadef]
      ring
    have hgoal_eq : chapter7PowerDifferenceTerm w x (n + J) =
        ((↑(n + J) + 1) ^ w - (↑(n + J) + 1 + x) ^ w) := rfl
    rw [hgoal_eq] at ⊢
    rw [hCdef] at ⊢
    rw [hL] at hb
    exact hb
  have htail_diff : DifferentiableOn ℂ (fun w => ∑' n : ℕ, chapter7PowerDifferenceTerm w x (n + J))
      B :=
    Complex.differentiableOn_tsum_of_summable_norm hmajor hFdiff hBopen hFbound
  -- head finite sum
  have hhead_diff : DifferentiableAt ℂ
      (fun w => ∑ j ∈ Finset.range J, chapter7PowerDifferenceTerm w x j) r0 :=
    DifferentiableAt.fun_sum (fun j _ => (entry9_term_differentiable x hx j) r0)
  have htail_at : DifferentiableAt ℂ (fun w => ∑' n : ℕ, chapter7PowerDifferenceTerm w x (n + J))
      r0 :=
    htail_diff.differentiableAt hBnhds
  have hsum_at : DifferentiableAt ℂ
      (fun w => (∑ j ∈ Finset.range J, chapter7PowerDifferenceTerm w x j) +
        ∑' n : ℕ, chapter7PowerDifferenceTerm w x (n + J)) r0 :=
    hhead_diff.add htail_at
  -- equality on the ball
  have heq_on : Set.EqOn (fun w => ∑' j : ℕ, chapter7PowerDifferenceTerm w x j)
      (fun w => (∑ j ∈ Finset.range J, chapter7PowerDifferenceTerm w x j) +
        ∑' n : ℕ, chapter7PowerDifferenceTerm w x (n + J)) B := by
    intro w hw
    have hsum_w : Summable (chapter7PowerDifferenceTerm w x) := hsumm w (hball_neg w hw)
    have hsplit := Summable.sum_add_tsum_nat_add J hsum_w
    exact hsplit.symm
  have hev : (fun w => ∑' j : ℕ, chapter7PowerDifferenceTerm w x j) =ᶠ[nhds r0]
      (fun w => (∑ j ∈ Finset.range J, chapter7PowerDifferenceTerm w x j) +
        ∑' n : ℕ, chapter7PowerDifferenceTerm w x (n + J)) :=
    heq_on.eventuallyEq_of_mem hBnhds
  have hAt : DifferentiableAt ℂ (fun w => ∑' j : ℕ, chapter7PowerDifferenceTerm w x j) r0 :=
    DifferentiableAt.congr_of_eventuallyEq hsum_at hev
  -- convert to the stated sum function
  have hAt2 : DifferentiableAt ℂ (fun r : ℂ => chapter7PowerDifferenceSum r x) r0 := hAt
  exact hAt2.differentiableWithinAt

end

/-- Compatibility alias for the former `Entry9Bernoulligrowth.chapter7Admissible`.

For new code, use `MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7Admissible` directly. -/
abbrev chapter7Admissible (x : ℂ) : Prop :=
  MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7Admissible x

/-- Compatibility alias for the former `Entry9Bernoulligrowth.chapter7PowerDifferenceTerm`.

For new code, use `MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceTerm`
directly. -/
noncomputable abbrev chapter7PowerDifferenceTerm (r x : ℂ) (j : ℕ) : ℂ :=
  MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceTerm r x j

/-- Compatibility alias for the former `Entry9Bernoulligrowth.chapter7PowerDifferenceSum`.

For new code, use `MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceSum`
directly. -/
noncomputable abbrev chapter7PowerDifferenceSum (r x : ℂ) : ℂ :=
  MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceSum r x

end Entry9Bernoulligrowth
end MathlibExt.Analysis.Ramanujan.Part1Ch7
end
