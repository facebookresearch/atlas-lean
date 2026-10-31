/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 6

The convergent-series extension `F(x) = ∑_{k ≥ 1} f(k) - ∑_{k ≥ 1} f(k + x)` of the partial sums
of `f` satisfies `F(x) - F(x - 1) = f(x)` and agrees with the partial sums at natural numbers. Under
domination hypotheses its derivatives at `0` are `-∑_{k ≥ 1} f⁽ⁿ⁾(k)`, and when `F` is analytic at
`0` its Taylor series converges to it near `0`.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch6

namespace Entry6Harmonic

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology

noncomputable section

/-- **Terms of the shifted derivative series.** For $f : \mathbb{R} \to \mathbb{R}$, natural numbers
$q$ and $k$, and $x \in \mathbb{R}$, the $k$-th term of the shifted series of $q$-th derivatives of
$f$ is $f^{(q)}(k + 1 + x)$, where $f^{(q)}$ is the $q$-th iterated derivative of $f$ and a
derivative that does not exist is taken to be $0$. -/
def chapter6ShiftedDerivedSeriesTerm
    (f : ℝ → ℝ) (q : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  iteratedDeriv q f ((k : ℝ) + 1 + x)

/-- **Ramanujan's derivative-series constants.** For $f : \mathbb{R} \to \mathbb{R}$ and a natural
number $q$, the constant $c_q$ is $\sum_{k \ge 1} f^{(q)}(k)$, the sum of the values of the
$q$-th iterated derivative of $f$ at the positive integers, where a derivative that does not
exist is taken to be $0$ and a series that is not summable is given the value $0$. -/
def chapter6DerivedSeriesConstant (f : ℝ → ℝ) (q : ℕ) : ℝ :=
  ∑' k : ℕ, chapter6ShiftedDerivedSeriesTerm f q 0 k

/-- **Ramanujan's extension of partial sums.** For $f : \mathbb{R} \to \mathbb{R}$, the extension of
the partial sums of $f$ to real arguments is the function
$F(x) = \sum_{k \ge 1} f(k) - \sum_{k \ge 1} f(k + x)$ on $\mathbb{R}$, where each series is an
unconditional sum and a series that is not summable is given the value $0$.

When $\sum_{k \ge 1} f(k)$ is summable, $F(m) = f(1) + \cdots + f(m)$ for every natural number
$m$. -/
def chapter6ConvergentSumExtension (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  chapter6DerivedSeriesConstant f 0 -
    ∑' k : ℕ, chapter6ShiftedDerivedSeriesTerm f 0 x k

/-- **Terms of the Taylor series in Entry 6.** For $f : \mathbb{R} \to \mathbb{R}$,
$x \in \mathbb{R}$ and a natural number $j$, the $j$-th term is $-c_{j+1} x^{j+1} / (j+1)!$, where
$c_q = \sum_{k \ge 1} f^{(q)}(k)$ with $f^{(q)}$ the $q$-th iterated derivative of $f$; a
derivative that does not exist is taken to be $0$ and a series that is not summable is given the
value $0$.

Under the smoothness, summability and domination hypotheses of Entry 6, these are the
nonconstant terms of the Taylor series at $0$ of Ramanujan's extension
$F(x) = \sum_{k \ge 1} f(k) - \sum_{k \ge 1} f(k + x)$, whose constant term is $F(0) = 0$. -/
def chapter6Entry6Term
    (f : ℝ → ℝ) (x : ℝ) (j : ℕ) : ℝ :=
  -chapter6DerivedSeriesConstant f (j + 1) * x ^ (j + 1) /
    ((j + 1).factorial : ℝ)

/-- **Partial sums of a real function over the positive integers.** For
$f : \mathbb{R} \to \mathbb{R}$ and a natural number $n$, the partial sum is
$f(1) + f(2) + \cdots + f(n)$, which is $0$ when $n = 0$. -/
def chapter6PartialSum (f : ℝ → ℝ) (x : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 x, f k

@[simp]
theorem chapter6PartialSum_zero (f : ℝ → ℝ) : chapter6PartialSum f 0 = 0 := by
  simp [chapter6PartialSum]

@[simp]
theorem chapter6PartialSum_succ (f : ℝ → ℝ) (m : ℕ) :
    chapter6PartialSum f (m + 1) = chapter6PartialSum f m + f (m + 1) := by
  simp only [chapter6PartialSum]
  rw [Finset.sum_Icc_succ_top (by omega)]
  push_cast
  rfl

/-- `chapter6DerivedSeriesConstant f q` is the sum of its series when that series converges. -/
theorem hasSum_chapter6DerivedSeriesConstant (f : ℝ → ℝ) (q : ℕ)
    (h : Summable (chapter6ShiftedDerivedSeriesTerm f q 0)) :
    HasSum (chapter6ShiftedDerivedSeriesTerm f q 0) (chapter6DerivedSeriesConstant f q) := by
  simpa [chapter6DerivedSeriesConstant] using h.hasSum

@[simp]
theorem chapter6ConvergentSumExtension_zero (f : ℝ → ℝ) :
    chapter6ConvergentSumExtension f 0 = 0 := by
  unfold chapter6ConvergentSumExtension chapter6DerivedSeriesConstant
  exact sub_self _

/-- **Difference equation for Ramanujan's extension.** Let $f : \mathbb{R} \to \mathbb{R}$ and let
$F(y) = \sum_{k \ge 1} f(k) - \sum_{k \ge 1} f(k + y)$, where a series that is not summable is
given the value $0$. If $x \in \mathbb{R}$ and the series $\sum_{k \ge 0} f(k + x)$ is summable,
then $F(x) - F(x - 1) = f(x)$. -/
theorem chapter6ConvergentSumExtension_sub_sub_one (f : ℝ → ℝ) (x : ℝ)
    (h : Summable (chapter6ShiftedDerivedSeriesTerm f 0 (x - 1))) :
    chapter6ConvergentSumExtension f x - chapter6ConvergentSumExtension f (x - 1) = f x := by
  have e1 : ∀ k : ℕ, chapter6ShiftedDerivedSeriesTerm f 0 (x - 1) k =
      f ((k : ℝ) + x) := by
    intro k
    change iteratedDeriv 0 f _ = _
    rw [show (k : ℝ) + 1 + (x - 1) = (k : ℝ) + x from by ring,
      iteratedDeriv_zero]
  have e2' : ∀ k : ℕ, chapter6ShiftedDerivedSeriesTerm f 0 x k =
      f (((k + 1 : ℕ) : ℝ) + x) := by
    intro k
    change iteratedDeriv 0 f _ = _
    rw [iteratedDeriv_zero]
    simp only [Nat.cast_add, Nat.cast_one]
  have hS1 : (∑' k : ℕ, chapter6ShiftedDerivedSeriesTerm f 0 (x - 1) k) =
      ∑' k : ℕ, f ((k : ℝ) + x) := tsum_congr e1
  have hS2 : (∑' k : ℕ, chapter6ShiftedDerivedSeriesTerm f 0 x k) =
      ∑' k : ℕ, f (((k + 1 : ℕ) : ℝ) + x) := tsum_congr e2'
  have hgsum : Summable (fun k : ℕ => f ((k : ℝ) + x)) :=
    (summable_congr e1).mp h
  have hdecomp : (∑' k : ℕ, f ((k : ℝ) + x)) =
      f (((0 : ℕ) : ℝ) + x) + (∑' k : ℕ, f (((k + 1 : ℕ) : ℝ) + x)) :=
    hgsum.tsum_eq_zero_add
  have hf0 : f (((0 : ℕ) : ℝ) + x) = f x := by simp
  simp only [chapter6ConvergentSumExtension]
  rw [hS1, hS2, hdecomp, hf0]
  ring

/-- **Tails of the shifted series of derivatives converge.** Let $f : \mathbb{R} \to \mathbb{R}$
and $q \in \mathbb{N}$, and write $f^{(q)}$ for the $q$-th iterated derivative of $f$, where a
derivative that does not exist is taken to be $0$. If the series
$\sum_{k \ge 0} f^{(q)}(k + 1)$ converges absolutely, then for every $m \in \mathbb{N}$ the series
$\sum_{k \ge 0} f^{(q)}(k + 1 + m)$ converges absolutely.

The second series is the $m$-th tail of the first. -/
theorem summable_chapter6ShiftedDerivedSeriesTerm_natCast (f : ℝ → ℝ) (q : ℕ)
    (h : Summable (chapter6ShiftedDerivedSeriesTerm f q 0)) (m : ℕ) :
    Summable (chapter6ShiftedDerivedSeriesTerm f q m) := by
  refine ((summable_nat_add_iff m).mpr h).congr fun k => ?_
  simp only [chapter6ShiftedDerivedSeriesTerm]
  congr 1
  push_cast
  ring

/-- **Ramanujan's extension agrees with the partial sums at natural numbers.** Let
$f : \mathbb{R} \to \mathbb{R}$ and let $F(x) = \sum_{k \ge 1} f(k) - \sum_{k \ge 1} f(k + x)$,
where a series that is not summable is given the value $0$. If the series
$\sum_{k \ge 1} f(k)$ is summable, then $F(m) = f(1) + f(2) + \cdots + f(m)$ for every natural
number $m$ (for $m = 0$ the right side is the empty sum $0$). -/
theorem chapter6ConvergentSumExtension_natCast (f : ℝ → ℝ)
    (h : Summable (chapter6ShiftedDerivedSeriesTerm f 0 0)) (m : ℕ) :
    chapter6ConvergentSumExtension f m = chapter6PartialSum f m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hcast : (((m + 1 : ℕ) : ℝ) - 1) = m := by push_cast; ring
    have h3m := chapter6ConvergentSumExtension_sub_sub_one f ((m + 1 : ℕ) : ℝ) (hcast ▸ summable_chapter6ShiftedDerivedSeriesTerm_natCast f 0 h m)
    rw [hcast] at h3m
    rw [chapter6PartialSum_succ, ← ih]
    push_cast at h3m ⊢
    linarith

/-- Each shifted term is smooth in `x`, with derivative the next order term. -/
private theorem hasDerivAt_chapter6ShiftedDerivedSeriesTerm {f : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ∞ f) (q k : ℕ) (y : ℝ) :
    HasDerivAt (fun z => chapter6ShiftedDerivedSeriesTerm f q z k)
      (chapter6ShiftedDerivedSeriesTerm f (q + 1) y k) y := by
  simp only [chapter6ShiftedDerivedSeriesTerm]
  have hdiff : DifferentiableAt ℝ (iteratedDeriv q f) ((k : ℝ) + 1 + y) :=
    (hsmooth.differentiable_iteratedDeriv q
      (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top _))).differentiableAt
  have hinner : HasDerivAt (fun z : ℝ => (k : ℝ) + 1 + z) 1 y :=
    (hasDerivAt_id y).const_add _
  have hcomp := hdiff.hasDerivAt.comp y hinner
  simp only [Function.comp_def] at hcomp
  have hderiv_eq : deriv (iteratedDeriv q f) ((k : ℝ) + 1 + y) =
      iteratedDeriv (q + 1) f ((k : ℝ) + 1 + y) :=
    congrFun iteratedDeriv_succ.symm _
  rw [hderiv_eq, mul_one] at hcomp
  exact hcomp

/-- Term-by-term derivative of the shifted sums on the open interval. -/
private theorem hasDerivAt_tsum_chapter6ShiftedDerivedSeriesTerm {f : ℝ → ℝ} {rho : ℝ}
    (hsmooth : ContDiff ℝ ∞ f)
    (hsummable : ∀ q : ℕ, Summable (chapter6ShiftedDerivedSeriesTerm f q 0))
    (hdominated : ∀ q : ℕ, 0 < q → ∃ bound : ℕ → ℝ,
      Summable bound ∧
        ∀ x ∈ Set.Icc (-rho) rho, ∀ k : ℕ,
          |chapter6ShiftedDerivedSeriesTerm f q x k| ≤ bound k)
    (q : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (-rho) rho) :
    HasDerivAt (fun z => ∑' k : ℕ, chapter6ShiftedDerivedSeriesTerm f q z k)
      (∑' k : ℕ, chapter6ShiftedDerivedSeriesTerm f (q + 1) y k) y := by
  obtain ⟨bound, hbound_sum, hbound_le⟩ := hdominated (q + 1) q.succ_pos
  refine hasDerivAt_tsum_of_isPreconnected (t := Set.Ioo (-rho) rho) hbound_sum
    isOpen_Ioo isPreconnected_Ioo
    (fun k z _ => hasDerivAt_chapter6ShiftedDerivedSeriesTerm hsmooth q k z) ?_
    ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩ (hsummable q) hy
  intro k z hz
  have hzIcc : z ∈ Set.Icc (-rho) rho := Set.Ioo_subset_Icc_self hz
  have h := hbound_le z hzIcc k
  rwa [Real.norm_eq_abs]

/-- Iterated derivatives of the extension on the open interval. -/
private theorem iteratedDeriv_succ_chapter6ConvergentSumExtension {f : ℝ → ℝ} {rho : ℝ}
    (hsmooth : ContDiff ℝ ∞ f)
    (hsummable : ∀ q : ℕ, Summable (chapter6ShiftedDerivedSeriesTerm f q 0))
    (hdominated : ∀ q : ℕ, 0 < q → ∃ bound : ℕ → ℝ,
      Summable bound ∧
        ∀ x ∈ Set.Icc (-rho) rho, ∀ k : ℕ,
          |chapter6ShiftedDerivedSeriesTerm f q x k| ≤ bound k)
    (n : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (-rho) rho) :
    iteratedDeriv (n + 1) (chapter6ConvergentSumExtension f) y =
      -(∑' k : ℕ, chapter6ShiftedDerivedSeriesTerm f (n + 1) y k) := by
  have hS_deriv := hasDerivAt_tsum_chapter6ShiftedDerivedSeriesTerm hsmooth hsummable hdominated
  induction n generalizing y with
  | zero =>
    rw [iteratedDeriv_succ, iteratedDeriv_zero]
    have hder := ((hasDerivAt_const y (chapter6DerivedSeriesConstant f 0)).sub
      (hS_deriv 0 y hy)).deriv
    rw [zero_sub] at hder
    exact hder
  | succ n ih =>
    have hnext := hS_deriv (n + 1) y hy
    have hneg : HasDerivAt
        (fun x => -(∑' k : ℕ, chapter6ShiftedDerivedSeriesTerm f (n + 1) x k))
        (-(∑' k : ℕ, chapter6ShiftedDerivedSeriesTerm f (n + 1 + 1) y k))
        y := hnext.neg
    have hmem : Set.Ioo (-rho) rho ∈ nhds y := isOpen_Ioo.mem_nhds hy
    have heq : (iteratedDeriv (n + 1) (chapter6ConvergentSumExtension f)) =ᶠ[nhds y]
        (fun x => -(∑' k : ℕ, chapter6ShiftedDerivedSeriesTerm f (n + 1) x k)) := by
      filter_upwards [hmem] with z hz
      exact ih z hz
    have htrans := hneg.congr_of_eventuallyEq heq
    have hrr : iteratedDeriv (n + 1 + 1) (chapter6ConvergentSumExtension f) y =
        deriv (iteratedDeriv (n + 1) (chapter6ConvergentSumExtension f)) y :=
      congrFun iteratedDeriv_succ y
    rw [hrr]
    exact htrans.deriv

/-- **Derivatives of Ramanujan's extension at the origin.** Let $f : \mathbb{R} \to \mathbb{R}$ be
infinitely differentiable and let $\rho > 0$. Write $c_q = \sum_{k \ge 1} f^{(q)}(k)$ and
$F(x) = c_0 - \sum_{k \ge 1} f(k + x)$, where a series that is not summable is given the value
$0$. Suppose that the series $\sum_{k \ge 1} f^{(q)}(k)$ is summable for every $q \ge 0$, and
that for every $q \ge 1$ there is a summable sequence $(b_k)_{k \ge 0}$ with
$|f^{(q)}(k + 1 + x)| \le b_k$ for all $x \in [-\rho, \rho]$ and all $k \ge 0$. Then
$F^{(n)}(0) = -c_n$ for every natural number $n \ge 1$. -/
theorem iteratedDeriv_chapter6ConvergentSumExtension_apply_zero (f : ℝ → ℝ) (rho : ℝ)
    (hrho : 0 < rho) (hsmooth : ContDiff ℝ ∞ f)
    (hsummable : ∀ q : ℕ, Summable (chapter6ShiftedDerivedSeriesTerm f q 0))
    (hdominated : ∀ q : ℕ, 0 < q → ∃ bound : ℕ → ℝ,
      Summable bound ∧
        ∀ x ∈ Set.Icc (-rho) rho, ∀ k : ℕ,
          |chapter6ShiftedDerivedSeriesTerm f q x k| ≤ bound k)
    (n : ℕ) (hn : 0 < n) :
    iteratedDeriv n (chapter6ConvergentSumExtension f) 0 =
      -chapter6DerivedSeriesConstant f n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-rho) rho := ⟨by linarith, by linarith⟩
  rw [iteratedDeriv_succ_chapter6ConvergentSumExtension hsmooth hsummable hdominated m 0 h0mem]
  simp only [chapter6DerivedSeriesConstant]

/-- **Taylor expansion of Ramanujan's extension at the origin.** Let $f : \mathbb{R} \to \mathbb{R}$
be infinitely differentiable and let $\rho > 0$. Write $c_q = \sum_{k \ge 1} f^{(q)}(k)$ and
$F(x) = c_0 - \sum_{k \ge 1} f(k + x)$, where a series that is not summable is given the value
$0$. Suppose that the series $\sum_{k \ge 1} f^{(q)}(k)$ is summable for every $q \ge 0$, that
for every $q \ge 1$ there is a summable sequence $(b_k)_{k \ge 0}$ with
$|f^{(q)}(k + 1 + x)| \le b_k$ for all $x \in [-\rho, \rho]$ and all $k \ge 0$, and that $F$ is
analytic at $0$. Then there is $r$ with $0 < r \le \rho$ such that for every real $x$ with
$|x| < r$ the series $\sum_{j \ge 0} -c_{j+1} x^{j+1} / (j+1)!$ is summable with sum $F(x)$. -/
theorem exists_hasSum_chapter6Entry6Term (f : ℝ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (hsmooth : ContDiff ℝ ∞ f)
    (hsummable : ∀ q : ℕ, Summable (chapter6ShiftedDerivedSeriesTerm f q 0))
    (hdominated : ∀ q : ℕ, 0 < q → ∃ bound : ℕ → ℝ,
      Summable bound ∧
        ∀ x ∈ Set.Icc (-rho) rho, ∀ k : ℕ,
          |chapter6ShiftedDerivedSeriesTerm f q x k| ≤ bound k)
    (hanalytic : AnalyticAt ℝ (chapter6ConvergentSumExtension f) 0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ rho ∧ ∀ x : ℝ, |x| < r →
      HasSum (chapter6Entry6Term f x) (chapter6ConvergentSumExtension f x) := by
  have hfp : HasFPowerSeriesAt (chapter6ConvergentSumExtension f)
      (FormalMultilinearSeries.ofScalars ℝ fun n =>
        iteratedDeriv n (chapter6ConvergentSumExtension f) 0 / ↑n.factorial)
      0 :=
    hanalytic.hasFPowerSeriesAt
  have hev := hfp.eventually_hasSum_sub
  simp only [sub_zero] at hev
  obtain ⟨ε, hεpos, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨min ε rho, lt_min hεpos hrho, min_le_right _ _,
    fun x hx => ?_⟩
  have hxε : x ∈ Metric.ball (0 : ℝ) ε := by
    have hle : |x| < ε := lt_of_lt_of_le hx (min_le_left _ _)
    rw [Metric.mem_ball, dist_zero_right x, Real.norm_eq_abs]
    exact hle
  have htaylor := hball x hxε
  -- Clean form of the Taylor coefficients (no power-series machinery).
  have htaylor2 : HasSum (fun n =>
      (iteratedDeriv n (chapter6ConvergentSumExtension f) 0 /
        ↑n.factorial) • x ^ n)
      (chapter6ConvergentSumExtension f x) := by
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq] using htaylor
  have hT0 : (iteratedDeriv 0 (chapter6ConvergentSumExtension f) 0 /
      ↑(Nat.factorial 0)) • x ^ (0 : ℕ) = 0 := by
    simp [iteratedDeriv_zero]
  have hsum := htaylor2.summable
  have hshift := (summable_nat_add_iff 1).mpr hsum
  have hshift_sum : (∑' n,
      ((iteratedDeriv (n + 1) (chapter6ConvergentSumExtension f) 0 /
        ↑(n + 1).factorial) • x ^ (n + 1))) =
      chapter6ConvergentSumExtension f x := by
    have hdecomp := hsum.sum_add_tsum_nat_add 1
    rw [htaylor2.tsum_eq] at hdecomp
    simp only [Finset.sum_range_one, hT0, zero_add] at hdecomp
    exact hdecomp
  have hentry : ∀ j : ℕ, chapter6Entry6Term f x j =
      ((iteratedDeriv (j + 1) (chapter6ConvergentSumExtension f) 0 /
        ↑(j + 1).factorial) • x ^ (j + 1)) := by
    intro j
    have hderiv : iteratedDeriv (j + 1) (chapter6ConvergentSumExtension f) 0 =
        -chapter6DerivedSeriesConstant f (j + 1) :=
      iteratedDeriv_chapter6ConvergentSumExtension_apply_zero f rho hrho hsmooth hsummable
        hdominated (j + 1) (by omega)
    simp only [chapter6Entry6Term, hderiv, smul_eq_mul]
    ring
  have hfinal : HasSum (fun n =>
      ((iteratedDeriv (n + 1) (chapter6ConvergentSumExtension f) 0 /
        ↑(n + 1).factorial) • x ^ (n + 1)))
      (chapter6ConvergentSumExtension f x) := by
    rw [← hshift_sum]
    exact hshift.hasSum
  exact hfinal.congr_fun hentry

/-- **Ramanujan's extension of the partial sums of a smooth function.** Let
$f : \mathbb{R} \to \mathbb{R}$ be infinitely differentiable and let $\rho > 0$. Suppose that for
every $q \in \mathbb{N}$ and every $x \in \mathbb{R}$ the series
$\sum_{k \ge 0} f^{(q)}(k + 1 + x)$ converges absolutely, and that for every $q \in \mathbb{N}$
there is a summable sequence $(b_k)_{k \ge 0}$ with $|f^{(q)}(k + 1 + x)| \le b_k$ for all
$k \in \mathbb{N}$ and all $x \in [-\rho, \rho]$. Put $c_q = \sum_{k \ge 0} f^{(q)}(k + 1)$ and
$F(x) = c_0 - \sum_{k \ge 0} f(k + 1 + x)$, and suppose that $F$ is analytic at $0$. Then
(i) for every $n \in \mathbb{N}$ the series $\sum_{k \ge 0} f^{(n)}(k + 1)$ converges absolutely
with sum $c_n$; (ii) $F(0) = 0$; (iii) $F(x) - F(x - 1) = f(x)$ for every $x \in \mathbb{R}$;
(iv) $F(m) = f(1) + f(2) + \dots + f(m)$ for every $m \in \mathbb{N}$, the empty sum being $0$;
(v) $F^{(n)}(0) = -c_n$ for every integer $n \ge 1$; and (vi) there is $r$ with $0 < r \le \rho$
such that for every real $x$ with $|x| < r$ the series
$\sum_{j \ge 0} -c_{j+1} x^{j+1} / (j + 1)!$ converges absolutely with sum $F(x)$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 6.
Proves `Wanted` entry `ramanujan_part1_ch6_entry6_harmonic`.
-/
theorem ramanujan_part1_ch6_entry6_harmonic
    (f : ℝ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (hsmooth : ContDiff ℝ ∞ f)
    (hsummable : ∀ q : ℕ, ∀ x : ℝ,
      Summable (chapter6ShiftedDerivedSeriesTerm f q x))
    (hdominated : ∀ q : ℕ, ∃ bound : ℕ → ℝ,
      Summable bound ∧
        ∀ x ∈ Set.Icc (-rho) rho, ∀ k : ℕ,
          |chapter6ShiftedDerivedSeriesTerm f q x k| ≤ bound k)
    (hanalytic : AnalyticAt ℝ (chapter6ConvergentSumExtension f) 0) :
    (∀ n : ℕ, HasSum (chapter6ShiftedDerivedSeriesTerm f n 0)
      (chapter6DerivedSeriesConstant f n)) ∧
      chapter6ConvergentSumExtension f 0 = 0 ∧
      (∀ x : ℝ, chapter6ConvergentSumExtension f x -
        chapter6ConvergentSumExtension f (x - 1) = f x) ∧
      (∀ m : ℕ, chapter6ConvergentSumExtension f m = chapter6PartialSum f m) ∧
      (∀ n : ℕ, 0 < n →
        iteratedDeriv n (chapter6ConvergentSumExtension f) 0 =
          -chapter6DerivedSeriesConstant f n) ∧
      ∃ r : ℝ, 0 < r ∧ r ≤ rho ∧
        ∀ x : ℝ, |x| < r →
          HasSum (chapter6Entry6Term f x)
            (chapter6ConvergentSumExtension f x) := by
  exact ⟨fun n => hasSum_chapter6DerivedSeriesConstant f n (hsummable n 0),
    chapter6ConvergentSumExtension_zero f,
    fun x => chapter6ConvergentSumExtension_sub_sub_one f x (hsummable 0 (x - 1)),
    chapter6ConvergentSumExtension_natCast f (hsummable 0 0),
    iteratedDeriv_chapter6ConvergentSumExtension_apply_zero f rho hrho hsmooth
      (fun q => hsummable q 0) (fun q _ => hdominated q),
    exists_hasSum_chapter6Entry6Term f rho hrho hsmooth (fun q => hsummable q 0) (fun q _ => hdominated q)
      hanalytic⟩

end

end Entry6Harmonic

end MathlibExt.Analysis.Ramanujan.Part1Ch6
