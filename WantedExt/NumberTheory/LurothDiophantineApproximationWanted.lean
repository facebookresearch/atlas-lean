/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import WantedExt.NumberTheory.LurothConsecutiveDigitsWanted

namespace MetaMathlibExt

open Filter MeasureTheory
open scoped ENNReal

@[expose] public section

/-! ### Classical well approximable numbers -/

/-- **Well approximable numbers.** For a function $\psi : \mathbb{N} \to \mathbb{R}$, the set
$W(\psi)$ of $\psi$-well approximable numbers consists of the real numbers $x \in [0, 1)$ such
that for infinitely many natural numbers $q$ there is an integer $p$ with
$|x - p/q| < \psi(q)/q$.

The fractions $p/q$ need not be in lowest terms, unlike Mathlib's well approximable sets,
which use points of exact additive order $q$. The value $\psi(0)$ is irrelevant.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (1). -/
public def wellApproximableSet (ψ : ℕ → ℝ) : Set ℝ :=
  {x | x ∈ Set.Ico 0 1 ∧ ∃ᶠ q : ℕ in atTop, ∃ p : ℤ, |x - p / q| < ψ q / q}

/-- **Well approximable numbers lie in $[0, 1)$.** For every function
$\psi : \mathbb{N} \to \mathbb{R}$, every point of the set $W(\psi)$ of $\psi$-well approximable
numbers lies in the interval $[0, 1)$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (1). -/
public theorem wellApproximableSet_subset_Ico (ψ : ℕ → ℝ) :
    wellApproximableSet ψ ⊆ Set.Ico 0 1 :=
  fun _ hx => hx.1

/-- **Lower order at infinity.** For $\psi : \mathbb{N} \to \mathbb{R}$, the lower order at infinity
of $1/\psi$ is
$$\tau_\psi = \liminf_{q \to \infty} \max\left(-\frac{\log \psi(q)}{\log q},\, 0\right),$$
with the liminf taken in $[0, \infty]$. Here $\log x$ means $\log |x|$ for $x \ne 0$ and
$\log 0 = 0$, and the ratio is read as $0$ when $\log q = 0$. For $\psi$ with values in $(0, 1]$
the ratio is nonnegative once $q \ge 2$, so the truncation at $0$ has no effect there, and
$\tau_\psi$ may be infinite.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (11). -/
public noncomputable def lowerOrderAtInfinity (ψ : ℕ → ℝ) : ℝ≥0∞ :=
  liminf (fun q : ℕ => ENNReal.ofReal (-Real.log (ψ q) / Real.log q)) atTop

/-- **Upper order at infinity.** For a function $\psi$ from the natural numbers to the reals, the
upper order at infinity of $\psi$ is the element
$$\bar\tau_\psi = \limsup_{q \to \infty} \max\left(0, \frac{-\log \psi(q)}{\log q}\right)$$
of $[0, \infty]$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (11). -/
public noncomputable def upperOrderAtInfinity (ψ : ℕ → ℝ) : ℝ≥0∞ :=
  limsup (fun q : ℕ => ENNReal.ofReal (-Real.log (ψ q) / Real.log q)) atTop

/-- **The order ratio of $q^{-\tau}$.** For every real $\tau$ and all sufficiently large natural
numbers $q$, $\max(0, -\log((q^{\tau})^{-1})/\log q) = \max(0, \tau)$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (11). -/
public theorem orderRatio_rpow_inv (τ : ℝ) :
    ∀ᶠ q : ℕ in atTop,
      ENNReal.ofReal (-Real.log (((q : ℝ) ^ τ)⁻¹) / Real.log q) = ENNReal.ofReal τ := by
  filter_upwards [eventually_ge_atTop 2] with q hq
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have hlog : Real.log q ≠ 0 := (Real.log_pos hq').ne'
  rw [Real.log_inv, Real.log_rpow (by linarith), neg_neg, mul_div_assoc, div_self hlog,
    mul_one]

/-- **Lower order at infinity of a power function.** For a real number $\tau$, let
$\psi : \mathbb{N} \to \mathbb{R}$ be given by $\psi(q) = q^{-\tau}$ (the value at $q = 0$ does not
matter). Then the lower order at infinity of $1/\psi$ is $\tau_\psi = \max(\tau, 0)$, an element of
$[0, \infty]$; in particular $\tau_\psi = \tau$ when $\tau \ge 0$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, remark after Theorem 7. -/
public theorem lowerOrderAtInfinity_rpow_inv (τ : ℝ) :
    lowerOrderAtInfinity (fun q => ((q : ℝ) ^ τ)⁻¹) = ENNReal.ofReal τ := by
  rw [lowerOrderAtInfinity, liminf_congr (orderRatio_rpow_inv τ), liminf_const]

/-- **Upper order at infinity of $q^{-\tau}$.** For every real $\tau$, the upper order at infinity
of $q \mapsto (q^{\tau})^{-1}$ is $\max(0, \tau)$; in particular it is $\tau$ when $\tau \ge 0$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, remark after Theorem 7. -/
public theorem upperOrderAtInfinity_rpow_inv (τ : ℝ) :
    upperOrderAtInfinity (fun q => ((q : ℝ) ^ τ)⁻¹) = ENNReal.ofReal τ := by
  rw [upperOrderAtInfinity, limsup_congr (orderRatio_rpow_inv τ), limsup_const]

/-- **Khintchine's theorem.** Let $\psi : \mathbb{N} \to \mathbb{R}$ be non-increasing on all of
$\mathbb{N}$ (including $\psi(0) \ge \psi(1)$) with $0 \le \psi(q) \le 1/2$ for every $q$. If the
series $\sum_q \psi(q)$ converges, then the set $W(\psi)$ of $\psi$-well approximable numbers has
Lebesgue measure $0$; if the series diverges, then $W(\psi)$ has Lebesgue measure $1$.

The value $\psi(0)$ affects neither $W(\psi)$ nor the convergence of the series, so the
condition at $0$ costs nothing: extend by $\psi(0) = \psi(1)$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 1 (Khintchine). -/
public theorem_wanted volume_wellApproximableSet_khintchine (ψ : ℕ → ℝ)
    (hψ0 : ∀ q, 0 ≤ ψ q) (hψ1 : ∀ q, ψ q ≤ 1 / 2) (hψ : Antitone ψ) :
    (Summable ψ → volume (wellApproximableSet ψ) = 0) ∧
      (¬ Summable ψ → volume (wellApproximableSet ψ) = 1)

/-- **Jarník–Besicovitch theorem.** For a real number $\tau \ge 1$, let $W(\tau)$ be the set of
$x \in [0, 1)$ such that for infinitely many natural numbers $q$ there is an integer $p$ with
$|x - p/q| < q^{-(1+\tau)}$; this is the set of $\psi$-well approximable numbers for
$\psi(q) = q^{-\tau}$. Then the Hausdorff dimension of $W(\tau)$ is $2/(1 + \tau)$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 2 (Jarník;
Besicovitch). -/
public theorem_wanted dimH_wellApproximableSet_rpow (τ : ℝ) (hτ : 1 ≤ τ) :
    dimH (wellApproximableSet (fun q => ((q : ℝ) ^ τ)⁻¹)) = ENNReal.ofReal (2 / (1 + τ))

/-- **Dodson's theorem.** Let $\psi$ be a non-increasing function from the natural numbers to
$(0, 1/2]$, let $W(\psi)$ be the set of $x \in [0, 1)$ such that for infinitely many $q$ there
is an integer $p$ with $|x - p/q| < \psi(q)/q$, and let
$\tau_\psi = \liminf_{q \to \infty} (-\log \psi(q) / \log q)$, taken in $[0, \infty]$, be the
lower order at infinity of $1/\psi$. If $\tau_\psi \ge 1$, then the Hausdorff dimension of
$W(\psi)$ is $2/(1 + \tau_\psi)$, read as $0$ when $\tau_\psi = \infty$.

The paper allows $\psi(q) = 0$; here $\psi$ is assumed positive, so that $\log \psi(q)$ is
defined. Without the hypothesis $\tau_\psi \ge 1$ the formula fails: the constant
$\psi = 1/4$ has $\tau_\psi = 0$ and $\dim_H W(\psi) = 1$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 3 (Dodson). -/
public theorem_wanted dimH_wellApproximableSet_dodson (ψ : ℕ → ℝ)
    (hψ0 : ∀ q, 0 < ψ q) (hψ1 : ∀ q, ψ q ≤ 1 / 2) (hψ : Antitone ψ)
    (hτ : 1 ≤ lowerOrderAtInfinity ψ) :
    dimH (wellApproximableSet ψ) = 2 * (1 + lowerOrderAtInfinity ψ)⁻¹

/-! ### Lüroth expansions -/

/-! The Lüroth map `T(x) = ⌊1/x⌋ ((⌊1/x⌋ + 1) x - 1)` and the digits
`d_{n+1}(x) = ⌊1/T^n(x)⌋ + 1` of the paper are the existing `lurothMap` and `lurothDigitSeq`
of `WantedExt/NumberTheory/LurothConsecutiveDigitsWanted.lean` (digits indexed from `0`):
there `lurothMap x = d₁(x) (d₁(x) - 1) x - (d₁(x) - 1)` with `d₁(x) = ⌊1/x⌋ + 1`, which is the
same map on `(0, 1]`. -/

/-- **Lüroth denominators.** For a sequence of natural numbers $d_0, d_1, d_2, \dots$ (numbered from
$0$), the $n$-th Lüroth denominator is
$$Q_n = d_n \prod_{j=0}^{n-1} d_j (d_j - 1), \qquad n \ge 0.$$
With digits numbered from $1$, as in the paper, this is the paper's $Q_{n+1}$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (8). -/
public def lurothDenominator (d : ℕ → ℕ) (n : ℕ) : ℕ :=
  d n * ∏ j ∈ Finset.range n, d j * (d j - 1)

/-- **Lüroth convergents.** For a sequence of natural numbers $d_0, d_1, d_2, \dots$ (numbered from
$0$) with Lüroth denominators $Q_0, Q_1, Q_2, \dots$, the $n$-th Lüroth convergent is the rational
number
$$x_n = \sum_{k=0}^{n} \frac{1}{Q_k}, \qquad n \ge 0,$$
where a term with $Q_k = 0$ is read as $0$. With digits numbered from $1$, as in the paper, this is
the paper's $x_{n+1} = P_{n+1}/Q_{n+1}$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Section 2. -/
public def lurothConvergent (d : ℕ → ℕ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), 1 / (lurothDenominator d k : ℚ)

/-- **The Lüroth digits of 1.** Every Lüroth digit of $1$ equals $2$, that is,
$1 = [2, 2, 2, \dots]$ in Lüroth notation.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Section 2. -/
public theorem lurothDigitSeq_one (n : ℕ) : lurothDigitSeq 1 n = 2 := by
  rw [lurothDigitSeq, Function.iterate_fixed lurothMap_one, lurothDigit_one]

/-- **The Lüroth orbit of $27/71$ has period two.** The Lüroth map $T$ sends $27/71$ to $20/71$
and sends $20/71$ to $27/71$; in particular $T(T(27/71)) = 27/71$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Section 2 (example). -/
public theorem lurothMap_lurothMap_27_71 :
    lurothMap (27 / 71) = 20 / 71 ∧ lurothMap (20 / 71) = 27 / 71 := by
  have h1 : lurothDigit ((27 : ℝ) / 71) = 3 := by
    have : ⌊(1 : ℝ) / (27 / 71)⌋₊ = 2 := by
      rw [Nat.floor_eq_iff (by norm_num)]; norm_num
    rw [lurothDigit, this]
  have h2 : lurothDigit ((20 : ℝ) / 71) = 4 := by
    have : ⌊(1 : ℝ) / (20 / 71)⌋₊ = 3 := by
      rw [Nat.floor_eq_iff (by norm_num)]; norm_num
    rw [lurothDigit, this]
  constructor
  · rw [lurothMap, h1]; norm_num
  · rw [lurothMap, h2]; norm_num

/-- **Recurrence for Lüroth denominators.** For every sequence of natural numbers
$d_0, d_1, d_2, \dots$ with Lüroth denominators $Q_0, Q_1, Q_2, \dots$ and every $n \ge 0$,
$$Q_{n+1} = Q_n (d_n - 1) d_{n+1}.$$

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (8). -/
public theorem lurothDenominator_succ (d : ℕ → ℕ) (n : ℕ) :
    lurothDenominator d (n + 1) = lurothDenominator d n * (d n - 1) * d (n + 1) := by
  simp only [lurothDenominator, Finset.prod_range_succ]
  ring

/-- **Lüroth denominators of the constant digit sequence 2.** If $d_j = 2$ for every $j \ge 0$,
then the Lüroth denominators are $Q_n = 2^{n+1}$ for every $n \ge 0$ (digits numbered from $0$;
this is the paper's $Q_{n+1} = 2^{n+1}$).

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (8). -/
public theorem lurothDenominator_two (n : ℕ) :
    lurothDenominator (fun _ => 2) n = 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [lurothDenominator_succ, ih]; ring

/-- **Recurrence for Lüroth convergents.** For every sequence of natural numbers
$d_0, d_1, d_2, \dots$ with Lüroth denominators $Q_n$ and Lüroth convergents $x_n$, and every
$n \ge 0$, $x_{n+1} = x_n + 1/Q_{n+1}$, where $1/Q_{n+1}$ is read as $0$ if $Q_{n+1} = 0$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Section 2. -/
public theorem lurothConvergent_succ (d : ℕ → ℕ) (n : ℕ) :
    lurothConvergent d (n + 1) =
      lurothConvergent d n + 1 / (lurothDenominator d (n + 1) : ℚ) := by
  rw [lurothConvergent, Finset.sum_range_succ, ← lurothConvergent]

/-- **Lüroth well approximable numbers.** For a function $\psi$ from the natural numbers to the
reals, $L(\psi)$ is the set of $x \in (0, 1]$ such that $|x - c_n(x)| < \psi(Q_n(x))/Q_n(x)$ for
infinitely many $n$, where $Q_n(x)$ and $c_n(x)$ are the $n$-th Lüroth denominator and the $n$-th
Lüroth convergent of the Lüroth digit sequence of $x$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Section 2. -/
public def lurothWellApproximableSet (ψ : ℕ → ℝ) : Set ℝ :=
  {x | x ∈ Set.Ioc 0 1 ∧ ∃ᶠ n in atTop,
    |x - lurothConvergent (lurothDigitSeq x) n| <
      ψ (lurothDenominator (lurothDigitSeq x) n) / lurothDenominator (lurothDigitSeq x) n}

/-- **Lüroth well approximable numbers lie in $(0, 1]$.** For every function $\psi$ from the
natural numbers to the reals, the set $L(\psi)$ of Lüroth $\psi$-well approximable numbers is
contained in $(0, 1]$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Section 2. -/
public theorem lurothWellApproximableSet_subset_Ioc (ψ : ℕ → ℝ) :
    lurothWellApproximableSet ψ ⊆ Set.Ioc 0 1 :=
  fun _ hx => hx.1

/-- **Lüroth convergent triples.** The set $S$ consists of the triples $(c_n(y), Q_n(y), d_n(y))$
for $y \in (0, 1]$ and $n \ge 0$, where $d_0(y), d_1(y), \dots$ are the Lüroth digits of $y$
(indexed from $0$), $Q_n(y) = d_n(y) \prod_{j < n} d_j(y)(d_j(y) - 1)$ is the $n$-th Lüroth
denominator of this digit sequence, and $c_n(y) = \sum_{k \le n} 1/Q_k(y)$ is its $n$-th Lüroth
convergent. The first entry is the rational number $c_n(y)$, the second the natural number
$Q_n(y)$ and the third the digit $d_n(y)$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (16). -/
public def lurothTripleSet : Set (ℚ × ℕ × ℕ) :=
  {t | ∃ y ∈ Set.Ioc (0 : ℝ) 1, ∃ n,
    t = (lurothConvergent (lurothDigitSeq y) n, lurothDenominator (lurothDigitSeq y) n,
      lurothDigitSeq y n)}

/-- **A Lüroth triple from the expansion of $1$.** Let $S$ be the set of triples
$(P_n(y)/Q_n(y), Q_n(y), d_n(y))$ for $y \in (0, 1]$ and $n \ge 0$, where $P_n(y)/Q_n(y)$ is the
$n$-th Lüroth convergent of $y$, $Q_n(y)$ its Lüroth denominator and $d_n(y)$ its $n$-th Lüroth
digit (indexed from $0$). Then $(1/2, 2, 2) \in S$: it is the triple of the first convergent of
$1 = [2, 2, 2, \ldots]$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, equation (16). -/
public theorem half_two_two_mem_lurothTripleSet : ((1 / 2 : ℚ), 2, 2) ∈ lurothTripleSet := by
  refine ⟨1, ⟨one_pos, le_rfl⟩, 0, ?_⟩
  simp [lurothConvergent, lurothDenominator, lurothDigitSeq_one]

/-- **Lüroth convergents approximate from below.** Let $x \in (0, 1]$ have Lüroth digits
$d_0, d_1, d_2, \dots$ (numbered from $0$), Lüroth denominators $Q_0, Q_1, Q_2, \dots$ and Lüroth
convergents $x_0, x_1, x_2, \dots$. Then for every $n \ge 0$,
$$0 < x - x_n \le \frac{1}{(d_n - 1) Q_n}.$$
In the paper's numbering from $1$ these are $d_{n+1}$, $Q_{n+1}$ and $x_{n+1} = P_{n+1}/Q_{n+1}$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Proposition 1. -/
public theorem_wanted lurothConvergent_lt_le (x : ℝ) (hx : x ∈ Set.Ioc 0 1) (n : ℕ) :
    0 < x - lurothConvergent (lurothDigitSeq x) n ∧
      x - lurothConvergent (lurothDigitSeq x) n ≤
        1 / (((lurothDigitSeq x n : ℝ) - 1) * lurothDenominator (lurothDigitSeq x) n)

/-- **Mass transference principle for intervals.** Let $(c_n)$ and $(r_n)$ be real sequences with
$r_n \ge 0$ for every $n$ and $r_n \to 0$, and let $I_n = [c_n - r_n, c_n + r_n]$. Assume that
$I_n \subseteq [0, 1]$ for every $n$, let $0 < s < 1$, and let $I_n^s = [c_n - r_n^s, c_n + r_n^s]$.
If $[0, 1] \cap \limsup_{n \to \infty} I_n^s$ has Lebesgue measure $1$, then the $s$-dimensional
Hausdorff measure of $\limsup_{n \to \infty} I_n$ is infinite and the Hausdorff dimension of
$\limsup_{n \to \infty} I_n$ is at least $s$.

The endpoints $s = 0$ and $s = 1$ admitted by the printed statement are excluded. For $s = 0$, the
intervals $I_n = [1/2 - 1/(n+2), 1/2 + 1/(n+2)]$ satisfy the hypothesis, but $\limsup I_n$ is the
single point $1/2$, whose $0$-dimensional Hausdorff measure is $1$. For $s = 1$, the
$1$-dimensional Hausdorff measure of a subset of $[0, 1]$ is at most $1$. The paper's proof treats
$0 < s < 1$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Proposition 3. -/
public theorem_wanted hausdorffMeasure_limsup_closedBall_of_volume (c r : ℕ → ℝ) (s : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) (hr0 : ∀ n, 0 ≤ r n)
    (hI : ∀ n, Metric.closedBall (c n) (r n) ⊆ Set.Icc 0 1)
    (hr : Tendsto r atTop (nhds 0))
    (hfull : volume (Set.Icc 0 1 ∩
      limsup (fun n => Metric.closedBall (c n) (r n ^ s)) atTop) = 1) :
    μH[s] (limsup (fun n => Metric.closedBall (c n) (r n)) atTop) = ∞ ∧
      ENNReal.ofReal s ≤ dimH (limsup (fun n => Metric.closedBall (c n) (r n)) atTop)

/-- **Recognising Lüroth convergents.** For $y \in (0, 1]$ and $n \ge 0$ let $P_n(y)/Q_n(y)$ be
the $n$-th Lüroth convergent of $y$, $Q_n(y)$ its Lüroth denominator and $d_n(y)$ the $n$-th
Lüroth digit of $y$, and let $S$ be the set of all triples $(P_n(y)/Q_n(y), Q_n(y), d_n(y))$ for
$y \in (0, 1]$ and $n \ge 0$. If $x \in (0, 1]$ and $(P/Q, Q, d) \in S$ satisfy
$0 < x - P/Q \le 1/((d - 1) Q)$, then $P/Q$ is a Lüroth convergent of $x$, that is,
$P/Q = P_n(x)/Q_n(x)$ for some $n$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Proposition 4. -/
public theorem_wanted exists_lurothConvergent_eq_of_mem_lurothTripleSet (x : ℝ)
    (hx : x ∈ Set.Ioc 0 1) (t : ℚ × ℕ × ℕ) (ht : t ∈ lurothTripleSet)
    (hpos : 0 < x - t.1) (hle : x - t.1 ≤ 1 / (((t.2.2 : ℝ) - 1) * t.2.1)) :
    ∃ n, lurothConvergent (lurothDigitSeq x) n = t.1

/-- **Lüroth $q^{-\tau}$-well approximable numbers as a limsup over convergent triples.** Let
$\tau \ge 0$ and let $L(\tau)$ be the set of Lüroth $\psi$-well approximable numbers for
$\psi(q) = q^{-\tau}$. For a triple $t = (c, Q, d)$ in the set $S$ of Lüroth convergent triples, put
$B_t = (c, c + Q^{-(1+\tau)}) \cap (c, c + 1/((d - 1)Q)]$. Then $L(\tau)$ consists of the real
numbers $x$ that lie in $B_t$ for infinitely many $t \in S$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Proposition 5. -/
public theorem_wanted lurothWellApproximableSet_rpow_eq_limsup (τ : ℝ) (hτ : 0 ≤ τ) :
    lurothWellApproximableSet (fun q => ((q : ℝ) ^ τ)⁻¹) =
      {x | {t ∈ lurothTripleSet |
        x ∈ Set.Ioo (t.1 : ℝ) (t.1 + ((t.2.1 : ℝ) ^ (1 + τ))⁻¹) ∩
          Set.Ioc (t.1 : ℝ) (t.1 + (((t.2.2 : ℝ) - 1) * t.2.1)⁻¹)}.Infinite}

/-- **Lüroth well approximable numbers as a limsup over convergent triples.** Let $\psi$ be a
function from the natural numbers to $(0, 1]$ whose lower order at infinity $\tau_\psi$ is greater
than $1$. Then the set $L(\psi)$ of Lüroth $\psi$-well approximable numbers consists of the real
numbers $x$ for which there are infinitely many triples $(c, Q, d)$ in the set $S$ of Lüroth
convergent triples with $c < x < c + \psi(Q)/Q$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Proposition 7. -/
public theorem_wanted lurothWellApproximableSet_eq_limsup (ψ : ℕ → ℝ)
    (hψ0 : ∀ q, 0 < ψ q) (hψ1 : ∀ q, ψ q ≤ 1) (hτ : 1 < lowerOrderAtInfinity ψ) :
    lurothWellApproximableSet ψ =
      {x | {t ∈ lurothTripleSet |
        x ∈ Set.Ioo (t.1 : ℝ) (t.1 + ψ t.2.1 / t.2.1)}.Infinite}

/-- **Tan–Zhou theorem (Lüroth analogue of Khintchine's theorem).** Let $\psi$ be a non-increasing
function from the natural numbers (including $0$) to $(0, 1]$, and let $L(\psi)$ be the set of
Lüroth $\psi$-well approximable numbers. If the series $\sum_{q \ge 1} -\psi(q) \log \psi(q) / q$
converges, then $L(\psi)$ has Lebesgue measure $0$; if it diverges, then $L(\psi)$ has Lebesgue
measure $1$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 4 (Tan and
Zhou). -/
public theorem_wanted volume_lurothWellApproximableSet (ψ : ℕ → ℝ)
    (hψ0 : ∀ q, 0 < ψ q) (hψ1 : ∀ q, ψ q ≤ 1) (hψ : Antitone ψ) :
    (Summable (fun q : ℕ => -ψ q * Real.log (ψ q) / q) →
        volume (lurothWellApproximableSet ψ) = 0) ∧
      (¬ Summable (fun q : ℕ => -ψ q * Real.log (ψ q) / q) →
        volume (lurothWellApproximableSet ψ) = 1)

/-- **Cao–Wu–Zhang theorem.** For $x \in (0, 1]$ let $P_n(x)/Q_n(x)$ be the $n$-th Lüroth
convergent of $x$, with Lüroth denominator $Q_n(x)$. For a real number $\tau \ge 1$ let $L(\tau)$
be the set of $x \in (0, 1]$ such that $|x - P_n(x)/Q_n(x)| < Q_n(x)^{-\tau}/Q_n(x)$ for
infinitely many $n$, that is, the set of Lüroth $\psi$-well approximable numbers for
$\psi(q) = q^{-\tau}$. Then the Hausdorff dimension of $L(\tau)$ is $1/(1 + \tau)$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 5 (Cao, Wu, and
Zhang). -/
public theorem_wanted dimH_lurothWellApproximableSet_rpow_of_one_le (τ : ℝ) (hτ : 1 ≤ τ) :
    dimH (lurothWellApproximableSet (fun q => ((q : ℝ) ^ τ)⁻¹)) =
      ENNReal.ofReal (1 / (1 + τ))

/-- **Hausdorff dimension and measure of Lüroth well approximable sets for powers.** For
$x \in (0, 1]$ let $P_n(x)/Q_n(x)$ be the $n$-th Lüroth convergent of $x$, with Lüroth
denominator $Q_n(x)$. For a real number $\tau \ge 0$ let $L(\tau)$ be the set of $x \in (0, 1]$
such that $|x - P_n(x)/Q_n(x)| < Q_n(x)^{-\tau}/Q_n(x)$ for infinitely many $n$, that is, the set
of Lüroth $\psi$-well approximable numbers for $\psi(q) = q^{-\tau}$. Then the Hausdorff dimension
of $L(\tau)$ is $1/(1 + \tau)$, and if $\tau > 0$, the $1/(1 + \tau)$-dimensional Hausdorff
measure of $L(\tau)$ is infinite.

The source also states the measure claim at $\tau = 0$, where it fails: $L(0)$ is contained in
$(0, 1]$, so its $1$-dimensional Hausdorff measure is at most $1$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 6. -/
public theorem_wanted dimH_hausdorffMeasure_lurothWellApproximableSet_rpow (τ : ℝ)
    (hτ : 0 ≤ τ) :
    dimH (lurothWellApproximableSet (fun q => ((q : ℝ) ^ τ)⁻¹)) =
        ENNReal.ofReal (1 / (1 + τ)) ∧
      (0 < τ → μH[1 / (1 + τ)] (lurothWellApproximableSet (fun q => ((q : ℝ) ^ τ)⁻¹)) = ∞)

/-- **Dimension bounds for Lüroth well approximable sets.** Let $\psi$ be a function from the
natural numbers to $(0, 1]$. Let $L(\psi)$ be the set of $x \in (0, 1]$ such that
$|x - P_n(x)/Q_n(x)| < \psi(Q_n(x))/Q_n(x)$ for infinitely many $n$, where $P_n(x)/Q_n(x)$ is the
$n$-th Lüroth convergent of $x$ and $Q_n(x)$ its Lüroth denominator. Let
$\tau_\psi = \liminf_{q \to \infty} (-\log \psi(q) / \log q)$ and
$\bar\tau_\psi = \limsup_{q \to \infty} (-\log \psi(q) / \log q)$, taken in $[0, \infty]$, be the
lower and upper orders at infinity of $1/\psi$. Then
$1/(1 + \bar\tau_\psi) \le \dim_H L(\psi) \le 1/(1 + \tau_\psi)$, where $1/\infty = 0$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 7. -/
public theorem_wanted dimH_lurothWellApproximableSet_bounds (ψ : ℕ → ℝ)
    (hψ0 : ∀ q, 0 < ψ q) (hψ1 : ∀ q, ψ q ≤ 1) :
    (1 + upperOrderAtInfinity ψ)⁻¹ ≤ dimH (lurothWellApproximableSet ψ) ∧
      dimH (lurothWellApproximableSet ψ) ≤ (1 + lowerOrderAtInfinity ψ)⁻¹

/-- **Dimension bounds for Lüroth well approximable sets via denominators.** Let $\psi$ be a
function from the natural numbers to $(0, 1]$. Let $L(\psi)$ be the set of $x \in (0, 1]$ such
that $|x - P_n(x)/Q_n(x)| < \psi(Q_n(x))/Q_n(x)$ for infinitely many $n$, where $P_n(x)/Q_n(x)$
is the $n$-th Lüroth convergent of $x$ and $Q_n(x)$ its Lüroth denominator. For $k \ge 0$ let
$S_k$ be the set of numbers $d_k \prod_{j < k} d_j (d_j - 1)$, where $d_0, \ldots, d_k$ are
integers at least $2$ (the $k$-th Lüroth denominators, indexed from $0$). For $q \ge 2$ put
$r(q) = -\log \psi(q) / \log q$, and let
$\lambda_\psi = \liminf_{k \to \infty} \liminf_{q \in S_k, q \to \infty} r(q)$,
$\bar\lambda_\psi = \liminf_{k \to \infty} \limsup_{q \in S_k, q \to \infty} r(q)$,
$\tau_\psi = \liminf_{q \to \infty} r(q)$ and $\bar\tau_\psi = \limsup_{q \to \infty} r(q)$,
all taken in $[0, \infty]$. Then $\tau_\psi \le \lambda_\psi$, $\bar\lambda_\psi \le \bar\tau_\psi$
and $1/(1 + \bar\lambda_\psi) \le \dim_H L(\psi) \le 1/(1 + \lambda_\psi)$, where $1/\infty = 0$.

Since $S_k$ is indexed from $0$, it is the paper's $S_{k+1}$; this does not change the outer
limit inferior.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 8. -/
public theorem_wanted dimH_lurothWellApproximableSet_bounds_denominators (ψ : ℕ → ℝ)
    (hψ0 : ∀ q, 0 < ψ q) (hψ1 : ∀ q, ψ q ≤ 1) :
    let S : ℕ → Set ℕ := fun k =>
      {q | ∃ d : ℕ → ℕ, (∀ n, 2 ≤ d n) ∧ lurothDenominator d k = q}
    let f : ℕ → ℝ≥0∞ := fun q => ENNReal.ofReal (-Real.log (ψ q) / Real.log q)
    let lowerLam : ℝ≥0∞ := liminf (fun k => liminf f (atTop ⊓ Filter.principal (S k))) atTop
    let upperLam : ℝ≥0∞ := liminf (fun k => limsup f (atTop ⊓ Filter.principal (S k))) atTop
    lowerOrderAtInfinity ψ ≤ lowerLam ∧ upperLam ≤ upperOrderAtInfinity ψ ∧
      (1 + upperLam)⁻¹ ≤ dimH (lurothWellApproximableSet ψ) ∧
      dimH (lurothWellApproximableSet ψ) ≤ (1 + lowerLam)⁻¹

/-- **Without monotonicity the Lüroth dimension can vanish.** For every real number $\tau \ge 0$
there is a function $\psi$ from the natural numbers to $(0, 1]$ such that: $\psi$ is not
non-increasing on $\{q : q \ge N\}$ for any $N$; the lower order at infinity
$\liminf_{q \to \infty} (-\log \psi(q) / \log q)$ of $1/\psi$ equals $\tau$; and the set
$L(\psi)$ of $x \in (0, 1]$ such that $|x - P_n(x)/Q_n(x)| < \psi(Q_n(x))/Q_n(x)$ for infinitely
many $n$, where $P_n(x)/Q_n(x)$ is the $n$-th Lüroth convergent of $x$ and $Q_n(x)$ its Lüroth
denominator, has Hausdorff dimension $0$.

Since $0 < 1/(1 + \tau)$, the Tan–Zhou conjecture fails without monotonicity.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 9. -/
public theorem_wanted exists_not_antitone_dimH_lurothWellApproximableSet_eq_zero (τ : ℝ)
    (hτ : 0 ≤ τ) :
    ∃ ψ : ℕ → ℝ, (∀ q, 0 < ψ q ∧ ψ q ≤ 1) ∧ (¬ ∃ N, AntitoneOn ψ (Set.Ici N)) ∧
      lowerOrderAtInfinity ψ = ENNReal.ofReal τ ∧ dimH (lurothWellApproximableSet ψ) = 0

/-- **Dimension of Lüroth well approximable sets under a divergence condition.** Let $\psi$ be a
function from the natural numbers to $(0, 1]$. Let $L(\psi)$ be the set of $x \in (0, 1]$ such
that $|x - P_n(x)/Q_n(x)| < \psi(Q_n(x))/Q_n(x)$ for infinitely many $n$, where $P_n(x)/Q_n(x)$
is the $n$-th Lüroth convergent of $x$ and $Q_n(x)$ its Lüroth denominator. Let
$\tau_\psi = \liminf_{q \to \infty} (-\log \psi(q) / \log q)$, taken in $[0, \infty]$, be the
lower order at infinity of $1/\psi$, and suppose $\tau_\psi > 1$. Put $t = 1/(1 + \tau_\psi)$,
with $t = 0$ if $\tau_\psi = \infty$, and $\theta_t(q) = \min\{1, 2^{-t} q^{1-t} \psi(q)^t\}$.
Suppose that $\theta_t$ is non-increasing on $\{q : q \ge 1\}$ and that the partial sums
$\sum_{q=1}^{N} -(\psi(q)/q)^t ((1 - t) \log q + t \log(\psi(q)/2))$ tend to $+\infty$ as
$N \to \infty$. Then the Hausdorff dimension of $L(\psi)$ is $1/(1 + \tau_\psi)$, read as $0$
when $\tau_\psi = \infty$.

The paper's monotonicity of $\theta_t$ on $\mathbb{N}$ is taken on $q \ge 1$ (at $q = 0$ the
formula gives $0$). The terms of the series need not be nonnegative, so its divergence to
$\infty$ is read as the partial sums tending to $+\infty$.

Source: Ying Wai Lee, *Lüroth Expansions in Diophantine Approximation: Metric
Properties and Conjectures*, INTEGERS 26 (2026), Article A45, Theorem 10
(`integers-2026-A45-thm-10`). -/
public theorem_wanted dimH_lurothWellApproximableSet_of_tendsto_sum (ψ : ℕ → ℝ)
    (hψ0 : ∀ q, 0 < ψ q) (hψ1 : ∀ q, ψ q ≤ 1) (hτ : 1 < lowerOrderAtInfinity ψ) (t : ℝ)
    (ht : t = ((1 + lowerOrderAtInfinity ψ)⁻¹).toReal)
    (hθ : AntitoneOn (fun q : ℕ => min 1 ((2 : ℝ) ^ (-t) * (q : ℝ) ^ (1 - t) * ψ q ^ t))
      (Set.Ici 1))
    (hdiv : Tendsto (fun N : ℕ => ∑ q ∈ Finset.Icc 1 N,
        -((ψ q / q) ^ t * ((1 - t) * Real.log q + t * Real.log (ψ q / 2)))) atTop atTop) :
    dimH (lurothWellApproximableSet ψ) = (1 + lowerOrderAtInfinity ψ)⁻¹

end

end MetaMathlibExt
