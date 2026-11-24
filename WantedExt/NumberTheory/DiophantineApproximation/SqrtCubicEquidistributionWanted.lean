/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-! # Square roots of cubic polynomials modulo one

Statement-only requests from Dong, Saettone, Song and Zaharescu's equidistribution paper on
square pyramidal numbers: the Kuipers–Niederreiter second-derivative exponential-sum bound they
quote, and their uniform distribution modulo one of `√q(n)` for a cubic `q` with positive leading
coefficient. Weyl's criterion (their Lemma 5) is `MetaMathlibExt.weyl_criterion` in
`MathlibExt/NumberTheory/DiophantineApproximation/WeylCriterion.lean`.

The main theorems concern `a_n = |P_n - y_n²|` (OEIS A351830), the distance from the square
pyramidal number `P_n = 1² + ⋯ + n²` to the nearest square; the definitions of `a_n`, `A(x)` and
`M_k(x)` were read from the arXiv version (arXiv:2412.10097v2), whose error terms
(`O(x^{17/12})`, `O_k(x^{3k/2 + 11/12})`) are weaker than the journal statements given here.
Proposition 9 and Lemmas 10 and 11 (`d_n = ‖√P_n‖`, the Fourier expansion of `‖u‖^k` and the
unweighted sum `G_k`) exist only in the journal version and were read from its TeX source.
-/

open Filter

namespace MetaMathlibExt

@[expose] public section

/-- **Second-derivative test for exponential sums.** Let $a < b$ be integers, let $\rho > 0$,
and let $f : \mathbb{R} \to \mathbb{R}$ be twice continuously differentiable, with either
$f''(t) \ge \rho$ for every $t \in [a, b]$ or $f''(t) \le -\rho$ for every $t \in [a, b]$. Then
$$\Bigl|\sum_{n=a}^{b} e(f(n))\Bigr| \le \bigl(|f'(b) - f'(a)| + 2\bigr)
\Bigl(\frac{4}{\sqrt{\rho}} + 3\Bigr),$$
where $e(x) = e^{2\pi i x}$.

Here $f$ is $C^2$ on all of $\mathbb{R}$; every $C^2$ function on $[a, b]$ extends to one, so
this loses nothing.

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, Lemma 4 (`jis-2026-26.5.5-lem-4`), quoted there from Kuipers and
Niederreiter, *Uniform Distribution of Sequences*, Thm. 2.7. -/
public theorem_wanted norm_sum_exp_two_pi_I_le_of_iteratedDeriv_two {a b : ℤ} (hab : a < b)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {ρ : ℝ} (hρ : 0 < ρ)
    (hf'' : (∀ t ∈ Set.Icc (a : ℝ) b, ρ ≤ deriv (deriv f) t) ∨
      (∀ t ∈ Set.Icc (a : ℝ) b, deriv (deriv f) t ≤ -ρ)) :
    ‖∑ n ∈ Finset.Icc a b, Complex.exp (2 * Real.pi * Complex.I * (f n : ℂ))‖ ≤
      (|deriv f b - deriv f a| + 2) * (4 / Real.sqrt ρ + 3)

/-- **Square roots of cubics with positive leading coefficient are uniformly distributed modulo
one.** Let $q(t) = a t^3 + b t^2 + c t + d$ with real coefficients $a, b, c, d$ and $a > 0$,
write $\{x\} = x - \lfloor x \rfloor$ for the fractional part of a real $x$, and let
$e(x) = e^{2\pi i x}$. Then there is an integer $T \ge 1$ with three properties. First,
$q(t) > 0$ for every real $t \ge T$. Second, the sequence $\sqrt{q(T)}, \sqrt{q(T + 1)}, \dots$
is uniformly distributed modulo one: for all real $\alpha, \beta$ with $0 \le \alpha < \beta \le 1$,
$$\lim_{N \to \infty} \frac{1}{N}
\#\bigl\{0 \le n < N : \alpha \le \{\sqrt{q(T + n)}\} < \beta\bigr\} = \beta - \alpha.$$
Third, there is a real constant $C$ such that for every integer $N \ge T$ and every nonzero
integer $\gamma$,
$$\Bigl|\sum_{n=T}^{N} e\bigl(\gamma \sqrt{q(n)}\bigr)\Bigr| \le
C \bigl(|\gamma|^{1/2} N^{3/4} + |\gamma| N^{1/2} + |\gamma|^{-1/2} N^{1/4} + 1\bigr).$$

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, Proposition 6 (`jis-2026-26.5.5-prop-6`). -/
public theorem_wanted exists_sqrt_cubic_equidistributed_mod_one {a b c d : ℝ} (ha : 0 < a) :
    ∃ T : ℕ, 1 ≤ T ∧ (∀ t : ℝ, (T : ℝ) ≤ t → 0 < a * t ^ 3 + b * t ^ 2 + c * t + d) ∧
      (∀ α β : ℝ, 0 ≤ α → α < β → β ≤ 1 →
        Tendsto (fun N : ℕ =>
          ((Finset.filter (fun n : ℕ =>
              α ≤ Int.fract (Real.sqrt (a * ((T + n : ℕ) : ℝ) ^ 3 + b * ((T + n : ℕ) : ℝ) ^ 2 +
                c * ((T + n : ℕ) : ℝ) + d)) ∧
              Int.fract (Real.sqrt (a * ((T + n : ℕ) : ℝ) ^ 3 + b * ((T + n : ℕ) : ℝ) ^ 2 +
                c * ((T + n : ℕ) : ℝ) + d)) < β)
            (Finset.range N)).card : ℝ) / (N : ℝ))
          atTop (nhds (β - α))) ∧
      ∃ C : ℝ, ∀ N : ℕ, T ≤ N → ∀ γ : ℤ, γ ≠ 0 →
        ‖∑ n ∈ Finset.Icc T N, Complex.exp (2 * Real.pi * Complex.I *
            ((γ * Real.sqrt (a * (n : ℝ) ^ 3 + b * (n : ℝ) ^ 2 + c * n + d) : ℝ) : ℂ))‖ ≤
          C * (|(γ : ℝ)| ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) + |(γ : ℝ)| * (N : ℝ) ^ (1 / 2 : ℝ) +
            |(γ : ℝ)| ^ (-(1 / 2) : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) + 1)


/-- **Square pyramidal number.** For a natural number $n$, the $n$-th square pyramidal number
is $P_n = 1^2 + 2^2 + \dots + n^2 = \sum_{i=1}^{n} i^2$ (so $P_0 = 0$).

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, equation (defn: square pyramidal number) of arXiv:2412.10097v2. -/
def squarePyramidalNumber (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 n, i ^ 2

/-- **Distance from a square pyramidal number to the nearest square.** For a natural number
$n$, let $P_n$ be the $n$-th square pyramidal number and $s = \lfloor \sqrt{P_n} \rfloor$. The
distance from $P_n$ to the nearest square is
$$a_n = \min\bigl(P_n - s^2, (s + 1)^2 - P_n\bigr).$$
Since $s^2 \le P_n < (s + 1)^2$, this is $a_n = |P_n - y_n^2|$, where $y_n^2$ is the square
nearest to $P_n$.

No ties occur, since the midpoint $m^2 + m + 1/2$ of two consecutive squares is never an integer.

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, equation (a_n first definition) of arXiv:2412.10097v2 (OEIS A351830). -/
def squarePyramidalSquareDistance (n : ℕ) : ℕ :=
  min (squarePyramidalNumber n - Nat.sqrt (squarePyramidalNumber n) ^ 2)
    ((Nat.sqrt (squarePyramidalNumber n) + 1) ^ 2 - squarePyramidalNumber n)

/-- **Small square pyramidal numbers and their distances to squares.** Let $P_n$ be the $n$-th
square pyramidal number and $a_n$ the distance from $P_n$ to the nearest square. Then
$P_1, P_2, P_3, P_4$ are $1, 5, 14, 30$; $a_2 = 1$ (since $P_2 = 5$ and the nearest square is
$4$); $P_{24} = 4900 = 70^2$; and $a_{24} = 0$ (the cannonball solution).

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, Introduction. -/
theorem squarePyramidalSquareDistance_examples :
    (List.range 4).map (fun i => squarePyramidalNumber (i + 1)) = [1, 5, 14, 30] ∧
      squarePyramidalSquareDistance 2 = 1 ∧ squarePyramidalNumber 24 = 4900 ∧
      squarePyramidalSquareDistance 24 = 0 := by
  have h2 : squarePyramidalNumber 2 = 5 := by decide
  have h24 : squarePyramidalNumber 24 = 4900 := by decide
  have s2 : Nat.sqrt 5 = 2 := (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
  have s24 : Nat.sqrt 4900 = 70 := (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
  refine ⟨by decide, ?_, h24, ?_⟩ <;> simp [squarePyramidalSquareDistance, h2, h24, s2, s24]

/-- **Average distance from square pyramidal numbers to the nearest square.** Let $a_n$ be the
distance from the $n$-th square pyramidal number to the nearest square, and for real $x \ge 1$
let $A(x) = \frac{1}{x} \sum_{1 \le n \le x} a_n$. There is a real constant $C$ such that for
every real $x \ge 1$,
$$\Bigl|A(x) - \frac{x^{3/2}}{5\sqrt{3}}\Bigr| \le C x^{5/4},$$
that is, $A(x) = x^{3/2} / (5\sqrt{3}) + O(x^{5/4})$ with an absolute implied constant.

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, Theorem 1 (`jis-2026-26.5.5-thm-1`); arXiv:2412.10097v2 states the error
`O(x^{17/12})`. -/
public theorem_wanted squarePyramidalSquareDistance_average_asymptotic :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |(1 / x) * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (squarePyramidalSquareDistance n : ℝ) -
          x ^ (3 / 2 : ℝ) / (5 * Real.sqrt 3)| ≤ C * x ^ (5 / 4 : ℝ)

/-- **Moments of the distance from square pyramidal numbers to the nearest square.** Let $a_n$
be the distance from the $n$-th square pyramidal number to the nearest square, and for a
positive integer $k$ and real $x \ge 1$ let $M_k(x) = \sum_{1 \le n \le x} a_n^k$. For every
positive integer $k$ there is a real constant $C_k$ such that for every real $x \ge 1$,
$$\Bigl|M_k(x) - \frac{x^{3k/2 + 1}}{3^{k/2} (3k/2 + 1)(k + 1)}\Bigr| \le C_k x^{3k/2 + 3/4}.$$

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, Theorem 3 (`jis-2026-26.5.5-thm-3`); arXiv:2412.10097v2 states the error
`O_k(x^{3k/2 + 11/12})`. -/
public theorem_wanted squarePyramidalSquareDistance_moment_asymptotic (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (squarePyramidalSquareDistance n : ℝ) ^ k -
          x ^ (3 / 2 * (k : ℝ) + 1) /
            ((3 : ℝ) ^ ((k : ℝ) / 2) * (3 / 2 * (k : ℝ) + 1) * ((k : ℝ) + 1))| ≤
        C * x ^ (3 / 2 * (k : ℝ) + 3 / 4)

/-- **The distance from the square root of a square pyramidal number to the nearest integer is
uniformly distributed.** Let $P_n$ be the $n$-th square pyramidal number, write
$\|x\| = |x - \operatorname{round}(x)|$ for the distance from a real $x$ to the nearest integer,
and let $(y_n)_{n \ge 0}$ be natural numbers such that $|P_n - y_n^2| \le |P_n - z^2|$ for all
natural numbers $n$ and $z$ (so $y_n^2$ is a square nearest to $P_n$). Put
$d_n = |\sqrt{P_n} - y_n|$. Then $d_n = \|\sqrt{P_n}\|$ and $d_n \le 1/2$ for every $n \ge 0$,
and $(d_n)_{n \ge 1}$ is uniformly distributed in $[0, 1/2]$: for all real $\alpha, \beta$ with
$0 \le \alpha < \beta \le 1/2$,
$$\lim_{N \to \infty} \frac{1}{N}
\#\{1 \le n \le N : \alpha \le d_n \le \beta\} = 2(\beta - \alpha).$$

The source shows that $y_n$ is unique, and takes the limit over real $x \to \infty$, which is
equivalent to the limit along integers $N$.

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, Proposition 9 (`jis-2026-26.5.5-prop-9`). -/
public theorem_wanted squarePyramidal_dist_nearest_square_root_equidistributed (y : ℕ → ℕ)
    (hy : ∀ n z : ℕ, |(squarePyramidalNumber n : ℤ) - (y n : ℤ) ^ 2| ≤
      |(squarePyramidalNumber n : ℤ) - (z : ℤ) ^ 2|) :
    (∀ n : ℕ, |Real.sqrt (squarePyramidalNumber n) - y n| =
        |Real.sqrt (squarePyramidalNumber n) - round (Real.sqrt (squarePyramidalNumber n))| ∧
      |Real.sqrt (squarePyramidalNumber n) - y n| ≤ 1 / 2) ∧
    ∀ α β : ℝ, 0 ≤ α → α < β → β ≤ 1 / 2 →
      Tendsto (fun N : ℕ =>
        ((Finset.filter (fun n : ℕ => |Real.sqrt (squarePyramidalNumber n) - y n| ∈ Set.Icc α β)
          (Finset.Icc 1 N)).card : ℝ) / (N : ℝ)) atTop (nhds (2 * (β - α)))

/-- **Fourier expansion of a power of the distance to the nearest integer.** Let $k$ be a
positive integer, let $g(u) = |u - \operatorname{round}(u)|^k$ be the $k$-th power of the
distance from a real $u$ to the nearest integer, let $e(x) = e^{2\pi i x}$, and for every
integer $m$ let $c(m) = \int_0^1 g(u)\, e(-mu)\, du$. Then $c(0) = 1/(2^k (k + 1))$, the mean of
$g$ over a period; there is a real constant $C$ with $|c(m)| \le C / m^2$ for every integer
$m \ne 0$; the series $\sum_{m \in \mathbb{Z}} |c(m)|$ converges; the symmetric partial sums
$\sum_{|m| \le H} c(m)\, e(mu)$ converge to $g(u)$ uniformly in real $u$ as $H \to \infty$; and
there is a real constant $C'$ such that for every integer $H \ge 1$ and every real $u$,
$$\Bigl|g(u) - c(0) - \sum_{0 < |m| \le H} c(m)\, e(mu)\Bigr| \le \frac{C'}{H}.$$

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, Lemma 10 (`jis-2026-26.5.5-lem-10`). -/
public theorem_wanted dist_round_pow_fourier_expansion (k : ℕ) (hk : 1 ≤ k) :
    let g : ℝ → ℝ := fun u => |u - round u| ^ k
    let c : ℤ → ℂ := fun m => ∫ u in (0 : ℝ)..1,
      (g u : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))
    c 0 = ((1 / (2 ^ k * ((k : ℝ) + 1)) : ℝ) : ℂ) ∧
      (∃ C : ℝ, ∀ m : ℤ, m ≠ 0 → ‖c m‖ ≤ C / (m : ℝ) ^ 2) ∧
      Summable (fun m : ℤ => ‖c m‖) ∧
      TendstoUniformly (fun (H : ℕ) (u : ℝ) => ∑ m ∈ Finset.Icc (-(H : ℤ)) H,
          c m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))
        (fun u => (g u : ℂ)) atTop ∧
      ∃ C : ℝ, ∀ H : ℕ, 1 ≤ H → ∀ u : ℝ,
        ‖(g u : ℂ) - c 0 - ∑ m ∈ (Finset.Icc (-(H : ℤ)) H).erase 0,
            c m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ))‖ ≤ C / H

/-- **Power sums of the distance from the square root of a square pyramidal number to the nearest
integer.** Let $P_n$ be the $n$-th square pyramidal number and write
$\|x\| = |x - \operatorname{round}(x)|$ for the distance from a real $x$ to the nearest integer.
For every positive integer $k$ there is a real constant $C_k$ such that for every real $t \ge 1$,
$$\Bigl|\sum_{1 \le n \le t} \|\sqrt{P_n}\|^k - \frac{t}{2^k (k + 1)}\Bigr| \le C_k t^{3/4},$$
that is, with $\mu_k = 1/(2^k (k + 1))$ and $G_k(t) = \sum_{1 \le n \le t} \|\sqrt{P_n}\|^k$,
one has $G_k(t) = \mu_k t + O_k(t^{3/4})$.

The source writes $h(n) = \sqrt{n(n+1)(2n+1)/6}$, which is $\sqrt{P_n}$.

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, Lemma 11 (`jis-2026-26.5.5-lem-11`). -/
public theorem_wanted sum_dist_round_sqrt_squarePyramidal_pow (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      |∑ n ∈ Finset.Icc 1 ⌊t⌋₊, |Real.sqrt (squarePyramidalNumber n) -
            round (Real.sqrt (squarePyramidalNumber n))| ^ k -
          t / (2 ^ k * ((k : ℝ) + 1))| ≤ C * t ^ (3 / 4 : ℝ)

end

end MetaMathlibExt
