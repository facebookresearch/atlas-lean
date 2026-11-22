/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.ModEq
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace MetaMathlibExt

@[expose] public section

/-! Definitions follow the arXiv version of the paper (arXiv:2503.12146v1), which states
`D_n`, Conjecture 2, `V(n)` and `ξ(θ, η)` explicitly. Implied constants of `≪` and `≫` are
absolute: every dependence on `θ`, `η` and `ε` is displayed in the paper's bounds. Corollary 1
and Proposition 5 appear only in the journal version (INTEGERS 26 (2026), A115, PDF) and are
taken from it. -/

open scoped Classical in
/-- **Number of divisors in a short interval.** For a natural number $n$ and real numbers $X$
and $Y$, Letendre's $D_n(X, Y)$ is the number of positive divisors $d$ of $n$ with
$X \le d \le X + Y$. Here $0$ is taken to have no divisors, so $D_0(X, Y) = 0$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Section 1 (definition of `D_n(X, Y)`). -/
public noncomputable def shortIntervalDivisorCount (n : ℕ) (X Y : ℝ) : ℕ :=
  (n.divisors.filter fun d : ℕ => X ≤ (d : ℝ) ∧ (d : ℝ) ≤ X + Y).card

/-- **Trivial bound for the short-interval divisor count.** For every natural number $n$ and
all real numbers $X$ and $Y$, the number $D_n(X, Y)$ of positive divisors of $n$ in
$[X, X + Y]$ is at most the number $\tau(n)$ of positive divisors of $n$. Here $0$ is taken to
have no divisors, so $D_0(X, Y) = \tau(0) = 0$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Section 1 (definition of `D_n(X, Y)`). -/
public theorem shortIntervalDivisorCount_le_card_divisors (n : ℕ) (X Y : ℝ) :
    shortIntervalDivisorCount n X Y ≤ n.divisors.card :=
  Finset.card_filter_le _ _

/-- **Letendre's saving exponent.** For real numbers $\theta$ and $\eta$, Letendre's saving
exponent $\xi(\theta, \eta)$ is defined as follows. If $\eta \le \theta^2$, then
$\xi(\theta, \eta) = 1$. Otherwise, if $\theta \le 1/2$, then $\xi(\theta, \eta) = \theta^2/\eta$
when $2\eta \le \theta$ and $\xi(\theta, \eta) = 4(\theta - \eta)$ when $2\eta > \theta$; and if
$\theta > 1/2$, then $\xi(\theta, \eta) = (1 - \theta)^2/((1 - \theta)^2 + \eta - \theta^2)$ when
$2\eta \le 3\theta - 1$ and $\xi(\theta, \eta) = 4(\theta - \eta)$ when $2\eta > 3\theta - 1$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Theorem 1, display (2). -/
public noncomputable def letendreXi (θ η : ℝ) : ℝ :=
  if η ≤ θ ^ 2 then 1
  else if θ ≤ 1 / 2 then (if 2 * η ≤ θ then θ ^ 2 / η else 4 * (θ - η))
  else if 2 * η ≤ 3 * θ - 1 then (1 - θ) ^ 2 / ((1 - θ) ^ 2 + η - θ ^ 2)
  else 4 * (θ - η)

/-- **Letendre's exponent equals $1$ when $\eta \le \theta^2$.** For all real numbers $\theta$ and
$\eta$ with $\eta \le \theta^2$, Letendre's saving exponent satisfies $\xi(\theta, \eta) = 1$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Theorem 1, display (2). -/
public theorem letendreXi_of_le_sq {θ η : ℝ} (h : η ≤ θ ^ 2) : letendreXi θ η = 1 := by
  simp [letendreXi, h]

/-- **Letendre's exponent for $\theta^2 < \eta$, $\theta \le 1/2$ and $\theta < 2\eta$.** For all
real numbers $\theta$ and $\eta$ with $\theta^2 < \eta$, $\theta \le 1/2$ and $\theta < 2\eta$,
Letendre's saving exponent satisfies $\xi(\theta, \eta) = 4(\theta - \eta)$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Theorem 1, display (2). -/
public theorem letendreXi_of_small_theta_large_eta {θ η : ℝ} (h : θ ^ 2 < η) (hθ : θ ≤ 1 / 2)
    (hη : θ < 2 * η) : letendreXi θ η = 4 * (θ - η) := by
  unfold letendreXi
  split_ifs <;> first | rfl | linarith

/-- **Cohen's lcm–gcd inequality.** Let $k$ be a natural number, let $d_1, \dots, d_k$ be
positive integers and let $t$ be an integer. Then, as an inequality of rational numbers,
$$\prod_{i=1}^{k} d_i^{\,t} \le \operatorname{lcm}(d_1, \dots, d_k)^{t(t+1)/2}
\prod_{1 \le i < j \le k} \gcd(d_i, d_j),$$
where the exponent $t(t+1)/2$ is an integer.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Lemma 1 (`integers-2026-A115-lem-1`). -/
public theorem_wanted prod_zpow_le_lcm_zpow_mul_prod_gcd {k : ℕ} (d : Fin k → ℕ)
    (hd : ∀ i, 0 < d i) (t : ℤ) :
    ∏ i, (d i : ℚ) ^ t ≤
      ((Finset.univ.lcm d : ℕ) : ℚ) ^ (t * (t + 1) / 2) *
        ∏ i, ∏ j ∈ Finset.Ioi i, ((Nat.gcd (d i) (d j) : ℕ) : ℚ)

/-- **Reordering so that prefix sums compare.** Let $k$ be a natural number and let
$x_1, \dots, x_k$ and $y_1, \dots, y_k$ be real numbers with $\sum_i x_i \le \sum_i y_i$. Then
there is a permutation $\sigma$ of $\{1, \dots, k\}$ such that
$\sum_{i \le s} x_{\sigma(i)} \le \sum_{i \le s} y_{\sigma(i)}$ for every $s$ with $0 \le s \le k$.

No positivity of the $x_i$ or $y_i$ is assumed.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Lemma 2 (`integers-2026-A115-lem-2`). -/
public theorem_wanted exists_perm_prefix_sum_le {k : ℕ} (x y : Fin k → ℝ)
    (h : ∑ i, x i ≤ ∑ i, y i) :
    ∃ σ : Equiv.Perm (Fin k), ∀ s ≤ k,
      ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < s), x (σ i) ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < s), y (σ i)

/-- **Arithmetic large sieve with prime-power moduli.** Let $N \ge 1$ be an integer and let $M$
be a finite set of integers contained in $[a, a + N)$ for some integer $a$. Let $S$ be a finite
set of primes and, for each $p \in S$, let $\beta_p \ge 1$ be an integer and let $\Omega_p$ be a
set of fewer than $p^{\beta_p}$ integers in $[0, p^{\beta_p})$ such that no $m \in M$ has its
remainder modulo $p^{\beta_p}$ in $\Omega_p$. Then for every real $Q \ge 1$,
$$|M| \le \frac{N + Q^2}{\sum_{1 \le q \le Q} h(q)},$$
where $q$ runs over the integers in $[1, Q]$ and $h(q) = \prod_{p \mid q} h_p(q)$, the product
over the prime factors $p$ of $q$ of $h_p(q) = |\Omega_p| / (p^{\beta_p} - |\Omega_p|)$ if
$p \in S$ and $p^{\beta_p}$ exactly divides $q$, and $h_p(q) = 0$ otherwise (so $h(1) = 1$).

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Lemma 3 (`integers-2026-A115-lem-3`). -/
public theorem_wanted card_le_of_avoids_residues_primePow (M : Finset ℤ) (N : ℕ) (hN : 1 ≤ N)
    (a : ℤ) (hM : ∀ m ∈ M, a ≤ m ∧ m < a + N) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (β : ℕ → ℕ) (hβ : ∀ p ∈ S, 1 ≤ β p) (Ω : ℕ → Finset ℤ)
    (hΩ : ∀ p ∈ S, ∀ c ∈ Ω p, 0 ≤ c ∧ c < (p : ℤ) ^ β p)
    (hΩcard : ∀ p ∈ S, (Ω p).card < p ^ β p)
    (havoid : ∀ p ∈ S, ∀ m ∈ M, m % (p : ℤ) ^ β p ∉ Ω p) (Q : ℝ) (hQ : 1 ≤ Q) :
    (M.card : ℝ) ≤ (N + Q ^ 2) /
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∏ p ∈ q.primeFactors,
        (if p ∈ S ∧ q.factorization p = β p then
          ((Ω p).card : ℝ) / ((p : ℝ) ^ β p - (Ω p).card) else 0)

open scoped Classical in
/-- **Counting $x$ with $x^2 + p^v u$ not a square modulo $p^{v+1}$.** Let $p \ge 3$ be a prime
and let $u$ be an integer not divisible by $p$. For $v \ge 0$ let $S_v$ be the number of integers
$0 \le x < p^{v+1}$ for which there is no integer $y$ with
$x^2 + p^v u \equiv y^2 \pmod{p^{v+1}}$. Then $2 S_0 = p - \left(\frac{-u}{p}\right)$, where
$\left(\frac{-u}{p}\right)$ is the Legendre symbol, $S_1 = p$, and $S_v = p S_{v-2}$ for every
$v \ge 2$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Lemma 4 (`integers-2026-A115-lem-4`). -/
public theorem_wanted card_unsolvable_sq_add_primePow {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) :
    let S : ℕ → ℕ := fun v => ((Finset.range (p ^ (v + 1))).filter fun x : ℕ =>
      ¬ ∃ y : ℤ, (x : ℤ) ^ 2 + (p : ℤ) ^ v * u ≡ y ^ 2 [ZMOD (p : ℤ) ^ (v + 1)]).card
    2 * (S 0 : ℤ) = p - legendreSym p (-u) ∧ S 1 = p ∧ ∀ v ≥ 2, S v = p * S (v - 2)

/-- **Divisors in windows of length $n^{\theta^2 - \varepsilon}$.** For a natural number $n$ and
real numbers $X$, $Y$, let $D_n(X, Y)$ be the number of divisors $d$ of $n$ with
$X \le d \le X + Y$. There is an absolute constant $C$ such that for every integer $n \ge 1$ and
all real numbers $\theta$, $\varepsilon$ with $0 < \theta < 1$ and $0 < \varepsilon < \theta^2$,
$D_n(n^\theta, n^{\theta^2 - \varepsilon}) \le
C \left(\theta(1 - \theta)/\varepsilon + 1/(\theta(1 - \theta))\right)$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Proposition 1 (`integers-2026-A115-prop-1`). -/
public theorem_wanted exists_shortIntervalDivisorCount_le_of_window_theta_sq :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ θ ε : ℝ, 0 < θ → θ < 1 → 0 < ε → ε < θ ^ 2 →
      (shortIntervalDivisorCount n ((n : ℝ) ^ θ) ((n : ℝ) ^ (θ ^ 2 - ε)) : ℝ) ≤
        C * (θ * (1 - θ) / ε + 1 / (θ * (1 - θ)))

/-- **Letendre's exponent as the largest admissible exponent.** Let $\theta$ and $\eta$ be real
numbers with $\theta^2 \le \eta < \theta$. Then Letendre's saving exponent $\xi(\theta, \eta)$ is
the largest real number $A$ with $0 < A \le 1$ such that
$$\left(\frac{\theta - t}{\alpha}\right)^2 - \frac{\eta - t}{\alpha} \ge 0$$
for all real numbers $\alpha$ and $t$ with $0 < \alpha \le A$ and $0 \le t \le 1 - \alpha$.

On this range $\xi(\theta, \eta)$ equals the paper's $\alpha(\theta, \eta)$ of display (4). The cap
$A \le 1$ reflects $\alpha$ being an exponent ($a = n^\alpha \le n$); without it the set of such
$A$ is unbounded when $\eta = \theta^2$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Proposition 2 (`integers-2026-A115-prop-2`). -/
public theorem_wanted isGreatest_letendreXi {θ η : ℝ} (h₁ : θ ^ 2 ≤ η) (h₂ : η < θ) :
    IsGreatest {A : ℝ | 0 < A ∧ A ≤ 1 ∧ ∀ α : ℝ, 0 < α → α ≤ A → ∀ t : ℝ, 0 ≤ t →
      t ≤ 1 - α → 0 ≤ ((θ - t) / α) ^ 2 - (η - t) / α} (letendreXi θ η)

/-- **Exponents with a margin in Letendre's inequality.** Let $\xi(\theta, \eta)$ denote Letendre's
saving exponent, and let $\theta$, $\eta$ and $\delta$ be real numbers with $0 \le \delta \le 1$,
$\eta < \theta < 1$ and $0 < \theta^2 - (\theta(1 - \theta))^2 \delta \le \eta$. Then there is a
real number $A > 0$ with $\xi(\theta, \eta) - \delta \le A \le \xi(\theta, \eta)$ such that
$((\theta - t)/\alpha)^2 - (\eta - t)/\alpha \ge (\theta(1 - \theta))^2 \delta$ for all real
numbers $\alpha$ and $t$ with $0 < \alpha \le A$ and $0 \le t \le 1 - \alpha$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Proposition 3 (`integers-2026-A115-prop-3`). -/
public theorem_wanted exists_alpha_with_margin {θ η δ : ℝ}
    (h₀ : 0 < θ ^ 2 - (θ * (1 - θ)) ^ 2 * δ) (h₁ : θ ^ 2 - (θ * (1 - θ)) ^ 2 * δ ≤ η)
    (h₂ : η < θ) (h₃ : θ < 1) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    ∃ A : ℝ, 0 < A ∧ letendreXi θ η - δ ≤ A ∧ A ≤ letendreXi θ η ∧
      ∀ α : ℝ, 0 < α → α ≤ A → ∀ t : ℝ, 0 ≤ t → t ≤ 1 - α →
        (θ * (1 - θ)) ^ 2 * δ ≤ ((θ - t) / α) ^ 2 - (η - t) / α

/-- **Letendre's bound for divisors in short intervals.** For a natural number $n$ and real numbers
$X$, $Y$, let $D_n(X, Y)$ be the number of divisors $d$ of $n$ with $X \le d \le X + Y$, let
$\tau(n)$ be the number of divisors of $n$, let $V(n)$ be the largest exponent in the prime
factorization of $n$, and let $\xi(\theta, \eta)$ be Letendre's saving exponent. There is an
absolute constant $C$ such that for all real numbers $\theta$, $\eta$ with $0 < \eta < \theta < 1$
and every integer $n \ge 2$,
$D_n(n^\theta, n^\eta) \le C \tau(n)^{1 - \xi(\theta, \eta)} V(n) \log \tau(n) /
(\theta(1 - \theta))$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Theorem 1 (`integers-2026-A115-thm-1`). -/
public theorem_wanted exists_shortIntervalDivisorCount_le_letendre :
    ∃ C : ℝ, ∀ θ η : ℝ, 0 < η → η < θ → θ < 1 → ∀ n : ℕ, 2 ≤ n →
      (shortIntervalDivisorCount n ((n : ℝ) ^ θ) ((n : ℝ) ^ η) : ℝ) ≤
        C * (n.divisors.card : ℝ) ^ (1 - letendreXi θ η) *
          ((n.primeFactors.sup n.factorization : ℕ) * Real.log n.divisors.card /
            (θ * (1 - θ)))

/-- **Arbitrarily large integers with a divisor in a short window.** Let $\theta$ and $\varepsilon$
be real numbers with $0 < \theta < 1$ and $0 < \varepsilon < \theta$. Then for every natural
number $N$ there is a natural number $n \ge N$ with at least one divisor $d$ satisfying
$n^\theta \le d \le n^\theta + n^{\theta - \varepsilon}$.

This is the nontrivial form of the statement that a constant bounding the number of such divisors
for all $n \ge 1$ is at least $1$; that weaker statement already follows from $n = 1$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Proposition 4 (`integers-2026-A115-prop-4`). -/
public theorem_wanted exists_large_shortIntervalDivisorCount_pos {θ ε : ℝ} (hθ₀ : 0 < θ)
    (hθ₁ : θ < 1) (hε₀ : 0 < ε) (hε : ε < θ) :
    ∀ N : ℕ, ∃ n ≥ N, 1 ≤ shortIntervalDivisorCount n ((n : ℝ) ^ θ) ((n : ℝ) ^ (θ - ε))

/-- **Lower bound for constants bounding divisors in short windows.** There is an absolute
constant $c > 0$ with the following property. Let $\theta$, $\varepsilon$ and $k$ be real numbers
with $0 < \theta < 1$ and $0 < \varepsilon < \theta$, and suppose that for every integer $n \ge 1$
the number of divisors $d$ of $n$ with $n^\theta \le d \le n^\theta + n^{\theta - \varepsilon}$ is
at most $k$. Then $c \sqrt{\varepsilon} \, (\theta(1 - \theta))^{3/2} \,
\left(1 / (\theta^\theta (1 - \theta)^{1 - \theta})\right)^{1/\varepsilon} \le k$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Theorem 2 (`integers-2026-A115-thm-2`). -/
public theorem_wanted exists_lower_bound_conjecture_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ θ ε k : ℝ, 0 < θ → θ < 1 → 0 < ε → ε < θ →
      (∀ n : ℕ, 1 ≤ n →
        (shortIntervalDivisorCount n ((n : ℝ) ^ θ) ((n : ℝ) ^ (θ - ε)) : ℝ) ≤ k) →
      c * Real.sqrt ε * (θ * (1 - θ)) ^ (3 / 2 : ℝ) *
          (1 / (θ ^ θ * (1 - θ) ^ (1 - θ))) ^ (1 / ε) ≤ k


/-- **Letendre's square-root bound for divisors in short intervals.** For a natural number $n$
and real numbers $X$, $Y$, let $D_n(X, Y)$ be the number of divisors $d$ of $n$ with
$X \le d \le X + Y$, let $\tau(n)$ be the number of divisors of $n$, and let $\xi(\theta, \eta)$
be Letendre's saving exponent. There is an absolute constant $C$ such that for all real numbers
$\theta$, $\eta$ with $0 < \eta < \theta < 1$ and every integer $n \ge 2$,
$D_n(n^\theta, n^\eta) \le C \tau(n)^{1 - \xi(\theta, \eta)/2}
\sqrt{\log \tau(n) / (\theta(1 - \theta))}$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Corollary 1 (`integers-2026-A115-cor-1`, journal version). -/
public theorem_wanted exists_shortIntervalDivisorCount_le_sqrt_letendre :
    ∃ C : ℝ, ∀ θ η : ℝ, 0 < η → η < θ → θ < 1 → ∀ n : ℕ, 2 ≤ n →
      (shortIntervalDivisorCount n ((n : ℝ) ^ θ) ((n : ℝ) ^ η) : ℝ) ≤
        C * (n.divisors.card : ℝ) ^ (1 - letendreXi θ η / 2) *
          Real.sqrt (Real.log n.divisors.card / (θ * (1 - θ)))

/-- **Divisors near $\sqrt{an/b}$.** Let $a$ and $b$ be coprime positive integers. For a natural
number $n$ and real numbers $X$, $Y$, let $D_n(X, Y)$ be the number of divisors $d$ of $n$ with
$X \le d \le X + Y$, and let $\omega(m)$ be the number of distinct prime factors of $m$. There is
a constant $C$, depending on $a$ and $b$, such that for all integers $n \ge 1$ and $i \ge 1$,
writing $x_0 = \sqrt{an/b}$ and $w = \omega(4abn)$,
$$D_n\bigl(x_0, \sqrt{i x_0 / b}\bigr) \le C \min\bigl(i, \; i/w + w (\log w)^2\bigr).$$

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Proposition 5 (`integers-2026-A115-prop-5`, journal version). -/
public theorem_wanted exists_shortIntervalDivisorCount_sqrt_window_le (a b : ℕ) (ha : 0 < a)
    (hb : 0 < b) (hab : Nat.Coprime a b) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ i : ℕ, 1 ≤ i →
      (shortIntervalDivisorCount n (Real.sqrt (a * n / b))
          (Real.sqrt (i * Real.sqrt (a * n / b) / b)) : ℝ) ≤
        C * min (i : ℝ) (i / (4 * a * b * n).primeFactors.card +
          (4 * a * b * n).primeFactors.card * Real.log (4 * a * b * n).primeFactors.card ^ 2)

end

end MetaMathlibExt
