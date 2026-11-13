/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace MetaMathlibExt

@[expose] public section

open Real Filter Topology

/-- **Iterated logarithms of power towers increase to a limit.** Let $a, b$ be real numbers
with $e^{1/e} < a < b$. For $n \ge 0$ let $b \uparrow\uparrow n$ be the $n$-fold iterate of
$x \mapsto b^x$ starting at $1$ (so $b \uparrow\uparrow 0 = 1$ and $b \uparrow\uparrow 1 = b$),
and let $a_n = \log_a^{(n)}(b \uparrow\uparrow n)$ be its $n$-fold iterated base-$a$
logarithm, so that $a_0 = 1$. Then the sequence $(a_n)_{n \ge 0}$ is strictly increasing and
converges to a real number.

The paper's "increasing" is read as strictly increasing, and its finite limit as convergence
to a real number.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of
Integer Sequences 28 (2025), Article 25.2.8, Lemma 2 (`jis-2025-25.2.8-lem-2`). -/
public theorem_wanted iterate_logb_tetration_strictMono_and_converges {a b : ℝ}
    (ha : Real.exp (1 / Real.exp 1) < a) (hab : a < b) :
    StrictMono (fun n : ℕ => (Real.logb a)^[n] ((fun x : ℝ => b ^ x)^[n] 1)) ∧
      ∃ L : ℝ, Tendsto (fun n : ℕ => (Real.logb a)^[n] ((fun x : ℝ => b ^ x)^[n] 1))
        atTop (𝓝 L)

/-- **Lower bound $\Gamma(x + 1) > (x/e)^x$ for the Gamma function.** For every real number
$x \ge 1$, $\Gamma(x + 1) > (x/e)^x$.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of
Integer Sequences 28 (2025), Article 25.2.8, Lemma 9 (`jis-2025-25.2.8-lem-9`). -/
public theorem_wanted div_exp_one_rpow_lt_Gamma_add_one {x : ℝ} (hx : 1 ≤ x) :
    (x / Real.exp 1) ^ x < Real.Gamma (x + 1)

/-- **Upper bound $\Gamma(x + 1) \ln \Gamma(x + 1) \le \Gamma(x)^{\Gamma(x)}$.** For every real
number $x > 4$, $\Gamma(x + 1) \ln \Gamma(x + 1) \le \Gamma(x)^{\Gamma(x)}$.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of
Integer Sequences 28 (2025), Article 25.2.8, Lemma 9 (`jis-2025-25.2.8-lem-9`). -/
public theorem_wanted Gamma_add_one_mul_log_le_Gamma_rpow_self {x : ℝ} (hx : 4 < x) :
    Real.Gamma (x + 1) * Real.log (Real.Gamma (x + 1)) ≤ Real.Gamma x ^ Real.Gamma x

/-- **Normalization of power towers.** Let $a, b > e^{1/e}$ be real numbers with $a \ne b$. For
a real number $c$ and $m \ge 0$ let $E_m(b, c)$ be the $m$-fold iterate of $x \mapsto b^x$
starting at $c$ (the tower $b^{b^{\cdots^{c}}}$ with $m$ copies of $b$), and let
$a \uparrow\uparrow n$ be the $n$-fold iterate of $x \mapsto a^x$ starting at $1$. Then there
are a natural number $N$, an integer $k$ and a convergent sequence $(c_n)$ of real numbers such
that for every $n \ge N$ we have $n + k \ge 0$, $1 < c_n < b$ and
$a \uparrow\uparrow n = E_{n+k}(b, c_n)$.

The paper leaves the condition $n + k \ge 0$ implicit.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer
Sequences 28 (2025), Article 25.2.8, Theorem 1 (`jis-2025-25.2.8-thm-1`), quoted from the
author's earlier paper. -/
public theorem_wanted exists_tetration_eq_iterate_rpow_eventually {a b : ℝ}
    (ha : Real.exp (1 / Real.exp 1) < a) (hb : Real.exp (1 / Real.exp 1) < b) (hab : a ≠ b) :
    ∃ N : ℕ, ∃ k : ℤ, ∃ c : ℕ → ℝ, (∃ L : ℝ, Tendsto c atTop (𝓝 L)) ∧
      ∀ n ≥ N, 0 ≤ (n : ℤ) + k ∧ 1 < c n ∧ c n < b ∧
        (fun x : ℝ => a ^ x)^[n] 1 = (fun x : ℝ => b ^ x)^[((n : ℤ) + k).toNat] (c n)

/-- **Power towers rewritten in another base.** Let $a, b > e^{1/e}$ be real numbers and $n > 0$
a natural number. Let $a \uparrow\uparrow n$ be the $n$-fold iterate of $x \mapsto a^x$ starting
at $1$, and $E_p(b, c)$ the $p$-fold iterate of $x \mapsto b^x$ starting at $c$. Then there are
a natural number $p$ and a real number $c$ with $1 < c \le b$ such that
$a \uparrow\uparrow n = E_p(b, c)$.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer
Sequences 28 (2025), Article 25.2.8, Lemma 3 (`jis-2025-25.2.8-lem-3`), quoted from the
author's earlier paper. -/
public theorem_wanted exists_tetration_eq_iterate_rpow {a b : ℝ}
    (ha : Real.exp (1 / Real.exp 1) < a) (hb : Real.exp (1 / Real.exp 1) < b) {n : ℕ}
    (hn : 0 < n) :
    ∃ p : ℕ, ∃ c ∈ Set.Ioc 1 b, (fun x : ℝ => a ^ x)^[n] 1 = (fun x : ℝ => b ^ x)^[p] c

/-- **Comparison of iterated factorials.** For natural numbers $j$ and $m$ let $F_j(m)$ be the
$j$-fold iterated factorial $m!\cdots!$ (with $j$ factorials). Let $n, n' \ge 3$ and $k > k'$ be
natural numbers. If $n' < F_{k-k'}(n)$, then $F_{k'}(n') < F_k(n)$.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer
Sequences 28 (2025), Article 25.2.8, Theorem 4 (`jis-2025-25.2.8-thm-4`). -/
public theorem_wanted iterate_factorial_lt_iterate_factorial {n n' k k' : ℕ} (hn : 3 ≤ n)
    (hn' : 3 ≤ n') (hk : k' < k) (h : n' < Nat.factorial^[k - k'] n) :
    Nat.factorial^[k'] n' < Nat.factorial^[k] n

/-- **Iterated factorials as base-$10$ power towers.** Let $k \ge 3$ be a natural number, let
$F_n(k)$ be the $n$-fold iterated factorial of $k$, viewed as a real number, and for a real
number $c$ and $m \ge 0$ let $E_m(10, c)$ be the $m$-fold iterate of $x \mapsto 10^x$ starting
at $c$. Then there are an integer $\ell$, a natural number $N > 0$, a sequence $(c_n)$ of real
numbers and a real number $L$ with the following properties: for every $n \ge N$ we have
$n + \ell \ge 0$, $1 < c_n \le 10$ and $F_n(k) = E_{n+\ell}(10, c_n)$; the sequence
$(c_n)_{n \ge N}$ is strictly increasing and converges to $L$; and
$E_{n+\ell}(10, L) / (F_n(k) \ln F_n(k)) \to 1 / \ln 10$ as $n \to \infty$.

The paper leaves the condition $n + \ell \ge 0$ implicit.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer
Sequences 28 (2025), Article 25.2.8, Theorem 5 (`jis-2025-25.2.8-thm-5`). -/
public theorem_wanted exists_iterate_factorial_eq_iterate_rpow_ten {k : ℕ} (hk : 3 ≤ k) :
    ∃ ℓ : ℤ, ∃ N : ℕ, 0 < N ∧ ∃ c : ℕ → ℝ, ∃ L : ℝ,
      (∀ n ≥ N, 0 ≤ (n : ℤ) + ℓ ∧ 1 < c n ∧ c n ≤ 10 ∧
        ((Nat.factorial^[n] k : ℕ) : ℝ) = (fun x : ℝ => 10 ^ x)^[((n : ℤ) + ℓ).toNat] (c n)) ∧
      StrictMonoOn c (Set.Ici N) ∧ Tendsto c atTop (𝓝 L) ∧
      Tendsto (fun n : ℕ => (fun x : ℝ => 10 ^ x)^[((n : ℤ) + ℓ).toNat] L /
          (((Nat.factorial^[n] k : ℕ) : ℝ) * Real.log ((Nat.factorial^[n] k : ℕ) : ℝ)))
        atTop (𝓝 (1 / Real.log 10))

/-- **Iterated factorials as tetrations.** Let $k \ge 3$ be a natural number and $F_n(k)$ the
$n$-fold iterated factorial of $k$; for a real number $\beta$ let $\beta \uparrow\uparrow n$ be
the $n$-fold iterate of $x \mapsto \beta^x$ starting at $1$. Then there is a sequence $(b_n)$ of
real numbers such that $b_n > e^{1/e}$ and $F_n(k) = b_n \uparrow\uparrow n$ for every
$n \ge 1$, and $(b_n)$ converges to a limit $b \le k!$.

The case $n = 0$ is excluded, as the paper defines power towers only for $n \ge 1$.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer
Sequences 28 (2025), Article 25.2.8, Theorem 8 (`jis-2025-25.2.8-thm-8`). -/
public theorem_wanted exists_iterate_factorial_eq_tetration {k : ℕ} (hk : 3 ≤ k) :
    ∃ b : ℕ → ℝ, (∀ n ≥ 1, Real.exp (1 / Real.exp 1) < b n ∧
        ((Nat.factorial^[n] k : ℕ) : ℝ) = (fun x : ℝ => b n ^ x)^[n] 1) ∧
      ∃ L ≤ ((k.factorial : ℕ) : ℝ), Tendsto b atTop (𝓝 L)

/-- **Iterated Gamma values as power towers.** Let $z > 1$ be a real number with
$\Gamma(z) = z$, let $b > e^{1/e}$ and $x > z$ be real numbers, let $\Gamma^n$ be the $n$-fold
iterate of $\Gamma$, and for a real number $c$ and $m \ge 0$ let $E_m(b, c)$ be the $m$-fold
iterate of $y \mapsto b^y$ starting at $c$. Then there are an integer $\ell$, a natural number
$N > 0$, a sequence $(c_n)$ of real numbers and a real number $L$ with the following
properties: for every $n \ge N$ we have $n + \ell \ge 0$, $1 < c_n \le b$ and
$\Gamma^n(x) = E_{n+\ell}(b, c_n)$; the sequence $(c_n)_{n \ge N}$ is strictly increasing and
converges to $L$; and
$E_{n+\ell}(b, L) / ((\Gamma^n(x) - 1) \ln(\Gamma^n(x) - 1)) \to 1 / \ln b$ as $n \to \infty$.

This is a corrected reading of the printed statement: $x > z$ for the printed $x \ge z$ (at
$x = z$ the orbit is constant while $E_{n+\ell}(b, c_n)$ tends to infinity); $\Gamma^n(x)$ for
the printed $\Gamma^n(k)$ ($k$ is unbound); and $c_n \le b$, the bound of the proof and of its
restatement in the proof of Theorem 12, for the printed $c_n \le 10$ (copied from Theorem 5).

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer
Sequences 28 (2025), Article 25.2.8, Theorem 10 (`jis-2025-25.2.8-thm-10`). -/
public theorem_wanted exists_iterate_Gamma_eq_iterate_rpow {z b x : ℝ} (hz : 1 < z)
    (hΓz : Real.Gamma z = z) (hb : Real.exp (1 / Real.exp 1) < b) (hx : z < x) :
    ∃ ℓ : ℤ, ∃ N : ℕ, 0 < N ∧ ∃ c : ℕ → ℝ, ∃ L : ℝ,
      (∀ n ≥ N, 0 ≤ (n : ℤ) + ℓ ∧ 1 < c n ∧ c n ≤ b ∧
        Real.Gamma^[n] x = (fun y : ℝ => b ^ y)^[((n : ℤ) + ℓ).toNat] (c n)) ∧
      StrictMonoOn c (Set.Ici N) ∧ Tendsto c atTop (𝓝 L) ∧
      Tendsto (fun n : ℕ => (fun y : ℝ => b ^ y)^[((n : ℤ) + ℓ).toNat] L /
          ((Real.Gamma^[n] x - 1) * Real.log (Real.Gamma^[n] x - 1)))
        atTop (𝓝 (1 / Real.log b))

/-- **Gamma of an iterated exponential exceeds the next iterate.** Let $b \ge e$ and, for
$m \ge 0$, let $E_m(b, b)$ be the $m$-fold iterate of $x \mapsto b^x$ started at $b$, so that
$E_0(b, b) = b$ and $E_{m+1}(b, b) = b^{E_m(b, b)}$. Then for every integer $n > 0$,
$E_{n+1}(b, b) < \Gamma(E_n(b, b))$.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer
Sequences 28 (2025), Article 25.2.8, Lemma 11 (`jis-2025-25.2.8-lem-11`). -/
public theorem_wanted iterate_rpow_succ_lt_Gamma_iterate_rpow {b : ℝ} (hb : Real.exp 1 ≤ b)
    {n : ℕ} (hn : 0 < n) :
    (fun x : ℝ => b ^ x)^[n + 1] b < Real.Gamma ((fun x : ℝ => b ^ x)^[n] b)

/-- **Tetrations as iterated Gamma values.** Let $z > 1$ be a real number with $\Gamma(z) = z$,
and let $b > z$. Let $b \uparrow\uparrow n$ be the $n$-fold iterate of $y \mapsto b^y$ starting
at $1$, and $\Gamma^n$ the $n$-fold iterate of $\Gamma$. Then there is a convergent sequence
$(x_n)$ of real numbers, strictly decreasing from some index on, such that
$b \uparrow\uparrow n = \Gamma^n(x_n)$ for every $n \ge 1$.

The case $n = 0$ is excluded, as the paper defines power towers only for $n \ge 1$.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer
Sequences 28 (2025), Article 25.2.8, Theorem 12 (`jis-2025-25.2.8-thm-12`). -/
public theorem_wanted exists_tetration_eq_iterate_Gamma {z b : ℝ} (hz : 1 < z)
    (hΓz : Real.Gamma z = z) (hb : z < b) :
    ∃ x : ℕ → ℝ, (∀ n ≥ 1, (fun y : ℝ => b ^ y)^[n] 1 = Real.Gamma^[n] (x n)) ∧
      (∃ L : ℝ, Tendsto x atTop (𝓝 L)) ∧ ∃ M : ℕ, StrictAntiOn x (Set.Ici M)

end

end MetaMathlibExt
