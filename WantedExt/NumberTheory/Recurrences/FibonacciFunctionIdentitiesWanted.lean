/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.Fib.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Instances.Real.Lemmas
public import MathlibExt.NumberTheory.LucasSequence

/-!
# Fibonacci identities via Fibonacci functions

Statements from Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*,
Journal of Integer Sequences 27 (2024), Article 24.6.2 (arXiv `2311.06287v4`; the Binet
constants and the Fibonacci function of the section "Justification of the method" are read
from the journal TeX source).

Conventions.

* `F_m` is Mathlib's signed Fibonacci number `Int.fib m`, cast to `ℝ`.
* An integer-indexed Lucas number `L_m` is passed as a function `L : ℤ → ℝ`
  with `L m = F_(m-1) + F_(m+1)` for every integer `m`; this identity determines
  the Lucas numbers on all of `ℤ`.  Where every index is a natural number the
  canonical `Nat.fib` and `MetaMathlibExt.lucasNumber` are used instead.
* A gibonacci sequence (`G`, `H`, `I`, ...) is a function `ℤ → ℝ` with
  `G (j + 2) = G (j + 1) + G j` for every integer `j`, i.e. the paper's sequence
  with arbitrary real seeds `G 0`, `G 1` extended to negative indices.
* The paper's generalized Fibonacci sequence `W_j(W_0, W_1; p)` is a function
  `W : ℤ → ℝ` with `W (j + 2) = p * W (j + 1) + W j`; its constant
  `γ_W = e_W (p ^ 2 - 1)` with `e_W = p W_0 W_1 + W_0 ^ 2 - W_1 ^ 2` is taken from
  the paper's section on the Gelin-Cesàro identity.
* A Horadam sequence `W_j(W_0, W_1; P, Q)` is a function `W : ℤ → ℝ` with
  `W (j + 2) = P * W (j + 1) - Q * W j` and `Q ≠ 0` (the paper extends it to
  negative indices by dividing by `Q`).
* Finite sums `∑_(j=1)^n` and `∑_(j=0)^n` take `n : ℕ`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Weighted binomial sums of Lucas and Fibonacci numbers with even step.** Let $F_m$ be the
Fibonacci numbers extended to all integers $m$ ($F_0 = 0$, $F_1 = 1$, $F_{m+2} = F_{m+1} + F_m$)
and $L_m = F_{m-1} + F_{m+1}$ the Lucas numbers. For every natural number $n$ and all integers
$k$, $r$ with $k$ even,
$$2 \sum_{j=0}^{n} j \binom{n}{j} L_{r+2kj} = 5 n L_k^{n-1} F_{r+nk} F_k + n L_k^n L_{r+nk}$$
and
$$2 \sum_{j=0}^{n} j \binom{n}{j} F_{r+2kj} = n L_k^{n-1} L_{r+nk} F_k + n L_k^n F_{r+nk}.$$

For $n = 0$ the exponent $n - 1$ is read as $0$; the term carrying it has the factor $n = 0$.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 2
(`jis-2024-24.6.2-prop-2`). -/
public theorem_wanted lucas_fib_weighted_binomial_sum_even_step
    (L : ℤ → ℝ) (hL : ∀ m : ℤ, L m = Int.fib (m - 1) + Int.fib (m + 1))
    (n : ℕ) (k r : ℤ) (hk : Even k) :
    2 * ∑ j ∈ Finset.range (n + 1), (j : ℝ) * (n.choose j : ℝ) * L (r + 2 * k * j) =
        5 * n * L k ^ (n - 1) * (Int.fib (r + n * k) : ℝ) * (Int.fib k : ℝ) +
          n * L k ^ n * L (r + n * k) ∧
      2 * ∑ j ∈ Finset.range (n + 1),
          (j : ℝ) * (n.choose j : ℝ) * (Int.fib (r + 2 * k * j) : ℝ) =
        n * L k ^ (n - 1) * L (r + n * k) * (Int.fib k : ℝ) +
          n * L k ^ n * (Int.fib (r + n * k) : ℝ)

/-- **Two telescoping relations between Lucas and Fibonacci numbers.** Let $F_m$ be the Fibonacci
numbers extended to all integers $m$ ($F_0 = 0$, $F_1 = 1$, $F_{m+2} = F_{m+1} + F_m$) and
$L_m = F_{m-1} + F_{m+1}$ the Lucas numbers. Then for every integer $k$,
$$\frac{L_{2k+1}}{F_{2k+1}^2 + 1} = \frac{L_{2k}}{F_{2k}^2 + 1} - \frac{L_{2k+2}}{F_{2k+2}^2 + 1}$$
and
$$\frac{L_{2k+1}}{L_{2k} L_{2k+2}} \cdot \frac{(F_{2k}^2 + 1)(F_{2k+2}^2 + 1)}{F_{2k+1}^2 + 1}
= \frac{F_{2k+2}^2 + 1}{L_{2k+2}} - \frac{F_{2k}^2 + 1}{L_{2k}}.$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 3
(`jis-2024-24.6.2-prop-3`). -/
public theorem_wanted lucas_div_fib_sq_add_one_telescoping
    (L : ℤ → ℝ) (hL : ∀ m : ℤ, L m = Int.fib (m - 1) + Int.fib (m + 1)) (k : ℤ) :
    L (2 * k + 1) / ((Int.fib (2 * k + 1) : ℝ) ^ 2 + 1) =
        L (2 * k) / ((Int.fib (2 * k) : ℝ) ^ 2 + 1) -
          L (2 * k + 2) / ((Int.fib (2 * k + 2) : ℝ) ^ 2 + 1) ∧
      L (2 * k + 1) / (L (2 * k) * L (2 * k + 2)) *
          (((Int.fib (2 * k) : ℝ) ^ 2 + 1) * ((Int.fib (2 * k + 2) : ℝ) ^ 2 + 1) /
            ((Int.fib (2 * k + 1) : ℝ) ^ 2 + 1)) =
        ((Int.fib (2 * k + 2) : ℝ) ^ 2 + 1) / L (2 * k + 2) -
          ((Int.fib (2 * k) : ℝ) ^ 2 + 1) / L (2 * k)

/-- **Telescoping sums of Lucas numbers over Fibonacci squares plus one.** Let $F_m$ denote the
Fibonacci numbers and $L_m$ the Lucas numbers ($L_0 = 2$, $L_1 = 1$, $L_{m+2} = L_{m+1} + L_m$).
For every natural number $n$,
$$\sum_{k=1}^{n} \frac{L_{2k+1}}{F_{2k+1}^2 + 1} = \frac{3}{2} - \frac{L_{2n+2}}{F_{2n+2}^2 + 1}$$
and
$$\sum_{k=1}^{n} \frac{L_{2k+1}}{L_{2k} L_{2k+2}} \cdot
\frac{(F_{2k}^2 + 1)(F_{2k+2}^2 + 1)}{F_{2k+1}^2 + 1} =
\frac{F_{2n+2}^2 + 1}{L_{2n+2}} - \frac{2}{3},$$
and the real series $\sum_{k \ge 1} L_{2k+1} / (F_{2k+1}^2 + 1)$ has sum $3/2$.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 4
(`jis-2024-24.6.2-prop-4`). -/
public theorem_wanted sum_lucas_div_fib_sq_add_one (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n,
          (lucasNumber (2 * k + 1) : ℝ) / ((Nat.fib (2 * k + 1) : ℝ) ^ 2 + 1) =
        3 / 2 - (lucasNumber (2 * (n + 1)) : ℝ) / ((Nat.fib (2 * (n + 1)) : ℝ) ^ 2 + 1) ∧
      ∑ k ∈ Finset.Icc 1 n,
          (lucasNumber (2 * k + 1) : ℝ) /
              ((lucasNumber (2 * k) : ℝ) * (lucasNumber (2 * k + 2) : ℝ)) *
            (((Nat.fib (2 * k) : ℝ) ^ 2 + 1) * ((Nat.fib (2 * k + 2) : ℝ) ^ 2 + 1) /
              ((Nat.fib (2 * k + 1) : ℝ) ^ 2 + 1)) =
        ((Nat.fib (2 * (n + 1)) : ℝ) ^ 2 + 1) / (lucasNumber (2 * n + 2) : ℝ) - 2 / 3 ∧
      HasSum (fun k : ℕ => (lucasNumber (2 * (k + 1) + 1) : ℝ) /
        ((Nat.fib (2 * (k + 1) + 1) : ℝ) ^ 2 + 1)) (3 / 2)

/-- **Binomial sum with even powers of a Lucas number.** Let $F_m$ and $L_m$ denote the Fibonacci
and Lucas numbers. For all natural numbers $k$ and $n$,
$$
F_k^3 \sum_{j=0}^{n} (-1)^{(k+1)(n+j)}\, j \binom{n+j}{2j} L_k^{2j}
= \frac{1}{10} \left((2n+1) F_{2k} L_{(2n+1)k} - F_{(2n+1)k} L_k^2\right).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 5
(`jis-2024-24.6.2-prop-5`). -/
public theorem_wanted fib_cube_mul_sum_choose_lucas_pow (k n : ℕ) :
    (Nat.fib k : ℝ) ^ 3 * ∑ j ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ ((k + 1) * (n + j)) * j * ((n + j).choose (2 * j) : ℝ) *
          (lucasNumber k : ℝ) ^ (2 * j) =
      1 / 10 * ((2 * n + 1) * (Nat.fib (2 * k) : ℝ) * (lucasNumber ((2 * n + 1) * k) : ℝ) -
        (Nat.fib ((2 * n + 1) * k) : ℝ) * (lucasNumber k : ℝ) ^ 2)

/-- **Ten times a Fibonacci cube divides a Fibonacci–Lucas combination.** Let $F_m$ denote the
Fibonacci numbers and $L_m$ the Lucas numbers. For all natural numbers $k$ and $n$, the integer
$10 F_k^3$ divides $(2n+1) F_{2k} L_{(2n+1)k} - F_{(2n+1)k} L_k^2$.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 6
(`jis-2024-24.6.2-prop-6`). -/
public theorem_wanted ten_mul_fib_cube_dvd (k n : ℕ) :
    10 * (Nat.fib k : ℤ) ^ 3 ∣
      (2 * n + 1) * (Nat.fib (2 * k) : ℤ) * (lucasNumber ((2 * n + 1) * k) : ℤ) -
        (Nat.fib ((2 * n + 1) * k) : ℤ) * (lucasNumber k : ℤ) ^ 2

/-- **Cubic gibonacci identity from Candido's identity.** Let $G : \mathbb{Z} \to \mathbb{R}$ be
a gibonacci sequence, that is, $G_{j+2} = G_{j+1} + G_j$ for every integer $j$. Then for every
integer $k$,

$$
G_k^2 \bigl(G_{k+1} (G_{k+2} + G_k) + G_{k+2} (G_{k+3} + G_{k+1}) -
G_k (G_{k+1} + G_{k-1})\bigr) +
G_{k+1}^2 \bigl(G_k (G_{k+1} + G_{k-1}) + G_{k+2} (G_{k+3} + G_{k+1}) -
G_{k+1} (G_{k+2} + G_k)\bigr) +
G_{k+2}^2 \bigl(G_k (G_{k+1} + G_{k-1}) + G_{k+1} (G_{k+2} + G_k) -
G_{k+2} (G_{k+3} + G_{k+1})\bigr) = 0.
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 7
(`jis-2024-24.6.2-prop-7`). -/
public theorem_wanted gibonacci_candido_derivative_identity
    (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (k : ℤ) :
    G k ^ 2 * (G (k + 1) * (G (k + 2) + G k) + G (k + 2) * (G (k + 3) + G (k + 1)) -
          G k * (G (k + 1) + G (k - 1))) +
        G (k + 1) ^ 2 * (G k * (G (k + 1) + G (k - 1)) +
          G (k + 2) * (G (k + 3) + G (k + 1)) - G (k + 1) * (G (k + 2) + G k)) +
        G (k + 2) ^ 2 * (G k * (G (k + 1) + G (k - 1)) +
          G (k + 1) * (G (k + 2) + G k) - G (k + 2) * (G (k + 3) + G (k + 1))) = 0

/-- **Companion of Melham's sum-of-squares identity for gibonacci sequences.** Let
$G : \mathbb{Z} \to \mathbb{R}$, written $j \mapsto G_j$, satisfy $G_{j+2} = G_{j+1} + G_j$ for
every integer $j$, and let $F_m$ be the Fibonacci numbers. Then for every natural number $n$ and
every integer $k$ (the sums below are empty when $n = 0$),
$$
6 \Bigl(\sum_{j=0}^{2n-1} G_{j+k}^2\Bigr)
\Bigl(\sum_{j=0}^{2n-1} G_{j+k} (G_{j+k+1} + G_{j+k-1})\Bigr) =
F_{2n}^2 \bigl(G_{k+n-2}^3 (G_{k+n-1} + G_{k+n-3}) + 4 G_{k+n-1}^3 (G_{k+n} + G_{k+n-2}) +
4 G_{k+n}^3 (G_{k+n+1} + G_{k+n-1}) + G_{k+n+1}^3 (G_{k+n+2} + G_{k+n})\bigr).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 8
(`jis-2024-24.6.2-prop-8`). -/
public theorem_wanted gibonacci_sum_sq_mul_sum_lucas_like
    (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (n : ℕ) (k : ℤ) :
    6 * (∑ j ∈ Finset.range (2 * n), G (j + k) ^ 2) *
        (∑ j ∈ Finset.range (2 * n), G (j + k) * (G (j + k + 1) + G (j + k - 1))) =
      (Nat.fib (2 * n) : ℝ) ^ 2 *
        (G (k + n - 2) ^ 3 * (G (k + n - 1) + G (k + n - 3)) +
          4 * G (k + n - 1) ^ 3 * (G (k + n) + G (k + n - 2)) +
          4 * G (k + n) ^ 3 * (G (k + n + 1) + G (k + n - 1)) +
          G (k + n + 1) ^ 3 * (G (k + n + 2) + G (k + n)))

/-- **Derivative form of the Gelin–Cesàro identity for generalized Fibonacci sequences.** Let
$p$ be a real number, let $W : \mathbb{Z} \to \mathbb{R}$ satisfy $W_{j+2} = p W_{j+1} + W_j$
for every integer $j$, and put $\gamma_W = (p W_0 W_1 + W_0^2 - W_1^2)(p^2 - 1)$. Then for every
integer $k$,

$$
(W_{k-1} + W_{k-3}) W_{k-1} W_{k+1} W_{k+2} + W_{k-2} (W_k + W_{k-2}) W_{k+1} W_{k+2} +
W_{k-2} W_{k-1} (W_k + W_{k+2}) W_{k+2} + W_{k-2} W_{k-1} W_{k+1} (W_{k+3} + W_{k+1}) =
2 W_k (W_{k+1} + W_{k-1}) \bigl(2 W_k^2 + (-1)^k \gamma_W\bigr).
$$

This is the derivative form of the Horadam–Shannon Gelin–Cesàro identity. The paper's standing
assumption $p \ne 0$ is not needed.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 9
(`jis-2024-24.6.2-prop-9`). -/
public theorem_wanted generalized_fibonacci_gelin_cesaro_derivative
    (W : ℤ → ℝ) (p : ℝ) (hW : ∀ j : ℤ, W (j + 2) = p * W (j + 1) + W j) (k : ℤ) :
    (W (k - 1) + W (k - 3)) * W (k - 1) * W (k + 1) * W (k + 2) +
        W (k - 2) * (W k + W (k - 2)) * W (k + 1) * W (k + 2) +
        W (k - 2) * W (k - 1) * (W k + W (k + 2)) * W (k + 2) +
        W (k - 2) * W (k - 1) * W (k + 1) * (W (k + 3) + W (k + 1)) =
      2 * W k * (W (k + 1) + W (k - 1)) *
        (2 * W k ^ 2 + (-1 : ℝ) ^ k *
          ((p * W 0 * W 1 + W 0 ^ 2 - W 1 ^ 2) * (p ^ 2 - 1)))

/-- **Alternating Fibonacci and Lucas sums from the Gelin–Cesàro identity.** Let $F_m$ and $L_m$
denote the Fibonacci and Lucas numbers. For every natural number $n$,
$$
\sum_{k=1}^{n} \frac{(-1)^{k-1} F_{k+2}^2 F_{2k+4}}{F_{k+2}^4 - 1}
= \frac{5}{6} + \frac{(-1)^{n+1}}{2} \left(\frac{F_{2n+3}}{F_{n+1} F_{n+2}} -
\frac{F_{2n+5}}{F_{n+2} F_{n+3}} + \frac{F_{2n+7}}{F_{n+3} F_{n+4}}\right)
$$
and
$$
\sum_{k=1}^{n} \frac{(-1)^{k-1} L_{k+2}^2 F_{2k+4}}{L_{k+2}^4 - 25}
= \frac{5}{14} + \frac{(-1)^{n+1}}{2} \left(\frac{F_{2n+3}}{L_{n+1} L_{n+2}} -
\frac{F_{2n+5}}{L_{n+2} L_{n+3}} + \frac{F_{2n+7}}{L_{n+3} L_{n+4}}\right).
$$

The source's limiting cases are not included: the absolute values of the summands tend to
$\sqrt{5}$ and $1/\sqrt{5}$, so the summands do not tend to $0$ and neither series converges.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 10
(`jis-2024-24.6.2-prop-10`). -/
public theorem_wanted alternating_sum_fib_sq_fib_div_fib_pow_four_sub (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ (k - 1) * (Nat.fib (k + 2) : ℝ) ^ 2 *
          (Nat.fib (2 * k + 4) : ℝ) / ((Nat.fib (k + 2) : ℝ) ^ 4 - 1) =
        5 / 6 + (-1 : ℝ) ^ (n + 1) / 2 *
          ((Nat.fib (2 * n + 3) : ℝ) / ((Nat.fib (n + 1) : ℝ) * (Nat.fib (n + 2) : ℝ)) -
            (Nat.fib (2 * n + 5) : ℝ) / ((Nat.fib (n + 2) : ℝ) * (Nat.fib (n + 3) : ℝ)) +
            (Nat.fib (2 * n + 7) : ℝ) / ((Nat.fib (n + 3) : ℝ) * (Nat.fib (n + 4) : ℝ))) ∧
      ∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ (k - 1) * (lucasNumber (k + 2) : ℝ) ^ 2 *
          (Nat.fib (2 * k + 4) : ℝ) / ((lucasNumber (k + 2) : ℝ) ^ 4 - 25) =
        5 / 14 + (-1 : ℝ) ^ (n + 1) / 2 *
          ((Nat.fib (2 * n + 3) : ℝ) /
              ((lucasNumber (n + 1) : ℝ) * (lucasNumber (n + 2) : ℝ)) -
            (Nat.fib (2 * n + 5) : ℝ) /
              ((lucasNumber (n + 2) : ℝ) * (lucasNumber (n + 3) : ℝ)) +
            (Nat.fib (2 * n + 7) : ℝ) /
              ((lucasNumber (n + 3) : ℝ) * (lucasNumber (n + 4) : ℝ)))

/-- **Alternating Gelin–Cesàro sum for generalized Fibonacci sequences.** Let $p$ be a real
number, let $W : \mathbb{Z} \to \mathbb{R}$ satisfy $W_{j+2} = p W_{j+1} + W_j$ for every integer
$j$, and put $\gamma_W = (p W_0 W_1 + W_0^2 - W_1^2)(p^2 - 1)$. Let $n \ge 0$ and $k$ be
integers such that $W_{j+k-2} W_{j+k-1} W_{j+k+1} W_{j+k+2} \ne 0$ for $1 \le j \le n$ and
$W_{n+k-1}$, $W_{k-1}$, $W_{n+k+2}$, $W_{k+2}$ are nonzero. Then

$$
\sum_{j=1}^{n} \frac{(-1)^{j-1} \cdot 2 W_{j+k} (W_{j+k+1} + W_{j+k-1})
\bigl(2 W_{j+k}^2 + (-1)^{j+k} \gamma_W\bigr)}{W_{j+k-2} W_{j+k-1} W_{j+k+1} W_{j+k+2}} =
(-1)^{n+1} \frac{W_{n+k} + W_{n+k-2}}{W_{n+k-1}} + \frac{W_k + W_{k-2}}{W_{k-1}} +
(-1)^{n+1} \frac{W_{n+k+3} + W_{n+k+1}}{W_{n+k+2}} + \frac{W_{k+3} + W_{k+1}}{W_{k+2}}.
$$

The paper's standing assumption $p \ne 0$ is not needed.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 11
(`jis-2024-24.6.2-prop-11`). -/
public theorem_wanted generalized_fibonacci_gelin_cesaro_alternating_sum
    (W : ℤ → ℝ) (p : ℝ) (hW : ∀ j : ℤ, W (j + 2) = p * W (j + 1) + W j)
    (n : ℕ) (k : ℤ)
    (hden : ∀ j ∈ Finset.Icc 1 n,
      W (j + k - 2) * W (j + k - 1) * W (j + k + 1) * W (j + k + 2) ≠ 0)
    (h₁ : W (n + k - 1) ≠ 0) (h₂ : W (k - 1) ≠ 0) (h₃ : W (n + k + 2) ≠ 0)
    (h₄ : W (k + 2) ≠ 0) :
    ∑ j ∈ Finset.Icc 1 n, (-1 : ℝ) ^ (j - 1) * 2 * W (j + k) *
          (W (j + k + 1) + W (j + k - 1)) *
          (2 * W (j + k) ^ 2 + (-1 : ℝ) ^ ((j : ℤ) + k) *
            ((p * W 0 * W 1 + W 0 ^ 2 - W 1 ^ 2) * (p ^ 2 - 1))) /
          (W (j + k - 2) * W (j + k - 1) * W (j + k + 1) * W (j + k + 2)) =
      (-1 : ℝ) ^ (n + 1) * (W (n + k) + W (n + k - 2)) / W (n + k - 1) +
        (W k + W (k - 2)) / W (k - 1) +
        (-1 : ℝ) ^ (n + 1) * (W (n + k + 3) + W (n + k + 1)) / W (n + k + 2) +
        (W (k + 3) + W (k + 1)) / W (k + 2)

/-- **Reciprocal series of Lucas sequences with doubling subscripts.** Let $P \ne 0$ be an
integer and let $U_m = U_m(P, -1)$ and $V_m = V_m(P, -1)$ be the Lucas sequences with parameters
$(P, -1)$, so $U_0 = 0$, $U_1 = 1$, $V_0 = 2$, $V_1 = P$, and both satisfy
$X_{m+2} = P X_{m+1} + X_m$. For every integer $k \ge 1$ and every integer $n \ge 1$,
$$\sum_{j=0}^{n} \frac{2^j V_{k 2^j}}{U_{k 2^j}^2} = \frac{2(-1)^k + V_k}{U_k^2} +
\frac{2(1 - (-1)^k) V_{2k}}{U_{2k}^2} - \frac{2^{n+1}}{U_{k 2^n}^2},$$
and the real series $\sum_{j \ge 0} 2^j V_{k 2^j} / U_{k 2^j}^2$ has sum
$$\frac{2(-1)^k + V_k}{U_k^2} + \frac{2(1 - (-1)^k) V_{2k}}{U_{2k}^2}.$$

The paper's real parameter $p$ is restricted here to integers $P$.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 12
(`jis-2024-24.6.2-prop-12`). -/
public theorem_wanted sum_two_pow_lucasV_div_lucasU_sq_doubling
    (P : ℤ) (hP : P ≠ 0) (k : ℕ) (hk : 0 < k) :
    (∀ n : ℕ, 0 < n →
      ∑ j ∈ Finset.range (n + 1), (2 : ℝ) ^ j *
          (lucasV ⟨P, -1, by norm_num⟩ (k * 2 ^ j) : ℝ) /
            (lucasU ⟨P, -1, by norm_num⟩ (k * 2 ^ j) : ℝ) ^ 2 =
        ((-1 : ℝ) ^ k * 2 + (lucasV ⟨P, -1, by norm_num⟩ k : ℝ)) /
            (lucasU ⟨P, -1, by norm_num⟩ k : ℝ) ^ 2 +
          2 * (1 - (-1 : ℝ) ^ k) * (lucasV ⟨P, -1, by norm_num⟩ (2 * k) : ℝ) /
            (lucasU ⟨P, -1, by norm_num⟩ (2 * k) : ℝ) ^ 2 -
          (2 : ℝ) ^ (n + 1) / (lucasU ⟨P, -1, by norm_num⟩ (k * 2 ^ n) : ℝ) ^ 2) ∧
      HasSum (fun j : ℕ => (2 : ℝ) ^ j *
          (lucasV ⟨P, -1, by norm_num⟩ (k * 2 ^ j) : ℝ) /
            (lucasU ⟨P, -1, by norm_num⟩ (k * 2 ^ j) : ℝ) ^ 2)
        (((-1 : ℝ) ^ k * 2 + (lucasV ⟨P, -1, by norm_num⟩ k : ℝ)) /
            (lucasU ⟨P, -1, by norm_num⟩ k : ℝ) ^ 2 +
          2 * (1 - (-1 : ℝ) ^ k) * (lucasV ⟨P, -1, by norm_num⟩ (2 * k) : ℝ) /
            (lucasU ⟨P, -1, by norm_num⟩ (2 * k) : ℝ) ^ 2)

/-- **A Fibonacci–Lucas identity for gibonacci sequences.** Let $F_m$ denote the Fibonacci
numbers, extended to all integers $m$ by $F_{-m} = (-1)^{m+1} F_m$, and let
$L_m = F_{m-1} + F_{m+1}$ be the Lucas numbers, for every integer $m$. If
$G : \mathbb{Z} \to \mathbb{R}$ satisfies $G_{j+2} = G_{j+1} + G_j$ for every integer $j$, then
for all integers $k$ and $r$,
$$
5 F_k G_{k+r} - L_k \left(G_{k+r+1} + G_{k+r-1}\right)
= 2 (-1)^{k-1} \left(G_{r+1} + G_{r-1}\right).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 18
(`jis-2024-24.6.2-prop-18`). -/
public theorem_wanted five_fib_mul_gibonacci_sub_lucas_mul
    (L : ℤ → ℝ) (hL : ∀ m : ℤ, L m = Int.fib (m - 1) + Int.fib (m + 1))
    (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (k r : ℤ) :
    5 * (Int.fib k : ℝ) * G (k + r) - L k * (G (k + r + 1) + G (k + r - 1)) =
      (-1 : ℝ) ^ (k - 1) * 2 * (G (r + 1) + G (r - 1))

/-- **An identity for products of two gibonacci sequences.** Let
$G, H : \mathbb{Z} \to \mathbb{R}$ satisfy $G_{j+2} = G_{j+1} + G_j$ and
$H_{j+2} = H_{j+1} + H_j$ for every integer $j$. Then for all integers $k$, $r$ and $s$,
$$
5 G_k H_{k+s-r} - \left(G_{k+1} + G_{k-1}\right) \left(H_{k+s-r+1} + H_{k+s-r-1}\right)
= 2 (-1)^{k-r+1} \left(G_{r+1} + G_{r-1}\right) \left(H_{s+1} + H_{s-1}\right) +
2 (-1)^{k-r} \left(G_0 \left(H_{r+s} + H_{r+s-2}\right) +
G_1 \left(H_{r+s+1} + H_{r+s-1}\right)\right).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 19
(`jis-2024-24.6.2-prop-19`). -/
public theorem_wanted five_gibonacci_mul_sub_two_gibonacci
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (k r s : ℤ) :
    5 * G k * H (k + s - r) - (G (k + 1) + G (k - 1)) * (H (k + s - r + 1) + H (k + s - r - 1)) =
      (-1 : ℝ) ^ (k - r + 1) * 2 * (G (r + 1) + G (r - 1)) * (H (s + 1) + H (s - 1)) +
        (-1 : ℝ) ^ (k - r) * 2 *
          (G 0 * (H (r + s) + H (r + s - 2)) + G 1 * (H (r + s + 1) + H (r + s - 1)))

/-- **Addition formula for gibonacci sequences.** Let $F_m$ denote the Fibonacci numbers,
extended to all integers $m$ by $F_{-m} = (-1)^{m+1} F_m$. If $G : \mathbb{Z} \to \mathbb{R}$
satisfies $G_{j+2} = G_{j+1} + G_j$ for every integer $j$, then
$F_{k+1} G_{s+1} + F_k G_s = G_{k+s+1}$ for all integers $k$ and $s$.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 20
(`jis-2024-24.6.2-prop-20`). -/
public theorem_wanted fib_mul_gibonacci_add_eq_gibonacci
    (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (k s : ℤ) :
    (Int.fib (k + 1) : ℝ) * G (s + 1) + (Int.fib k : ℝ) * G s = G (k + s + 1)

/-- **A sum of two gibonacci products in terms of the seeds.** Let
$G, H : \mathbb{Z} \to \mathbb{R}$, written $j \mapsto G_j$ and $j \mapsto H_j$, satisfy
$G_{j+2} = G_{j+1} + G_j$ and $H_{j+2} = H_{j+1} + H_j$ for every integer $j$. Then for all
integers $k$ and $s$,
$$
H_{k+1} G_{s+1} + H_k G_s = G_0 H_{k+s} + G_1 H_{k+s+1}.
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 21
(`jis-2024-24.6.2-prop-21`). -/
public theorem_wanted gibonacci_mul_gibonacci_add_eq_seed_combination
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (k s : ℤ) :
    H (k + 1) * G (s + 1) + H k * G s = G 0 * H (k + s) + G 1 * H (k + s + 1)

/-- **d'Ocagne-type identity for two gibonacci sequences.** Let $G$ and $H$ be gibonacci
sequences, that is, functions $X : \mathbb{Z} \to \mathbb{R}$ with $X_{j+2} = X_{j+1} + X_j$
for every integer $j$. Then for all integers $r$, $s$, $k$,

$$
H_{r+s} G_{k+1} - H_{r+s+1} G_k =
(-1)^{r-1} (H_{s+1} + H_{s-1}) G_{k-r} + (-1)^r (G_0 H_{k+s-r-1} + G_1 H_{k+s-r}).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 23
(`jis-2024-24.6.2-prop-23`). -/
public theorem_wanted gibonacci_dOcagne_type_identity
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (r s k : ℤ) :
    H (r + s) * G (k + 1) - H (r + s + 1) * G k =
      (-1 : ℝ) ^ (r - 1) * (H (s + 1) + H (s - 1)) * G (k - r) +
        (-1 : ℝ) ^ r * (G 0 * H (k + s - r - 1) + G 1 * H (k + s - r))

/-- **Shifted product identity for two gibonacci sequences.** Let
$G, H : \mathbb{Z} \to \mathbb{R}$, written $j \mapsto G_j$ and $j \mapsto H_j$, satisfy
$G_{j+2} = G_{j+1} + G_j$ and $H_{j+2} = H_{j+1} + H_j$ for every integer $j$. Then for all
integers $s$ and $k$,
$$
G_{k+1} H_{s+1} + G_{k-2} H_{s-2} = 2 G_k H_s + 2 G_{k-1} H_{s-1}.
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 24
(`jis-2024-24.6.2-prop-24`). -/
public theorem_wanted gibonacci_product_shift_identity
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (s k : ℤ) :
    G (k + 1) * H (s + 1) + G (k - 2) * H (s - 2) = 2 * G k * H s + 2 * G (k - 1) * H (s - 1)

/-- **Product recurrence for three gibonacci sequences.** Let
$G, H, I : \mathbb{Z} \to \mathbb{R}$, written $j \mapsto G_j$, $j \mapsto H_j$ and
$j \mapsto I_j$, satisfy $G_{j+2} = G_{j+1} + G_j$, $H_{j+2} = H_{j+1} + H_j$ and
$I_{j+2} = I_{j+1} + I_j$ for every integer $j$. Then for all integers $k$, $r$ and $s$,
$$
G_{k+1} H_{r+1} I_{s+1} = 3 G_k H_r I_s + 6 G_{k-1} H_{r-1} I_{s-1} -
3 G_{k-2} H_{r-2} I_{s-2} - G_{k-3} H_{r-3} I_{s-3}.
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 25
(`jis-2024-24.6.2-prop-25`). -/
public theorem_wanted gibonacci_triple_product_recurrence
    (G H I : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j)
    (hI : ∀ j : ℤ, I (j + 2) = I (j + 1) + I j) (k r s : ℤ) :
    G (k + 1) * H (r + 1) * I (s + 1) =
      3 * G k * H r * I s + 6 * G (k - 1) * H (r - 1) * I (s - 1) -
        3 * G (k - 2) * H (r - 2) * I (s - 2) - G (k - 3) * H (r - 3) * I (s - 3)

/-- **Gibonacci index doubling via Fibonacci squares.** Let $F_m$ be the Fibonacci numbers
extended to all integers $m$ ($F_0 = 0$, $F_1 = 1$, $F_{m+2} = F_{m+1} + F_m$), and let
$G \colon \mathbb{Z} \to \mathbb{R}$ satisfy $G_{j+2} = G_{j+1} + G_j$ for every integer $j$.
Then for all integers $k$, $s$,
$$G_{2k+s} = F_{k+1}^2 G_{s+1} + F_k^2 G_s - F_{k-1}^2 G_{s-1}.$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 26
(`jis-2024-24.6.2-prop-26`). -/
public theorem_wanted gibonacci_two_mul_add_eq_fib_sq_combination
    (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (k s : ℤ) :
    G (2 * k + s) = (Int.fib (k + 1) : ℝ) ^ 2 * G (s + 1) + (Int.fib k : ℝ) ^ 2 * G s -
      (Int.fib (k - 1) : ℝ) ^ 2 * G (s - 1)

/-- **Seed expansion of a triple gibonacci product.** Let $G, H, I \colon \mathbb{Z} \to \mathbb{R}$
satisfy $G_{j+2} = G_{j+1} + G_j$, $H_{j+2} = H_{j+1} + H_j$ and $I_{j+2} = I_{j+1} + I_j$ for
every integer $j$. Then for all integers $k$, $r$, $s$,
$$G_0 H_0 I_{k+r+s-2} + (G_0 H_1 + G_1 H_0) I_{k+r+s-1} + G_1 H_1 I_{k+r+s}
= G_{s+1} H_{r+1} I_{k+1} + G_s H_r I_k - G_{s-1} H_{r-1} I_{k-1}.$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 27
(`jis-2024-24.6.2-prop-27`). -/
public theorem_wanted gibonacci_triple_product_seed_identity
    (G H I : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j)
    (hI : ∀ j : ℤ, I (j + 2) = I (j + 1) + I j) (k r s : ℤ) :
    G 0 * H 0 * I (k + r + s - 2) + (G 0 * H 1 + G 1 * H 0) * I (k + r + s - 1) +
        G 1 * H 1 * I (k + r + s) =
      G (s + 1) * H (r + 1) * I (k + 1) + G s * H r * I k - G (s - 1) * H (r - 1) * I (k - 1)

/-- **Lucas expansion of shifted gibonacci sums.** Let $F_m$ be the Fibonacci numbers, extended
to all integers $m$ by $F_{m+2} = F_{m+1} + F_m$, and let $L_m = F_{m-1} + F_{m+1}$ be the
Lucas numbers. Let $G : \mathbb{Z} \to \mathbb{R}$ be a gibonacci sequence, that is,
$G_{j+2} = G_{j+1} + G_j$ for every integer $j$. Then for all integers $k$ and $r$,
$G_{k+r+1} + G_{k+r-1} = L_k G_{r+1} + L_{k-1} G_r$.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 28
(`jis-2024-24.6.2-prop-28`). -/
public theorem_wanted gibonacci_add_gibonacci_eq_lucas_combination
    (L : ℤ → ℝ) (hL : ∀ m : ℤ, L m = Int.fib (m - 1) + Int.fib (m + 1))
    (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (k r : ℤ) :
    G (k + r + 1) + G (k + r - 1) = L k * G (r + 1) + L (k - 1) * G r

/-- **Seed form of a Lucas-type product identity for two gibonacci sequences.** Let
$G, H : \mathbb{Z} \to \mathbb{R}$, written $j \mapsto G_j$ and $j \mapsto H_j$, satisfy
$G_{j+2} = G_{j+1} + G_j$ and $H_{j+2} = H_{j+1} + H_j$ for every integer $j$. Then for all
integers $k$ and $r$,
$$
G_0 (H_{r+k} + H_{r+k-2}) + G_1 (H_{r+k+1} + H_{r+k-1}) =
G_r (H_k + H_{k-2}) + G_{r+1} (H_{k+1} + H_{k-1}).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 29
(`jis-2024-24.6.2-prop-29`). -/
public theorem_wanted gibonacci_seed_lucas_like_identity
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (k r : ℤ) :
    G 0 * (H (r + k) + H (r + k - 2)) + G 1 * (H (r + k + 1) + H (r + k - 1)) =
      G r * (H k + H (k - 2)) + G (r + 1) * (H (k + 1) + H (k - 1))

/-- **Sum of products of two gibonacci sequences.** Let $G, H \colon \mathbb{Z} \to \mathbb{R}$
satisfy $G_{j+2} = G_{j+1} + G_j$ and $H_{j+2} = H_{j+1} + H_j$ for every integer $j$. For every
natural number $n$ and all integers $k$ and $s$,
$$2 \sum_{j=1}^{n} G_{j+k} H_{j+s} = G_{n+k} H_{n+s+1} + G_{n+k+1} H_{n+s} -
G_{k+1} H_s - G_k H_{s+1}.$$

The printed statement lacks the factor $2$: it fails for the Fibonacci sequence $G = H = F$
with $k = s = 0$ and $n = 1$, where the left side is $1$ and the right side $2$. The paper's own
derivation (its display before the proposition) carries the factor $2$.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 30
(`jis-2024-24.6.2-prop-30`). -/
public theorem_wanted two_mul_sum_gibonacci_mul_gibonacci
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (n : ℕ) (k s : ℤ) :
    2 * ∑ j ∈ Finset.Icc 1 n, G (j + k) * H (j + s) =
      G (n + k) * H (n + s + 1) + G (n + k + 1) * H (n + s) - G (k + 1) * H s -
        G k * H (s + 1)

/-- **Hoggatt–Bicknell-type binomial sum with Fibonacci cubes.** Let $F_m$ denote the Fibonacci
numbers, extended to all integers $m$ by $F_{-m} = (-1)^{m+1} F_m$. If
$G : \mathbb{Z} \to \mathbb{R}$ satisfies $G_{j+2} = G_{j+1} + G_j$ for every integer $j$, then
for every natural number $n$ and all integers $k$ and $r$,
$$
\sum_{j=0}^{4n+1} (-1)^{j+1} \binom{4n+1}{j} F_{j+k}^3 G_{j+r}
= 25^n \left(F_{2n+k+1}^3 G_{2n+r+1} - F_{2n+k}^3 G_{2n+r}\right).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 31
(`jis-2024-24.6.2-prop-31`). -/
public theorem_wanted alternating_binomial_sum_fib_cube_mul_gibonacci
    (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (n : ℕ) (k r : ℤ) :
    ∑ j ∈ Finset.range (4 * n + 2), -(-1 : ℝ) ^ j * ((4 * n + 1).choose j : ℝ) *
        (Int.fib (j + k) : ℝ) ^ 3 * G (j + r) =
      (25 : ℝ) ^ n * ((Int.fib (2 * n + k + 1) : ℝ) ^ 3 * G (2 * n + r + 1) -
        (Int.fib (2 * n + k) : ℝ) ^ 3 * G (2 * n + r))

/-- **Hoggatt–Bicknell-type binomial sum of four gibonacci sequences.** Let
$E, G, H, I : \mathbb{Z} \to \mathbb{R}$ satisfy $E_{j+2} = E_{j+1} + E_j$ for every integer $j$,
and likewise $G$, $H$ and $I$. Then for every natural number $n$ and all integers $k$, $r$, $s$
and $t$,
$$
\sum_{j=0}^{4n+1} (-1)^{j+1} \binom{4n+1}{j} E_{j+k} G_{j+r} H_{j+s} I_{j+t}
= 25^n \left(E_{2n+k+1} G_{2n+r+1} H_{2n+s+1} I_{2n+t+1} -
E_{2n+k} G_{2n+r} H_{2n+s} I_{2n+t}\right).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 32
(`jis-2024-24.6.2-prop-32`). -/
public theorem_wanted alternating_binomial_sum_four_gibonacci_product
    (E G H I : ℤ → ℝ) (hE : ∀ j : ℤ, E (j + 2) = E (j + 1) + E j)
    (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j)
    (hI : ∀ j : ℤ, I (j + 2) = I (j + 1) + I j) (n : ℕ) (k r s t : ℤ) :
    ∑ j ∈ Finset.range (4 * n + 2), -(-1 : ℝ) ^ j * ((4 * n + 1).choose j : ℝ) *
        E (j + k) * G (j + r) * H (j + s) * I (j + t) =
      (25 : ℝ) ^ n *
        (E (2 * n + k + 1) * G (2 * n + r + 1) * H (2 * n + s + 1) * I (2 * n + t + 1) -
          E (2 * n + k) * G (2 * n + r) * H (2 * n + s) * I (2 * n + t))

/-- **Mixed Melham-type sum for two gibonacci sequences.** Let $F_m$ be the Fibonacci numbers
($F_0 = 0$, $F_1 = 1$, $F_{m+2} = F_{m+1} + F_m$), and let $G, H \colon \mathbb{Z} \to \mathbb{R}$
satisfy $G_{j+2} = G_{j+1} + G_j$ and $H_{j+2} = H_{j+1} + H_j$ for every integer $j$. Then for
every natural number $n$ and all integers $k$, $r$,
$$6 \Bigl(\sum_{j=0}^{2n-1} G_{k+j}^2\Bigr) \Bigl(\sum_{j=0}^{2n-1} H_{r+j} G_{k+j}\Bigr)
= F_{2n}^2 \bigl(H_{r+n-2} G_{k+n-2}^3 + 4 H_{r+n-1} G_{k+n-1}^3 +
4 H_{r+n} G_{k+n}^3 + H_{r+n+1} G_{k+n+1}^3\bigr).$$

The paper leaves $n$ unquantified; it is taken as a natural number, as in
Proposition 8.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 33
(`jis-2024-24.6.2-prop-33`). -/
public theorem_wanted six_mul_sum_gibonacci_sq_mul_sum_mixed
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (n : ℕ) (k r : ℤ) :
    6 * (∑ j ∈ Finset.range (2 * n), G (k + j) ^ 2) *
        (∑ j ∈ Finset.range (2 * n), H (r + j) * G (k + j)) =
      (Nat.fib (2 * n) : ℝ) ^ 2 *
        (H (r + n - 2) * G (k + n - 2) ^ 3 + 4 * H (r + n - 1) * G (k + n - 1) ^ 3 +
          4 * H (r + n) * G (k + n) ^ 3 + H (r + n + 1) * G (k + n + 1) ^ 3)

/-- **Four-sequence Melham-type identity for gibonacci sequences.** Let
$G, H, I, J : \mathbb{Z} \to \mathbb{R}$ satisfy $G_{j+2} = G_{j+1} + G_j$ for every integer $j$,
and likewise $H$, $I$ and $J$, and let $F_m$ denote the Fibonacci numbers. For every natural
number $n$ and all integers $k$, $r$, $s$ and $t$, writing
$S(X, x; Y, y) = \sum_{j=0}^{2n-1} X_{x+j} Y_{y+j}$ for sequences $X, Y$ and integers $x, y$,
$$
2 S(G, k; J, t) S(H, r; I, s) + 2 S(I, s; J, t) S(G, k; H, r) +
2 S(G, k; I, s) S(H, r; J, t)
= F_{2n}^2 \big(G_{k+n-2} H_{r+n-2} I_{s+n-2} J_{t+n-2} +
4 G_{k+n-1} H_{r+n-1} I_{s+n-1} J_{t+n-1} + 4 G_{k+n} H_{r+n} I_{s+n} J_{t+n} +
G_{k+n+1} H_{r+n+1} I_{s+n+1} J_{t+n+1}\big).
$$

The source leaves $n$ unquantified; it is taken to be a natural number.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 34
(`jis-2024-24.6.2-prop-34`). -/
public theorem_wanted four_gibonacci_melham_type_identity
    (G H I J : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j)
    (hI : ∀ j : ℤ, I (j + 2) = I (j + 1) + I j)
    (hJ : ∀ j : ℤ, J (j + 2) = J (j + 1) + J j) (n : ℕ) (k r s t : ℤ) :
    2 * (∑ j ∈ Finset.range (2 * n), G (k + j) * J (t + j)) *
          (∑ j ∈ Finset.range (2 * n), H (r + j) * I (s + j)) +
        2 * (∑ j ∈ Finset.range (2 * n), I (s + j) * J (t + j)) *
          (∑ j ∈ Finset.range (2 * n), G (k + j) * H (r + j)) +
        2 * (∑ j ∈ Finset.range (2 * n), G (k + j) * I (s + j)) *
          (∑ j ∈ Finset.range (2 * n), H (r + j) * J (t + j)) =
      (Nat.fib (2 * n) : ℝ) ^ 2 *
        (G (k + n - 2) * H (r + n - 2) * I (s + n - 2) * J (t + n - 2) +
          4 * G (k + n - 1) * H (r + n - 1) * I (s + n - 1) * J (t + n - 1) +
          4 * G (k + n) * H (r + n) * I (s + n) * J (t + n) +
          G (k + n + 1) * H (r + n + 1) * I (s + n + 1) * J (t + n + 1))

/-- **Two-sequence gibonacci identity with a Fibonacci factor.** Let
$G, H : \mathbb{Z} \to \mathbb{R}$, written $j \mapsto G_j$ and $j \mapsto H_j$, satisfy
$G_{j+2} = G_{j+1} + G_j$ and $H_{j+2} = H_{j+1} + H_j$ for every integer $j$, and let $F_m$ be
the Fibonacci numbers, extended to negative indices by $F_{-m} = (-1)^{m+1} F_m$. Then for all
integers $r$, $s$ and $k$,
$$
H_s G_{k+r} + (-1)^{r-1} H_{s-r} G_k = F_r (G_0 H_{k+s-1} + G_1 H_{k+s}).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 35
(`jis-2024-24.6.2-prop-35`). -/
public theorem_wanted gibonacci_mul_add_neg_one_pow_eq_fib_mul
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (r s k : ℤ) :
    H s * G (k + r) + (-1 : ℝ) ^ (r - 1) * H (s - r) * G k =
      (Int.fib r : ℝ) * (G 0 * H (k + s - 1) + G 1 * H (k + s))

/-- **Four-index product identity for two gibonacci sequences.** Let
$G, H : \mathbb{Z} \to \mathbb{R}$, written $j \mapsto G_j$ and $j \mapsto H_j$, satisfy
$G_{j+2} = G_{j+1} + G_j$ and $H_{j+2} = H_{j+1} + H_j$ for every integer $j$, and let $F_m$ be
the Fibonacci numbers, extended to negative indices by $F_{-m} = (-1)^{m+1} F_m$. Then for all
integers $k$, $r$, $s$ and $t$,
$$
F_s (G_0 H_{k+r+t-1} + G_1 H_{k+r+t}) - (-1)^r F_{s-r} G_k (H_{t+1} + H_{t-1}) +
(-1)^r G_k H_{s-r+t} = G_{k+s} H_{r+t}.
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 36
(`jis-2024-24.6.2-prop-36`). -/
public theorem_wanted gibonacci_product_four_index_identity
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (k r s t : ℤ) :
    (Int.fib s : ℝ) * (G 0 * H (k + r + t - 1) + G 1 * H (k + r + t)) -
        (-1 : ℝ) ^ r * (Int.fib (s - r) : ℝ) * G k * (H (t + 1) + H (t - 1)) +
        (-1 : ℝ) ^ r * G k * H (s - r + t) =
      G (k + s) * H (r + t)

/-- **Two-sequence Candido-type identity for gibonacci sequences.** Let $G$ and $H$ be gibonacci
sequences, that is, functions $X : \mathbb{Z} \to \mathbb{R}$ with $X_{j+2} = X_{j+1} + X_j$
for every integer $j$. Then for all integers $r$ and $k$,

$$
2 (H_r G_k^3 + H_{r+1} G_{k+1}^3 + H_{r+2} G_{k+2}^3) =
(G_k^2 + G_{k+1}^2 + G_{k+2}^2)(H_r G_k + H_{r+1} G_{k+1} + H_{r+2} G_{k+2}).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 37
(`jis-2024-24.6.2-prop-37`). -/
public theorem_wanted gibonacci_candido_two_sequence
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (r k : ℤ) :
    2 * (H r * G k ^ 3 + H (r + 1) * G (k + 1) ^ 3 + H (r + 2) * G (k + 2) ^ 3) =
      (G k ^ 2 + G (k + 1) ^ 2 + G (k + 2) ^ 2) *
        (H r * G k + H (r + 1) * G (k + 1) + H (r + 2) * G (k + 2))

/-- **Four-sequence Candido-type identity for gibonacci sequences.** Let $G$, $H$, $M$, $N$ be
gibonacci sequences, that is, functions $X : \mathbb{Z} \to \mathbb{R}$ with
$X_{j+2} = X_{j+1} + X_j$ for every integer $j$. For two such sequences $X$, $Y$ and integers
$x$, $y$ write $T(X, x; Y, y) = X_x Y_y + X_{x+1} Y_{y+1} + X_{x+2} Y_{y+2}$. Then for all
integers $k$, $r$, $s$, $t$,

$$
6 (G_k H_r M_s N_t + G_{k+1} H_{r+1} M_{s+1} N_{t+1} + G_{k+2} H_{r+2} M_{s+2} N_{t+2}) =
T(G, k; M, s) \, T(H, r; N, t) + T(G, k; H, r) \, T(M, s; N, t) +
T(G, k; N, t) \, T(H, r; M, s).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 38
(`jis-2024-24.6.2-prop-38`). -/
public theorem_wanted gibonacci_candido_four_sequence
    (G H M N : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j)
    (hM : ∀ j : ℤ, M (j + 2) = M (j + 1) + M j)
    (hN : ∀ j : ℤ, N (j + 2) = N (j + 1) + N j) (k r s t : ℤ) :
    6 * (G k * H r * M s * N t + G (k + 1) * H (r + 1) * M (s + 1) * N (t + 1) +
        G (k + 2) * H (r + 2) * M (s + 2) * N (t + 2)) =
      (G k * M s + G (k + 1) * M (s + 1) + G (k + 2) * M (s + 2)) *
          (H r * N t + H (r + 1) * N (t + 1) + H (r + 2) * N (t + 2)) +
        (G k * H r + G (k + 1) * H (r + 1) + G (k + 2) * H (r + 2)) *
          (M s * N t + M (s + 1) * N (t + 1) + M (s + 2) * N (t + 2)) +
        (G k * N t + G (k + 1) * N (t + 1) + G (k + 2) * N (t + 2)) *
          (H r * M s + H (r + 1) * M (s + 1) + H (r + 2) * M (s + 2))

/-- **Lucas multiplier identity for gibonacci sequences.** Let $F_m$ be the Fibonacci numbers,
extended to all integers $m$ by $F_{m+2} = F_{m+1} + F_m$, and let $L_m = F_{m-1} + F_{m+1}$ be
the Lucas numbers. Let $G : \mathbb{Z} \to \mathbb{R}$ be a gibonacci sequence, that is,
$G_{j+2} = G_{j+1} + G_j$ for every integer $j$. Then for all integers $r$ and $s$,
$G_{s+r} + (-1)^r G_{s-r} = L_r G_s$.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 39
(`jis-2024-24.6.2-prop-39`). -/
public theorem_wanted gibonacci_add_neg_one_pow_mul_eq_lucas_mul
    (L : ℤ → ℝ) (hL : ∀ m : ℤ, L m = Int.fib (m - 1) + Int.fib (m + 1))
    (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (r s : ℤ) :
    G (s + r) + (-1 : ℝ) ^ r * G (s - r) = L r * G s

/-- **Two-sequence gibonacci identity with a Fibonacci factor and Lucas-type sums.** Let
$G, H : \mathbb{Z} \to \mathbb{R}$, written $j \mapsto G_j$ and $j \mapsto H_j$, satisfy
$G_{j+2} = G_{j+1} + G_j$ and $H_{j+2} = H_{j+1} + H_j$ for every integer $j$, and let $F_m$ be
the Fibonacci numbers, extended to negative indices by $F_{-m} = (-1)^{m+1} F_m$. Then for all
integers $r$, $k$ and $s$,
$$
G_s (H_{r+k+1} + H_{r+k-1}) + (-1)^{r-1} G_{s-r} (H_{k+1} + H_{k-1}) =
G_0 F_r (H_{k+s} + H_{k+s-2}) + G_1 F_r (H_{k+s+1} + H_{k+s-1}).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 40
(`jis-2024-24.6.2-prop-40`). -/
public theorem_wanted gibonacci_lucas_like_mul_add_eq_fib_mul
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (r k s : ℤ) :
    G s * (H (r + k + 1) + H (r + k - 1)) +
        (-1 : ℝ) ^ (r - 1) * G (s - r) * (H (k + 1) + H (k - 1)) =
      G 0 * (Int.fib r : ℝ) * (H (k + s) + H (k + s - 2)) +
        G 1 * (Int.fib r : ℝ) * (H (k + s + 1) + H (k + s - 1))

/-- **Two-sequence Gelin–Cesàro derivative identity for gibonacci sequences.** Let
$G, H : \mathbb{Z} \to \mathbb{R}$, written $j \mapsto G_j$ and $j \mapsto H_j$, satisfy
$G_{j+2} = G_{j+1} + G_j$ and $H_{j+2} = H_{j+1} + H_j$ for every integer $j$, and put
$e_G = G_0^2 - G_1^2 + G_0 G_1$. Then for all integers $k$ and $r$,
$$
H_{k+r-2} G_{k-1} G_{k+1} G_{k+2} + G_{k-2} H_{k+r-1} G_{k+1} G_{k+2} +
G_{k-2} G_{k-1} H_{k+r+1} G_{k+2} + G_{k-2} G_{k-1} G_{k+1} H_{k+r+2} =
4 H_{k+r} G_k^3 - 2 e_G G_0 (H_{r+2} + H_r) + 2 e_G G_1 (H_{r+1} + H_{r-1}).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 42
(`jis-2024-24.6.2-prop-42`). -/
public theorem_wanted gibonacci_gelin_cesaro_two_sequence
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (k r : ℤ) :
    H (k + r - 2) * G (k - 1) * G (k + 1) * G (k + 2) +
        G (k - 2) * H (k + r - 1) * G (k + 1) * G (k + 2) +
        G (k - 2) * G (k - 1) * H (k + r + 1) * G (k + 2) +
        G (k - 2) * G (k - 1) * G (k + 1) * H (k + r + 2) =
      4 * H (k + r) * G k ^ 3 -
        2 * (G 0 ^ 2 - G 1 ^ 2 + G 0 * G 1) * G 0 * (H (r + 2) + H r) +
        2 * (G 0 ^ 2 - G 1 ^ 2 + G 0 * G 1) * G 1 * (H (r + 1) + H (r - 1))

/-- **Catalan-type identity for Fibonacci and gibonacci numbers.** Let $F_m$ denote the Fibonacci
numbers, extended to all integers $m$ by $F_{-m} = (-1)^{m+1} F_m$. If
$G : \mathbb{Z} \to \mathbb{R}$ satisfies $G_{j+2} = G_{j+1} + G_j$ for every integer $j$, then
for all integers $k$, $r$ and $s$,
$$
F_{k+r} G_{k-r+s} + F_{k-r} G_{k+r+s}
= 2 F_k G_{k+s} + (-1)^{k+r+1} F_r^2 \left(G_{s+1} + G_{s-1}\right).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 43
(`jis-2024-24.6.2-prop-43`). -/
public theorem_wanted fib_gibonacci_catalan_type_identity
    (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (k r s : ℤ) :
    (Int.fib (k + r) : ℝ) * G (k - r + s) + (Int.fib (k - r) : ℝ) * G (k + r + s) =
      2 * (Int.fib k : ℝ) * G (k + s) +
        (-1 : ℝ) ^ (k + r + 1) * (Int.fib r : ℝ) ^ 2 * (G (s + 1) + G (s - 1))

/-- **Lucas-weighted identity for two gibonacci sequences.** Let $F_m$ be the Fibonacci numbers
extended to all integers $m$ ($F_0 = 0$, $F_1 = 1$, $F_{m+2} = F_{m+1} + F_m$) and
$L_m = F_{m-1} + F_{m+1}$ the Lucas numbers, and let $G, H \colon \mathbb{Z} \to \mathbb{R}$
satisfy $G_{j+2} = G_{j+1} + G_j$ and $H_{j+2} = H_{j+1} + H_j$ for every integer $j$. Then for
all integers $r$, $s$, $t$,
$$L_r (G_0 H_{s+t-1} + G_1 H_{s+t}) - (-1)^r G_{s-r} (H_{t+1} + H_{t-1})
= H_{r+t} (G_{s+1} + G_{s-1}).$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 44
(`jis-2024-24.6.2-prop-44`). -/
public theorem_wanted lucas_mul_gibonacci_seed_sub_eq
    (L : ℤ → ℝ) (hL : ∀ m : ℤ, L m = Int.fib (m - 1) + Int.fib (m + 1))
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (r s t : ℤ) :
    L r * (G 0 * H (s + t - 1) + G 1 * H (s + t)) -
        (-1 : ℝ) ^ r * G (s - r) * (H (t + 1) + H (t - 1)) =
      H (r + t) * (G (s + 1) + G (s - 1))

/-- **Two-sequence Catalan-type identity for gibonacci sequences.** Let $F_m$ be the Fibonacci
numbers, extended to all integers $m$ by $F_{m+2} = F_{m+1} + F_m$, and let $G$ and $H$ be
gibonacci sequences, that is, functions $X : \mathbb{Z} \to \mathbb{R}$ with
$X_{j+2} = X_{j+1} + X_j$ for every integer $j$. Then for all integers $k$, $r$, $s$, $t$,

$$
G_{k+s-r} H_{k+r+t} + G_{k+s+r} H_{k-r+t} =
2 G_{k+s} H_{k+t} +
(-1)^{k+r} F_r^2 \bigl(G_0 (H_{s+t} + H_{s+t-2}) + G_1 (H_{s+t+1} + H_{s+t-1})\bigr) -
(-1)^{k+r} F_r^2 (G_{s+1} + G_{s-1}) (H_{t+1} + H_{t-1}).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 45
(`jis-2024-24.6.2-prop-45`). -/
public theorem_wanted gibonacci_catalan_type_two_sequence
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (k r s t : ℤ) :
    G (k + s - r) * H (k + r + t) + G (k + s + r) * H (k - r + t) =
      2 * G (k + s) * H (k + t) +
        (-1 : ℝ) ^ (k + r) * (Int.fib r : ℝ) ^ 2 *
          (G 0 * (H (s + t) + H (s + t - 2)) + G 1 * (H (s + t + 1) + H (s + t - 1))) -
        (-1 : ℝ) ^ (k + r) * (Int.fib r : ℝ) ^ 2 *
          (G (s + 1) + G (s - 1)) * (H (t + 1) + H (t - 1))

/-- **Gibonacci identity with Fibonacci-square denominators.** Let $G : \mathbb{Z} \to \mathbb{R}$,
written $j \mapsto G_j$, satisfy $G_{j+2} = G_{j+1} + G_j$ for every integer $j$, and let $F_m$ be
the Fibonacci numbers, extended to negative indices by $F_{-m} = (-1)^{m+1} F_m$. Then for all
integers $r$ and $k$,
$$
\frac{G_{r+2}}{F_{2k}^2 + 1} - \frac{G_r}{F_{2k+2}^2 + 1} =
\frac{G_{2k+r+3} + G_{2k+r+1}}{F_{2k+1} (F_{2k+1}^2 + 1)} - \frac{G_{r+1}}{F_{2k+1}^2 + 1}.
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 46
(`jis-2024-24.6.2-prop-46`). -/
public theorem_wanted gibonacci_div_fib_sq_add_one_identity
    (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (r k : ℤ) :
    G (r + 2) / ((Int.fib (2 * k) : ℝ) ^ 2 + 1) - G r / ((Int.fib (2 * k + 2) : ℝ) ^ 2 + 1) =
      (G (2 * k + r + 3) + G (2 * k + r + 1)) /
          ((Int.fib (2 * k + 1) : ℝ) * ((Int.fib (2 * k + 1) : ℝ) ^ 2 + 1)) -
        G (r + 1) / ((Int.fib (2 * k + 1) : ℝ) ^ 2 + 1)

/-- **Ratio form of the Binet formula for Horadam sequences.** Let $P$, $Q$, $\sigma$, $\tau$ be
real numbers with $Q \neq 0$, $\sigma + \tau = P$ and $\sigma \tau = Q$, and let
$W \colon \mathbb{Z} \to \mathbb{R}$ satisfy $W_{j+2} = P W_{j+1} - Q W_j$ for every integer $j$.
Then for every integer $k$: if $W_1 \neq \sigma W_0$, then
$$\frac{W_{k+1} - \sigma W_k}{W_1 - \sigma W_0} = \tau^k,$$
and if $W_1 \neq \tau W_0$, then
$$\frac{W_{k+1} - \tau W_k}{W_1 - \tau W_0} = \sigma^k.$$

This covers the paper's sequence $W_j(W_0, W_1; p)$, the case $P = p$, $Q = -1$.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Lemma 47
(`jis-2024-24.6.2-lem-47`). -/
public theorem_wanted horadam_sub_root_mul_div_eq_zpow
    (W : ℤ → ℝ) (P Q σ τ : ℝ) (hQ : Q ≠ 0)
    (hW : ∀ j : ℤ, W (j + 2) = P * W (j + 1) - Q * W j)
    (hsum : σ + τ = P) (hprod : σ * τ = Q) (k : ℤ) :
    (W 1 - σ * W 0 ≠ 0 → (W (k + 1) - σ * W k) / (W 1 - σ * W 0) = τ ^ k) ∧
      (W 1 - τ * W 0 ≠ 0 → (W (k + 1) - τ * W k) / (W 1 - τ * W 0) = σ ^ k)

/-- **Product exchange identity for two Horadam sequences.** Let $P$, $Q$ be real numbers with
$Q \neq 0$, and let $W, Z \colon \mathbb{Z} \to \mathbb{R}$ satisfy
$W_{j+2} = P W_{j+1} - Q W_j$ and $Z_{j+2} = P Z_{j+1} - Q Z_j$ for every integer $j$. Then for
all integers $r$, $k$,
$$Z_r W_{k+1} - Q Z_{r-1} W_k = W_1 Z_{k+r} - Q W_0 Z_{k+r-1}.$$

The paper states this for $Q < 0$; the identity holds for every $Q \neq 0$.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 48
(`jis-2024-24.6.2-prop-48`). -/
public theorem_wanted horadam_product_exchange_identity
    (W Z : ℤ → ℝ) (P Q : ℝ) (hQ : Q ≠ 0)
    (hW : ∀ j : ℤ, W (j + 2) = P * W (j + 1) - Q * W j)
    (hZ : ∀ j : ℤ, Z (j + 2) = P * Z (j + 1) - Q * Z j) (r k : ℤ) :
    Z r * W (k + 1) - Q * Z (r - 1) * W k = W 1 * Z (k + r) - Q * W 0 * Z (k + r - 1)

/-- **Companion Lucas sequence identity for Horadam sequences.** Let $P$, $Q$ be real numbers
with $Q \neq 0$. Let $W \colon \mathbb{Z} \to \mathbb{R}$ satisfy $W_{j+2} = P W_{j+1} - Q W_j$
for every integer $j$, and let $V \colon \mathbb{Z} \to \mathbb{R}$ (the companion Lucas sequence)
satisfy the same recurrence with $V_0 = 2$ and $V_1 = P$. Then for all integers $k$, $r$,
$$V_r W_{k+1} - Q V_{r-1} W_k = W_{k+r+1} - Q W_{k+r-1}.$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 49
(`jis-2024-24.6.2-prop-49`). -/
public theorem_wanted horadam_companion_lucas_mul_identity
    (V W : ℤ → ℝ) (P Q : ℝ) (hQ : Q ≠ 0)
    (hV : ∀ j : ℤ, V (j + 2) = P * V (j + 1) - Q * V j) (hV0 : V 0 = 2) (hV1 : V 1 = P)
    (hW : ∀ j : ℤ, W (j + 2) = P * W (j + 1) - Q * W j) (k r : ℤ) :
    V r * W (k + 1) - Q * V (r - 1) * W k = W (k + r + 1) - Q * W (k + r - 1)

/-- **Companion Binet formula for generalized Fibonacci sequences.** Let $p$ be a real number and
let $W : \mathbb{Z} \to \mathbb{R}$ satisfy $W_{j+2} = p W_{j+1} + W_j$ for every integer $j$. Put
$\sigma = (p + \sqrt{p^2 + 4})/2$ and $\tau = (p - \sqrt{p^2 + 4})/2$. Then for every integer
$j$,
$$
(W_1 - W_0 \tau) \sigma^j + (W_1 - W_0 \sigma) \tau^j = W_{j+1} + W_{j-1}.
$$

Here $A = W_1 - W_0 \tau$ and $B = W_1 - W_0 \sigma$ are the Binet constants of $W$, so that
$W_j = (A \sigma^j - B \tau^j)/(\sigma - \tau)$.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Lemma 13
(`jis-2024-24.6.2-lem-13`). -/
public theorem_wanted generalizedFibonacci_binet_add_eq_add
    (W : ℤ → ℝ) (p : ℝ) (hW : ∀ j : ℤ, W (j + 2) = p * W (j + 1) + W j) (σ τ : ℝ)
    (hσ : σ = (p + √(p ^ 2 + 4)) / 2) (hτ : τ = (p - √(p ^ 2 + 4)) / 2) (j : ℤ) :
    (W 1 - W 0 * τ) * σ ^ j + (W 1 - W 0 * σ) * τ ^ j = W (j + 1) + W (j - 1)

/-- **Derivative of a branch of $\lambda^x$ for negative $\lambda$.** Let $\lambda < 0$ be real
and $m$ an integer, and consider the branch $\lambda^y = (-\lambda)^y e^{i\pi(2m+1)y}$, a function
of real $y$ with complex values, where $(-\lambda)^y$ is the real power of the positive number
$-\lambda$. For every real $x$ this function has derivative
$\lambda^x \bigl(i\pi(2m+1) + \ln(-\lambda)\bigr)$ at $x$. The branch corresponds to the
journal proof's evaluation $\ln(-1) = i\pi(2m+1)$.

The case of a positive base, where $\lambda^x$ has derivative $\lambda^x \ln \lambda$, is standard
and is not part of this statement.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Lemma 14
(`jis-2024-24.6.2-lem-14`). -/
public theorem_wanted hasDerivAt_neg_rpow_branch (lam : ℝ) (hlam : lam < 0) (m : ℤ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => (((-lam) ^ y : ℝ) : ℂ) * Complex.exp (Real.pi * (2 * m + 1) * y * Complex.I))
      ((((-lam) ^ x : ℝ) : ℂ) * Complex.exp (Real.pi * (2 * m + 1) * x * Complex.I) *
        (Real.pi * (2 * m + 1) * Complex.I + Real.log (-lam))) x

/-- **Real part of the derivative of the generalized Fibonacci function at integers.** Let $p$
be a real number and let $W : \mathbb{Z} \to \mathbb{R}$ satisfy $W_{j+2} = p W_{j+1} + W_j$ for
every integer $j$. Put $\delta = \sqrt{p^2 + 4}$, $\sigma = (p + \delta)/2$,
$\tau = (p - \delta)/2$, $A = W_1 - W_0 \tau$ and $B = W_1 - W_0 \sigma$. For an integer $m$,
define $w : \mathbb{R} \to \mathbb{C}$ by

$$
w(x) = \frac{A \sigma^x - B (-\tau)^x e^{i \pi (2m + 1) x}}{\delta}.
$$

Then for every integer $j$, $\operatorname{Re} w'(j) = (W_{j+1} + W_{j-1}) \ln \sigma / \delta$.

Since $\tau < 0$, $w(x)$ is $(A \sigma^x - B \tau^x)/\delta$ with $\tau^x$ read on the branch
$(-\tau)^x e^{i \pi (2m + 1) x}$; this is the generalized Fibonacci function of the journal text.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Theorem 15
(`jis-2024-24.6.2-thm-15`). -/
public theorem_wanted generalizedFibonacci_function_deriv_re
    (W : ℤ → ℝ) (p : ℝ) (hW : ∀ j : ℤ, W (j + 2) = p * W (j + 1) + W j) (σ τ : ℝ)
    (hσ : σ = (p + √(p ^ 2 + 4)) / 2) (hτ : τ = (p - √(p ^ 2 + 4)) / 2) (m j : ℤ) :
    (deriv (fun x : ℝ => ((((W 1 - W 0 * τ) * σ ^ x : ℝ) : ℂ) -
        ((W 1 - W 0 * σ : ℝ) : ℂ) * (((-τ) ^ x : ℝ) : ℂ) *
          Complex.exp (Real.pi * (2 * m + 1) * x * Complex.I)) / (√(p ^ 2 + 4) : ℝ))
      (j : ℝ)).re =
      (W (j + 1) + W (j - 1)) / √(p ^ 2 + 4) * Real.log σ

end

end MetaMathlibExt
