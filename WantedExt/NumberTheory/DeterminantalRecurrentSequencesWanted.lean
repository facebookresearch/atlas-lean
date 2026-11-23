/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.PellLucasNumber
public import MathlibExt.NumberTheory.GibonacciNumber
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-! Sums `∑_{α} m_n(α) a_1^{α_1} ⋯ a_n^{α_n}` over `α_1 + 2α_2 + ⋯ + nα_n = n`, with
`m_n(α)` the multinomial coefficient of `(α_1, …, α_n)`, are written below as sums over
the compositions of `n` of the product of `a` over the parts, which is the same number. -/

/-- **Trudi's formula as a generating function.** Let $K$ be a field and $a_0, a_1, a_2, \dots$
a sequence in $K$ with $a_0 \ne 0$. For $n \ge 1$ let $A_n$ be the $n \times n$
Toeplitz–Hessenberg matrix whose $(i, j)$ entry is $a_{i-j+1}$ if $j \le i + 1$ and $0$
otherwise. In the ring of formal power series over $K$, let $f(x) = \sum_{n \ge 1} \det(A_n) x^n$,
$g(x) = \sum_{i \ge 1} a_i x^i$ and $h(x) = a_0^{-1} g(-a_0 x)$. Then $f(x)(1 + h(x)) = -h(x)$,
that is, $f(x) = -h(x)/(1 + h(x))$.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Lemma 2. -/
public theorem_wanted toeplitzHessenberg_det_generatingFunction {K : Type*} [Field K]
    (a : ℕ → K) (ha0 : a 0 ≠ 0) :
    PowerSeries.mk (fun n => if n = 0 then 0 else
        Matrix.det (fun i j : Fin n =>
          if (j : ℕ) ≤ (i : ℕ) + 1 then a ((i : ℕ) + 1 - (j : ℕ)) else 0)) *
      (1 + PowerSeries.C (a 0)⁻¹ *
        PowerSeries.rescale (-a 0) (PowerSeries.mk fun i => if i = 0 then 0 else a i)) =
    -(PowerSeries.C (a 0)⁻¹ *
        PowerSeries.rescale (-a 0) (PowerSeries.mk fun i => if i = 0 then 0 else a i))

/-- **Generating function of Toeplitz–Hessenberg determinants with entries $(bk + c)d^k$.** Let
$R$ be a commutative ring and $a, b, c, d \in R$. Put $t_0 = a$ and $t_k = (bk + c) d^k$ for
$k \ge 1$, and for $n \ge 1$ let $u_n$ be the determinant of the $n \times n$ matrix whose
$(i, j)$ entry is $t_{i-j+1}$ if $j \le i + 1$ and $0$ otherwise. Then the formal power series
$u(x) = \sum_{n \ge 1} u_n x^n$ over $R$ satisfies
$$u(x) \bigl(1 + d(2a - b - c) x + a d^2 (a - c) x^2\bigr) = d x (b + c + a c d x).$$
Since the second factor on the left has constant term $1$, this says
$u(x) = dx(b + c + acdx)/(1 + d(2a - b - c)x + ad^2(a - c)x^2)$.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Lemma 3. -/
public theorem_wanted toeplitzHessenberg_det_linear_mul_pow_generatingFunction
    {R : Type*} [CommRing R] (a b c d : R) :
    PowerSeries.mk (fun n => if n = 0 then 0 else
        Matrix.det (fun i j : Fin n =>
          if (j : ℕ) ≤ (i : ℕ) + 1 then
            (if (i : ℕ) + 1 - (j : ℕ) = 0 then a
              else (b * (((i : ℕ) + 1 - (j : ℕ) : ℕ) : R) + c) * d ^ ((i : ℕ) + 1 - (j : ℕ)))
          else 0)) *
      (1 + PowerSeries.C (d * (2 * a - b - c)) * X +
        PowerSeries.C (a * d ^ 2 * (a - c)) * X ^ 2) =
    PowerSeries.C d * X * (PowerSeries.C (b + c) + PowerSeries.C (a * c * d) * X)

/-- **Composition-sum formulas for $F_{2n}$, $F_{3n-1}$ and $P_{n-1}$.** Let $F_k$ be the
Fibonacci numbers and $P_k$ the Pell numbers. For every $n \ge 1$, with each sum running over all
compositions $(c_1, \dots, c_r)$ of $n$ (tuples of positive integers with
$c_1 + \dots + c_r = n$),
$F_{2n} = \sum \prod_{i=1}^{r} c_i$,
$F_{3n-1} = 2^{n-1} \sum \prod_{i=1}^{r} \frac{2 c_i - 1}{2^{c_i - 1}}$ and
$P_{n-1} = 2^{n-1} \sum \prod_{i=1}^{r} \frac{c_i - 1}{2^{c_i - 1}}$.

In the last sum only compositions with no part equal to $1$ contribute; the source writes it as
a multinomial sum over $2s_1 + 3s_2 + \dots + n s_{n-1} = n$.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Proposition 1. -/
public theorem_wanted fib_pell_composition_sums (n : ℕ) (hn : 1 ≤ n) :
    (Nat.fib (2 * n) : ℚ) =
        ∑ c : Composition n, ∏ i : Fin c.length, (c.blocksFun i : ℚ) ∧
      (Nat.fib (3 * n - 1) : ℚ) = 2 ^ (n - 1) *
        ∑ c : Composition n, ∏ i : Fin c.length,
          (2 * (c.blocksFun i : ℚ) - 1) / 2 ^ (c.blocksFun i - 1) ∧
      (pellNumber (n - 1) : ℚ) = 2 ^ (n - 1) *
        ∑ c : Composition n, ∏ i : Fin c.length,
          ((c.blocksFun i : ℚ) - 1) / 2 ^ (c.blocksFun i - 1)

/-- **A composition sum with weights $(c_i + 1) 2^{c_i - 2}$ in terms of Fibonacci and Lucas
numbers.** Let $F_k$ be the Fibonacci numbers and $L_k$ the Lucas numbers. For every $n \ge 1$,
the sum of $\prod_{i=1}^{r} (c_i + 1) 2^{c_i - 2}$ over all compositions $(c_1, \dots, c_r)$ of
$n$ (tuples of positive integers with $c_1 + \dots + c_r = n$) equals $5^{(n-1)/2} F_{n+1}$ if $n$
is odd and $5^{(n-2)/2} L_{n+1}$ if $n$ is even.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 1, equation (8). -/
public theorem_wanted composition_sum_succ_mul_two_zpow (n : ℕ) (hn : 1 ≤ n) :
    ∑ c : Composition n, ∏ i : Fin c.length,
        ((c.blocksFun i : ℚ) + 1) * (2 : ℚ) ^ ((c.blocksFun i : ℤ) - 2) =
      if Odd n then 5 ^ ((n - 1) / 2) * (Nat.fib (n + 1) : ℚ)
      else 5 ^ ((n - 2) / 2) * (lucasNumber (n + 1) : ℚ)

/-- **Composition-sum formulas for $F_{n+3}$, $F_{3n+1}$ and Jacobsthal and Pell numbers.** Let
$F_k$ be the Fibonacci numbers, $P_k$ the Pell numbers and $J_k$ the Jacobsthal numbers, that is,
the Lucas sequence $U(1, -2)$, with $J_0 = 0$, $J_1 = 1$ and $J_{k+2} = J_{k+1} + 2 J_k$. For
every $n \ge 1$, with each sum running over all compositions $(c_1, \dots, c_r)$ of $n$ (tuples
of positive integers with $c_1 + \dots + c_r = n$),
$\sum \prod_{i=1}^{r} (-1)^{c_i - 1} (c_i + 2) = F_{n+3}$,
$\sum \prod_{i=1}^{r} (-1)^{c_i - 1} (4 c_i + 2) = 2 F_{3n+1}$,
$\sum \prod_{i=1}^{r} (-2)^{c_i - 1} (2 c_i + 3) = J_{n+3}$,
$\sum \prod_{i=1}^{r} c_i 2^{c_i - 1} = J_{2n}$ and
$\sum \prod_{i=1}^{r} 4 c_i = 2 P_{2n}$.

Identity (14) of the source is not included.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 3, equations (13) and
(15)-(18). -/
public theorem_wanted fib_jacobsthal_pell_composition_sums (n : ℕ) (hn : 1 ≤ n) :
    ∑ c : Composition n, ∏ i : Fin c.length,
        (-1 : ℚ) ^ (c.blocksFun i - 1) * ((c.blocksFun i : ℚ) + 2) = Nat.fib (n + 3) ∧
      ∑ c : Composition n, ∏ i : Fin c.length,
        (-1 : ℚ) ^ (c.blocksFun i - 1) * (4 * (c.blocksFun i : ℚ) + 2) =
          2 * Nat.fib (3 * n + 1) ∧
      ∑ c : Composition n, ∏ i : Fin c.length,
        (-2 : ℚ) ^ (c.blocksFun i - 1) * (2 * (c.blocksFun i : ℚ) + 3) =
          lucasU ⟨1, -2, by decide⟩ (n + 3) ∧
      ∑ c : Composition n, ∏ i : Fin c.length,
        (c.blocksFun i : ℚ) * 2 ^ (c.blocksFun i - 1) = lucasU ⟨1, -2, by decide⟩ (2 * n) ∧
      ∑ c : Composition n, ∏ i : Fin c.length, 4 * (c.blocksFun i : ℚ) =
          2 * (pellNumber (2 * n) : ℚ)

/-- **Fibonacci subsequences $F_{\ell n + m}$ that are Toeplitz–Hessenberg determinants.** For
complex numbers $a, b, c, d$ and $n \ge 1$, let $u_n(a, b, c, d)$ be the determinant of the
$n \times n$ matrix whose entry in row $i$ and column $j$ is $a$ if $j = i + 1$, is
$(bp + c) d^p$ with $p = i - j + 1$ if $j \le i$, and is $0$ if $j > i + 1$. Let $F_k$ be the
Fibonacci numbers and let $\ell \ge 1$ and $m \ge 0$ be integers. There are complex numbers
$a, b, c, d$ with $F_{\ell n + m} = u_n(a, b, c, d)$ for every $n \ge 1$ if and only if
$(\ell, m) = (1, 3)$ or $(\ell, m) = (2, 0)$, that is, exactly for the sequences $F_{n+3}$ and
$F_{2n}$.

In the source's terms, $F_{n+3}$ and $F_{2n}$ are the only good sequences among the
$F_{\ell n + m}$.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Proposition 2
(`integers-2025-A97-prop-2`). -/
public theorem_wanted fib_mul_add_eq_toeplitzHessenberg_det_iff (ℓ m : ℕ) (hℓ : 1 ≤ ℓ) :
    (∃ a b c d : ℂ, ∀ n : ℕ, 1 ≤ n →
      (Nat.fib (ℓ * n + m) : ℂ) =
        Matrix.det (fun i j : Fin n =>
          if (j : ℕ) ≤ (i : ℕ) + 1 then
            (if (i : ℕ) + 1 - (j : ℕ) = 0 then a
              else (b * (((i : ℕ) + 1 - (j : ℕ) : ℕ) : ℂ) + c) * d ^ ((i : ℕ) + 1 - (j : ℕ)))
          else 0)) ↔
      (ℓ = 1 ∧ m = 3) ∨ (ℓ = 2 ∧ m = 0)

/-- **Pell and Pell–Lucas numbers as composition sums with $\sqrt 2$ weights.** Let $P_n$ be the
Pell numbers and $Q_n$ the Pell–Lucas numbers ($Q_0 = Q_1 = 2$, $Q_{k+2} = 2Q_{k+1} + Q_k$). For
every $n \ge 1$, with $c$ running over the compositions of $n$ (ordered tuples of positive
integers with sum $n$) and the products running over the parts $j$ of $c$, the real number
$$\sum_c \prod_{j \in c} (j - 1) (\sqrt 2)^{j-2}$$
equals $\sqrt 2\, P_{n-1}$ for odd $n$ and $Q_{n-1}/2$ for even $n$ (identity (10)), and
$$\sum_c \prod_{j \in c} \frac{j + 1}{(\sqrt 2)^j}$$
equals $P_{n+1}/\sqrt 2$ for odd $n$ and $Q_{n+1}/4$ for even $n$ (identity (11)).

In the source both are multinomial sums; the weight of the first vanishes on parts $1$, so its
sum runs over the compositions of $n$ without parts $1$.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 2 (`integers-2025-A97-cor-2`). -/
public theorem_wanted pell_pellLucas_composition_sums_sqrt_two (n : ℕ) (hn : 1 ≤ n) :
    ∑ c : Composition n, ∏ i : Fin c.length,
        ((c.blocksFun i : ℝ) - 1) * Real.sqrt 2 ^ (c.blocksFun i - 2) =
      (if Odd n then Real.sqrt 2 * (pellNumber (n - 1) : ℝ)
        else (pellLucas (n - 1) : ℝ) / 2) ∧
    ∑ c : Composition n, ∏ i : Fin c.length,
        ((c.blocksFun i : ℝ) + 1) / Real.sqrt 2 ^ c.blocksFun i =
      (if Odd n then (pellNumber (n + 1) : ℝ) / Real.sqrt 2
        else (pellLucas (n + 1) : ℝ) / 4)

/-- **Toeplitz–Hessenberg determinants with Oresme entries.** For numbers $a_0, a_1, \dots, a_n$,
let $\det(a_0; a_1, \dots, a_n)$ be the determinant of the $n \times n$ matrix whose $(i, j)$
entry is $a_{i-j+1}$ if $j \le i + 1$ and $0$ otherwise, so that $a_0$ fills the superdiagonal.
Let $O_k = k/2^k$ be the Oresme numbers, $F_n$ the Fibonacci numbers, $L_n$ the Lucas numbers,
$P_n$ the Pell numbers, $Q_n$ the Pell–Lucas numbers ($Q_0 = Q_1 = 2$) and $J_n$ the Jacobsthal
numbers, the Lucas sequence $U(1, -2)$ ($J_0 = 0$, $J_1 = 1$, $J_{k+2} = J_{k+1} + 2J_k$). Then
for every $n \ge 1$ the following hold in $\mathbb{Q}$:
(19) $\det(-2; O_2, \dots, O_{n+1})$ equals $5^{(n-1)/2} F_{n+1}/2^n$ for odd $n$ and
$5^{(n-2)/2} L_{n+1}/2^n$ for even $n$;
(20) $\det(-4; O_0, \dots, O_{n-1})$ equals $2^{(n+1)/2} P_{n-1}$ for odd $n$ and
$2^{(n-2)/2} Q_{n-1}$ for even $n$;
(21) $\det(-1/2; O_2, \dots, O_{n+1})$ equals $P_{n+1}/2^{(3n+1)/2}$ for odd $n$ and
$Q_{n+1}/2^{(3n+4)/2}$ for even $n$;
(22) $\det(1/4; O_3, \dots, O_{n+2}) = F_{n+3}/2^{3n}$;
(23) $\det(-1/8; O_4, \dots, O_{n+3}) = F_{2n+4}/2^{3n+2}$;
(24) $\det(1/4; O_3, O_5, \dots, O_{2n+1}) = F_{3n+1}/2^{4n-1}$;
(25) $\det(1/4; O_5, O_7, \dots, O_{2n+3}) = J_{n+3}/2^{5n}$;
(26) $\det(-2; O_1, \dots, O_n) = J_{2n}/2^n$;
(27) $\det(-1/4; O_1, \dots, O_n) = P_{2n}/2^{3n-1}$.

The exponents of (20) are typeset $2^{(n+1/2)}$ and $2^{(n-2/2)}$ in the source; they are read as
$2^{(n+1)/2}$ and $2^{(n-2)/2}$, since the literal $2^{n+1/2}$ is irrational while the
determinant is rational (for $n = 3$ the determinant is $8 = 2^2 P_2$).

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 4 (`integers-2025-A97-cor-4`). -/
public theorem_wanted oresme_toeplitzHessenberg_det_formulas (n : ℕ) (hn : 1 ≤ n) :
    Matrix.det (fun i j : Fin n => if (j : ℕ) ≤ (i : ℕ) + 1 then
        (if (i : ℕ) + 1 - (j : ℕ) = 0 then (-2 : ℚ) else
          (((i : ℕ) + 1 - (j : ℕ) + 1 : ℕ) : ℚ) / 2 ^ ((i : ℕ) + 1 - (j : ℕ) + 1)) else 0) =
      (if Odd n then 5 ^ ((n - 1) / 2) / 2 ^ n * (Nat.fib (n + 1) : ℚ)
        else 5 ^ ((n - 2) / 2) / 2 ^ n * (lucasNumber (n + 1) : ℚ)) ∧
    Matrix.det (fun i j : Fin n => if (j : ℕ) ≤ (i : ℕ) + 1 then
        (if (i : ℕ) + 1 - (j : ℕ) = 0 then (-4 : ℚ) else
          (((i : ℕ) + 1 - (j : ℕ) - 1 : ℕ) : ℚ) / 2 ^ ((i : ℕ) + 1 - (j : ℕ) - 1)) else 0) =
      (if Odd n then 2 ^ ((n + 1) / 2) * (pellNumber (n - 1) : ℚ)
        else 2 ^ ((n - 2) / 2) * (pellLucas (n - 1) : ℚ)) ∧
    Matrix.det (fun i j : Fin n => if (j : ℕ) ≤ (i : ℕ) + 1 then
        (if (i : ℕ) + 1 - (j : ℕ) = 0 then (-1 / 2 : ℚ) else
          (((i : ℕ) + 1 - (j : ℕ) + 1 : ℕ) : ℚ) / 2 ^ ((i : ℕ) + 1 - (j : ℕ) + 1)) else 0) =
      (if Odd n then (pellNumber (n + 1) : ℚ) / 2 ^ ((3 * n + 1) / 2)
        else (pellLucas (n + 1) : ℚ) / 2 ^ ((3 * n + 4) / 2)) ∧
    Matrix.det (fun i j : Fin n => if (j : ℕ) ≤ (i : ℕ) + 1 then
        (if (i : ℕ) + 1 - (j : ℕ) = 0 then (1 / 4 : ℚ) else
          (((i : ℕ) + 1 - (j : ℕ) + 2 : ℕ) : ℚ) / 2 ^ ((i : ℕ) + 1 - (j : ℕ) + 2)) else 0) =
      (Nat.fib (n + 3) : ℚ) / 2 ^ (3 * n) ∧
    Matrix.det (fun i j : Fin n => if (j : ℕ) ≤ (i : ℕ) + 1 then
        (if (i : ℕ) + 1 - (j : ℕ) = 0 then (-1 / 8 : ℚ) else
          (((i : ℕ) + 1 - (j : ℕ) + 3 : ℕ) : ℚ) / 2 ^ ((i : ℕ) + 1 - (j : ℕ) + 3)) else 0) =
      (Nat.fib (2 * n + 4) : ℚ) / 2 ^ (3 * n + 2) ∧
    Matrix.det (fun i j : Fin n => if (j : ℕ) ≤ (i : ℕ) + 1 then
        (if (i : ℕ) + 1 - (j : ℕ) = 0 then (1 / 4 : ℚ) else
          ((2 * ((i : ℕ) + 1 - (j : ℕ)) + 1 : ℕ) : ℚ) / 2 ^ (2 * ((i : ℕ) + 1 - (j : ℕ)) + 1))
        else 0) =
      (Nat.fib (3 * n + 1) : ℚ) / 2 ^ (4 * n - 1) ∧
    Matrix.det (fun i j : Fin n => if (j : ℕ) ≤ (i : ℕ) + 1 then
        (if (i : ℕ) + 1 - (j : ℕ) = 0 then (1 / 4 : ℚ) else
          ((2 * ((i : ℕ) + 1 - (j : ℕ)) + 3 : ℕ) : ℚ) / 2 ^ (2 * ((i : ℕ) + 1 - (j : ℕ)) + 3))
        else 0) =
      (lucasU ⟨1, -2, by decide⟩ (n + 3) : ℚ) / 2 ^ (5 * n) ∧
    Matrix.det (fun i j : Fin n => if (j : ℕ) ≤ (i : ℕ) + 1 then
        (if (i : ℕ) + 1 - (j : ℕ) = 0 then (-2 : ℚ) else
          (((i : ℕ) + 1 - (j : ℕ) : ℕ) : ℚ) / 2 ^ ((i : ℕ) + 1 - (j : ℕ))) else 0) =
      (lucasU ⟨1, -2, by decide⟩ (2 * n) : ℚ) / 2 ^ n ∧
    Matrix.det (fun i j : Fin n => if (j : ℕ) ≤ (i : ℕ) + 1 then
        (if (i : ℕ) + 1 - (j : ℕ) = 0 then (-1 / 4 : ℚ) else
          (((i : ℕ) + 1 - (j : ℕ) : ℕ) : ℚ) / 2 ^ ((i : ℕ) + 1 - (j : ℕ))) else 0) =
      (pellNumber (2 * n) : ℚ) / 2 ^ (3 * n - 1)

/-- **Horadam sequences as composition sums.** Let $p, q, r, s$ be complex numbers with
$(q - r)^2 = 4s(p - 1)$ and $4s(p - 1) \ne 0$, and let $(v_k)_{k \ge 0}$ be the complex sequence
with $v_0 = p$, $v_1 = q$ and $v_{k+2} = r v_{k+1} + s v_k$ for every $k \ge 0$. Put
$e = 2ps/(r - q)$. Then for every $n \ge 1$,
$$v_n = \sum_c \bigl((r - q)/2\bigr)^{n - \ell(c)} \prod_{j \in c} \bigl((q + e) j - e\bigr),$$
where $c$ runs over the compositions of $n$ (ordered tuples of positive integers with sum $n$),
$\ell(c)$ is the number of parts of $c$ and the product runs over the parts $j$ of $c$.

In the source this is identity (12), a sum over $\alpha$ with
$\alpha_1 + 2\alpha_2 + \dots + n\alpha_n = n$ weighted by multinomial coefficients, which is the
same number.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Theorem 1 (`integers-2025-A97-thm-1`). -/
public theorem_wanted horadam_eq_composition_sum (p q r s : ℂ)
    (h : (q - r) ^ 2 = 4 * s * (p - 1)) (h0 : 4 * s * (p - 1) ≠ 0) (v : ℕ → ℂ)
    (hv0 : v 0 = p) (hv1 : v 1 = q) (hv : ∀ k, v (k + 2) = r * v (k + 1) + s * v k)
    (n : ℕ) (hn : 1 ≤ n) :
    v n = ∑ c : Composition n, ((r - q) / 2) ^ (n - c.length) *
      ∏ i : Fin c.length,
        ((q + 2 * p * s / (r - q)) * (c.blocksFun i : ℂ) - 2 * p * s / (r - q))

/-- **Horadam composition sums satisfy the Horadam recurrence.** Let $p, q, r, s$ be complex
numbers with $(q - r)^2 = 4s(p - 1)$ and $4s(p - 1) \ne 0$, put $e = 2ps/(r - q)$, and for every
natural number $m$ let
$$w_m = \sum_c \bigl((r - q)/2\bigr)^{m - \ell(c)} \prod_{j \in c} \bigl((q + e) j - e\bigr),$$
where $c$ runs over the compositions of $m$ (ordered tuples of positive integers with sum $m$),
$\ell(c)$ is the number of parts of $c$ and the product runs over the parts $j$ of $c$. Then
$w_n = r w_{n-1} + s w_{n-2}$ for every $n \ge 3$.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Theorem 1 (`integers-2025-A97-thm-1`). -/
public theorem_wanted horadam_composition_sum_recurrence (p q r s : ℂ)
    (h : (q - r) ^ 2 = 4 * s * (p - 1)) (h0 : 4 * s * (p - 1) ≠ 0) (n : ℕ) (hn : 3 ≤ n) :
    ∑ c : Composition n, ((r - q) / 2) ^ (n - c.length) *
        ∏ i : Fin c.length,
          ((q + 2 * p * s / (r - q)) * (c.blocksFun i : ℂ) - 2 * p * s / (r - q)) =
      r * ∑ c : Composition (n - 1), ((r - q) / 2) ^ (n - 1 - c.length) *
        ∏ i : Fin c.length,
          ((q + 2 * p * s / (r - q)) * (c.blocksFun i : ℂ) - 2 * p * s / (r - q)) +
      s * ∑ c : Composition (n - 2), ((r - q) / 2) ^ (n - 2 - c.length) *
        ∏ i : Fin c.length,
          ((q + 2 * p * s / (r - q)) * (c.blocksFun i : ℂ) - 2 * p * s / (r - q))

/-- **Translates of a Gibonacci sequence as composition sums.** Let $y$ and $z$ be non-negative
integers, not both zero, and let $(G_k)$ be the Gibonacci sequence with $G_0 = y$ and $G_1 = z$.
Let $m \ge 3$ and $n \ge 1$, and let $D$ be a complex number with
$D^2 = (-1)^m (y^2 + yz - z^2)$. Then
$$G_{n+m} = \frac{(G_{m+2} + G_m + 2D)^{n-1}}{G_{m+1}^{n-2} (G_m + D)^n} \sum_c
\left(-\frac{(G_m + D)^2}{G_{m+2} + G_m + 2D}\right)^{n-r} \prod_{i=1}^{r} (D c_i + G_m),$$
where the sum runs over all compositions $c = (c_1, \dots, c_r)$ of $n$ (tuples of positive
integers with $c_1 + \dots + c_r = n$) and $r$ is the number of parts of $c$.

The two square roots $D$ give the two sign choices of identity (28) of the source.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Theorem 2 (`integers-2025-A97-thm-2`). -/
public theorem_wanted gibonacci_add_eq_composition_sum (y z : ℤ) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hyz : y ≠ 0 ∨ z ≠ 0) (m : ℕ) (hm : 3 ≤ m) (D : ℂ)
    (hD : D ^ 2 = (-1) ^ m * ((y : ℂ) ^ 2 + y * z - z ^ 2)) (n : ℕ) (hn : 1 ≤ n) :
    (gibonacciNumber y z (n + m) : ℂ) =
      ((gibonacciNumber y z (m + 2) : ℂ) + gibonacciNumber y z m + 2 * D) ^ (n - 1) /
        ((gibonacciNumber y z (m + 1) : ℂ) ^ ((n : ℤ) - 2) *
          ((gibonacciNumber y z m : ℂ) + D) ^ n) *
      ∑ c : Composition n,
        (-((gibonacciNumber y z m : ℂ) + D) ^ 2 /
          ((gibonacciNumber y z (m + 2) : ℂ) + gibonacciNumber y z m + 2 * D)) ^
            (n - c.length) *
        ∏ i : Fin c.length, (D * (c.blocksFun i : ℂ) + gibonacciNumber y z m)

/-- **Multiples of a shifted Gibonacci sequence that are Toeplitz–Hessenberg determinants.** Let
$y$ and $z$ be non-negative integers, not both zero, and let $(G_k)$ be the Gibonacci sequence
with $G_0 = y$ and $G_1 = z$. For complex numbers $a, b, c, d$ and $n \ge 1$, let
$u_n(a, b, c, d)$ be the determinant of the $n \times n$ matrix whose entry in row $i$ and column
$j$ is $a$ if $j = i + 1$, is $(bp + c) d^p$ with $p = i - j + 1$ if $j \le i$, and is $0$ if
$j > i + 1$. Let $m \ge 3$ and let $k$ be a nonzero complex number. There are complex numbers
$a, b, c, d$ with $k G_{n+m} = u_n(a, b, c, d)$ for every $n \ge 1$ if and only if there is a
complex number $D$ with $D^2 = (-1)^m (y^2 + yz - z^2)$ and
$k = (G_{m+2} + G_m + 2D) / G_{m+1}^2$.

This is the uniqueness part of Theorem 2 of the source. The case $k = 0$ is excluded: there any
$a, b, c$ with $d = 0$ work trivially, since $u_n(a, b, c, 0) = 0$.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Theorem 2 (`integers-2025-A97-thm-2`). -/
public theorem_wanted gibonacci_mul_add_eq_toeplitzHessenberg_det_iff (y z : ℤ) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hyz : y ≠ 0 ∨ z ≠ 0) (m : ℕ) (hm : 3 ≤ m) (k : ℂ) (hk : k ≠ 0) :
    (∃ a b c d : ℂ, ∀ n : ℕ, 1 ≤ n →
      k * (gibonacciNumber y z (n + m) : ℂ) =
        Matrix.det (fun i j : Fin n =>
          if (j : ℕ) ≤ (i : ℕ) + 1 then
            (if (i : ℕ) + 1 - (j : ℕ) = 0 then a
              else (b * (((i : ℕ) + 1 - (j : ℕ) : ℕ) : ℂ) + c) * d ^ ((i : ℕ) + 1 - (j : ℕ)))
          else 0)) ↔
      ∃ D : ℂ, D ^ 2 = (-1) ^ m * ((y : ℂ) ^ 2 + y * z - z ^ 2) ∧
        k = ((gibonacciNumber y z (m + 2) : ℂ) + gibonacciNumber y z m + 2 * D) /
          (gibonacciNumber y z (m + 1) : ℂ) ^ 2

/-- **Subsequences $G_{\ell n + m}$ of a Gibonacci sequence as composition sums.** Let $y$ and $z$
be non-negative integers, not both zero, let $(G_k)$ be the Gibonacci sequence with $G_0 = y$
and $G_1 = z$, and let $L_k$ be the Lucas numbers. Let $\ell \ge 1$, $m \ge 0$ and $n \ge 1$, and
let $E$ be a complex number with $E^2 = (-1)^\ell G_\ell (G_\ell - L_\ell y) + y^2$ if $m$ is
even and $E^2 = (-1)^\ell G_{\ell+1} (G_{\ell+1} - L_\ell z) + z^2$ if $m$ is odd. Write
$A = L_\ell G_{\ell+m} - 2(-1)^\ell G_m + 2E$ and $B = (-1)^{\ell+1} G_m + E$, and assume that
$m \ge \ell + 2$ or $G_{\ell+m} B \ne 0$. Then
$$G_{\ell n + m} = \frac{A^{n-1}}{G_{\ell+m}^{n-2} B^n} \sum_c \left(-\frac{B^2}{A}\right)^{n-r}
\prod_{i=1}^{r} (E c_i - (-1)^\ell G_m),$$
where the sum runs over all compositions $c = (c_1, \dots, c_r)$ of $n$ (tuples of positive
integers with $c_1 + \dots + c_r = n$) and $r$ is the number of parts of $c$.

This is identity (35) of the source; for $0 \le m \le \ell + 1$ the condition $G_{\ell+m} B \ne 0$
is the source's sufficient condition.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Theorem 3 (`integers-2025-A97-thm-3`). -/
public theorem_wanted gibonacci_mul_add_eq_composition_sum (y z : ℤ) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hyz : y ≠ 0 ∨ z ≠ 0) (ℓ m : ℕ) (hℓ : 1 ≤ ℓ) (E : ℂ)
    (hE : E ^ 2 = if Even m then
        (-1) ^ ℓ * (gibonacciNumber y z ℓ : ℂ) *
          ((gibonacciNumber y z ℓ : ℂ) - lucasNumber ℓ * y) + (y : ℂ) ^ 2
      else
        (-1) ^ ℓ * (gibonacciNumber y z (ℓ + 1) : ℂ) *
          ((gibonacciNumber y z (ℓ + 1) : ℂ) - lucasNumber ℓ * z) + (z : ℂ) ^ 2)
    (hm : ℓ + 2 ≤ m ∨
      (gibonacciNumber y z (ℓ + m) : ℂ) * ((-1) ^ (ℓ + 1) * gibonacciNumber y z m + E) ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) :
    (gibonacciNumber y z (ℓ * n + m) : ℂ) =
      ((lucasNumber ℓ : ℂ) * gibonacciNumber y z (ℓ + m) -
          2 * (-1) ^ ℓ * gibonacciNumber y z m + 2 * E) ^ (n - 1) /
        ((gibonacciNumber y z (ℓ + m) : ℂ) ^ ((n : ℤ) - 2) *
          ((-1) ^ (ℓ + 1) * (gibonacciNumber y z m : ℂ) + E) ^ n) *
      ∑ c : Composition n,
        (-((-1) ^ (ℓ + 1) * (gibonacciNumber y z m : ℂ) + E) ^ 2 /
          ((lucasNumber ℓ : ℂ) * gibonacciNumber y z (ℓ + m) -
            2 * (-1) ^ ℓ * gibonacciNumber y z m + 2 * E)) ^ (n - c.length) *
        ∏ i : Fin c.length,
          (E * (c.blocksFun i : ℂ) - (-1) ^ ℓ * gibonacciNumber y z m)

/-- **Fibonacci and Lucas translates as composition sums.** Let $F_k$ be the Fibonacci numbers and
$L_k$ the Lucas numbers, let $m \ge 0$ and $n \ge 1$, and write $\sum_c$ for the sum over all
compositions $c = (c_1, \dots, c_r)$ of $n$ (tuples of positive integers with
$c_1 + \dots + c_r = n$), where $r$ is the number of parts of $c$. For every complex number
$\lambda$ with $\lambda^2 = (-1)^{m+1}$, and with $\lambda = 1$ if $m = 1$,
$$F_{n+m} = \frac{(L_{m+1} + 2\lambda)^{n-1}}{F_{m+1}^{n-2} (F_m + \lambda)^n} \sum_c
\left(-\frac{(F_m + \lambda)^2}{L_{m+1} + 2\lambda}\right)^{n-r}
\prod_{j=1}^{r} (\lambda c_j + F_m),$$
and for every complex number $\rho$ with $\rho^2 = 5 (-1)^m$,
$$L_{n+m} = \frac{(L_{m+2} + L_m + 2\rho)^{n-1}}{L_{m+1}^{n-2} (L_m + \rho)^n} \sum_c
\left(-\frac{(L_m + \rho)^2}{L_{m+2} + L_m + 2\rho}\right)^{n-r}
\prod_{j=1}^{r} (\rho c_j + L_m).$$

These are identities (30) and (31) of the source.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 5 (`integers-2025-A97-cor-5`). -/
public theorem_wanted fib_lucas_add_eq_composition_sum (m n : ℕ) (hn : 1 ≤ n) :
    (∀ lam : ℂ, lam ^ 2 = (-1) ^ (m + 1) → (m = 1 → lam = 1) →
      (Nat.fib (n + m) : ℂ) =
        ((lucasNumber (m + 1) : ℂ) + 2 * lam) ^ (n - 1) /
          ((Nat.fib (m + 1) : ℂ) ^ ((n : ℤ) - 2) * ((Nat.fib m : ℂ) + lam) ^ n) *
        ∑ c : Composition n,
          (-((Nat.fib m : ℂ) + lam) ^ 2 / ((lucasNumber (m + 1) : ℂ) + 2 * lam)) ^
              (n - c.length) *
          ∏ j : Fin c.length, (lam * (c.blocksFun j : ℂ) + Nat.fib m)) ∧
    (∀ rho : ℂ, rho ^ 2 = 5 * (-1) ^ m →
      (lucasNumber (n + m) : ℂ) =
        ((lucasNumber (m + 2) : ℂ) + lucasNumber m + 2 * rho) ^ (n - 1) /
          ((lucasNumber (m + 1) : ℂ) ^ ((n : ℤ) - 2) * ((lucasNumber m : ℂ) + rho) ^ n) *
        ∑ c : Composition n,
          (-((lucasNumber m : ℂ) + rho) ^ 2 /
            ((lucasNumber (m + 2) : ℂ) + lucasNumber m + 2 * rho)) ^ (n - c.length) *
          ∏ j : Fin c.length, (rho * (c.blocksFun j : ℂ) + lucasNumber m))

/-- **Companion composition-sum formula for $F_{n+3}$.** Let $F_k$ be the Fibonacci numbers. For
every $n \ge 1$,
$$\frac{5}{9} F_{n+3} = \left(-\frac{1}{3}\right)^n \sum \prod_{i=1}^{r} (5 c_i - 10),$$
where the sum runs over all compositions $(c_1, \dots, c_r)$ of $n$ (tuples of positive integers
with $c_1 + \dots + c_r = n$).

This is the companion of identity (13) of the source: identity (30) with $m = 3$ and the square
root $\lambda = -1$.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 5 (`integers-2025-A97-cor-5`). -/
public theorem_wanted fib_add_three_companion_composition_sum (n : ℕ) (hn : 1 ≤ n) :
    5 / 9 * (Nat.fib (n + 3) : ℚ) =
      (-1 / 3) ^ n * ∑ c : Composition n, ∏ i : Fin c.length, (5 * (c.blocksFun i : ℚ) - 10)

/-- **Gibonacci subsequences $G_{2n+m}$ as composition sums.** Let $y$ and $z$ be non-negative
integers, not both zero, and let $(G_k)$ be the Gibonacci sequence with $G_0 = y$ and $G_1 = z$.
Let $m \ge 0$ and $n \ge 1$, and let $F$ be a complex number with
$F^2 = (-1)^{m+1} (y^2 + yz - z^2)$ such that $m \ge 4$ or $F \ne G_m$. Then
$$G_{2n+m} = \frac{(G_{m+3} + G_{m+1} + 2F)^{n-1}}{G_{m+2}^{n-2} (F - G_m)^n} \sum_c
\left(-\frac{(F - G_m)^2}{G_{m+3} + G_{m+1} + 2F}\right)^{n-r} \prod_{i=1}^{r} (F c_i - G_m),$$
where the sum runs over all compositions $c = (c_1, \dots, c_r)$ of $n$ (tuples of positive
integers with $c_1 + \dots + c_r = n$) and $r$ is the number of parts of $c$.

This is identity (43) of the source. For $m \le 3$ the condition $F \ne G_m$ excludes exactly
the source's cases (i) $m = 0$, $z = 2y$, (ii) $m = 1$, $y = z$, (iii) $m = 2$, $y = 0$ and
(iv) $m = 3$, $z = 0$, each with the positive root, which there equals $G_m$.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 6 (`integers-2025-A97-cor-6`). -/
public theorem_wanted gibonacci_two_mul_add_eq_composition_sum (y z : ℤ) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hyz : y ≠ 0 ∨ z ≠ 0) (m : ℕ) (F : ℂ)
    (hF : F ^ 2 = (-1) ^ (m + 1) * ((y : ℂ) ^ 2 + y * z - z ^ 2))
    (hm : 4 ≤ m ∨ F ≠ (gibonacciNumber y z m : ℂ)) (n : ℕ) (hn : 1 ≤ n) :
    (gibonacciNumber y z (2 * n + m) : ℂ) =
      ((gibonacciNumber y z (m + 3) : ℂ) + gibonacciNumber y z (m + 1) + 2 * F) ^ (n - 1) /
        ((gibonacciNumber y z (m + 2) : ℂ) ^ ((n : ℤ) - 2) *
          (-(gibonacciNumber y z m : ℂ) + F) ^ n) *
      ∑ c : Composition n,
        (-(-(gibonacciNumber y z m : ℂ) + F) ^ 2 /
          ((gibonacciNumber y z (m + 3) : ℂ) + gibonacciNumber y z (m + 1) + 2 * F)) ^
            (n - c.length) *
        ∏ i : Fin c.length, (F * (c.blocksFun i : ℂ) - gibonacciNumber y z m)

end

end MetaMathlibExt
