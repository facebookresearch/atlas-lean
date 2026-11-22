/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# General convolution sums involving Fibonacci `m`-step numbers

Statements from Robert Frontczak and Karol Gryszka,
"General Convolution Sums Involving Fibonacci `m`-Step
Numbers", *Journal of Integer Sequences* 27 (2024),
Article 24.8.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Gryszka/gryszka12.tex>).

The Fibonacci `m`-step numbers `F⁽ᵐ⁾ₙ` (`F₀ = 0`,
`F₁ = 1`, `Fₙ = F_{n-1} + ⋯ + F_{n-m}` for `n ≥ 2`, terms
at negative indices being `0`) are `fibStep m n`, defined
by list recursion; `F⁽²⁾, F⁽³⁾, F⁽⁴⁾, F⁽⁵⁾` are the paper's
`F, T, Q, P`. Jacobsthal numbers are `jacobsthalSeq`, Pell
numbers are MathlibExt's `pellNumber`, sums over
`K(r, n)` (compositions of `n` into `r` nonnegative parts)
are `compProdSum`, and ordinary generating functions are
`fibStepGF m = ∑ₙ F⁽ᵐ⁾ₙ Xⁿ`. Two printed statements are
corrected, each found numerically and checked against the
paper's own derivations: Theorem 8's inner coefficients
are `m-1-k`, not `k` (its proof's penultimate display has
the right coefficients), and Corollary 13's fourth
identity has `Q_{n+2-j}`, not `Q_{n-j}`; Theorem 34's
printed `F^{(m+3)}_{k_3}` is `F^{(m+3)}_{k_4}`. Displayed
fractions `1/2`, `1/5`, `1/(m-1)` are cleared by
multiplication to stay in `ℤ`. Corollary 16 repeats
Corollary 9's first identity and maps to the same
declaration.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.NumberTheory.PellNumberSequence

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted

/-- **Initial segments of the Fibonacci $m$-step sequence.** For natural numbers $m$ and $n$,
this is the list of integers $[F_0, F_1, \dots, F_n]$, built recursively: the list for $n = 0$
is $[0]$, the list for $n = 1$ is $[0, 1]$, and for $n \ge 2$ the list for $n$ is the list for
$n - 1$ followed by $F_n = \sum_{j=1}^{m} F_{n-j}$, where $F_i = 0$ for $i < 0$. -/
def fibStepSeq (m : ℕ) : ℕ → List ℤ
  | 0 => [0]
  | 1 => [0, 1]
  | n + 2 =>
      let prev := fibStepSeq m (n + 1)
      prev ++ [∑ j ∈ Finset.Icc 1 m, prev.getD (n + 2 - j) 0]

/-- **Fibonacci $m$-step numbers.** For natural numbers $m$ and $n$, the integer $F^{(m)}_n$ is
defined by $F^{(m)}_0 = 0$, $F^{(m)}_1 = 1$ and $F^{(m)}_n = \sum_{j=1}^{m} F^{(m)}_{n-j}$ for
$n \ge 2$, where $F^{(m)}_i = 0$ for $i < 0$. -/
def fibStep (m n : ℕ) : ℤ := (fibStepSeq m n).getD n 0

/-- **Jacobsthal numbers.** The Jacobsthal numbers are the integers $J_n$ defined by $J_0 = 0$,
$J_1 = 1$ and $J_{n+2} = J_{n+1} + 2 J_n$ for all $n \ge 0$. -/
def jacobsthalSeq : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => jacobsthalSeq (n + 1) + 2 * jacobsthalSeq n

/-- **Generating function of the Fibonacci $m$-step numbers.** For a natural number $m$,
$F^{(m)}(X)$ is the formal power series $\sum_{n \ge 0} F^{(m)}_n X^n$ with rational
coefficients, where $F^{(m)}_n$ is the $n$-th Fibonacci $m$-step number. -/
noncomputable def fibStepGF (m : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (fibStep m n : ℚ)

/-- **Sums over compositions.** Given integer sequences $a_0, \dots, a_{r-1}$ and a natural
number $n$, the sum over the compositions $K(r, n)$ of $n$ into $r$ nonnegative parts is the
sum, over all $(k_0, \dots, k_{r-1}) \in \mathbb{N}^r$ with $k_0 + \dots + k_{r-1} = n$, of
$\prod_{i=0}^{r-1} a_i(k_i)$. -/
def compProdSum {r : ℕ} (seqs : Fin r → ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ (Finset.univ : Finset (Fin r → Fin (n + 1))).filter
      (fun k => ∑ i, (k i).val = n), ∏ i, seqs i (k i).val

/-- **Truncated convolution of the $m$-step and $(m+1)$-step Fibonacci numbers.** Write
$F^{(m)}_n$ for the Fibonacci $m$-step numbers ($F^{(m)}_0 = 0$, $F^{(m)}_1 = 1$, and each later
term is the sum of the $m$ terms before it, terms at negative indices being $0$). For all natural
numbers $m \ge 1$ and $n \ge m$,
$$\sum_{j=0}^{n-m} F^{(m)}_j F^{(m+1)}_{n-m-j} = F^{(m+1)}_n - F^{(m)}_n.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 1. -/
theorem_wanted sum_fibStep_mul_succ (m n : ℕ) (hm : 1 ≤ m)
    (hn : m ≤ n) :
    ∑ j ∈ Finset.range (n - m + 1),
        fibStep m j * fibStep (m + 1) (n - m - j) =
      fibStep (m + 1) n - fibStep m n

/-- **Convolution of the Fibonacci and tribonacci numbers.** Write $F_n$ and $T_n$ for the
Fibonacci and tribonacci numbers, that is, the Fibonacci $m$-step numbers $F^{(m)}_n$ for
$m = 2, 3$ ($F^{(m)}_0 = 0$, $F^{(m)}_1 = 1$, and each later term is the sum of the $m$ terms
before it, terms at negative indices being $0$). For every natural number $n$,
$$\sum_{j=0}^{n} F_j T_{n-j} = T_{n+2} - F_{n+2}.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 2. -/
theorem_wanted sum_fib_mul_trib (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), fibStep 2 j * fibStep 3 (n - j) =
      fibStep 3 (n + 2) - fibStep 2 (n + 2)

/-- **Convolution of the Fibonacci 3-step and 4-step numbers.** Let $T_j$ and $Q_j$ be the
Fibonacci $3$-step and $4$-step numbers, where the Fibonacci $k$-step numbers start $0, 1$ and
each later term is the sum of the $k$ terms before it (terms of negative index being $0$). For
every natural number $n$,

$$\sum_{j=0}^{n} T_j \, Q_{n-j} = Q_{n+3} - T_{n+3}.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 2. -/
theorem_wanted sum_trib_mul_tetra (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), fibStep 3 j * fibStep 4 (n - j) =
      fibStep 4 (n + 3) - fibStep 3 (n + 3)

/-- **Convolution of the Fibonacci 4-step and 5-step numbers.** Let $Q_j$ and $P_j$ be the
Fibonacci $4$-step and $5$-step numbers, where the Fibonacci $k$-step numbers start $0, 1$ and
each later term is the sum of the $k$ terms before it (terms of negative index being $0$). For
every natural number $n$,

$$\sum_{j=0}^{n} Q_j \, P_{n-j} = P_{n+4} - Q_{n+4}.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 2. -/
theorem_wanted sum_tetra_mul_penta (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), fibStep 4 j * fibStep 5 (n - j) =
      fibStep 5 (n + 4) - fibStep 4 (n + 4)

/-- **Iterated convolution of Fibonacci $m$-step and $(m+p)$-step numbers.** Let $F^{(k)}_j$ be
the $j$-th Fibonacci $k$-step number: the sequence starts $F^{(k)}_0 = 0$, $F^{(k)}_1 = 1$, and each
later term is the sum of the $k$ terms before it (terms of negative index being $0$). For all
natural numbers $m$, $p$ and $n$ with $m \ge 1$ and $n \ge m$,

$$\sum_{k=0}^{p-1} \sum_{j=0}^{n-m-k} F^{(m)}_j \, F^{(m+p)}_{n-m-k-j} =
F^{(m+p)}_n - F^{(m)}_n,$$

where an inner sum whose upper limit $n - m - k$ is negative counts as $0$.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 3. -/
theorem_wanted sum_sum_fibStep_mul (m p n : ℕ) (hm : 1 ≤ m)
    (hn : m ≤ n) :
    ∑ k ∈ Finset.range p, ∑ j ∈ Finset.range (n - m - k + 1),
        fibStep m j * fibStep (m + p) (n - m - k - j) =
      fibStep (m + p) n - fibStep m n

/-- **Convolution of the $m$-step Fibonacci numbers with consecutive sums of the
$(m+2)$-step ones.** Write $F^{(m)}_n$ for the Fibonacci $m$-step numbers ($F^{(m)}_0 = 0$,
$F^{(m)}_1 = 1$, and each later term is the sum of the $m$ terms before it, terms at negative
indices being $0$). For all natural numbers $m \ge 1$ and $n \ge m$,
$$\sum_{j=0}^{n-m-1} F^{(m)}_j \bigl(F^{(m+2)}_{n-m-j} + F^{(m+2)}_{n-m-j-1}\bigr) =
F^{(m+2)}_n - F^{(m)}_n.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 4. -/
theorem_wanted sum_fibStep_mul_add (m n : ℕ) (hm : 1 ≤ m)
    (hn : m ≤ n) :
    ∑ j ∈ Finset.range (n - m), fibStep m j *
        (fibStep (m + 2) (n - m - j) +
          fibStep (m + 2) (n - m - j - 1)) =
      fibStep (m + 2) n - fibStep m n

/-- **Double partial sums of Fibonacci step numbers.** For natural numbers $p$ and $n$ with
$1 \le p \le n$, the Fibonacci $(p+1)$-step numbers $F^{(p+1)}_j$ satisfy
$$F^{(p+1)}_n - 1 = \sum_{k=0}^{p-1} \sum_{j=0}^{n-2-k} F^{(p+1)}_j,$$
where an inner sum whose upper limit is $-1$ is empty.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 7. -/
theorem_wanted fibStep_sub_one_eq_sum_sum (p n : ℕ)
    (hp : 1 ≤ p) (hn : p ≤ n) :
    fibStep (p + 1) n - 1 =
      ∑ k ∈ Finset.range p, ∑ j ∈ Finset.range (n - 1 - k),
        fibStep (p + 1) j

/-- **Partial sums of the Fibonacci $m$-step numbers.** For natural numbers $m \ge 2$ and $n$,
the Fibonacci $m$-step numbers $F^{(m)}_k$ satisfy
$$(m-1) \sum_{k=0}^{n} F^{(m)}_k =
F^{(m)}_{n+m} - \sum_{k=1}^{m-2} (m-1-k) F^{(m)}_{n+k} - 1.$$

The source prints this identity divided by $m - 1$ and with coefficients $k$ in place of
$m-1-k$; its proof gives $m-1-k$, and the printed form already fails at $m = 4$, $n = 1$, where
it gives $2/3$ instead of $1$.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 8. -/
theorem_wanted mul_sum_fibStep (m n : ℕ) (hm : 2 ≤ m) :
    ((m : ℤ) - 1) * ∑ k ∈ Finset.range (n + 1), fibStep m k =
      fibStep m (n + m) -
        ∑ k ∈ Finset.Icc 1 (m - 2),
          ((m - 1 - k : ℕ) : ℤ) * fibStep m (n + k) - 1

/-- **Convolution of the Fibonacci and tetranacci numbers.** Write $F_n$ and $Q_n$ for the
Fibonacci and tetranacci numbers, that is, the Fibonacci $m$-step numbers $F^{(m)}_n$ for
$m = 2, 4$ ($F^{(m)}_0 = 0$, $F^{(m)}_1 = 1$, and each later term is the sum of the $m$ terms
before it, terms at negative indices being $0$). For every natural number $n$,
$$\sum_{j=0}^{n} F_j Q_{n-j} = Q_{n+1} + Q_{n-1} - F_{n+1},$$
where for $n = 0$ the term $Q_{n-1}$ is $Q_0 = 0$.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollaries 9 and 16. -/
theorem_wanted sum_fib_mul_tetra (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), fibStep 2 j * fibStep 4 (n - j) =
      fibStep 4 (n + 1) + fibStep 4 (n - 1) - fibStep 2 (n + 1)

/-- **Convolution of the Fibonacci and pentanacci numbers.** Write $F_n$ for the Fibonacci numbers
and $P_n$ for the pentanacci numbers (the Fibonacci $m$-step numbers $F^{(m)}_n$ with $m = 2$ and
$m = 5$). For every integer $n \ge 0$,
$2 \sum_{j=0}^{n} F_j P_{n-j} = P_{n+2} + P_{n-1} - F_{n+2}$, where $P_{n-1}$ is read as
$P_0 = 0$ when $n = 0$.

The source prints this identity with a factor $1/2$; it is stated here multiplied by $2$.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 9. -/
theorem_wanted two_mul_sum_fib_mul_penta (n : ℕ) :
    2 * ∑ j ∈ Finset.range (n + 1),
        fibStep 2 j * fibStep 5 (n - j) =
      fibStep 5 (n + 2) + fibStep 5 (n - 1) - fibStep 2 (n + 2)

/-- **Convolution of the pentanacci and tribonacci numbers.** Write $P_n$ for the pentanacci
numbers and $T_n$ for the tribonacci numbers (the Fibonacci $m$-step numbers $F^{(m)}_n$ with
$m = 5$ and $m = 3$). For every integer $n \ge 0$,
$2 \sum_{j=0}^{n} P_j T_{n-j} = P_{n+3} + P_{n+1} + P_{n-1} - T_{n+3} - T_{n+1}$, where
$P_{n-1}$ is read as $P_0 = 0$ when $n = 0$.

The source prints this identity with a factor $1/2$; it is stated here multiplied by $2$.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 9. -/
theorem_wanted two_mul_sum_penta_mul_trib (n : ℕ) :
    2 * ∑ j ∈ Finset.range (n + 1),
        fibStep 5 j * fibStep 3 (n - j) =
      fibStep 5 (n + 3) + fibStep 5 (n + 1) + fibStep 5 (n - 1) -
        fibStep 3 (n + 3) - fibStep 3 (n + 1)

/-- **Exchange identity for convolutions of $(m-2)$-, $(m-1)$- and $m$-step Fibonacci numbers.**
Write $F^{(m)}_n$ for the Fibonacci $m$-step numbers ($F^{(m)}_0 = 0$, $F^{(m)}_1 = 1$, and each
later term is the sum of the $m$ terms before it, terms at negative indices being $0$). For all
natural numbers $m \ge 3$ and $n \ge 1$,
$$\sum_{j=0}^{n} F^{(m-2)}_j \bigl(F^{(m)}_{n-j} - F^{(m-1)}_{n-j}\bigr) =
\sum_{j=0}^{n-1} F^{(m)}_j \bigl(F^{(m-1)}_{n-1-j} - F^{(m-2)}_{n-1-j}\bigr).$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 10. -/
theorem_wanted sum_fibStep_sub_eq (m n : ℕ) (hm : 3 ≤ m)
    (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range (n + 1), fibStep (m - 2) j *
        (fibStep m (n - j) - fibStep (m - 1) (n - j)) =
      ∑ j ∈ Finset.range n, fibStep m j *
        (fibStep (m - 1) (n - 1 - j) - fibStep (m - 2) (n - 1 - j))

/-- **Difference of the Fibonacci 3-step and 2-step numbers as a convolution.** Let $F_j$ and
$T_j$ be the Fibonacci $2$-step and $3$-step numbers, where the Fibonacci $k$-step numbers start
$0, 1$ and each later term is the sum of the $k$ terms before it (terms of negative index being
$0$). For every natural number $n \ge 1$,

$$T_{n+1} - F_{n+1} = \sum_{j=0}^{n-1} T_j \, F_{n-1-j}.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 11. -/
theorem_wanted trib_sub_fib_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    fibStep 3 (n + 1) - fibStep 2 (n + 1) =
      ∑ j ∈ Finset.range n, fibStep 3 j * fibStep 2 (n - 1 - j)

/-- **Convolution of the Fibonacci numbers with tribonacci minus tetranacci.** Write $F_n$, $T_n$
and $Q_n$ for the Fibonacci, tribonacci and tetranacci numbers, that is, the Fibonacci $m$-step
numbers $F^{(m)}_n$ for $m = 2, 3, 4$ ($F^{(m)}_0 = 0$, $F^{(m)}_1 = 1$, and each later term is the
sum of the $m$ terms before it, terms at negative indices being $0$). For every natural number
$n \ge 1$,
$$\sum_{j=0}^{n} F_j (T_{n-j} - Q_{n-j}) = \sum_{j=0}^{n-1} (F_j - T_j) Q_{n-1-j}.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 11. -/
theorem_wanted sum_fib_mul_sub_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range (n + 1), fibStep 2 j *
        (fibStep 3 (n - j) - fibStep 4 (n - j)) =
      ∑ j ∈ Finset.range n,
        (fibStep 2 j - fibStep 3 j) * fibStep 4 (n - 1 - j)

/-- **Convolution of the Fibonacci 3-step numbers with differences of 4- and 5-step numbers.**
Let $T_j$, $Q_j$ and $P_j$ be the Fibonacci $3$-, $4$- and $5$-step numbers, where the Fibonacci
$k$-step numbers start $0, 1$ and each later term is the sum of the $k$ terms before it (terms of
negative index being $0$). For every natural number $n \ge 1$,

$$\sum_{j=0}^{n} T_j \bigl(Q_{n-j} - P_{n-j}\bigr) =
\sum_{j=0}^{n-1} \bigl(T_j - Q_j\bigr) P_{n-1-j}.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 11. -/
theorem_wanted sum_trib_mul_sub_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range (n + 1), fibStep 3 j *
        (fibStep 4 (n - j) - fibStep 5 (n - j)) =
      ∑ j ∈ Finset.range n,
        (fibStep 3 j - fibStep 4 j) * fibStep 5 (n - 1 - j)

/-- **Convolution of the $(m-1)$-step and $m$-step Fibonacci numbers against powers of two.**
Write $F^{(m)}_n$ for the Fibonacci $m$-step numbers ($F^{(m)}_0 = 0$, $F^{(m)}_1 = 1$, and each
later term is the sum of the $m$ terms before it, terms at negative indices being $0$). For all
natural numbers $m \ge 2$ and $n \ge 2$,
$$\sum_{j=0}^{n} F^{(m-1)}_j F^{(m)}_{n-j} =
\sum_{j=0}^{n-2} 2^j \bigl(F^{(m-1)}_{n-1-j} - F^{(m)}_{n-2-j}\bigr).$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 12. -/
theorem_wanted sum_fibStep_pred_mul (m n : ℕ) (hm : 2 ≤ m)
    (hn : 2 ≤ n) :
    ∑ j ∈ Finset.range (n + 1),
        fibStep (m - 1) j * fibStep m (n - j) =
      ∑ j ∈ Finset.range (n - 1), 2 ^ j *
        (fibStep (m - 1) (n - 1 - j) - fibStep m (n - 2 - j))

/-- **Convolution of the Fibonacci 3-step and 4-step numbers as a sum weighted by powers of 2.**
Let $T_j$ and $Q_j$ be the Fibonacci $3$-step and $4$-step numbers, where the Fibonacci $k$-step
numbers start $0, 1$ and each later term is the sum of the $k$ terms before it (terms of negative
index being $0$). For every natural number $n$,

$$\sum_{j=0}^{n+2} T_j \, Q_{n+2-j} = \sum_{j=0}^{n} 2^j \bigl(T_{n+1-j} - Q_{n-j}\bigr).$$

This is the case $m = 4$ of the paper's Theorem 12 with $n$ replaced by $n + 2$. The paper prints
$Q_{n-j}$ in place of $Q_{n+2-j}$ on the left; as printed, the identity fails at $n = 0$, where
the left side is $0$ and the right side is $1$.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 13. -/
theorem_wanted sum_trib_mul_tetra_eq (n : ℕ) :
    ∑ j ∈ Finset.range (n + 3), fibStep 3 j * fibStep 4 (n + 2 - j) =
      ∑ j ∈ Finset.range (n + 1), 2 ^ j *
        (fibStep 3 (n + 1 - j) - fibStep 4 (n - j))

/-- **Alternating sum of differences of $2m$-step and $(2m-2)$-step Fibonacci numbers.** Write
$F^{(m)}_n$ for the Fibonacci $m$-step numbers ($F^{(m)}_0 = 0$, $F^{(m)}_1 = 1$, and each later
term is the sum of the $m$ terms before it, terms at negative indices being $0$). For all natural
numbers $m \ge 2$ and $n \ge 2m - 1$,
$$\sum_{j=0}^{n-1} (-1)^j \bigl(F^{(2m)}_j - F^{(2m-2)}_j\bigr) =
(-1)^{n+1} \sum_{j=0}^{n-2m+1} F^{(2m)}_j F^{(2m-2)}_{n-2m+1-j}.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 15. -/
theorem_wanted sum_neg_one_pow_sub_even (m n : ℕ)
    (hm : 2 ≤ m) (hn : 2 * m - 1 ≤ n) :
    ∑ j ∈ Finset.range n, (-1 : ℤ) ^ j *
        (fibStep (2 * m) j - fibStep (2 * m - 2) j) =
      (-1 : ℤ) ^ (n + 1) *
        ∑ j ∈ Finset.range (n - 2 * m + 2),
          fibStep (2 * m) j * fibStep (2 * m - 2) (n - 2 * m + 1 - j)

/-- **Alternating sums of differences of odd-order Fibonacci step numbers.** Let $F^{(k)}_j$ be
the $j$-th Fibonacci $k$-step number: the sequence starts $F^{(k)}_0 = 0$, $F^{(k)}_1 = 1$, and each
later term is the sum of the $k$ terms before it (terms of negative index being $0$). For all
natural numbers $m$ and $n$ with $m \ge 1$ and $n \ge 2m$,

$$\sum_{j=0}^{n-1} (-1)^{j+1} \bigl(F^{(2m+1)}_j - F^{(2m-1)}_j\bigr) =
(-1)^n \sum_{j=0}^{n-2m} F^{(2m+1)}_j \, F^{(2m-1)}_{n-2m-j}.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 17. -/
theorem_wanted sum_neg_one_pow_sub_odd (m n : ℕ)
    (hm : 1 ≤ m) (hn : 2 * m ≤ n) :
    ∑ j ∈ Finset.range n, (-1 : ℤ) ^ (j + 1) *
        (fibStep (2 * m + 1) j - fibStep (2 * m - 1) j) =
      (-1 : ℤ) ^ n *
        ∑ j ∈ Finset.range (n - 2 * m + 1),
          fibStep (2 * m + 1) j * fibStep (2 * m - 1) (n - 2 * m - j)

/-- **Alternating sum of the tribonacci numbers.** Write $T_n$ for the tribonacci numbers (the
Fibonacci $3$-step numbers $F^{(3)}_n$). For every integer $n \ge 0$,
$2 \sum_{j=0}^{n} (-1)^j T_j = (-1)^n (T_{n+1} - T_{n-1}) - 1$, where $T_{n-1}$ is read as
$T_0 = 0$ when $n = 0$.

The source prints this identity with a factor $1/2$; it is stated here multiplied by $2$.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 18. -/
theorem_wanted two_mul_sum_neg_one_pow_trib (n : ℕ) :
    2 * ∑ j ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ j * fibStep 3 j =
      (-1 : ℤ) ^ n * (fibStep 3 (n + 1) - fibStep 3 (n - 1)) - 1

/-- **Convolution of the pentanacci and tribonacci numbers, second closed form.** Write $P_n$ for
the pentanacci numbers and $T_n$ for the tribonacci numbers (the Fibonacci $m$-step numbers
$F^{(m)}_n$ with $m = 5$ and $m = 3$). For every integer $n \ge 0$,
$2 \sum_{j=0}^{n} P_j T_{n-j} = -P_{n+7} + 2P_{n+6} - P_{n+5} + 2P_{n+4} + P_{n+3} - T_{n+4} +
T_{n+2}$.

The source prints this identity with a factor $1/2$; it is stated here multiplied by $2$.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 18. -/
theorem_wanted two_mul_sum_penta_mul_trib' (n : ℕ) :
    2 * ∑ j ∈ Finset.range (n + 1),
        fibStep 5 j * fibStep 3 (n - j) =
      -fibStep 5 (n + 7) + 2 * fibStep 5 (n + 6) -
        fibStep 5 (n + 5) + 2 * fibStep 5 (n + 4) +
        fibStep 5 (n + 3) - fibStep 3 (n + 4) + fibStep 3 (n + 2)

/-- **Convolution of the $m$-step and $(m-2)$-step Fibonacci numbers via Jacobsthal numbers.**
Write $F^{(m)}_n$ for the Fibonacci $m$-step numbers ($F^{(m)}_0 = 0$, $F^{(m)}_1 = 1$, and each
later term is the sum of the $m$ terms before it, terms at negative indices being $0$), and $J_n$
for the Jacobsthal numbers ($J_0 = 0$, $J_1 = 1$, $J_{n+2} = J_{n+1} + 2 J_n$). For all natural
numbers $m \ge 3$ and $n \ge 2$,
$$\sum_{j=0}^{n} F^{(m)}_j F^{(m-2)}_{n-j} =
J_{n-1} + \sum_{j=0}^{n-2} J_j \bigl(F^{(m-2)}_{n-j} - F^{(m)}_{n-2-j}\bigr).$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 19. -/
theorem_wanted sum_fibStep_mul_sub_two (m n : ℕ) (hm : 3 ≤ m)
    (hn : 2 ≤ n) :
    ∑ j ∈ Finset.range (n + 1),
        fibStep m j * fibStep (m - 2) (n - j) =
      jacobsthalSeq (n - 1) +
        ∑ j ∈ Finset.range (n - 1), jacobsthalSeq j *
          (fibStep (m - 2) (n - j) - fibStep m (n - 2 - j))

/-- **Convolution of the Jacobsthal and tribonacci numbers.** Write $J_n$ for the Jacobsthal
numbers ($J_0 = 0$, $J_1 = 1$, $J_{n+2} = J_{n+1} + 2J_n$) and $T_n$ for the tribonacci numbers
(the Fibonacci $3$-step numbers $F^{(3)}_n$). For every integer $n \ge 0$,
$2 \sum_{j=0}^{n} J_j T_{n-j} = 2J_{n+1} + J_{n+2} - T_{n+3} - T_{n+1}$.

The source prints this identity with a factor $1/2$ on part of the right-hand side; it is stated
here multiplied by $2$.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 20. -/
theorem_wanted two_mul_sum_jacobsthal_mul_trib (n : ℕ) :
    2 * ∑ j ∈ Finset.range (n + 1),
        jacobsthalSeq j * fibStep 3 (n - j) =
      2 * jacobsthalSeq (n + 1) + jacobsthalSeq (n + 2) -
        fibStep 3 (n + 3) - fibStep 3 (n + 1)

/-- **Triple convolution of Pell numbers with two consecutive Fibonacci step sequences.** Write
$P_k$ for the Pell numbers ($P_0 = 0$, $P_1 = 1$, $P_{k+2} = 2P_{k+1} + P_k$), $F^{(s)}_k$ for
the Fibonacci $s$-step numbers, and $\sum_{K(3,N)}$ for a sum over all
$(k_1, k_2, k_3) \in \mathbb{N}^3$ with $k_1 + k_2 + k_3 = N$. For all natural numbers $m \ge 2$
and $n \ge 1$,
$$
\sum_{K(3, n - 1)} P_{k_1} F^{(m-1)}_{k_2} F^{(m)}_{k_3} =
\sum_{j=0}^{n} F^{(m-1)}_j \left(P_{n-j} - F^{(m)}_{n-j}\right) -
\sum_{j=0}^{n-1} P_j F^{(m)}_{n-1-j}.
$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 21. -/
theorem_wanted compProdSum_pell_fibStep (m n : ℕ)
    (hm : 2 ≤ m) (hn : 1 ≤ n) :
    compProdSum
        (fun i k => ![fun t => (MetaMathlibExt.pellNumber t : ℤ),
          fibStep (m - 1), fibStep m] i k) (n - 1) =
      ∑ j ∈ Finset.range (n + 1), fibStep (m - 1) j *
          ((MetaMathlibExt.pellNumber (n - j) : ℤ) -
            fibStep m (n - j)) -
        ∑ j ∈ Finset.range n,
          (MetaMathlibExt.pellNumber j : ℤ) * fibStep m (n - 1 - j)

/-- **Convolution of the Pell numbers with the Fibonacci numbers.** Let $\mathcal{P}_j$ be the
Pell numbers ($\mathcal{P}_0 = 0$, $\mathcal{P}_1 = 1$,
$\mathcal{P}_{j+2} = 2\mathcal{P}_{j+1} + \mathcal{P}_j$) and $F_j$ the Fibonacci numbers
($F_0 = 0$, $F_1 = 1$, $F_{j+2} = F_{j+1} + F_j$), that is, the Fibonacci $2$-step numbers. For
every natural number $n$,

$$\sum_{j=0}^{n} \mathcal{P}_j \, F_{n-j} = \mathcal{P}_n - F_n.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 22. -/
theorem_wanted sum_pell_mul_fib (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1),
        (MetaMathlibExt.pellNumber j : ℤ) * fibStep 2 (n - j) =
      (MetaMathlibExt.pellNumber n : ℤ) - fibStep 2 n

/-- **Pell–Fibonacci–tribonacci triple sum via a Pell–tribonacci convolution.** Write $P_k$ for
the Pell numbers ($P_0 = 0$, $P_1 = 1$, $P_{k+2} = 2P_{k+1} + P_k$), $F_k$ and $T_k$ for the
Fibonacci $2$- and $3$-step numbers, and $\sum_{K(3,n)}$ for a sum over all
$(k_1, k_2, k_3) \in \mathbb{N}^3$ with $k_1 + k_2 + k_3 = n$. For every natural number $n$,
$$
\sum_{K(3,n)} P_{k_1} F_{k_2} T_{k_3} = P_{n+1} + F_{n+2} - T_{n+3} - \sum_{j=0}^{n} P_j T_{n-j}.
$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 23. -/
theorem_wanted compProdSum_pell_fib_trib (n : ℕ) :
    compProdSum
        (fun i k => ![fun t => (MetaMathlibExt.pellNumber t : ℤ),
          fibStep 2, fibStep 3] i k) n =
      (MetaMathlibExt.pellNumber (n + 1) : ℤ) + fibStep 2 (n + 2) -
        fibStep 3 (n + 3) -
        ∑ j ∈ Finset.range (n + 1),
          (MetaMathlibExt.pellNumber j : ℤ) * fibStep 3 (n - j)

/-- **Closed form for the Pell–Fibonacci–tribonacci triple convolution.** Write $\mathcal{P}_n$
for the Pell numbers, $F_n$ for the Fibonacci numbers and $T_n$ for the tribonacci numbers (the
Fibonacci $m$-step numbers $F^{(m)}_n$ with $m = 2$ and $m = 3$). For every integer $n \ge 0$,
$2 \sum \mathcal{P}_{k_1} F_{k_2} T_{k_3} = \mathcal{P}_{n+1} - T_{n+3} - T_{n+2} + 2F_{n+2}$,
where the sum runs over all triples $(k_1, k_2, k_3)$ of nonnegative integers with
$k_1 + k_2 + k_3 = n$.

The source prints this identity with a factor $1/2$; it is stated here multiplied by $2$.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 23. -/
theorem_wanted two_mul_compProdSum_pell_fib_trib (n : ℕ) :
    2 * compProdSum
        (fun i k => ![fun t => (MetaMathlibExt.pellNumber t : ℤ),
          fibStep 2, fibStep 3] i k) n =
      (MetaMathlibExt.pellNumber (n + 1) : ℤ) - fibStep 3 (n + 3) -
        fibStep 3 (n + 2) + 2 * fibStep 2 (n + 2)

/-- **A product identity for Fibonacci step generating functions of orders $m$, $m+p$,
$m+p+q$.** Let $m, p, q \ge 1$ be natural numbers. For each $k$, let
$F^{(k)} = \sum_{n \ge 0} F^{(k)}_n X^n$ in $\mathbb{Q}[[X]]$ be the ordinary generating function
of the Fibonacci $k$-step numbers $F^{(k)}_n$. Then
$$X^{2m+p} (1-X^p)(1-X^q) F^{(m)} F^{(m+p)} F^{(m+p+q)} =
X^m (1-X)(1-X^p) F^{(m)} F^{(m+p+q)} - (1-X)^2 \left(F^{(m+p)} - F^{(m)}\right).$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 24. -/
theorem_wanted fibStepGF_triple_identity (m p q : ℕ)
    (hm : 1 ≤ m) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    PowerSeries.X ^ (2 * m + p) *
        (1 - PowerSeries.X ^ p) * (1 - PowerSeries.X ^ q) *
        fibStepGF m * fibStepGF (m + p) * fibStepGF (m + p + q) =
      PowerSeries.X ^ m * (1 - PowerSeries.X) *
          (1 - PowerSeries.X ^ p) * fibStepGF m *
          fibStepGF (m + p + q) -
        (1 - PowerSeries.X) ^ 2 *
          (fibStepGF (m + p) - fibStepGF m)

/-- **A product identity for three consecutive Fibonacci step generating functions.** Let
$m \ge 1$ be a natural number. For each $k$, let $F^{(k)} = \sum_{n \ge 0} F^{(k)}_n X^n$ in
$\mathbb{Q}[[X]]$ be the ordinary generating function of the Fibonacci $k$-step numbers
$F^{(k)}_n$. Then
$$X^{2m+1} F^{(m)} F^{(m+1)} F^{(m+2)} = X^m F^{(m)} F^{(m+2)} - F^{(m+1)} + F^{(m)}.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 24. -/
theorem_wanted fibStepGF_triple_consecutive (m : ℕ)
    (hm : 1 ≤ m) :
    PowerSeries.X ^ (2 * m + 1) * fibStepGF m * fibStepGF (m + 1) *
        fibStepGF (m + 2) =
      PowerSeries.X ^ m * fibStepGF m * fibStepGF (m + 2) -
        fibStepGF (m + 1) + fibStepGF m

/-- **Generating-function form of the triple convolution with two consecutive step sequences.**
For a natural number $s$ let $F^{(s)}(X) = \sum_{n \ge 0} F^{(s)}_n X^n$ be the ordinary
generating function, with rational coefficients, of the Fibonacci $s$-step numbers
$F^{(s)}_n$. For all natural numbers $m \ge 1$ and $p \ge 1$, the formal power series over
$\mathbb{Q}$ satisfy
$$
X^m F^{(m)}(X) F^{(m+1)}(X) F^{(p)}(X) = F^{(p)}(X) F^{(m+1)}(X) - F^{(p)}(X) F^{(m)}(X).
$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 25. -/
theorem_wanted fibStepGF_mixed_triple (m p : ℕ) (hm : 1 ≤ m)
    (hp : 1 ≤ p) :
    PowerSeries.X ^ m * fibStepGF m * fibStepGF (m + 1) *
        fibStepGF p =
      fibStepGF p * fibStepGF (m + 1) - fibStepGF p * fibStepGF m

/-- **Triple convolution of two consecutive Fibonacci step sequences with a third.** Write
$F^{(s)}_k$ for the Fibonacci $s$-step numbers, and write $\sum_{K(3,N)}$ for a sum over all
$(k_1, k_2, k_3) \in \mathbb{N}^3$ with $k_1 + k_2 + k_3 = N$. For all natural numbers $m \ge 1$,
$p \ge 1$ and $n \ge m$,
$$
\sum_{K(3, n - m)} F^{(m)}_{k_1} F^{(m+1)}_{k_2} F^{(p)}_{k_3} =
\sum_{j=0}^{n} F^{(p)}_j F^{(m+1)}_{n-j} - \sum_{j=0}^{n} F^{(p)}_j F^{(m)}_{n-j}.
$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 25. -/
theorem_wanted compProdSum_fibStep_triple (m p n : ℕ)
    (hm : 1 ≤ m) (hp : 1 ≤ p) (hn : m ≤ n) :
    compProdSum (fun i k => ![fibStep m, fibStep (m + 1),
        fibStep p] i k) (n - m) =
      ∑ j ∈ Finset.range (n + 1),
          fibStep p j * fibStep (m + 1) (n - j) -
        ∑ j ∈ Finset.range (n + 1),
          fibStep p j * fibStep m (n - j)

/-- **Closed form of the Fibonacci–tribonacci–tetranacci triple sum.** Write $F_k$, $T_k$ and
$Q_k$ for the Fibonacci $2$-, $3$- and $4$-step numbers, and write $\sum_{K(3,n)}$ for a sum over
all $(k_1, k_2, k_3) \in \mathbb{N}^3$ with $k_1 + k_2 + k_3 = n$. For every natural number $n$,
$$
\sum_{K(3,n)} F_{k_1} T_{k_2} Q_{k_3} = Q_{n+4} + Q_{n+2} - T_{n+5} + F_{n+3}.
$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 26. -/
theorem_wanted compProdSum_fib_trib_tetra (n : ℕ) :
    compProdSum (fun i k => ![fibStep 2, fibStep 3, fibStep 4] i k) n =
      fibStep 4 (n + 4) + fibStep 4 (n + 2) - fibStep 3 (n + 5) +
        fibStep 2 (n + 3)

/-- **Triple convolution of the tribonacci, tetranacci and pentanacci numbers.** Write $T_n$,
$Q_n$ and $P_n$ for the Fibonacci $m$-step numbers $F^{(m)}_n$ with $m = 3, 4, 5$ respectively.
For every integer $n \ge 7$,
$2 \sum T_{k_1} Q_{k_2} P_{k_3} = P_n + P_{n-2} + P_{n-4} + T_n - T_{n-2} - 2Q_n$, where the sum
runs over all triples $(k_1, k_2, k_3)$ of nonnegative integers with $k_1 + k_2 + k_3 = n - 7$.

The source prints this identity with a factor $1/2$; it is stated here multiplied by $2$.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 27. -/
theorem_wanted two_mul_compProdSum_trib_tetra_penta (n : ℕ)
    (hn : 7 ≤ n) :
    2 * compProdSum
        (fun i k => ![fibStep 3, fibStep 4, fibStep 5] i k) (n - 7) =
      fibStep 5 n + fibStep 5 (n - 2) + fibStep 5 (n - 4) +
        fibStep 3 n - fibStep 3 (n - 2) - 2 * fibStep 4 n

/-- **Triple convolution of the Fibonacci 2-, 4- and 5-step numbers.** Let $F_j$, $Q_j$ and $P_j$
be the Fibonacci $2$-, $4$- and $5$-step numbers, where the Fibonacci $k$-step numbers start
$0, 1$ and each later term is the sum of the $k$ terms before it (terms of negative index being
$0$). For every natural number $n \ge 5$,

$$2 \sum_{k_1 + k_2 + k_3 = n - 5} F_{k_1} Q_{k_2} P_{k_3}
= -2Q_n - 2Q_{n-2} + P_{n+1} + P_{n-2} - F_{n+1} + 2F_n,$$

where the sum runs over all triples $(k_1, k_2, k_3)$ of natural numbers with
$k_1 + k_2 + k_3 = n - 5$.

The paper prints this identity with a factor $\tfrac{1}{2}$ on part of the right side.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 28. -/
theorem_wanted two_mul_compProdSum_fib_tetra_penta (n : ℕ)
    (hn : 5 ≤ n) :
    2 * compProdSum
        (fun i k => ![fibStep 2, fibStep 4, fibStep 5] i k) (n - 5) =
      -2 * fibStep 4 n - 2 * fibStep 4 (n - 2) +
        fibStep 5 (n + 1) + fibStep 5 (n - 2) - fibStep 2 (n + 1) +
        2 * fibStep 2 n

/-- **Triple convolution of the Fibonacci 2-, 3- and 5-step numbers.** Let $F_j$, $T_j$ and $P_j$
be the Fibonacci $2$-, $3$- and $5$-step numbers, where the Fibonacci $k$-step numbers start
$0, 1$ and each later term is the sum of the $k$ terms before it (terms of negative index being
$0$). For every natural number $n \ge 5$,

$$2 \sum_{k_1 + k_2 + k_3 = n - 5} F_{k_1} T_{k_2} P_{k_3} =
P_n - P_{n-1} + P_{n-2} - T_n - T_{n-2} + F_{n-1},$$

where the sum runs over all triples $(k_1, k_2, k_3)$ of natural numbers with
$k_1 + k_2 + k_3 = n - 5$.

The paper prints this identity with a factor $\tfrac{1}{2}$.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 29. -/
theorem_wanted two_mul_compProdSum_fib_trib_penta (n : ℕ)
    (hn : 5 ≤ n) :
    2 * compProdSum
        (fun i k => ![fibStep 2, fibStep 3, fibStep 5] i k) (n - 5) =
      fibStep 5 n - fibStep 5 (n - 1) + fibStep 5 (n - 2) -
        fibStep 3 n - fibStep 3 (n - 2) + fibStep 2 (n - 1)

/-- **A product identity for four consecutive Fibonacci step generating functions.** Let
$m \ge 1$ be a natural number. For each $k$, let $F^{(k)} = \sum_{n \ge 0} F^{(k)}_n X^n$ in
$\mathbb{Q}[[X]]$ be the ordinary generating function of the Fibonacci $k$-step numbers
$F^{(k)}_n$. Then
$$X^{2m+1} F^{(m)} F^{(m+1)} F^{(m+2)} F^{(m+3)} =
X^m F^{(m)} F^{(m+2)} F^{(m+3)} - F^{(m+1)} F^{(m+3)} + F^{(m)} F^{(m+3)}.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 31. -/
theorem_wanted fibStepGF_quadruple_consecutive (m : ℕ)
    (hm : 1 ≤ m) :
    PowerSeries.X ^ (2 * m + 1) * fibStepGF m * fibStepGF (m + 1) *
        fibStepGF (m + 2) * fibStepGF (m + 3) =
      PowerSeries.X ^ m * fibStepGF m * fibStepGF (m + 2) *
          fibStepGF (m + 3) -
        fibStepGF (m + 1) * fibStepGF (m + 3) +
        fibStepGF m * fibStepGF (m + 3)

/-- **Four-fold convolution of the Fibonacci, tribonacci, tetranacci and pentanacci numbers.**
Write $F_n$, $T_n$, $Q_n$ and $P_n$ for the Fibonacci $m$-step numbers $F^{(m)}_n$ with
$m = 2, 3, 4, 5$ respectively. For every integer $n \ge 5$,
$2 \sum F_{k_1} T_{k_2} Q_{k_3} P_{k_4} = P_{n+4} - P_{n+3} + P_{n+2} + T_{n+3} + T_{n+1} -
F_n - 2Q_{n+3} - 2Q_{n+1}$, where the sum runs over all $4$-tuples $(k_1, k_2, k_3, k_4)$ of
nonnegative integers with $k_1 + k_2 + k_3 + k_4 = n - 5$.

The source prints this identity with a factor $1/2$; it is stated here multiplied by $2$.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 32. -/
theorem_wanted two_mul_compProdSum_four (n : ℕ) (hn : 5 ≤ n) :
    2 * compProdSum (fun i k => ![fibStep 2, fibStep 3,
        fibStep 4, fibStep 5] i k) (n - 5) =
      fibStep 5 (n + 4) - fibStep 5 (n + 3) + fibStep 5 (n + 2) +
        fibStep 3 (n + 3) + fibStep 3 (n + 1) - fibStep 2 n -
        2 * fibStep 4 (n + 3) - 2 * fibStep 4 (n + 1)

/-- **Convolution of four consecutive Fibonacci step sequences.** Write $F^{(s)}_k$ for the
Fibonacci $s$-step numbers, and write $\sum_{K(4,N)}$ for a sum over all
$(k_1, k_2, k_3, k_4) \in \mathbb{N}^4$ with $k_1 + k_2 + k_3 + k_4 = N$. For all natural numbers
$m \ge 1$ and $n \ge 2m + 2$,
$$
\sum_{K(4, n - 2m - 2)} F^{(m)}_{k_1} F^{(m+1)}_{k_2} F^{(m+2)}_{k_3} F^{(m+3)}_{k_4} =
\sum_{j=0}^{n} \left(F^{(m+3)}_j - F^{(m+2)}_j\right) \left(F^{(m+1)}_{n-j} - F^{(m)}_{n-j}\right).
$$

The paper prints the index of the last factor on the left as $k_3$; it is corrected to $k_4$
here.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 34. -/
theorem_wanted compProdSum_four_consecutive (m n : ℕ)
    (hm : 1 ≤ m) (hn : 2 * m + 2 ≤ n) :
    compProdSum (fun i k => ![fibStep m, fibStep (m + 1),
        fibStep (m + 2), fibStep (m + 3)] i k) (n - 2 * m - 2) =
      ∑ j ∈ Finset.range (n + 1),
        (fibStep (m + 3) j - fibStep (m + 2) j) *
          (fibStep (m + 1) (n - j) - fibStep m (n - j))

/-- **Convolution of an even number of consecutive Fibonacci step sequences.** Write $F^{(s)}_k$
for the Fibonacci $s$-step numbers, and write $\sum_{K(r,N)}$ for a sum over all
$(k_1, \dots, k_r) \in \mathbb{N}^r$ with $k_1 + \dots + k_r = N$. For all natural numbers
$\ell \ge 1$, $m \ge 1$ and $n \ge \ell(m + \ell - 1)$,
$$
\sum_{K(2\ell, n - \ell(m + \ell - 1))} \prod_{j=0}^{2\ell-1} F^{(m+j)}_{k_{j+1}} =
\sum_{K(\ell, n)} \prod_{j=0}^{\ell-1} \left(F^{(m+2j+1)}_{k_{j+1}} - F^{(m+2j)}_{k_{j+1}}\right).
$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 35. -/
theorem_wanted compProdSum_even (l m n : ℕ) (hl : 1 ≤ l)
    (hm : 1 ≤ m) (hn : l * (m + l - 1) ≤ n) :
    @compProdSum (2 * l) (fun (j : Fin (2 * l)) k =>
        fibStep (m + j.val) k) (n - l * (m + l - 1)) =
      @compProdSum l (fun (j : Fin l) k =>
        fibStep (m + 2 * j.val + 1) k - fibStep (m + 2 * j.val) k) n

/-- **Convolution of an odd number of consecutive Fibonacci step sequences.** Write $F^{(s)}_k$
for the Fibonacci $s$-step numbers, and write $\sum_{K(r,N)}$ for a sum over all
$(k_1, \dots, k_r) \in \mathbb{N}^r$ with $k_1 + \dots + k_r = N$. For all natural numbers
$\ell \ge 1$, $m \ge 1$ and $n \ge \ell(m + \ell - 1)$,
$$
\sum_{K(2\ell+1, n - \ell(m + \ell - 1))} \prod_{j=0}^{2\ell} F^{(m+j)}_{k_{j+1}} =
\sum_{K(\ell+1, n)} F^{(m+2\ell)}_{k_{\ell+1}} \prod_{j=0}^{\ell-1}
\left(F^{(m+2j+1)}_{k_{j+1}} - F^{(m+2j)}_{k_{j+1}}\right).
$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 35. -/
theorem_wanted compProdSum_odd (l m n : ℕ) (hl : 1 ≤ l)
    (hm : 1 ≤ m) (hn : l * (m + l - 1) ≤ n) :
    @compProdSum (2 * l + 1) (fun (j : Fin (2 * l + 1)) k =>
        fibStep (m + j.val) k) (n - l * (m + l - 1)) =
      @compProdSum (l + 1) (fun (j : Fin (l + 1)) k =>
        if (j.val : ℕ) = l then fibStep (m + 2 * l) k
        else fibStep (m + 2 * j.val + 1) k -
          fibStep (m + 2 * j.val) k) n

/-- **Two convolution forms of the Fibonacci–tribonacci–tetranacci triple sum.** Write $F_k$,
$T_k$ and $Q_k$ for the Fibonacci $2$-, $3$- and $4$-step numbers, and write $\sum_{K(3,N)}$ for
a sum over all $(k_1, k_2, k_3) \in \mathbb{N}^3$ with $k_1 + k_2 + k_3 = N$. For every natural
number $n \ge 2$,
$$
\sum_{K(3, n - 2)} F_{k_1} T_{k_2} Q_{k_3} = \sum_{j=0}^{n} (T_j - F_j) Q_{n-j} =
\sum_{j=0}^{n+1} F_{n+1-j} (Q_j - T_j).
$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 36. -/
theorem_wanted compProdSum_fib_trib_tetra_eq (n : ℕ)
    (hn : 2 ≤ n) :
    compProdSum (fun i k => ![fibStep 2, fibStep 3, fibStep 4] i k)
          (n - 2) =
        ∑ j ∈ Finset.range (n + 1),
          (fibStep 3 j - fibStep 2 j) * fibStep 4 (n - j) ∧
      compProdSum (fun i k => ![fibStep 2, fibStep 3, fibStep 4] i k)
          (n - 2) =
        ∑ j ∈ Finset.range (n + 2),
          fibStep 2 (n + 1 - j) * (fibStep 4 j - fibStep 3 j)

/-- **Sum of $2m + 2$ consecutive Fibonacci $m$-step numbers.** Write $F^{(m)}_n$ for the
Fibonacci $m$-step numbers ($F^{(m)}_0 = 0$, $F^{(m)}_1 = 1$, and each later term is the sum of
the $m$ terms before it, terms at negative indices being $0$). For every natural number $m \ge 2$
and every natural number $n$,
$$\sum_{k=0}^{2m+1} F^{(m)}_{n+k} = 4 F^{(m)}_{n+2m}.$$

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Lemma 39. -/
theorem_wanted sum_fibStep_window (m n : ℕ) (hm : 2 ≤ m) :
    ∑ k ∈ Finset.range (2 * m + 2), fibStep m (n + k) =
      4 * fibStep m (n + 2 * m)

/-- **Convolution of the Fibonacci $6$-step numbers with the Fibonacci numbers.** Write
$s_n = F^{(6)}_n$ for the Fibonacci $6$-step numbers and $F_n = F^{(2)}_n$ for the Fibonacci
numbers. For every natural number $n \ge 3$,
$$5 \sum_{j=0}^{n} s_j F_{n-j} =
s_{n+3} + s_{n+1} - s_n + 3 s_{n-1} + s_{n-3} - F_{n+3} - F_{n+1}.$$

The source prints this identity divided by $5$.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 41. -/
theorem_wanted five_mul_sum_fibStep6_mul_fib (n : ℕ)
    (hn : 3 ≤ n) :
    5 * ∑ j ∈ Finset.range (n + 1),
        fibStep 6 j * fibStep 2 (n - j) =
      fibStep 6 (n + 3) + fibStep 6 (n + 1) - fibStep 6 n +
        3 * fibStep 6 (n - 1) + fibStep 6 (n - 3) -
        fibStep 2 (n + 3) - fibStep 2 (n + 1)

end MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted
