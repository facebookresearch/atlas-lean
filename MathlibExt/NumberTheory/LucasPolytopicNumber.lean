/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Real.Basic

/-!
# Lucas-polytopic numbers

This file formalizes the definitions in Orozco López,
*Simplicial d-Polytopic Numbers Defined on Lucas Sequences*:
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Orozco/oroz2.tex>.
-/

@[expose] public section

open scoped BigOperators

namespace MetaMathlibExt

/-- **Lucas brackets for arbitrary real parameters.** For real numbers $s$ and $t$, this is the
sequence of real numbers $a_0, a_1, a_2, \dots$ defined by $a_0 = 0$, $a_1 = 1$ and
$a_{n+2} = s a_{n+1} + t a_n$ for every natural number $n$.

No condition is imposed on $s$ and $t$. -/
def lucasBracketAux (s t : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | n + 2 => s * lucasBracketAux s t (n + 1) + t * lucasBracketAux s t n

/-- **Nondegenerate Lucas parameters.** For real numbers $s$ and $t$, let $\{n\}_{s,t}$ be the
sequence of real numbers with $\{0\}_{s,t} = 0$, $\{1\}_{s,t} = 1$ and
$\{n+2\}_{s,t} = s\{n+1\}_{s,t} + t\{n\}_{s,t}$ for every natural number $n$. Nondegenerate
Lucas parameters are a pair of real numbers $(s, t)$ with $s \ne 0$, $t \ne 0$ and
$\{n\}_{s,t} \ne 0$ for every natural number $n \ne 0$.

The last condition ensures that the $s,t$-factorials are nonzero, so quotients of them never
divide by zero. -/
structure LucasParameters where
  s : ℝ
  t : ℝ
  s_ne_zero : s ≠ 0
  t_ne_zero : t ≠ 0
  bracket_ne_zero : ∀ n, n ≠ 0 → lucasBracketAux s t n ≠ 0

/-- **Lucas brackets.** For nondegenerate Lucas parameters $(s, t)$, the Lucas brackets are the
real numbers $\{n\}_{s,t}$, for natural numbers $n$, defined by $\{0\}_{s,t} = 0$,
$\{1\}_{s,t} = 1$ and $\{n+2\}_{s,t} = s\{n+1\}_{s,t} + t\{n\}_{s,t}$ for every natural
number $n$. -/
def lucasBracket (P : LucasParameters) : ℕ → ℝ
  | n => lucasBracketAux P.s P.t n

theorem lucasBracket_ne_zero (P : LucasParameters) {n : ℕ} (hn : n ≠ 0) :
    lucasBracket P n ≠ 0 :=
  P.bracket_ne_zero n hn

/-- **Factorial of Lucas brackets.** For nondegenerate Lucas parameters $(s, t)$, write
$\{k\}_{s,t}$ for the $k$-th Lucas bracket. For a natural number $n$, the $s,t$-factorial is the
real number $\{n\}_{s,t}! = \prod_{k=1}^{n} \{k\}_{s,t}$, the product of
$\{1\}_{s,t}, \dots, \{n\}_{s,t}$; for $n = 0$ it is the empty product $1$. -/
def lucasFactorial (P : LucasParameters) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, lucasBracket P (k + 1)

theorem lucasFactorial_ne_zero (P : LucasParameters) (n : ℕ) :
    lucasFactorial P n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  exact lucasBracket_ne_zero P (Nat.succ_ne_zero k)

/-- **Lucasnomial coefficients.** Let $(s, t)$ be nondegenerate Lucas parameters and write
$\{m\}_{s,t}!$ for the $s,t$-factorial of a natural number $m$. For natural numbers $n$ and
$k$, the Lucasnomial coefficient is the real number
$$\binom{n}{k}_{s,t} = \frac{\{n\}_{s,t}!}{\{k\}_{s,t}! \{n-k\}_{s,t}!}$$
when $k \le n$, and $\binom{n}{k}_{s,t} = 0$ when $k > n$. -/
noncomputable def lucasnomial (P : LucasParameters) (n k : ℕ) : ℝ :=
  if k ≤ n then lucasFactorial P n / (lucasFactorial P k * lucasFactorial P (n - k)) else 0

@[simp]
theorem lucasnomial_eq_zero_of_lt (P : LucasParameters) {n k : ℕ} (h : n < k) :
    lucasnomial P n k = 0 := by
  simp [lucasnomial, Nat.not_le.mpr h]

/-- **Simplicial Lucas-polytopic numbers.** For nondegenerate Lucas parameters $(s, t)$ and
natural numbers $n$ and $d$, the $n$-th simplicial $d$-Lucas-polytopic number is the
Lucasnomial coefficient $\binom{n+d-1}{d}_{s,t}$, where $n + d - 1$ is read as $0$ when
$n = d = 0$. -/
noncomputable def lucasPolytopicNumber (P : LucasParameters) (n d : ℕ) : ℝ :=
  lucasnomial P (n + d - 1) d

/-- **Lucas triangular numbers.** For nondegenerate Lucas parameters $(s, t)$ and a natural
number $n$, the $n$-th Lucas triangular number is the Lucasnomial coefficient
$\binom{n+1}{2}_{s,t}$. -/
noncomputable def lucasTriangularNumber (P : LucasParameters) (n : ℕ) : ℝ :=
  lucasnomial P (n + 1) 2

/-- **Lucas tetrahedral numbers.** For nondegenerate Lucas parameters $(s, t)$ and a natural
number $n$, the $n$-th Lucas tetrahedral number is the Lucasnomial coefficient
$\binom{n+2}{3}_{s,t}$. -/
noncomputable def lucasTetrahedralNumber (P : LucasParameters) (n : ℕ) : ℝ :=
  lucasnomial P (n + 2) 3

/-- **Lucas pentachoron numbers.** For nondegenerate Lucas parameters $(s, t)$ and a natural
number $n$, the $n$-th Lucas pentachoron number is the Lucasnomial coefficient
$\binom{n+3}{4}_{s,t}$. -/
noncomputable def lucasPentachoronNumber (P : LucasParameters) (n : ℕ) : ℝ :=
  lucasnomial P (n + 3) 4

/-- **Lucas hexateron numbers.** For nondegenerate Lucas parameters $(s, t)$ and a natural
number $n$, the $n$-th Lucas hexateron number is the Lucasnomial coefficient
$\binom{n+4}{5}_{s,t}$. -/
noncomputable def lucasHexateronNumber (P : LucasParameters) (n : ℕ) : ℝ :=
  lucasnomial P (n + 4) 5

end MetaMathlibExt
