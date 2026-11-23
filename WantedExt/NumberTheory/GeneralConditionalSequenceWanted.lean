/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Linear recurrences satisfied by general conditional sequences

Statements from Emre Güday and Murat Sahin, *Linear Recurrence Relations Satisfied by the
General Conditional Sequences*, INTEGERS 26 (2026), Article A5. The paper's sequence `s_n`
satisfies the `mr`-th order recurrence (3)
`s_{n+mr} = A_{m-1} s_{n+(m-1)r} + A_{m-2} s_{n+(m-2)r} + ⋯ + A_0 s_n` (`n ≥ 0`) with arbitrary
initial values; here the coefficients are `A : ℕ → R` (only `A 0, …, A (m-1)` are used) and the
hypothesis is `s (n + m * r) = ∑_{j < m} A j * s (n + j * r)`.
-/

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- **Decimation coefficients.** Let $(A_j)_{j \ge 0}$ and $(s_n)_{n \ge 0}$ be sequences in a
commutative ring and let $m$, $r$ be natural numbers. For natural numbers $l$ and $i$, the
decimation coefficient is
$$v_l^{(i)} = s_{lr+i} - \sum_{j<l} A_{m-1-j} s_{(l-1-j)r+i},$$
an index $m-1-j$ that would be negative being read as $0$. For $l \le m$ this is
$v_l^{(i)} = s_{lr+i} - A_{m-1} s_{(l-1)r+i} - \cdots - A_{m-l} s_i$.

Source: Emre Güday and Murat Sahin, *Linear Recurrence Relations Satisfied by the General
Conditional Sequences*, INTEGERS 26 (2026), Article A5, Theorem 1. -/
public def decimationCoeff {R : Type*} [CommRing R] (A s : ℕ → R) (m r l i : ℕ) : R :=
  s (l * r + i) - ∑ j ∈ Finset.range l, A (m - 1 - j) * s ((l - 1 - j) * r + i)

/-- **Zeroth decimation coefficient.** For sequences $(A_j)_{j \ge 0}$ and $(s_n)_{n \ge 0}$ in
a commutative ring and natural numbers $m$, $r$, $i$, the decimation coefficient $v_0^{(i)}$
equals $s_i$.

Source: Emre Güday and Murat Sahin, *Linear Recurrence Relations Satisfied by the General
Conditional Sequences*, INTEGERS 26 (2026), Article A5, Theorem 1. -/
public theorem decimationCoeff_zero {R : Type*} [CommRing R] (A s : ℕ → R) (m r i : ℕ) :
    decimationCoeff A s m r 0 i = s i := by
  simp [decimationCoeff]

/-- **First decimation coefficient.** For sequences $(A_j)_{j \ge 0}$ and $(s_n)_{n \ge 0}$ in a
commutative ring and natural numbers $m$, $r$, $i$, the decimation coefficient $v_1^{(i)}$
equals $s_{r+i} - A_{m-1} s_i$, where $A_{m-1}$ is read as $A_0$ when $m = 0$.

Source: Emre Güday and Murat Sahin, *Linear Recurrence Relations Satisfied by the General
Conditional Sequences*, INTEGERS 26 (2026), Article A5, Theorem 1. -/
public theorem decimationCoeff_one {R : Type*} [CommRing R] (A s : ℕ → R) (m r i : ℕ) :
    decimationCoeff A s m r 1 i = s (r + i) - A (m - 1) * s i := by
  simp [decimationCoeff]

/-- **Generating function of a decimated linear recurrence.** Let $R$ be a commutative ring,
let $m$ and $r$ be natural numbers, and let $(A_j)_{j \ge 0}$ and $(s_n)_{n \ge 0}$ be
sequences in $R$ such that $s_{n+mr} = \sum_{j<m} A_j s_{n+jr}$ for all $n \ge 0$. Then, in
the ring $R[[x]]$ of formal power series,
$$
\Bigl(\sum_{n \ge 0} s_n x^n\Bigr)\Bigl(1 - \sum_{j<m} A_j x^{(m-j)r}\Bigr) =
\sum_{i<r} \sum_{l<m} v_l^{(i)} x^{lr+i},
$$
where $v_l^{(i)} = s_{lr+i} - \sum_{j<l} A_{m-1-j} s_{(l-1-j)r+i}$ are the decimation
coefficients. The second factor on the left is the denominator
$1 - A_{m-1} x^r - A_{m-2} x^{2r} - \cdots - A_0 x^{mr}$ of the generating function.

The printed denominator ends in $- A_1 x^{mr} - A_0$ and the printed hypothesis names
Relation (1); this is the reading of the paper's derivation and of its Example 2 ($m = 2$:
$1 - A_1 x^r - A_0 x^{2r}$).

Source: Emre Güday and Murat Sahin, *Linear Recurrence Relations Satisfied by the General
Conditional Sequences*, INTEGERS 26 (2026), Article A5, Theorem 1 (`integers-2026-A5-thm-1`). -/
public theorem_wanted decimation_generating_function {R : Type*} [CommRing R] {m r : ℕ}
    {A s : ℕ → R} (hs : ∀ n, s (n + m * r) = ∑ j ∈ Finset.range m, A j * s (n + j * r)) :
    PowerSeries.mk s *
        (1 - ∑ j ∈ Finset.range m, PowerSeries.C (A j) * PowerSeries.X ^ ((m - j) * r)) =
      ∑ i ∈ Finset.range r, ∑ l ∈ Finset.range m,
        PowerSeries.C (decimationCoeff A s m r l i) * PowerSeries.X ^ (l * r + i)

/-- **Binet formula for decimated linear recurrences.** Let $m$ and $r$ be natural numbers and
let $(A_j)_{j \ge 0}$ and $(s_n)_{n \ge 0}$ be sequences of complex numbers such that
$s_{n+mr} = \sum_{j<m} A_j s_{n+jr}$ for all $n \ge 0$. Let $f(x) = x^m - \sum_{j<m} A_j x^j$
and let $\alpha_1, \ldots, \alpha_m$ be pairwise distinct roots of $f$ in $\mathbb{C}$. Then
for every $n \ge 0$
$$
s_n = \sum_{l<m} v_l^{(n \bmod r)}
\sum_{t=1}^{m} \frac{\alpha_t^{m-1-l+\lfloor n/r \rfloor}}{f'(\alpha_t)},
$$
where $v_l^{(i)} = s_{lr+i} - \sum_{j<l} A_{m-1-j} s_{(l-1-j)r+i}$ are the decimation
coefficients. For $r = 0$ the formula is read with $n \bmod 0 = n$ and
$\lfloor n/0 \rfloor = 0$.

Source: Emre Güday and Murat Sahin, *Linear Recurrence Relations Satisfied by the General
Conditional Sequences*, INTEGERS 26 (2026), Article A5, Theorem 2 (`integers-2026-A5-thm-2`). -/
public theorem_wanted decimation_binet {m r : ℕ} {A s : ℕ → ℂ}
    (hs : ∀ n, s (n + m * r) = ∑ j ∈ Finset.range m, A j * s (n + j * r))
    {α : Fin m → ℂ} (hα : Function.Injective α)
    (hroot : ∀ t, (X ^ m - ∑ j ∈ Finset.range m, C (A j) * X ^ j : ℂ[X]).eval (α t) = 0)
    (n : ℕ) :
    s n = ∑ l ∈ Finset.range m, decimationCoeff A s m r l (n % r) *
      ∑ t, α t ^ (m - 1 - l + n / r) /
        (derivative (X ^ m - ∑ j ∈ Finset.range m, C (A j) * X ^ j : ℂ[X])).eval (α t)

end

end MetaMathlibExt
