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

/-- The coefficient `v_l^{(i)} = s_{lr+i} - A_{m-1} s_{(l-1)r+i} - ⋯ - A_{m-l} s_i` of Theorems 1
and 2.

Source: Emre Güday and Murat Sahin, *Linear Recurrence Relations Satisfied by the General
Conditional Sequences*, INTEGERS 26 (2026), Article A5, Theorem 1. -/
public def decimationCoeff {R : Type*} [CommRing R] (A s : ℕ → R) (m r l i : ℕ) : R :=
  s (l * r + i) - ∑ j ∈ Finset.range l, A (m - 1 - j) * s ((l - 1 - j) * r + i)

/-- `v_0^{(i)} = s_i`.

Source: Emre Güday and Murat Sahin, *Linear Recurrence Relations Satisfied by the General
Conditional Sequences*, INTEGERS 26 (2026), Article A5, Theorem 1. -/
public theorem decimationCoeff_zero {R : Type*} [CommRing R] (A s : ℕ → R) (m r i : ℕ) :
    decimationCoeff A s m r 0 i = s i := by
  simp [decimationCoeff]

/-- `v_1^{(i)} = s_{r+i} - A_{m-1} s_i`.

Source: Emre Güday and Murat Sahin, *Linear Recurrence Relations Satisfied by the General
Conditional Sequences*, INTEGERS 26 (2026), Article A5, Theorem 1. -/
public theorem decimationCoeff_one {R : Type*} [CommRing R] (A s : ℕ → R) (m r i : ℕ) :
    decimationCoeff A s m r 1 i = s (r + i) - A (m - 1) * s i := by
  simp [decimationCoeff]

/-- Generating function of a solution of (3):
`∑ s_n x^n = (∑_{i<r} ∑_{l<m} v_l^{(i)} x^{lr+i}) / (1 - A_{m-1} x^r - A_{m-2} x^{2r} - ⋯ - A_0 x^{mr})`,
stated multiplied through by the denominator. The printed denominator ends in
`- A_1 x^{mr} - A_0` and the printed hypothesis names Relation (1); this is the reading of the
paper's derivation and of its Example 2 (`m = 2`: `1 - A_1 x^r - A_0 x^{2r}`).

Source: Emre Güday and Murat Sahin, *Linear Recurrence Relations Satisfied by the General
Conditional Sequences*, INTEGERS 26 (2026), Article A5, Theorem 1 (`integers-2026-A5-thm-1`). -/
public theorem_wanted decimation_generating_function {R : Type*} [CommRing R] {m r : ℕ}
    {A s : ℕ → R} (hs : ∀ n, s (n + m * r) = ∑ j ∈ Finset.range m, A j * s (n + j * r)) :
    PowerSeries.mk s *
        (1 - ∑ j ∈ Finset.range m, PowerSeries.C (A j) * PowerSeries.X ^ ((m - j) * r)) =
      ∑ i ∈ Finset.range r, ∑ l ∈ Finset.range m,
        PowerSeries.C (decimationCoeff A s m r l i) * PowerSeries.X ^ (l * r + i)

/-- Binet form of a solution of (3): if `f(x) = x^m - A_{m-1} x^{m-1} - ⋯ - A_0` has `m` distinct
roots `α_1, …, α_m`, then for all `n ≥ 0`, with `ξ(n) = n mod r`,
`s_n = ∑_{l<m} v_l^{(ξ(n))} ∑_t α_t^{m-1-l+⌊n/r⌋} / f'(α_t)`.

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
