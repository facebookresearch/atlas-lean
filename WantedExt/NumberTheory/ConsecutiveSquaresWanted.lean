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
public import Mathlib.Data.Set.Finite.Basic

namespace MetaMathlibExt

@[expose] public section

/-- The Sum of Consecutive Squares (SoCS) equation
`(a+1)^2 + ⋯ + b^2 = (b+1)^2 + ⋯ + c^2`, written in cleared square-pyramidal
form `2 * P b = P a + P c` with `6 * P x = x * (x + 1) * (2 * x + 1)`.

Verified verbatim against the primary source (arXiv:2411.08398, the TeX
source of the published article): equation (1) there is
`(a+1)^2 + (a+2)^2 + ⋯ + b^2 = (b+1)^2 + (b+2)^2 + ⋯ + c^2`, restated with
`P_n = n(n+1)(2n+1)/6` as `P_b - P_a = P_c - P_b`, i.e. equation (2)
`P_a + P_c = 2 P_b`, under the range `0 < a + 1 < b < c`. The form used here
is (2) multiplied through by `6`.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, equations (1) and (2). -/
public def SoCSEq (a b c : ℤ) : Prop :=
  2 * (b * (b + 1) * (2 * b + 1))
    = a * (a + 1) * (2 * a + 1) + c * (c + 1) * (2 * c + 1)

/-- A solution of the Sum of Consecutive Squares Problem in the paper's
range `0 < a + 1 < b < c`.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Section 1. -/
public def IsSoCSSolution (a b c : ℤ) : Prop :=
  0 < a + 1 ∧ a + 1 < b ∧ b < c ∧ SoCSEq a b c

/-- Characteristic example: `(2, 4, 5)` is a SoCS solution, since
`3^2 + 4^2 = 5^2`.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Section 1. -/
public theorem isSoCSSolution_two_four_five : IsSoCSSolution 2 4 5 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  unfold SoCSEq
  norm_num

/-- Bounds on the ratio `(b - a) / (c - b)` for SoCS solutions:
`1 < (b - a) / (c - b) < 1 + 2^{1/3} + 2^{2/3}`.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Lemma 1
(`integers-2026-A1-lem-1`). -/
public theorem_wanted soCS_ratio_bounds (a b c : ℤ) (h : IsSoCSSolution a b c) :
    1 < (b - a : ℝ) / (c - b) ∧
    (b - a : ℝ) / (c - b) < 1 + (2 : ℝ) ^ (1 / 3 : ℝ) + (2 : ℝ) ^ (2 / 3 : ℝ)

/-- For a SoCS solution `(a, b, c)`, the Pell-type parameter
`A = 3 * (b - c)^2 * (12 * (b - a)^2 * (c - b)^2 - (a - 2b + c)^4)` is
positive and is not a square.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Corollary 1
(`integers-2026-A1-cor-1`), verified against arXiv:2411.08398 (the formula
is garbled in the statement extraction). -/
public theorem_wanted soCS_pell_param_pos_nonsquare (a b c : ℤ)
    (h : IsSoCSSolution a b c) :
    0 < 3 * (b - c) ^ 2 * (12 * (b - a) ^ 2 * (c - b) ^ 2 - (a - 2 * b + c) ^ 4) ∧
    ¬ IsSquare (3 * (b - c) ^ 2 * (12 * (b - a) ^ 2 * (c - b) ^ 2 - (a - 2 * b + c) ^ 4))

/-- From any SoCS solution `(a, b, c)` one obtains an infinite family of
integer solutions of the SoCS equation, all lying in the plane
`(b - c) * x + (c - a) * y + (a - b) * z = 0`, with `z - x ≡ c - a (mod 2)`.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Proposition 1
(`integers-2026-A1-prop-1`). -/
public theorem_wanted soCS_infinite_family_plane (a b c : ℤ)
    (h : IsSoCSSolution a b c) :
    ∃ f : ℕ → ℤ × ℤ × ℤ, Function.Injective f ∧
      ∀ n, SoCSEq (f n).1 (f n).2.1 (f n).2.2 ∧
        (b - c) * (f n).1 + (c - a) * (f n).2.1 + (a - b) * (f n).2.2 = 0 ∧
        (f n).2.2 - (f n).1 ≡ c - a [ZMOD 2]

/-- For each odd `N ≥ 3` there is a SoCS solution `(a, b, c)` with
`c - a = N`, and an infinite family of SoCS solutions with odd span, all
lying in the plane `(b - c) * x + (c - a) * y + (a - b) * z = 0` determined
by that solution (the plane through `(a, b, c)` and the line `x = y = z`, as
in Proposition 1). Partial scope: the paper additionally states that this
plane is unique for each `N`; that uniqueness clause is not encoded here.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Theorem 2
(`integers-2026-A1-thm-2`), verified against arXiv:2411.08398. -/
public theorem_wanted soCS_odd_span (N : ℤ) (hN : Odd N) (h3 : 3 ≤ N) :
    ∃ a b c : ℤ, IsSoCSSolution a b c ∧ c - a = N ∧
    ∃ f : ℕ → ℤ × ℤ × ℤ, Function.Injective f ∧
      ∀ n, IsSoCSSolution (f n).1 (f n).2.1 (f n).2.2 ∧
        Odd ((f n).2.2 - (f n).1) ∧
        (b - c) * (f n).1 + (c - a) * (f n).2.1 + (a - b) * (f n).2.2 = 0

/-- There are infinitely many SoCS solutions with `c - a` even.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Theorem 3
(`integers-2026-A1-thm-3`). -/
public theorem_wanted soCS_even_span_infinite :
    {t : ℤ × ℤ × ℤ | IsSoCSSolution t.1 t.2.1 t.2.2 ∧ Even (t.2.2 - t.1)}.Infinite

/-- For each `N > 1` there are at most `2 * (N - 1)` SoCS solutions with
`c - a = N`.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Theorem 5
(`integers-2026-A1-thm-5`). -/
public theorem_wanted soCS_card_le (N : ℤ) (hN : 1 < N)
    (s : Finset (ℤ × ℤ × ℤ))
    (hs : ∀ t ∈ s, IsSoCSSolution t.1 t.2.1 t.2.2 ∧ t.2.2 - t.1 = N) :
    s.card ≤ 2 * (N - 1).toNat

/-- No finite collection of planes in `ℝ^3` contains all SoCS solutions:
for every finite set of affine planes `u * x + v * y + w * z = t` with
nonzero normal vector, some SoCS solution lies outside all of them.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Corollary 2
(`integers-2026-A1-cor-2`); the proof text appended to the extracted
statement is not part of the claim. -/
public theorem_wanted soCS_not_finite_planes
    (S : Finset (ℝ × ℝ × ℝ × ℝ))
    (hS : ∀ p ∈ S, (p.1, p.2.1, p.2.2.1) ≠ 0) :
    ∃ a b c : ℤ, IsSoCSSolution a b c ∧
      ∀ p ∈ S, p.1 * (a : ℝ) + p.2.1 * (b : ℝ) + p.2.2.1 * (c : ℝ) ≠ p.2.2.2

end

end MetaMathlibExt
