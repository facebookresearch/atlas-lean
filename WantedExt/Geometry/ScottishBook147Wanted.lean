/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MathlibExt.Geometry.ScottishBook147Wanted

/--
The unfolding/lattice step of the billiard argument for Scottish Book
Problem 147 (Auerbach–Mazur): for a rectangle with rational side ratio,
the unfolded diagonal first meets a corner of the tiling at `(t, t)` with
`t = k * a = l * b` for positive coprime integers `k, l` (coprimality is
the first-hit condition: without it the diagonal would pass through an
earlier lattice corner), and the number `N` of reflections satisfies
`N + 2 = k + l` (the diagonal crosses `k - 1` vertical and `l - 1`
horizontal grid lines). Folding back, the corner reached is
`(if k % 2 = 1 then a else 0, if l % 2 = 1 then b else 0)`, one of the
three remaining corners `(a, 0)`, `(0, b)`, `(a, b)` (coprimality gives
`k % 2 = 1 ∨ l % 2 = 1`, so the folded corner is never the starting
`(0, 0)`). This is ONLY the unfolding/lattice step: it does not by itself
formalize the reflected trajectory in the rectangle, and does not by itself
prove Problem 147.
Source: H. Auerbach and S. Mazur, Problem 147 of the Scottish Book; the
typescript labels the entry Theorem (Problem Mazur). Elementary unfolding
argument for polygonal billiards, see e.g. S. Tabachnikov, Geometry and
Billiards.
-/
theorem_wanted billiardUnfoldingDiagonalLemma :
    ∀ a b : ℝ, 0 < a → 0 < b →
      (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ a * (n : ℝ) = b * (m : ℝ)) →
      ∃ t : ℝ, ∃ k l N : ℕ, 0 < t ∧ 0 < k ∧ 0 < l ∧ t = (k : ℝ) * a ∧
        t = (l : ℝ) * b ∧ N + 2 = k + l ∧ Nat.Coprime k l ∧
        (if k % 2 = 1 then a else 0, if l % 2 = 1 then b else 0) ∈
          ({(a, 0), (0, b), (a, b)} : Set (ℝ × ℝ))

end MathlibExt.Geometry.ScottishBook147Wanted
