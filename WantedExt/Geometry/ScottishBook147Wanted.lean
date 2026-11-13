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
**Lattice step of the billiard unfolding in a rectangle.** For a natural number $j$, let
$\varepsilon_j = 1$ if $j$ is odd and $\varepsilon_j = 0$ if $j$ is even. Let $a, b > 0$ be real
numbers with $a n = b m$ for some positive integers $m, n$. Then there are a real number $t > 0$
and natural numbers $k > 0$, $l > 0$ and $N$ such that $t = k a = l b$, $N + 2 = k + l$, $k$ and
$l$ are coprime, and the point $(\varepsilon_k a, \varepsilon_l b)$ is one of $(a, 0)$, $(0, b)$,
$(a, b)$.

In the billiard argument for the $a \times b$ rectangle, the unfolded diagonal from the
corner $(0, 0)$ first meets a corner of the tiling at $(t, t)$ (coprimality is the first-hit
condition), $N$ counts the reflections, and folding back yields the corner
$(\varepsilon_k a, \varepsilon_l b)$. This lemma covers only that lattice step; it does not
formalize the reflected trajectory and does not prove Problem 147.

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
