/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Geometry.ScottishBook59Wanted

/--
**Squaring the square with distinct squares.** There are an integer $n > 1$ and real numbers
$x_i$, $y_i$ and $s_i > 0$ for $i = 1, \dots, n$, with the $s_i$ pairwise distinct, such that
the union of the closed squares $[x_i, x_i + s_i] \times [y_i, y_i + s_i]$ is the unit square
$[0, 1] \times [0, 1]$ and any two of these squares with different indices have disjoint
interiors.

Source: S. Ruziewicz, Problem 59 of the
Scottish Book, asking whether a square can be decomposed into a finite
number of squares all different from one another; the answer is
affirmative. The first published solution is R. Sprague's 1939
squaring of the square with distinct squares; see the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015),
and the 2026 survey "90+ years of the Scottish Book"
(arXiv:2603.27867).
-/
theorem_wanted squaringTheSquareDistinctSquares :
    ∃ (n : ℕ) (x y s : Fin n → ℝ),
      (1 < n) ∧
      (∀ i, 0 < s i) ∧
      (∀ i j, i ≠ j → s i ≠ s j) ∧
      (⋃ i, Set.Icc (x i, y i) (x i + s i, y i + s i) =
        Set.Icc (0, 0) (1, 1)) ∧
      ∀ i j, i ≠ j →
        Disjoint
          (interior (Set.Icc (x i, y i) (x i + s i, y i + s i)))
          (interior (Set.Icc (x j, y j) (x j + s j, y j + s j)))

end MathlibExt.Geometry.ScottishBook59Wanted
