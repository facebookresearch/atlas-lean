/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.GridLRamsey
import MathlibExt.Combinatorics.GridLRamseyThree772

/-!
# Monochromatic L-shapes in the three-colored 1804 × 1804 grid

The bound 1804 follows from the stronger bound 772 by restricting to a smaller square.
-/

namespace MetaMathlibExt

/-- **Three-coloring the 1804 × 1804 grid forces a monochromatic L.** Write
$[n] = \{1, \dots, n\}$. Every coloring of the grid $[1804] \times [1804]$ with $3$ colors contains
a monochromatic L: positive integers $x$, $y$, $d$ with $x + d \le 1804$ and $y + d \le 1804$ such
that the points $(x, y)$, $(x + d, y)$ and $(x + d, y + d)$ have the same color. Equivalently,
the grid Ramsey number $R_3(L)$, the least $n$ for which every coloring of $[n] \times [n]$ with
$3$ colors contains a monochromatic L, is at most $1804$.

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21, Theorem 3. -/
public theorem gridLRamseyProperty_three_1804 : GridLRamseyProperty 3 1804 :=
  gridLRamseyProperty_three_772.mono (by decide)

end MetaMathlibExt
