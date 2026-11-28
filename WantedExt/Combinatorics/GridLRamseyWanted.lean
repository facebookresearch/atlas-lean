/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.GridLRamseyThree772
public import MathlibExt.Combinatorics.GridLRamseyThree1573
public import MathlibExt.Combinatorics.GridLRamseyThree1804
public import MathlibExt.Combinatorics.GridLRamseyThree2593

namespace MetaMathlibExt

@[expose] public section

/-- **Three-coloring the 493 × 493 grid forces a monochromatic L.** Write
$[n] = \{1, \dots, n\}$. Every coloring of the grid $[493] \times [493]$ with $3$ colors contains
a monochromatic L: positive integers $x$, $y$, $d$ with $x + d \le 493$ and $y + d \le 493$ such
that the points $(x, y)$, $(x + d, y)$ and $(x + d, y + d)$ have the same color. Equivalently,
the grid Ramsey number $R_3(L)$, the least $n$ for which every coloring of $[n] \times [n]$ with
$3$ colors contains a monochromatic L, is at most $493$.

This is the paper's main bound. Since a larger grid contains every L of a smaller one, it implies
the bounds $772$, $1573$, $1804$ and $2593$.

Source: Isaac Mammel, William Smith, and Carl Yerger, *Ramsey Theory on the Integer
Grid: The "L" Problem*, INTEGERS 25 (2025), Article A21, Theorem 6. -/
public theorem_wanted gridLRamseyProperty_three_493 : GridLRamseyProperty 3 493

end

end MetaMathlibExt
