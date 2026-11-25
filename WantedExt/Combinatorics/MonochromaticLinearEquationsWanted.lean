/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.MonochromaticLinearEquations.NoCancelingPartition
public import MathlibExt.Combinatorics.MonochromaticLinearEquations.OneTwo

/-!
# Uncommon linear equations over the integers

Remaining statements on monochromatic solutions over the integers.
-/

namespace MetaMathlibExt

/-- **Uncommonness of odd-length equations over the integers.** Let $m \ge 1$ and let
$a_1, \dots, a_{2m+1}$ be nonzero integers, at least one negative and at least one positive.
Then for every $r \ge 3$ the equation $a_1x_1 + \cdots + a_{2m+1}x_{2m+1} = 0$ is
$r$-uncommon over the integers.

The sign condition excludes equations such as $x_1 + x_2 + x_3 = 0$, which have no solutions
in positive integers and for which the proportion of monochromatic solutions is undefined.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Corollary 1 (`integers-2025-A88-cor-1`). -/
public theorem_wanted isUncommonOverIntegers_of_odd (m : ℕ) (hm : 1 ≤ m)
    (a : Fin (2 * m + 1) → ℤ) (ha : ∀ i, a i ≠ 0) (hsign : ∃ i j, a i < 0 ∧ 0 < a j)
    (r : ℕ) (hr : 3 ≤ r) :
    IsUncommonOverIntegers a r

end MetaMathlibExt
