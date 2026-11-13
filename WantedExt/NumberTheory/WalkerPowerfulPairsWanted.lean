/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Walker's theorem on consecutive powerful pairs — wishlist
This file records Walker's theorem as a `theorem_wanted` declaration.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Set.Finite.Basic
public import MathlibExt.NumberTheory.KFull

@[expose] public section

namespace MathlibExt.NumberTheory.WalkerPowerfulPairsWanted

/--
Walker's theorem: there are infinitely many pairs of consecutive powerful
numbers, neither of which is a perfect square.

Source: David T. Walker, Consecutive integer pairs of powerful numbers and
related Diophantine equations, Fibonacci Quart. 14 (1976), 111–116. Walker
classifies all such pairs (his TYPE II) via solutions of a Diophantine
equation; the Pell-equation families give infinitely many. This answers the
first question of Erdős Problem 365 in the negative: it is not the case that
one of two consecutive powerful numbers must be a square.
-/
public theorem_wanted infinite_consecutive_powerful_pairs_neither_square :
    Set.Infinite {n : ℕ | Nat.IsKFull 2 n ∧ Nat.IsKFull 2 (n + 1) ∧
      ¬ IsSquare n ∧ ¬ IsSquare (n + 1)}

end MathlibExt.NumberTheory.WalkerPowerfulPairsWanted
