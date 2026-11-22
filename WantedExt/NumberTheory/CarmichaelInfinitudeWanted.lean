/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Infinitely many Carmichael numbers — wishlist
This file records the Alford–Granville–Pomerance theorem as a `theorem_wanted` declaration.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Finite.Basic
public import MathlibExt.NumberTheory.CarmichaelNumber

@[expose] public section

namespace MathlibExt.NumberTheory.CarmichaelInfinitudeWanted

/--
Alford–Granville–Pomerance theorem: there are infinitely many Carmichael
numbers.

Source: W. R. Alford, A. Granville, and C. Pomerance, There are infinitely
many Carmichael numbers, Ann. of Math. 139 (1994), 703–722.
-/
public theorem_wanted infinite_carmichael_numbers :
    Set.Infinite {n : ℕ | Nat.IsCarmichaelNumber n}

end MathlibExt.NumberTheory.CarmichaelInfinitudeWanted
