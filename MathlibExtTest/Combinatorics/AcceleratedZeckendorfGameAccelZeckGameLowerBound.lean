/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.AcceleratedZeckendorfGameAccelZeckGameLowerBound

/-!
# Tests for the lower bound on Accelerated Zeckendorf Game length

Apply the lower bound to complete games on `8`.

Statements from D. Garcia-Fernandezsesma, S. J. Miller, T. Rascon, R. Vandegrift and
A. Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1.
-/

namespace MathlibExtTest.Combinatorics.AcceleratedZeckendorfGameAccelZeckGameLowerBound

example (L : ℕ) (g : ℕ → ℕ →₀ ℕ) (hg : MetaMathlibExt.IsAccelZeckGame 8 L g) :
    4 ≤ L := by
  simpa only [show Nat.greatestFib 8 = 6 by decide] using
    MetaMathlibExt.accelZeckGame_lower_bound 8 (by decide) L g hg

end MathlibExtTest.Combinatorics.AcceleratedZeckendorfGameAccelZeckGameLowerBound
