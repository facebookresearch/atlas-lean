/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.EuclidGameCalkinWilf

/-!
# Tests for counts of Calkin–Wilf arch tops

The arch-count formula gives one, zero, and two left arch tops in rows two, three, and four.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Corollary 4.7.
-/

namespace MathlibExtTest.GameTheory.EuclidGameCalkinWilfCountArchTopsCalkinWilfRow

open MetaMathlibExt

example : (calkinWilfRow 2).countP (fun p => (calkinWilfRow 0).any fun V =>
    euclidPPosition V.1 V.2 && p == (2 * V.1 + V.2, V.1 + V.2)) = 1 := by
  have h := count_arch_tops_calkinWilfRow 2 (by decide)
  change 3 * (((calkinWilfRow 2).countP fun p => (calkinWilfRow 0).any fun V =>
    euclidPPosition V.1 V.2 && p == (2 * V.1 + V.2, V.1 + V.2)) : ℤ) = 3 at h
  omega

example : (calkinWilfRow 3).countP (fun p => (calkinWilfRow 1).any fun V =>
    euclidPPosition V.1 V.2 && p == (2 * V.1 + V.2, V.1 + V.2)) = 0 := by
  have h := count_arch_tops_calkinWilfRow 3 (by decide)
  change 3 * (((calkinWilfRow 3).countP fun p => (calkinWilfRow 1).any fun V =>
    euclidPPosition V.1 V.2 && p == (2 * V.1 + V.2, V.1 + V.2)) : ℤ) = 0 at h
  omega

example : (calkinWilfRow 4).countP (fun p => (calkinWilfRow 2).any fun V =>
    euclidPPosition V.1 V.2 && p == (2 * V.1 + V.2, V.1 + V.2)) = 2 := by
  have h := count_arch_tops_calkinWilfRow 4 (by decide)
  change 3 * (((calkinWilfRow 4).countP fun p => (calkinWilfRow 2).any fun V =>
    euclidPPosition V.1 V.2 && p == (2 * V.1 + V.2, V.1 + V.2)) : ℤ) = 6 at h
  omega

end MathlibExtTest.GameTheory.EuclidGameCalkinWilfCountArchTopsCalkinWilfRow
