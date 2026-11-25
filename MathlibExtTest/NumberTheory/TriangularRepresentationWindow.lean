/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TriangularRepresentationWindow

/-!
# Tests for the window congruence for triangular representation counts
-/

open MetaMathlibExt

-- The smallest odd prime, with both bounds attained.
example : (3 : ℤ) ∣ ∑ i ∈ Finset.range 3, sumOfTriangularRepCount (3 - i) 1 := by
  exact sum_sumOfTriangularRepCount_window (n := 1) (p := 3) (s := 3)
    (hn := by decide) (hp := by decide) (hp2 := by decide) (hpn := by decide) (hs := by decide)

-- The maximal allowed degree for p = 5, with the window shifted past p.
example : (5 : ℤ) ∣ ∑ i ∈ Finset.range 5, sumOfTriangularRepCount (7 - i) 3 := by
  exact sum_sumOfTriangularRepCount_window (n := 3) (p := 5) (s := 7)
    (hn := by decide) (hp := by decide) (hp2 := by decide) (hpn := by decide) (hs := by decide)
