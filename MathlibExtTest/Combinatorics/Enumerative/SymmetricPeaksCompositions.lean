/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SymmetricPeaksCompositions

/-! # Tests for symmetric peaks and valleys in compositions -/

open MetaMathlibExt

-- Two overlapping valleys of depth three share an outer part and enclose a peak.
example : symmetricValleyDepthSum [4, 1, 4, 1, 4] = 6 ∧
    symmetricValleyCount [4, 1, 4, 1, 4] = 2 ∧ symmetricPeakCount [4, 1, 4, 1, 4] = 1 ∧
    symmetricPeakHeightSum [4, 1, 4, 1, 4] = 3 := by decide

-- Unequal outer parts give no symmetric valley, even with a strict middle minimum.
example : symmetricValleyDepthSum [3, 1, 2] = 0 := by decide

-- The index interval is empty for zero.
example : ∑ c ∈ Finset.univ.filter (fun c : Composition 0 => c.length = 3),
    symmetricValleyDepthSum c.blocks = 0 := by
  rw [symmetricValleyDepthSum_compositions_length_three]
  decide

-- At six, the interval contains one middle part, but parity excludes it.
example : ∑ c ∈ Finset.univ.filter (fun c : Composition 6 => c.length = 3),
    symmetricValleyDepthSum c.blocks = 0 := by
  rw [symmetricValleyDepthSum_compositions_length_three]
  decide

-- At eleven, [5, 1, 5] and [4, 3, 4] contribute four and one.
example : ∑ c ∈ Finset.univ.filter (fun c : Composition 11 => c.length = 3),
    symmetricValleyDepthSum c.blocks = 5 := by
  rw [symmetricValleyDepthSum_compositions_length_three]
  decide
