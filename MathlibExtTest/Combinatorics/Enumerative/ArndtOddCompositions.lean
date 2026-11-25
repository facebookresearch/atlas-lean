/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ArndtOddCompositions

/-! # Tests for the equality of the Arndt and odd-part counts -/

open MetaMathlibExt

-- Both families contain the empty composition at weight zero.
example : kArndtTotalCount 0 0 = 1 :=
  (kArndtTotalCount_zero_eq_odd_compositions 0).trans (by decide)

-- The odd-part compositions of four are (1, 3), (3, 1), and (1, 1, 1, 1).
example : kArndtTotalCount 0 4 = 3 :=
  (kArndtTotalCount_zero_eq_odd_compositions 4).trans (by decide)
