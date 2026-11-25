/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FloorDivisionCounts

open MetaMathlibExt

-- The endpoint `d = 3` is counted even though `3` does not divide `10`.
example : ((Finset.Icc 1 10).filter (fun d : ℕ => 3 ≤ 10 / d)).card = 3 :=
  floor_div_sequence_card_ge 10 3 (by decide)

-- A threshold above the numerator gives an empty qualifying interval.
example : ((Finset.Icc 1 3).filter (fun d : ℕ => 4 ≤ 3 / d)).card = 0 :=
  floor_div_sequence_card_ge 3 4 (by decide)
