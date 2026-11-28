/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Data.Finset.PowersetCardOverlap

/-! # Tests for counting fixed-size subsets with prescribed overlap -/

open Finset

-- The ambient finset is not a universe, and the marked set and sample have different sizes.
example : (({0, 1, 2, 3} : Finset ℕ).powersetCard 3).filter
    (fun S => (S ∩ {0, 1}).card = 1) = {{0, 2, 3}, {1, 2, 3}} := by decide

example : ((({0, 1, 2, 3} : Finset ℕ).powersetCard 3).filter
    fun S => (S ∩ {0, 1}).card = 1).card = 2 := by
  exact (card_filter_powersetCard_inter_eq_choose (A := {0, 1}) (by decide) (by decide)).trans
    (by decide)
