/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Chemistry.ProcessBalances.MixerSplitter
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum

open Domains.Chemistry.ProcessBalances.MixerSplitter

-- A zero-flow inlet is excluded. A half-flow splitter outlet preserves a nontrivial fraction.
example : ((1 : ℝ) / 4 = 1 / 4) ∧ ((1 / 2 : ℝ) / 2 = 1 / 4) := by
  let feed (s : Bool) : ℝ := if s then 1 else 3
  let inlet (i s : Bool) : ℝ := if i then feed s else 0
  let share (_ : Bool) : ℝ := 1 / 2
  have h := mixer_splitter_balances inlet feed share
    (by intro i s; cases i <;> cases s <;> norm_num [inlet, feed])
    (by intro s; cases s <;> norm_num [feed])
    (by intro k; norm_num [share]) (by norm_num [share, Fintype.sum_bool])
  have hm := h.2.1 (by norm_num [inlet, feed, Fintype.sum_bool])
  have hs := h.2.2.2 true (by norm_num [share, feed, Fintype.sum_bool])
  constructor
  · convert hm.2.2 true using 1 <;> norm_num [inlet, feed, Finset.sum_filter, Fintype.sum_bool]
  · convert hs.2 true using 1 <;> norm_num [share, feed, Fintype.sum_bool]
