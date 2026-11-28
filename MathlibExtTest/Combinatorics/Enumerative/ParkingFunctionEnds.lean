/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fintype.Pi
import MathlibExt.Combinatorics.Enumerative.ParkingFunctionEnds

/-! # Regression tests for peakless-tieless parking function endpoint counts -/

namespace MetaMathlibExt

set_option quotPrecheck false in
local notation "ends" m:max r:max =>
  ((Finset.univ.filter (fun f : Fin m → Fin m => IsParkingFunction m f ∧
    (∀ i j, j.val = i.val + 1 → f i ≠ f j) ∧
    (∀ i j k, j.val = i.val + 1 → k.val = j.val + 1 → ¬ (f i < f j ∧ f k < f j)))).filter
    (fun f => ∃ i j : Fin m, i.val = 0 ∧ j.val + 1 = m ∧ r (f i) (f j))).card

-- At length one neither strict comparison is possible.
example : ends 1 (fun a b => b < a) = 0 := by decide

example : ends 1 (fun a b => b < a) = ends 1 (fun a b => a < b) :=
  (peakless_tieless_ends_card 0).2

-- At length two equal endpoints would be a tie; at length three they can occur.
example : ends 2 (fun a b => a = b) = 0 := by decide

example : ends 3 (fun a b => a = b) = 1 := by
  rw [(peakless_tieless_ends_card 2).1 (by decide)]
  decide

-- At length two, reversal pairs the increasing and decreasing parking functions.
example : ends 2 (fun a b => b < a) = 1 := by
  rw [(peakless_tieless_ends_card 1).2]
  decide

end MetaMathlibExt
