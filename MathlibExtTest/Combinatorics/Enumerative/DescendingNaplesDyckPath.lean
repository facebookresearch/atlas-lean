/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.Combinatorics.Enumerative.DescendingNaplesDyckPath

open MetaMathlibExt

-- Three cars preferring spot 3 correspond to DDUUUD, which reaches height -2.
example : IsNaplesParkingFunction 2 ![3, 3, 3] ∧ ¬ IsNaplesParkingFunction 1 ![3, 3, 3] := by
  decide

example : IsKDyckPath 3 2 ![false, false, true, true, true, false] ∧
    ¬ IsKDyckPath 3 1 ![false, false, true, true, true, false] := by
  decide

-- UDDU returns to zero and stays above -2, but ends with an Up step.
example : ¬ IsKDyckPath 2 2 ![true, false, false, true] := by decide

example : (Finset.univ.filter (IsKDyckPath 3 1)).card = 9 := by
  rw [← descendingNaplesCount_eq_card_kDyckPath (by decide) (by decide)]
  decide
