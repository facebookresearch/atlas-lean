/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.YangChen

open MetaMathlibExt

-- Both extremal choices partially fill the middle coordinate.
example (a : Fin 3 → ℤ) (ha : StrictMono a) :
    5 ≤ (generalizedHFoldSumset a ![2, 3, 2] 3).card := by
  have lower := (yangChen_card_generalizedHFoldSumset_ge ![2, 3, 2] (by decide) 3
    (by decide) (by decide)).1 a ha
  rw [show yangChenBound ![2, 3, 2] 3 = 5 by decide] at lower
  exact_mod_cast lower

-- A translated interval attains the five-element bound.
example : generalizedHFoldSumset ![(-1 : ℤ), 0, 1] ![2, 3, 2] 3 = Finset.Icc (-2) 2 := by
  decide

-- At full capacity both greedy choices use every copy, including repeated terms.
example : yangChenBound ![2, 1] 3 = 1 ∧
    generalizedHFoldSumset ![(-3 : ℤ), 4] ![2, 1] 3 = {-2} := by
  decide
