/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Combinatorics.Enumerative.KBoxPaths

/-! Tests for the sharp semilength bound and its factor-count convention. -/

open MetaMathlibExt SkewDyckStep

-- The first nontrivial separator: two boxes reach the lower bound of five up steps.
example : let w := [U, U, U, D, L, D, U, U, D, L]
    IsSkewDyckWord w ∧ skewFactorCount (boxFactor 1) w = 2 ∧ w.count U = 5 := by
  decide

-- Removing the separator and one up step preserves balance and both boxes, but creates LU.
example : let w := [U, U, D, L, U, U, D, L]
    w.count U = w.count D + w.count L ∧ skewFactorCount (boxFactor 1) w = 2 ∧
      ¬ IsSkewDyckWord w := by
  decide

-- Factor counts include overlapping occurrences and the empty suffix.
example : skewFactorCount [U, U] [U, U, U] = 2 ∧ skewFactorCount [] [U, U, U] = 4 := by
  decide

example (w : List SkewDyckStep) (hw : IsSkewDyckWord w) (hc : skewFactorCount (boxFactor 2) w = 3) :
    11 ≤ w.count U :=
  (min_semilength_boxFactor (k := 2) (n := 3) (by decide) (by decide)).2 w hw hc
