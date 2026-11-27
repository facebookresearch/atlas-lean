/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.LonelyMarriageableSinglesLimits

open Filter MetaMathlibExt

-- Both bounds can be imposed at once, even with different thresholds.
example (m l : ℕ) :
    ∀ᶠ n in atTop, m ≤ marriageableSinglesCount n ∧ l ≤ lonelySinglesCount n :=
  ((tendsto_atTop.mp tendsto_marriageable_lonely_atTop.1) m).and
    ((tendsto_atTop.mp tendsto_marriageable_lonely_atTop.2) l)
