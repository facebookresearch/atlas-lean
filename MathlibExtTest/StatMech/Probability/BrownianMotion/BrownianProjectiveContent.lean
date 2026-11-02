/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianMotion.BrownianProjectiveContent
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.BrownianMotion.BrownianProjectiveContent`

* `brownianProjectiveContent` of the whole space is `1` and of `∅` is `0`; it is finite on every
  set.
-/

@[expose] public section

open StatMech.SLE MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianProjectiveContent

example : brownianProjectiveContent (Set.univ : Set (ℝ → ℝ)) = 1 := brownianProjectiveContent_univ

example : brownianProjectiveContent (∅ : Set (ℝ → ℝ)) = 0 := brownianProjectiveContent_empty

example (A : Set (ℝ → ℝ)) : brownianProjectiveContent A ≠ ∞ := brownianProjectiveContent_ne_top A

end MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianProjectiveContent
