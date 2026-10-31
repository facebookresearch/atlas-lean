/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The Lindelöf hypothesis

The Lindelöf hypothesis is an open conjecture: `ζ(1/2 + i t) = O(|t| ^ δ)` for every `δ > 0`. We
state it in the equivalent form that is uniform on the closed half-plane `re s ≥ 1 / 2` (the two
forms are equivalent by the Phragmén–Lindelöf principle). Results proved under this hypothesis
take `LindelofHypothesis` as an explicit argument, so they are visibly conditional.

## Main definitions

* `LindelofHypothesis`: the statement of the Lindelöf hypothesis.
-/

@[expose] public section

/-- The **Lindelöf hypothesis** (an open conjecture): for every `δ > 0` there is `A > 0` with
`‖ζ s‖ ≤ A * |im s| ^ δ` whenever `re s ≥ 1 / 2` and `|im s| ≥ 1`. -/
def LindelofHypothesis : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 0 < A ∧ ∀ s : ℂ,
    1 / 2 ≤ s.re → 1 ≤ |s.im| → ‖riemannZeta s‖ ≤ A * |s.im| ^ δ
