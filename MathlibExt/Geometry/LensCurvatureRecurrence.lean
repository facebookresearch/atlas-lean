/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic

namespace MetaMathlibExt

@[expose] public section

/-!
# Curvature recurrences for circles in a lens

Source: J. Kocik, *Lens Sequences*, Journal of Integer Sequences 23 (2020),
[`kocik5.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL23/Kocik/kocik5.tex),
Theorem `thm:abgeo`.
-/

/-- A sequence satisfies the source's second-order nonhomogeneous recurrence for curvatures
of a chain of circles in a symmetric lens. Here `K` is the product of the two lens circles and
`A` is their common curvature. The denominator condition makes explicit the nondegeneracy
used by the source formula. -/
public def IsLensCurvatureRecurrence (b : ℕ → ℝ) (K A : ℝ) : Prop :=
  1 + K ≠ 0 ∧ ∀ n,
    b (n + 2) = ((6 - 2 * K) / (1 + K)) * b (n + 1) - b n + (-8 * A) / (1 + K)

end

end MetaMathlibExt
