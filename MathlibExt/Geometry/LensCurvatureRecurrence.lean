/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic

namespace MetaMathlibExt

@[expose] public section

/-!
# Curvature recurrences for circles in a lens

Source: J. Kocik, *Lens Sequences*, Journal of Integer Sequences 23 (2020),
[`kocik5.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL23/Kocik/kocik5.tex),
Theorem `thm:abgeo`.
-/

/-- **Lens curvature recurrence.** For real numbers $K$ and $A$, a real sequence
$(b_n)_{n \ge 0}$ satisfies the lens curvature recurrence with parameters $K$ and $A$ when
$1 + K \neq 0$ and, for every $n \ge 0$,
$$b_{n+2} = \frac{6 - 2K}{1 + K}\, b_{n+1} - b_n + \frac{-8A}{1 + K}.$$

This is the second-order nonhomogeneous recurrence of the source for the curvatures of a chain
of circles in a symmetric lens, where $A$ is the common curvature of the two lens circles. -/
public def IsLensCurvatureRecurrence (b : ℕ → ℝ) (K A : ℝ) : Prop :=
  1 + K ≠ 0 ∧ ∀ n,
    b (n + 2) = ((6 - 2 * K) / (1 + K)) * b (n + 1) - b n + (-8 * A) / (1 + K)

end

end MetaMathlibExt
