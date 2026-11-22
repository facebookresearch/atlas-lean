/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Instances.Complex

@[expose] public section

namespace MathlibExt.Analysis.Complex.ScottishBook39Wanted

/--
Auerbach, Problem 39 of the Scottish Book. A function `φ` is said to satisfy:
(1) `φ(x) ≥ 0` for all `x`, and `φ` is neither identically `0` nor the
trivial absolute value (`φ 0 = 0` and `φ x = 1` for `x ≠ 0`); (2)
`φ(x + y) ≤ φ(x) + φ(y)`; (3) `φ(x * y) = φ(x) * φ(y)`.
The continuous functions meeting these conditions are exactly
`φ(x) = |x|^α` with constant `α`, `0 < α ≤ 1`. The problem asks whether
discontinuous functions meeting these conditions exist. The answer is yes:
there is a discontinuous field automorphism `f` of the complex numbers, and
`φ(x) = |f(x)|` satisfies (1), (2), (3) and is discontinuous. Condition (1)
is read as in the addendum: the source's "not identically `1`" excludes the
trivial absolute value, which is discontinuous at `0` and meets (2) and (3).
For `φ(x) = |f(x)|` one has `φ(2) = 2`.
Source: H. Auerbach, Problem 39 of the Scottish Book; addendum of S. Mazur,
10 April 1937, in the Scottish Book, via Lebesgue's theorem on the existence
of a discontinuous automorphism of `ℂ` (Kamke); see the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted exists_discontinuous_subadditive_multiplicative :
    ∃ φ : ℂ → ℝ, ¬ Continuous φ ∧ (∀ x, 0 ≤ φ x) ∧
      ¬ (∀ x, φ x = 0) ∧ ¬ (∀ x, x ≠ 0 → φ x = 1) ∧
      (∀ x y, φ (x + y) ≤ φ x + φ y) ∧ (∀ x y, φ (x * y) = φ x * φ y)

end MathlibExt.Analysis.Complex.ScottishBook39Wanted
