/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Small values of `x² + y² - α z²` (Erdős Problem 496)

Erdős Problem 496 (Oppenheim): for irrational `α` and `ε > 0`, are there positive integers `x, y, z`
with `|x² + y² - z² α| < ε`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

namespace MathlibExt.NumberTheory.IrrationalTernaryFormSmallValueErdosProblem496Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #496, https://www.erdosproblems.com/496 (status
PROVED). UnsolvedMath record UM-30006902 (`EP-496`), dataset ulamai/UnsolvedMath v1.8.0.

`α > 0` is assumed: for `α < 0` the form is positive definite and `x² + y² - z² α ≥ 2` at positive
integers, so the literal question fails there; Oppenheim's conjecture concerns indefinite forms.
Since the form depends only on `x², y², z²`, positive means nonzero. Margulis's theorem, as stated,
gives a nonzero integer vector with `|Q| < ε`. Positive coordinates, as erdosproblems.com/496 asks,
are covered by the remark of S. G. Dani (Pure Appl. Math. Q. 4 (2008), 147-166, after Theorem 4.1,
p. 158): for `n ≥ 3`, a nondegenerate indefinite form not a multiple of a rational form whose null
cone contains a vector with all coordinates positive has a dense set of values at points with
positive integer coordinates; here `(1, 1, √(2/α))` is such a null vector.
-/

/-- Erdős Problem 496 (Oppenheim), for `α > 0`: for every irrational `α > 0` and `ε > 0` there are
positive integers `x, y, z` with `|x ^ 2 + y ^ 2 - z ^ 2 α| < ε`. -/
def ternaryFormSmallPositiveValue : Prop :=
  ∀ α : ℝ, Irrational α → 0 < α → ∀ ε : ℝ, 0 < ε →
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ |(x : ℝ) ^ 2 + (y : ℝ) ^ 2 - (z : ℝ) ^ 2 * α| < ε

/--
Resolved true: erdosproblems.com/496 records the answer yes, proved by Margulis (Oppenheim
conjecture), whose theorem covers the indefinite ternary form `x² + y² - α z²` for `α > 0` (not
proportional to a rational form since `α` is irrational); Dani's remark (module note) gives the
values at positive integers. Source: T. F. Bloom, Erdős Problems, Problem #496,
https://www.erdosproblems.com/496 (status PROVED); resolution: G. A. Margulis, Discrete subgroups
and ergodic theory, in Number theory, trace formulas and discrete groups (Oslo, 1987) (1989),
377-398, erdosproblems.com/496: true, proved by Margulis (Oppenheim conjecture),
https://www.erdosproblems.com/496.
-/
public theorem_wanted ternaryFormSmallPositiveValue_holds : ternaryFormSmallPositiveValue

end MathlibExt.NumberTheory.IrrationalTernaryFormSmallValueErdosProblem496Wanted
