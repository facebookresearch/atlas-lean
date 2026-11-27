/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Roots

/-!
# Eventual hyperbolicity of Jensen polynomials for colored partitions

Work in progress. This module will prove
`MetaMathlibExt.eventually_jensen_hyperbolic_coloredPartitions` (Bal, Haraldson, Males and
Thompson, *Jensen Polynomials Associated with Wright's Circle Method: Hyperbolicity and Turán
Inequalities*, INTEGERS 25 (2025), Article A36, Theorem 3, part 1) and move it here from
`WantedExt.Combinatorics.Enumerative.JensenPolynomialsWrightCircleWanted`.

Plan of the proof:

* the number `C_r(n)` of `r`-colored partitions of `n` satisfies
  `C_r(n) = c'_r · I((r+1)/2, κ_r √(n − r/24)) · (1 + ρ(n))` with `‖ρ(n)‖ ≤ e^{−c√n}`, where
  `I(a, z) = ∫_{−1}^{1} (1 − t²)^a e^{z t} dt`, by the circle method on `|q| = e^{−y}`
  (the modular transformation of the partition generating function, a minor-arc bound and the
  major-arc integral);
* `x ↦ log I((r+1)/2, κ_r √(x − r/24))` is a smooth, strictly concave model of growth `√x`
  with derivative bounds `|Λ^{(k)}(x)| ≤ C x^{1/2−k}`;
* such a model gives the log-ratio expansion of Griffin, Ono, Rolen and Zagier through
  forward differences, and `MetaMathlibExt.eventually_jensen_hyperbolic_of_log_ratio_expansion`
  concludes.
-/
