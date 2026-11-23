/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Gaps between critical points of polynomials with equally spaced roots (Erdős Problem 1114)

Erdős Problem 1114: let `f ∈ ℝ[x]` have real roots `a₀ < ⋯ < a_m` forming an arithmetic progression.
The differences between consecutive zeros of `f'`, beginning from the midpoint of `(a₀, a_m)`
towards the endpoints, are monotonically increasing.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MathlibExt.Analysis.ArithmeticRootsCriticalGapsErdosProblem1114Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1114, https://www.erdosproblems.com/1114 (status
PROVED). UnsolvedMath record UM-30007164 (`EP-1114`), dataset ulamai/UnsolvedMath v1.8.0.

The page's degree `n` with roots `a₀, …, a_n` is read as `m + 1` roots `a + i d` (`d > 0`); the
polynomial is taken monic, which does not change the zeros of `f'`. "Monotonically increasing" is
read as non-decreasing (`≤`), the literal reading: the page does not say strictly, and Bálint's
paper was not available to check strictness (numerically the gaps increase strictly). A gap counts
as right of the centre when its midpoint is at or right of `(a₀ + a_m) / 2` (this includes the
central gap when `m` is even), and symmetrically on the left; consecutive zeros are zeros of `f'`
with no zero strictly between them.
-/

/-- The monic polynomial whose roots are the arithmetic progression `a, a + d, …, a + m d`. -/
noncomputable def apPolynomial (a d : ℝ) (m : ℕ) : Polynomial ℝ :=
  ∏ i ∈ Finset.range (m + 1), (Polynomial.X - Polynomial.C (a + i * d))

/-- Erdős Problem 1114: if the roots of `f` form an arithmetic progression `a₀ < ⋯ < a_m`, the gaps
between consecutive zeros of `f'` do not decrease from the midpoint `(a₀ + a_m) / 2` outward: for
consecutive zeros `x < y < z` of `f'`, the gap `[x, y]` is at most `[y, z]` when the midpoint of
`[x, y]` is at or right of the centre, and at least `[y, z]` when the midpoint of `[y, z]` is at or
left of it. -/
def criticalGapsIncreaseOutward : Prop :=
  ∀ (a d : ℝ) (m : ℕ), 0 < d → ∀ x y z : ℝ, x < y → y < z →
    (apPolynomial a d m).derivative.IsRoot x → (apPolynomial a d m).derivative.IsRoot y →
    (apPolynomial a d m).derivative.IsRoot z →
    (∀ w, (apPolynomial a d m).derivative.IsRoot w → w ≤ x ∨ w = y ∨ z ≤ w) →
    (a + m * d / 2 ≤ (x + y) / 2 → y - x ≤ z - y) ∧
      ((y + z) / 2 ≤ a + m * d / 2 → z - y ≤ y - x)

/--
Resolved true: Bálint proved that the gaps between consecutive zeros of `f'` increase monotonically
from the centre outward; erdosproblems.com/1114 lists the problem as proved (Lorch gave
generalizations). Source: T. F. Bloom, Erdős Problems, Problem #1114,
https://www.erdosproblems.com/1114 (status PROVED); resolution: E. Bálint, Proof of a conjecture of
P. Erdős, Mat. Lapok (1960), 33-40, erdosproblems.com/1114: proved by Bálint; generalizations by L.
Lorch, Acta Math. Acad. Sci. Hungar. (1976), 293-300, https://www.erdosproblems.com/1114.
-/
public theorem_wanted criticalGapsIncreaseOutward_holds : criticalGapsIncreaseOutward

end MathlibExt.Analysis.ArithmeticRootsCriticalGapsErdosProblem1114Wanted
