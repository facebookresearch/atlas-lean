/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Blumenthal's minimax angle problem (Erdős Problem 504)

Erdős Problem 504 (Blumenthal): let `α_N` be the supremum of the `α ∈ [0, π]` such that every set of
`N` points in the plane has three distinct points `x, y, z` with `∠xyz ≥ α`. Determine `α_N`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

@[expose] public section

namespace MathlibExt.Combinatorics.BlumenthalMinimaxAngleErdosProblem504Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #504, https://www.erdosproblems.com/504 (status
SOLVED). UnsolvedMath record UM-30006907 (`EP-504`), dataset ulamai/UnsolvedMath v1.8.0.

The angle is taken at the middle point `y`. The values follow Sendov's paper as reviewed in zbMATH
(Zbl 0853.52009). erdosproblems.com/504 prints the lower branch as `π(1 - 1/(2n - 1))`, a misprint
for `π(1 - 2/(2n - 1))` (the printed value would exceed `α_{2^n}`, but `α_N` is nondecreasing in
`N`). Compared with the formal-conjectures statement `ErdosProblems/504.lean` (it states the same
values with n shifted by one; no code imported).
-/

/-- **Minimax angle.** For a natural number $N$, the minimax angle $\alpha_N$ is the supremum of
the $\alpha \in [0, \pi]$ such that every set of $N$ points in the Euclidean plane contains three
distinct points $x, y, z$ with $\angle xyz \ge \alpha$, where $\angle xyz$ is the unoriented angle
at $y$.

For $N \le 2$ no set of $N$ points has three distinct points, so the set of such $\alpha$ is empty
and $\alpha_N$ is $0$ by the convention for the supremum of the empty set. -/
noncomputable def minimaxAngle (N : ℕ) : ℝ :=
  sSup {α : ℝ | 0 ≤ α ∧ α ≤ Real.pi ∧ ∀ S : Finset (EuclideanSpace ℝ (Fin 2)), S.card = N →
    ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ α ≤ EuclideanGeometry.angle x y z}

/-- **Blumenthal's minimax angle values (Erdős Problem 504).** For a natural number $N$, let
$\alpha_N$ be the minimax angle of $N$ points in the plane: the supremum of the
$\alpha \in [0, \pi]$ such that every set of $N$ points in the plane contains three distinct
points $x, y, z$ with $\angle xyz \ge \alpha$ (the angle at $y$). The statement is Sendov's
answer: $\alpha_3 = \pi/3$, $\alpha_4 = \pi/2$, and for all natural numbers $n \ge 2$ and $N$,
if $2^n < N \le 2^n + 2^{n-2}$, then $\alpha_N = \left(1 - \frac{2}{2n + 1}\right)\pi$, and if
$2^n + 2^{n-2} < N \le 2^{n+1}$, then $\alpha_N = \left(1 - \frac{1}{n + 1}\right)\pi$. -/
def minimaxAngleValues : Prop :=
  minimaxAngle 3 = Real.pi / 3 ∧ minimaxAngle 4 = Real.pi / 2 ∧
    ∀ n N : ℕ, 2 ≤ n →
      (2 ^ n < N → N ≤ 2 ^ n + 2 ^ (n - 2) →
        minimaxAngle N = (1 - 2 / (2 * n + 1 : ℝ)) * Real.pi) ∧
      (2 ^ n + 2 ^ (n - 2) < N → N ≤ 2 ^ (n + 1) →
        minimaxAngle N = (1 - 1 / (n + 1 : ℝ)) * Real.pi)

/--
**Sendov's solution of Blumenthal's minimax angle problem (Erdős Problem 504).** For a natural
number $N$, let $\alpha_N$ be the minimax angle of $N$ points in the plane: the supremum of the
$\alpha \in [0, \pi]$ such that every set of $N$ points in the plane contains three distinct points
$x, y, z$ with $\angle xyz \ge \alpha$ (the angle at $y$). Then $\alpha_3 = \pi/3$,
$\alpha_4 = \pi/2$, and for all natural numbers $n \ge 2$ and $N$: if $2^n < N \le 2^n + 2^{n-2}$,
then $\alpha_N = \left(1 - \frac{2}{2n + 1}\right)\pi$, and if $2^n + 2^{n-2} < N \le 2^{n+1}$,
then $\alpha_N = \left(1 - \frac{1}{n + 1}\right)\pi$.

Source: T. F. Bloom, Erdős Problems, Problem #504,
https://www.erdosproblems.com/504 (status SOLVED); resolution: Bl. Sendov, Minimax of the angles in
a plane configuration of points, Acta Math. Hungar. 69 (1995), 27-46, main theorem, as stated in Zbl
0853.52009: α(N) = (1 - 2/(2n+1))π for 2^n < N ≤ 2^n + 2^{n-2} and (1 - 1/(n+1))π for 2^n + 2^{n-2}
< N ≤ 2^{n+1}, n ≥ 2; α(3) = π/3, α(4) = π/2, https://doi.org/10.1007/BF01874605.
-/
public theorem_wanted minimaxAngleValues_holds : minimaxAngleValues

end MathlibExt.Combinatorics.BlumenthalMinimaxAngleErdosProblem504Wanted
