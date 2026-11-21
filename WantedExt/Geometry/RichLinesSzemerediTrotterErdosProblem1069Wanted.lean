/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bounding `k`-rich lines (Erdős Problem 1069)

Erdős Problem 1069 (Erdős, Croft and Purdy): given any `n` points in `ℝ²`, the number of lines
containing at least `k` of the points is, provided `k ≤ n^{1/2}`, `≪ n² / k³`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MathlibExt.Geometry.RichLinesSzemerediTrotterErdosProblem1069Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1069, https://www.erdosproblems.com/1069 (status
SOLVED). UnsolvedMath record UM-30007152 (`EP-1069`), dataset ulamai/UnsolvedMath v1.8.0.

`k ≥ 2`: for `k ≤ 1` there are infinitely many `k`-rich lines. A line with at least two of the
points is `line[ℝ, p, q]` for two of them, so `k`-rich lines are counted among those; the constant
is absolute.
-/

/-- The lines through two distinct points of `P ⊆ ℝ²` that contain at least `k` points of `P`. -/
def richLines (P : Finset (EuclideanSpace ℝ (Fin 2))) (k : ℕ) :
    Set (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :=
  {L | (∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ L = line[ℝ, p, q]) ∧
    k ≤ ((P : Set (EuclideanSpace ℝ (Fin 2))) ∩ (L : Set (EuclideanSpace ℝ (Fin 2)))).ncard}

/-- Erdős Problem 1069 (Erdős, Croft and Purdy): for `n` points in the plane and `2 ≤ k ≤ n^{1/2}`,
the number of lines containing at least `k` of the points is `O(n² / k³)`. -/
def richLinesBound : Prop :=
  ∃ C : ℝ, ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))) (k : ℕ), 2 ≤ k →
    (k : ℝ) ≤ Real.sqrt P.card → ((richLines P k).ncard : ℝ) ≤ C * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 3

/--
Resolved true: the Szemerédi-Trotter theorem bounds the number of `k`-rich lines by `O(n² / k³ + n /
k)`, which is `O(n² / k³)` for `k ≤ n^{1/2}`; erdosproblems.com/1069 lists the problem as solved by
Szemerédi and Trotter. Source: T. F. Bloom, Erdős Problems, Problem #1069,
https://www.erdosproblems.com/1069 (status SOLVED); resolution: E. Szemerédi and W. T. Trotter,
Extremal problems in discrete geometry, Combinatorica (1983), 381-392, the number of k-rich lines is
≪ n²/k³ + n/k (erdosproblems.com/1069: proved by Szemerédi and Trotter),
https://doi.org/10.1007/BF02579194.
-/
public theorem_wanted richLinesBound_holds : richLinesBound

end MathlibExt.Geometry.RichLinesSzemerediTrotterErdosProblem1069Wanted
