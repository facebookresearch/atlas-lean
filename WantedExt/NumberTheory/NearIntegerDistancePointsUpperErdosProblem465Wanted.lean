/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Points with distances far from integers, upper bounds (Erdős Problem 465)

Erdős Problem 465: let `N(X, δ)` be the largest number of points in a disc of radius `X` whose
pairwise distances are all at distance `≥ δ` from the nearest integer. Is `N(X, δ) = o(X)` for `0 <
δ < 1/2`? Is `N(X, δ) < X ^ (1/2 + o(1))` for fixed `δ > 0`?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.NumberTheory.NearIntegerDistancePointsShared

@[expose] public section

namespace MathlibExt.NumberTheory.NearIntegerDistancePointsUpperErdosProblem465Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #465, https://www.erdosproblems.com/465 (status
PROVED). UnsolvedMath record UM-30006884 (`EP-465`), dataset ulamai/UnsolvedMath v1.8.0.

`‖x‖ = |x - round x|`. `N(X, δ)` is not defined as a supremum: both bounds are stated for every
admissible finite configuration in some closed disc of radius `X`. `o(X)` and `X ^ (1/2 + o(1))` are
unfolded as "for every `ε > 0`, for all large `X`". The two questions are separate targets.
-/

open MathlibExt.NumberTheory.NearIntegerDistancePointsShared

/-- Erdős Problem 465, first question: for every `0 < δ < 1/2`, `N(X, δ) = o(X)`. For every
`ε > 0` and all large `X`, every admissible configuration in a disc of radius `X` has at most
`ε X` points. -/
def nearIntegerDistancePointsLittleO : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    ∀ P : Finset (EuclideanSpace ℝ (Fin 2)), IsNearIntegerAvoiding X δ P →
      (P.card : ℝ) ≤ ε * X

/-- Erdős Problem 465, second question: for every fixed `δ > 0`, `N(X, δ) < X ^ (1/2 + o(1))`.
For every `ε > 0` and all large `X`, every admissible configuration in a disc of radius `X` has
fewer than `X ^ (1/2 + ε)` points. -/
def nearIntegerDistancePointsSqrtBound : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    ∀ P : Finset (EuclideanSpace ℝ (Fin 2)), IsNearIntegerAvoiding X δ P →
      (P.card : ℝ) < X ^ (1 / 2 + ε)

/--
Resolved true: Sárközy proved `N(X, δ) ≪ δ ^ (-3) X / log log X` for `0 < δ < 1/2`, which is `o(X)`.
Source: T. F. Bloom, Erdős Problems, Problem #465, https://www.erdosproblems.com/465 (status
PROVED); resolution: A. Sárközy, On distances near integers. I, II, Studia Sci. Math. Hungar.
(1976), 37-50, 105-111; S. V. Konyagin, On the distances between points on the plane, Mat. Zametki
(2001), 630-633, erdosproblems.com/465: Sárközy proved N(X, δ) ≪ δ^{-3} X / log log X; Konyagin
proved N(X, δ) ≪_δ X^{1/2}, https://www.erdosproblems.com/465.
-/
public theorem_wanted nearIntegerDistancePointsLittleO_holds : nearIntegerDistancePointsLittleO

/--
Resolved true: Konyagin proved `N(X, δ) ≪_δ X ^ (1/2)`, so `N(X, δ) < X ^ (1/2 + ε)` for every `ε >
0` and all large `X`. Source: T. F. Bloom, Erdős Problems, Problem #465,
https://www.erdosproblems.com/465 (status PROVED); resolution: A. Sárközy, On distances near
integers. I, II, Studia Sci. Math. Hungar. (1976), 37-50, 105-111; S. V. Konyagin, On the distances
between points on the plane, Mat. Zametki (2001), 630-633, erdosproblems.com/465: Sárközy proved
N(X, δ) ≪ δ^{-3} X / log log X; Konyagin proved N(X, δ) ≪_δ X^{1/2},
https://www.erdosproblems.com/465.
-/
public theorem_wanted nearIntegerDistancePointsSqrtBound_holds : nearIntegerDistancePointsSqrtBound

end MathlibExt.NumberTheory.NearIntegerDistancePointsUpperErdosProblem465Wanted
