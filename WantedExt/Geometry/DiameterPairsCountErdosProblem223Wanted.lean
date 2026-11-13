/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Pairs at the diameter distance (Erdős Problem 223)

Erdős Problem 223 (Vázsonyi's problem): for `d ≥ 2` and `n ≥ 2` let `f_d(n)` be the largest number
of pairs at distance `1` among `n` points of `ℝ^d` of diameter `1`. Estimate `f_d(n)`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MathlibExt.Geometry.DiameterPairsCountErdosProblem223Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #223, https://www.erdosproblems.com/223 (status
SOLVED). UnsolvedMath record UM-30006775 (`EP-223`), dataset ulamai/UnsolvedMath v1.8.0.

Counts are of ordered pairs of distinct points at distance `1`, twice the number of pairs, so the
statements read `2 n`, `2 (2n - 2)` and `2 ((p - 1) / (2p) ± ε) n²`. The answer has three targets:
`f₂(n) = n` for `n ≥ 3` and `f₃(n) = 2n - 2` for `n ≥ 4` (each a maximum, so an upper bound attained
by some set), the ranges in which Swanepoel (§1.2) states these values (`f₂(2) = 1` and `f₃(3) = 3`
fall outside the formulas), and `f_d(n) = ((p - 1) / (2p) + o(1)) n²` for `d ≥ 4` with `p = ⌊d /
2⌋`. Swanepoel's exact values for `d ≥ 4` and large `n` are not formalized.
-/

open Filter

open Classical in
/-- The number of ordered pairs of distinct points of `A` at distance `1` (twice the number of
unordered pairs). -/
noncomputable def unitPairCount {d : ℕ} (A : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  (A.offDiag.filter (fun p => dist p.1 p.2 = 1)).card

/-- Erdős Problem 223, `d = 2` (Hopf and Pannwitz): for `n ≥ 3`, the maximum number of pairs at
distance `1` among `n` points of `ℝ²` of diameter `1` is `n`. -/
def planarDiameterPairsMax : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (∀ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = n →
      Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) = 1 → unitPairCount A ≤ 2 * n) ∧
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = n ∧
      Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) = 1 ∧ unitPairCount A = 2 * n

/-- Erdős Problem 223, `d = 3` (Grünbaum, Heppes, Straszewicz): for `n ≥ 4`, the maximum number of
pairs at distance `1` among `n` points of `ℝ³` of diameter `1` is `2n - 2`. -/
def spatialDiameterPairsMax : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    (∀ A : Finset (EuclideanSpace ℝ (Fin 3)), A.card = n →
      Metric.diam (A : Set (EuclideanSpace ℝ (Fin 3))) = 1 → unitPairCount A ≤ 2 * (2 * n - 2)) ∧
    ∃ A : Finset (EuclideanSpace ℝ (Fin 3)), A.card = n ∧
      Metric.diam (A : Set (EuclideanSpace ℝ (Fin 3))) = 1 ∧ unitPairCount A = 2 * (2 * n - 2)

/-- Erdős Problem 223, `d ≥ 4` (Erdős): with `p = ⌊d / 2⌋`, the maximum number of pairs at distance
`1` among `n` points of `ℝ^d` of diameter `1` is `((p - 1) / (2p) + o(1)) n²`. -/
def highDimDiameterPairsAsymptotic : Prop :=
  ∀ d : ℕ, 4 ≤ d → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (∀ A : Finset (EuclideanSpace ℝ (Fin d)), A.card = n →
      Metric.diam (A : Set (EuclideanSpace ℝ (Fin d))) = 1 →
      (unitPairCount A : ℝ) ≤ 2 * (((d / 2 : ℕ) - 1 : ℝ) / (2 * (d / 2 : ℕ)) + ε) * n ^ 2) ∧
    ∃ A : Finset (EuclideanSpace ℝ (Fin d)), A.card = n ∧
      Metric.diam (A : Set (EuclideanSpace ℝ (Fin d))) = 1 ∧
      2 * (((d / 2 : ℕ) - 1 : ℝ) / (2 * (d / 2 : ℕ)) - ε) * n ^ 2 ≤ unitPairCount A

/--
Resolved true: Hopf and Pannwitz proved that `n` points of diameter `1` in the plane have at most
`n` pairs at distance `1`, and the maximum is `n` for every `n ≥ 3` (Swanepoel, §1.2). Source: T. F.
Bloom, Erdős Problems, Problem #223, https://www.erdosproblems.com/223 (status SOLVED); resolution:
H. Hopf and E. Pannwitz (1934) (d = 2); B. Grünbaum (1956), A. Heppes (1956) and S. Straszewicz
(1957) (d = 3); P. Erdős, On sets of distances of n points in Euclidean space, Magyar Tud. Akad.
Mat. Kutató Int. Közl. 5 (1960), 165-169 (d ≥ 4); K. J. Swanepoel, Unit distances and diameters in
Euclidean spaces, Discrete Comput. Geom. 41 (2009), 1-27, Swanepoel §1.2: M_2(n) = n for n ≥ 3,
M_3(n) = 2n - 2 for n ≥ 4 (Grünbaum, Heppes, Straszewicz), M_d(n) = ((p - 1)/(2p)) n² + o(n²) for d
≥ 4 (Erdős), with M_d(n) the largest number of diameters of n points in ℝ^d; erdosproblems.com/223:
f_2(n) = n (Hopf-Pannwitz), f_3(n) = 2n - 2, f_d(n) = ((p - 1)/(2p) + o(1)) n² for d ≥ 4, exact for
large n (Swanepoel), https://doi.org/10.1007/s00454-008-9082-x.
-/
public theorem_wanted planarDiameterPairsMax_holds : planarDiameterPairsMax

/--
Resolved true: Grünbaum, Heppes and Straszewicz independently proved Vázsonyi's conjecture that the
maximum for `n ≥ 4` points of diameter `1` in `ℝ³` is `2n - 2` (Swanepoel, §1.2). Source: T. F.
Bloom, Erdős Problems, Problem #223, https://www.erdosproblems.com/223 (status SOLVED); resolution:
H. Hopf and E. Pannwitz (1934) (d = 2); B. Grünbaum (1956), A. Heppes (1956) and S. Straszewicz
(1957) (d = 3); P. Erdős, On sets of distances of n points in Euclidean space, Magyar Tud. Akad.
Mat. Kutató Int. Közl. 5 (1960), 165-169 (d ≥ 4); K. J. Swanepoel, Unit distances and diameters in
Euclidean spaces, Discrete Comput. Geom. 41 (2009), 1-27, Swanepoel §1.2: M_2(n) = n for n ≥ 3,
M_3(n) = 2n - 2 for n ≥ 4 (Grünbaum, Heppes, Straszewicz), M_d(n) = ((p - 1)/(2p)) n² + o(n²) for d
≥ 4 (Erdős), with M_d(n) the largest number of diameters of n points in ℝ^d; erdosproblems.com/223:
f_2(n) = n (Hopf-Pannwitz), f_3(n) = 2n - 2, f_d(n) = ((p - 1)/(2p) + o(1)) n² for d ≥ 4, exact for
large n (Swanepoel), https://doi.org/10.1007/s00454-008-9082-x.
-/
public theorem_wanted spatialDiameterPairsMax_holds : spatialDiameterPairsMax

/--
Resolved true: Erdős proved that for `d ≥ 4` the maximum is `((p - 1) / (2p) + o(1)) n²` with `p =
⌊d / 2⌋` (Swanepoel, §1.2), and Swanepoel determined it exactly for large `n`. Source: T. F. Bloom,
Erdős Problems, Problem #223, https://www.erdosproblems.com/223 (status SOLVED); resolution: H. Hopf
and E. Pannwitz (1934) (d = 2); B. Grünbaum (1956), A. Heppes (1956) and S. Straszewicz (1957) (d =
3); P. Erdős, On sets of distances of n points in Euclidean space, Magyar Tud. Akad. Mat. Kutató
Int. Közl. 5 (1960), 165-169 (d ≥ 4); K. J. Swanepoel, Unit distances and diameters in Euclidean
spaces, Discrete Comput. Geom. 41 (2009), 1-27, Swanepoel §1.2: M_2(n) = n for n ≥ 3, M_3(n) = 2n -
2 for n ≥ 4 (Grünbaum, Heppes, Straszewicz), M_d(n) = ((p - 1)/(2p)) n² + o(n²) for d ≥ 4 (Erdős),
with M_d(n) the largest number of diameters of n points in ℝ^d; erdosproblems.com/223: f_2(n) = n
(Hopf-Pannwitz), f_3(n) = 2n - 2, f_d(n) = ((p - 1)/(2p) + o(1)) n² for d ≥ 4, exact for large n
(Swanepoel), https://doi.org/10.1007/s00454-008-9082-x.
-/
public theorem_wanted highDimDiameterPairsAsymptotic_holds : highDimDiameterPairsAsymptotic

end MathlibExt.Geometry.DiameterPairsCountErdosProblem223Wanted
