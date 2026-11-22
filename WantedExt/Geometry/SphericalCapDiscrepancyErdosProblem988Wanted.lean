/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Spherical cap discrepancy tends to infinity (Erdős Problem 988)

Erdős Problem 988: if `P ⊆ S²` is a subset of the unit sphere then define the discrepancy `D(P) =
max_C | |C ∩ P| - α_C |P| |`, where the maximum is taken over all spherical caps `C`, and `α_C` is
the appropriately normalised measure of `C`. Is it true that `min_{|P| = n} D(P) → ∞` as `n → ∞`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

@[expose] public section

namespace MathlibExt.Geometry.SphericalCapDiscrepancyErdosProblem988Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #988, https://www.erdosproblems.com/988 (status
SOLVED). UnsolvedMath record UM-30007111 (`EP-988`), dataset ulamai/UnsolvedMath v1.8.0.

`S²` is the unit sphere of `EuclideanSpace ℝ (Fin 3)`. A spherical cap is a set `{x : ⟪x, v⟫ ≥ t}`
with pole `v ∈ S²` and `t ∈ ℝ` (closed caps; `t` outside `[-1, 1]` gives the empty set or the
sphere, of discrepancy `0`). `α_C` is the measure of `C` under Mathlib's `volume.toSphere` divided
by its total mass, the normalized surface measure. `min_{|P| = n} D(P) → ∞` is stated as: for every
`M` and all large `n`, every `n`-point `P` has a cap with discrepancy greater than `M`.
formal-conjectures has no statement of this problem.
-/

open MeasureTheory

/-- The unit sphere `S²` of `ℝ³`. -/
abbrev UnitSphere : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The (closed) spherical cap of `S²` with pole `v ∈ S²` and height parameter `t`: the points `x`
of the sphere with `⟪x, v⟫ ≥ t`. -/
def sphericalCap (v : UnitSphere) (t : ℝ) : Set UnitSphere :=
  {x | t ≤ inner ℝ (x : EuclideanSpace ℝ (Fin 3)) (v : EuclideanSpace ℝ (Fin 3))}

/-- The normalized surface measure of a set of `S²` (the whole sphere has measure `1`): Mathlib's
measure `volume.toSphere` on the unit sphere, divided by its total mass. -/
noncomputable def normalizedArea (s : Set UnitSphere) : ℝ :=
  ((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere s /
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere Set.univ).toReal

/-- Erdős Problem 988: `min_{|P| = n} D(P) → ∞`, where `D(P)` is the largest value of
`| |C ∩ P| - α_C |P| |` over spherical caps `C` (`α_C` the normalized area of `C`): for every
`M` and all large `n`, every `n`-point set `P ⊆ S²` has a cap `C` with `| |C ∩ P| - α_C n | > M`. -/
def capDiscrepancyTendsToInfinity : Prop :=
  ∀ M : ℝ, ∀ᶠ n : ℕ in Filter.atTop, ∀ P : Finset UnitSphere, P.card = n →
    ∃ v t, M < |(((P : Set UnitSphere) ∩ sphericalCap v t).ncard : ℝ) -
      normalizedArea (sphericalCap v t) * n|

/--
Resolved true: Schmidt proved that the spherical cap discrepancy of `n` points on the sphere tends
to infinity with `n`, in every dimension; erdosproblems.com/988 lists the problem as solved in the
affirmative. Source: T. F. Bloom, Erdős Problems, Problem #988, https://www.erdosproblems.com/988
(status SOLVED); resolution: W. M. Schmidt, Irregularities of distribution. IV, Invent. Math.
(1969), 55-82, erdosproblems.com/988: 'This is true, and was proved (in any number of dimensions) by
Schmidt' (Roth had the analogue for the square), https://www.erdosproblems.com/988.
-/
public theorem_wanted capDiscrepancyTendsToInfinity_holds : capDiscrepancyTendsToInfinity

end MathlibExt.Geometry.SphericalCapDiscrepancyErdosProblem988Wanted
