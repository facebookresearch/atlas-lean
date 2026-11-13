/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cap discrepancy of points maximising the product of distances (Erdős Problem 991)

Erdős Problem 991: suppose `A = {w_1, …, w_n} ⊂ S²` maximises `∏_{i<j} |w_i - w_j|` over all
possible sets of size `n`. Is it true that `max_C | |A ∩ C| - α_C n | = o(n)`, where the maximum is
taken over all spherical caps `C` and `α_C` is the area of `C` (normalised so that the entire sphere
has area `1`)?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Geometry.SphericalCapDiscrepancyErdosProblem988Wanted

@[expose] public section

namespace MathlibExt.Geometry.FeketePointsCapDiscrepancyErdosProblem991Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #991, https://www.erdosproblems.com/991 (status
PROVED). UnsolvedMath record UM-30007113 (`EP-991`), dataset ulamai/UnsolvedMath v1.8.0.

Spherical caps and normalized area are those of Problem 988 (`sphericalCap`, `normalizedArea`,
imported from that module). The product is taken over ordered pairs of distinct points, the square
of `∏_{i<j} |w_i - w_j|`, which has the same maximisers. `o(n)` is quantified as: for every `ε > 0`
and all large `n`, every maximiser `A` with `|A| = n` has discrepancy at most `ε n` for every cap.
formal-conjectures has no statement of this problem.
-/

open MathlibExt.Geometry.SphericalCapDiscrepancyErdosProblem988Wanted

/-- The product `∏ |w_i - w_j|` over ordered pairs of distinct points of `A`, the square of
`∏_{i<j} |w_i - w_j|` (so it has the same maximisers). -/
noncomputable def pairDistanceProduct (A : Finset UnitSphere) : ℝ :=
  ∏ p ∈ A.offDiag, dist p.1 p.2

/-- Erdős Problem 991: if `A ⊆ S²` with `|A| = n` maximises `∏_{i<j} |w_i - w_j|` among `n`-point
subsets of `S²`, then `max_C | |A ∩ C| - α_C n | = o(n)` over spherical caps `C` (`α_C` the
normalized area): for every `ε > 0` and all large `n`, every such maximiser has
`| |A ∩ C| - α_C n | ≤ ε n` for every cap `C` (`sphericalCap` and `normalizedArea` are those of
Problem 988). -/
def feketePointsCapDiscrepancySmall : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset UnitSphere, A.card = n →
    (∀ B : Finset UnitSphere, B.card = n → pairDistanceProduct B ≤ pairDistanceProduct A) →
      ∀ v t, |(((A : Set UnitSphere) ∩ sphericalCap v t).ncard : ℝ) -
        normalizedArea (sphericalCap v t) * n| ≤ ε * n

/--
Resolved true: Brauchart proved that the spherical cap discrepancy of `n` points maximising `∏_{i<j}
|w_i - w_j|` (optimal logarithmic energy points) is `≪ n^{3/4} = o(n)`, improved to `≪ n^{2/3}` by
Marzo and Mas; erdosproblems.com/991 lists the problem as proved. Source: T. F. Bloom, Erdős
Problems, Problem #991, https://www.erdosproblems.com/991 (status PROVED); resolution: J. S.
Brauchart, Optimal logarithmic energy points on the unit sphere, Math. Comp. (2008), 1599-1613,
erdosproblems.com/991: Brauchart proves that the cap discrepancy of such maximisers is ≪ n^{3/4}
(the qualitative o(n) follows from classical potential theory); Marzo and Mas give ≪ n^{2/3},
https://www.erdosproblems.com/991.
-/
public theorem_wanted feketePointsCapDiscrepancySmall_holds : feketePointsCapDiscrepancySmall

end MathlibExt.Geometry.FeketePointsCapDiscrepancyErdosProblem991Wanted
