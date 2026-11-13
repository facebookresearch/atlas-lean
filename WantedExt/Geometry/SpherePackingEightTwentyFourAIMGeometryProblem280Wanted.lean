/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Optimal sphere packing densities in dimensions 8 and 24 (AIM sphere packings, Question 1)

AIM workshop Sphere packings, lattices, groups and infinite dimensional algebra, problems, Question
1 (S. Miller and H. Cohn): can the technique of Cohn-Elkies prove that the `E₈` and Leech lattices
have the highest sphere packing densities in dimensions 8 and 24, respectively? The list adds that a
positive answer is the complete solution of the sphere packing problem there.
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Geometry.KeplerConjectureWanted

@[expose] public section

namespace MathlibExt.Geometry.SpherePackingEightTwentyFourAIMGeometryProblem280Wanted

/-!
Source: AIM workshop Sphere packings, lattices, groups and infinite dimensional algebra, problems
compiled by L. Carbone, Question 1 (contributed by S. Miller and H. Cohn),
https://aimath.org/WWN/spherepacking/spherepacking.pdf. UnsolvedMath record UM-20001942
(`AIM-GEOMETRY-0280`), dataset ulamai/UnsolvedMath v1.8.0.

Densities are those of `WantedExt.Geometry.KeplerConjectureWanted`: a packing is a set of centres
whose open unit balls are pairwise disjoint, its density is the limit superior of the covered
fraction of `B_R(0)`, and `Δ d` is the supremum over all packings, lattice or not. The answer is
stated as the optimal densities: `π⁴/384` is the density of the `E₈` lattice packing and `π¹²/12!`
that of the Leech lattice packing (both papers). That these lattices attain the values, and the
question's method clause (both proofs use the Cohn-Elkies linear programming bound), are not
formalized, so the declaration is labeled `partial_scope`.
-/

open MathlibExt.Geometry.KeplerConjectureWanted.Geometry.KeplerConjectureProblem

/-- AIM Sphere packings, lattices, and infinite dimensional algebra, Question 1, as a claim on the
optimal densities: the largest density of a packing of unit balls is `π⁴/384` (the density of the
`E₈` lattice packing) in `ℝ⁸` and `π¹²/12!` (the density of the Leech lattice packing) in `ℝ²⁴`. -/
def spherePackingDensityEightTwentyFour : Prop :=
  Δ 8 = Real.pi ^ 4 / 384 ∧ Δ 24 = Real.pi ^ 12 / (Nat.factorial 12 : ℝ)

/--
Resolved true: Viazovska proved that no packing of unit balls in `ℝ⁸` is denser than the `E₈`
lattice packing (density `π⁴/384`), and Cohn, Kumar, Miller, Radchenko and Viazovska that the Leech
lattice packing (density `π¹²/12!`) is optimal in `ℝ²⁴`, both with the Cohn-Elkies linear
programming bound. Source: AIM workshop Sphere packings, lattices, groups and infinite dimensional
algebra, problems compiled by L. Carbone, Question 1 (contributed by S. Miller and H. Cohn),
https://aimath.org/WWN/spherepacking/spherepacking.pdf; resolution: M. S. Viazovska, The sphere
packing problem in dimension 8, Ann. of Math. (2) 185 (2017), no. 3, 991-1015, arXiv:1603.04246; H.
Cohn, A. Kumar, S. D. Miller, D. Radchenko and M. Viazovska, The sphere packing problem in dimension
24, Ann. of Math. (2) 185 (2017), no. 3, 1017-1033, arXiv:1603.06518, Viazovska, Theorem 1: no
packing of unit balls in ℝ⁸ has density greater than that of the E₈ lattice packing, Δ₈ = π⁴/384 ≈
0.25367 (introduction), via an optimal Cohn-Elkies function
(https://doi.org/10.4007/annals.2017.185.3.7); Cohn-Kumar-Miller-Radchenko-Viazovska, Theorem 1.1:
the Leech lattice achieves the optimal sphere packing density in ℝ²⁴, namely π¹²/12! =
0.0019295743…, via the linear programming bound, https://doi.org/10.4007/annals.2017.185.3.8.
-/
public theorem_wanted spherePackingDensityEightTwentyFour_holds :
    spherePackingDensityEightTwentyFour

end MathlibExt.Geometry.SpherePackingEightTwentyFourAIMGeometryProblem280Wanted
