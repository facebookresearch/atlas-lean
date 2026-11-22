/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Simple groups with Sylow 2-subgroup a product of `Q₈` (Kourovka Notebook Problem 1.80)

Kourovka Notebook, Archive of Solved Problems, Problem 1.80 (A. I. Starostin): does there exist a
finite simple group whose Sylow 2-subgroup is a direct product of quaternion groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Sylow

@[expose] public section

namespace MathlibExt.GroupTheory.SimpleGroupQuaternionSylowKourovka1Problem80Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.80 (A. I.
Starostin). UnsolvedMath record UM-00700069 (`KOU-1.80`), dataset ulamai/UnsolvedMath v1.8.0.

"Quaternion group" is read as `Q₈` (`QuaternionGroup 2`); products of generalized quaternion groups
are not asserted. At least one factor is required: with zero factors the Sylow 2-subgroup is trivial
and any simple group of odd prime order would qualify.
-/

/-- Kourovka 1.80 (A. I. Starostin): some finite simple group has a Sylow 2-subgroup isomorphic to
a direct product of `k ≥ 1` copies of the quaternion group `Q₈` (`QuaternionGroup 2`). -/
def simpleGroupWithQuaternionProductSylow : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G), IsSimpleGroup G ∧
    ∃ (P : Sylow 2 G) (k : ℕ), 0 < k ∧ Nonempty ((P : Subgroup G) ≃* (Fin k → QuaternionGroup 2))

/--
Resolved false: the Kourovka Archive answers 1.80 No, citing Glauberman's Z*-theorem paper: no
finite simple group has a Sylow 2-subgroup isomorphic to a direct product of `k ≥ 1` quaternion
groups. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.80
(A. I. Starostin); resolution: G. Glauberman, Central elements in core-free groups, J. Algebra 4
(1966), 403-420, Z*-theorem and its application to Sylow 2-subgroups of simple groups (Section 6);
Kourovka Archive, Problem 1.80, https://doi.org/10.1016/0021-8693(66)90030-5.
-/
public theorem_wanted simpleGroupWithQuaternionProductSylow_refuted :
    ¬ simpleGroupWithQuaternionProductSylow

end MathlibExt.GroupTheory.SimpleGroupQuaternionSylowKourovka1Problem80Wanted
