/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.GroupTheory.SpecificGroups.Dihedral
import MathlibExt.GroupTheory.VirtuallyNilpotentGrowth

open MathlibExt.GroupTheory.PolynomialGrowthWanted

-- The infinite dihedral group has two cosets of its cyclic rotation subgroup.
example {ι : Type*} [Finite ι] (P : Group.Generators (DihedralGroup 0) ι) :
    P.HasPolynomialGrowth := by
  let H := Subgroup.zpowers (DihedralGroup.r (1 : ZMod 0))
  let rep (b : Bool) : DihedralGroup 0 := if b then .sr 0 else 1
  have hrot (i : ZMod 0) : DihedralGroup.r i ∈ H :=
    ⟨(i : ℤ), DihedralGroup.r_one_zpow _⟩
  have : Finite (DihedralGroup 0 ⧸ H) := by
    apply Finite.of_surjective (fun b => (QuotientGroup.mk (rep b) : DihedralGroup 0 ⧸ H))
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    cases g with
    | r i => exact ⟨false, QuotientGroup.eq.mpr (by simpa [rep] using hrot i)⟩
    | sr i => exact ⟨true, QuotientGroup.eq.mpr (by simpa [rep] using hrot i)⟩
  exact hasPolynomialGrowth_of_virtuallyNilpotent P H
    (hH := Subgroup.finiteIndex_of_finite_quotient) (hn := inferInstance)
