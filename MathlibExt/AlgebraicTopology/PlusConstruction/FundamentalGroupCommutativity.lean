/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberFundamentalSurjectivity
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Commutativity of the original plus-target fundamental group

The actual plus map is surjective on the fundamental group, and its kernel
is the specified subgroup. Therefore its target fundamental group is
commutative exactly when that subgroup contains the source commutator.
The existing fundamental-group structures and based map are retained.
There is no H-space, CW, or desired commutativity input on the target.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory

universe u

namespace TopCat.IsPlusConstructionAt

variable {X Y : TopCat.{u}} {f : X ⟶ Y}
  {x : X} {y : Y} {hxy : f x = y}
  {P : Subgroup (FundamentalGroup X x)}
  [P.Normal] [Group.IsPerfect P]

/-- The native target fundamental group is commutative exactly when the
actual kernel of the plus map contains the native source commutator. -/
public theorem fundamentalGroup_isMulCommutative_iff_commutator_le
    (hp : TopCat.IsPlusConstructionAt f x y hxy P) :
    IsMulCommutative (FundamentalGroup Y y) ↔
      commutator (FundamentalGroup X x) ≤ P := by
  rw [← commutator_eq_bot_iff,
    ← map_commutator_of_surjective hp.pi1Map_surjective,
    Subgroup.map_eq_bot_iff, hp.kernel_eq]

/-- An inclusion of the whole source commutator into the specified kernel
gives commutativity of the actual target fundamental group. -/
public theorem fundamentalGroup_isMulCommutative_of_commutator_le
    (hp : TopCat.IsPlusConstructionAt f x y hxy P)
    (hcomm : commutator (FundamentalGroup X x) ≤ P) :
    IsMulCommutative (FundamentalGroup Y y) :=
  hp.fundamentalGroup_isMulCommutative_iff_commutator_le.mpr hcomm

/-- The same commutativity holds at another target point along its actual
basepoint path. Only the old path-transport equivalence is used. -/
public theorem fundamentalGroup_isMulCommutative_of_path
    (hp : TopCat.IsPlusConstructionAt f x y hxy P)
    (hcomm : commutator (FundamentalGroup X x) ≤ P)
    {z : Y} (p : Path y z) : IsMulCommutative (FundamentalGroup Y z) := by
  have hc : ∀ a b : FundamentalGroup Y y, a * b = b * a :=
    isMulCommutative_iff.mp
      (hp.fundamentalGroup_isMulCommutative_of_commutator_le hcomm)
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPath p
  apply IsMulCommutative.of_comm
  intro a b
  apply e.symm.injective
  calc
    e.symm (a * b) = e.symm a * e.symm b := e.symm.map_mul a b
    _ = e.symm b * e.symm a := hc _ _
    _ = e.symm (b * a) := (e.symm.map_mul b a).symm

/-- For a path-connected target, the derived commutativity applies to
every original target basepoint, with no new group structure. -/
public theorem fundamentalGroup_isMulCommutative_at
    [PathConnectedSpace Y]
    (hp : TopCat.IsPlusConstructionAt f x y hxy P)
    (hcomm : commutator (FundamentalGroup X x) ≤ P) (z : Y) :
    IsMulCommutative (FundamentalGroup Y z) :=
  hp.fundamentalGroup_isMulCommutative_of_path hcomm
    (PathConnectedSpace.somePath y z)

end TopCat.IsPlusConstructionAt

end
