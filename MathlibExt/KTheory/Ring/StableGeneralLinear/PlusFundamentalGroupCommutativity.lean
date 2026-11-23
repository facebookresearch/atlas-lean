/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.FundamentalGroupCommutativity
public import MathlibExt.KTheory.Ring.StableGeneralLinear.ClassifyingSpacePlusSubgroup

/-!
# Fundamental-group commutativity of the actual BGL plus target

Stable Whitehead identifies the stable elementary subgroup with the
whole stable general-linear commutator. Through the original BGL
fundamental-group equivalence, the specified plus subgroup therefore
contains the source commutator. The target commutativity follows from
the original plus map, not an assumed H-space or a K1 comparison map.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe w u v

namespace AlgebraicKTheory.StableGL

private theorem commutator_le_comap_elementary
    {G : Type v} [Group G] (R : Type u) [Ring R]
    (e : G ≃* StableGL R) :
    commutator G ≤ (stableElementarySubgroup R).comap e.toMonoidHom := by
  intro q hq
  have hm : (commutator G).map e.toMonoidHom ≤ commutator (StableGL R) := by
    rw [map_commutator_eq, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  exact commutator_le_stableElementarySubgroup R
    (hm (Subgroup.mem_map_of_mem e.toMonoidHom hq))

/-- The whole commutator of the original ordinary BGL fundamental group
lies in its actual specified plus subgroup. -/
public theorem ordinaryBGL_commutator_le_plusSubgroup (R : Type u) [Ring R] :
    commutator (FundamentalGroup (ordinaryBGL R) (ordinaryBGLBasepoint R)) ≤
      BGLPlusSubgroup R :=
  commutator_le_comap_elementary R (ordinaryBGLFundamentalMulEquiv R)

/-- The same inclusion for the actual native CGWH BGL and its original
marked point, with the native comparison rather than a replacement. -/
public theorem BGL_commutator_le_plusSubgroup (R : Type u) [Ring R] :
    commutator (FundamentalGroup (CGWH.cgwhToTop.obj (BGL.{w} R))
      (BGLBasepoint.{w} R)) ≤ BGLPlusSubgroupCGWH.{w} R :=
  commutator_le_comap_elementary R (BGLFundamentalMulEquiv.{w} R)

/-- Any actual plus target of ordinary BGL has commutative native
fundamental group at its original image point, over every ring. -/
public theorem ordinaryBGL_plus_fundamentalGroup_isMulCommutative
    (R : Type u) [Ring R] {Y : TopCat.{u}}
    {i : ordinaryBGL R ⟶ Y} {y : Y}
    {hi : i (ordinaryBGLBasepoint R) = y}
    (hp : TopCat.IsPlusConstructionAt i (ordinaryBGLBasepoint R) y hi
      (BGLPlusSubgroup R)) : IsMulCommutative (FundamentalGroup Y y) :=
  hp.fundamentalGroup_isMulCommutative_of_commutator_le
    (ordinaryBGL_commutator_le_plusSubgroup R)

/-- The actual native CGWH plus map yields the same conclusion, without
changing the target fundamental-group dictionary. -/
public theorem BGL_plus_fundamentalGroup_isMulCommutative
    (R : Type u) [Ring R] {Y : CGWH.{w, u}}
    {i : BGL.{w} R ⟶ Y} {y : Y}
    {hi : i (BGLBasepoint.{w} R) = y}
    (hp : CGWH.IsPlusConstructionAt i (BGLBasepoint.{w} R) y hi
      (BGLPlusSubgroupCGWH.{w} R)) :
    IsMulCommutative (FundamentalGroup (CGWH.cgwhToTop.obj Y) y) :=
  TopCat.IsPlusConstructionAt.fundamentalGroup_isMulCommutative_of_commutator_le hp
    (BGL_commutator_le_plusSubgroup.{w} R)

end AlgebraicKTheory.StableGL

end
