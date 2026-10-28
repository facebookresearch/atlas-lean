/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The genuine original C322 image inside the independent full isometry group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3Faithfulness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3FullOrder
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationDerivedTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationAbelianization

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The genuine source reflection image inside the independently defined full isometry group. -/
def y322Orthogonal3FullImage : Subgroup y322Orthogonal3FullGroup :=
  y322Orthogonal3Image.subgroupOf y322Orthogonal3FullGroup

/-- The original source group is isomorphic to its actual image in the independent full group. -/
noncomputable def y322Orthogonal3FullImageEquiv : Y322Presentation ≃* y322Orthogonal3FullImage :=
  y322Orthogonal3Equiv.trans
    (Subgroup.subgroupOfEquivOfLe y322Orthogonal3Image_le_full).symm

/-- The actual original-source image in the independent full group has order 9170703360. -/
theorem y322Orthogonal3FullImage_card : Nat.card y322Orthogonal3FullImage = 9170703360 := by
  rw [← Nat.card_congr y322Orthogonal3FullImageEquiv.toEquiv]
  exact y322Orthogonal3_exact_order_faithful.1

/-- The actual original-source image has index at most two in the independent full group. -/
theorem y322Orthogonal3FullImage_index_le : y322Orthogonal3FullImage.index ≤ 2 := by
  have h := y322Orthogonal3FullImage.index_mul_card
  rw [y322Orthogonal3FullImage_card] at h
  have hc := y322Orthogonal3FullGroup_card_le
  have hm : y322Orthogonal3FullImage.index * 9170703360 ≤ 2 * 9170703360 := by
    rw [h]
    exact hc
  exact Nat.le_of_mul_le_mul_right hm (by decide)

/-- The independent full-group sign is its literal finite-field determinant. -/
def y322Orthogonal3FullSign : y322Orthogonal3FullGroup →* (ZMod 3)ˣ :=
  Matrix.GeneralLinearGroup.det.comp y322Orthogonal3FullGroup.subtype

/-- Restricting the independent full determinant gives precisely the actual original source sign. -/
theorem y322Orthogonal3FullImageEquiv_sign :
    (y322Orthogonal3FullSign.comp y322Orthogonal3FullImage.subtype).comp
      y322Orthogonal3FullImageEquiv.toMonoidHom = y322Orthogonal3Sign := by
  rfl

/-- The actual source image determinant kernel is exactly its derived subgroup. -/
theorem y322Orthogonal3FullImage_sign_ker :
    (y322Orthogonal3FullSign.comp y322Orthogonal3FullImage.subtype).ker =
      commutator y322Orthogonal3FullImage := by
  apply y322Derived_kernel_transport y322Orthogonal3FullImageEquiv
  rw [y322Orthogonal3FullImageEquiv_sign]
  exact y322Orthogonal3Sign_ker

/-- The independently defined full derived subgroup is the actual source-image derived subgroup. -/
theorem y322Orthogonal3FullDerived_eq :
    commutator y322Orthogonal3FullGroup =
      (commutator y322Orthogonal3FullImage).map y322Orthogonal3FullImage.subtype :=
  y322SmallIndex_derived_eq y322Orthogonal3FullImage y322Orthogonal3FullSign
    y322Orthogonal3FullImage_index_le y322Orthogonal3FullImage_sign_ker

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
