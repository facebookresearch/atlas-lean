/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Original local commutator recognition as the independent finite-form derived group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3FullImage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3CentralProduct

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The genuine source commutator maps isomorphically onto the actual full-image commutator. -/
noncomputable def y322Orthogonal3SourceDerivedEquiv :
    commutator Y322Presentation ≃* commutator y322Orthogonal3FullImage :=
  (y322Orthogonal3FullImageEquiv.subgroupMap (commutator Y322Presentation)).trans
    (MulEquiv.subgroupCongr (y322Derived_map_equiv y322Orthogonal3FullImageEquiv))

/-- The actual full-image derived group is isomorphic to the independent full-form derived group. -/
noncomputable def y322Orthogonal3ImageDerivedEquiv :
    commutator y322Orthogonal3FullImage ≃* y322Orthogonal3FullDerived :=
  ((commutator y322Orthogonal3FullImage).equivMapOfInjective
      y322Orthogonal3FullImage.subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr y322Orthogonal3FullDerived_eq.symm)

/-- The source commutator is the independent seven-dimensional finite-form derived group. -/
noncomputable def y322Orthogonal3DerivedEquiv :
    commutator Y322Presentation ≃* y322Orthogonal3FullDerived :=
  y322Orthogonal3SourceDerivedEquiv.trans y322Orthogonal3ImageDerivedEquiv

/-- The independent full-form derived group has actual order 4585351680. -/
theorem y322Orthogonal3FullDerived_card :
    Nat.card y322Orthogonal3FullDerived = 4585351680 := by
  rw [← Nat.card_congr y322Orthogonal3DerivedEquiv.toEquiv]
  exact y322Presentation_commutator_card

/-- The local source group is the independent full-form derived group times central sign. -/
noncomputable def y322Orthogonal3IndependentProductEquiv :
    Y322Presentation ≃* y322Orthogonal3FullDerived × (ZMod 3)ˣ :=
  y322SignProductEquiv.symm.trans
    (((MulEquiv.subgroupCongr y322Orthogonal3Sign_ker).trans
      y322Orthogonal3DerivedEquiv).prodCongr (MulEquiv.refl _))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
