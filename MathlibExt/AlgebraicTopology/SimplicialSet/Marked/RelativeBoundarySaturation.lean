/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeBoundarySmallObject
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverCotensorLeibniz

/-!
# Full native scalar-boundary closure of the small relative left class

The next original boundary of each retained generator is the generator
with that dimension prepended to its word. The actual cotensor Leibniz
adjunction therefore proves boundary closure for the entire generated
left class against every original marked right map, without a fibrancy
hypothesis on its codomain. This concerns the proved small anodyne
prerequisite, not a uniform generation of all weak marked monos.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty
open scoped Simplicial

namespace SSet.Marked

/-- Prepending the supplied original dimension keeps the whole Cartesian boundary corner in the actual small family. -/
theorem cartesianRelativeBoundaryCells_boundary {B : SSet.{u}}
    (s : RelativeBoundaryCellIndex cartesianCell.{u} B) (n : ℕ) :
    cartesianRelativeBoundaryCells B
      (overParameterPushoutProduct (boundary.{u} n).ι (cartesianRelativeBoundaryCell B s).hom) :=
  ofHoms.mk (f := fun t => (cartesianRelativeBoundaryCell B t).hom) (n :: s.1, s.2)

/-- The dual original operator word has the same exact next-boundary membership. -/
theorem cocartesianRelativeBoundaryCells_boundary {B : SSet.{u}}
    (s : RelativeBoundaryCellIndex cocartesianCell.{u} B) (n : ℕ) :
    cocartesianRelativeBoundaryCells B
      (overParameterPushoutProduct (boundary.{u} n).ι (cocartesianRelativeBoundaryCell B s).hom) :=
  ofHoms.mk (f := fun t => (cocartesianRelativeBoundaryCell B t).hom) (n :: s.1, s.2)

/-- Every original scalar boundary preserves the full generated Cartesian left class against arbitrary
  marked slice right maps. -/
theorem cartesianRelativeBoundary_left_boundary {B : SSet.{u}} {X Y : Over (max B)}
    (i : X ⟶ Y) (hi : (cartesianRelativeBoundaryCells B).rlp.llp i) (n : ℕ) :
    (cartesianRelativeBoundaryCells B).rlp.llp (overParameterPushoutProduct (boundary.{u} n).ι i) := by
  intro E F p hp
  let q := overCotensorComparison (boundary.{u} n).ι p
  have hq : (cartesianRelativeBoundaryCells B).rlp q := by
    rintro A D f ⟨s⟩
    exact (overParameter_cotensor_lifting_iff _ _ p).mp
      (hp _ (cartesianRelativeBoundaryCells_boundary s n))
  exact (overParameter_cotensor_lifting_iff _ i p).mpr (hi q hq)

/-- The same whole original dual left class is closed under its supplied scalar boundary corners. -/
theorem cocartesianRelativeBoundary_left_boundary {B : SSet.{u}} {X Y : Over (max B)}
    (i : X ⟶ Y) (hi : (cocartesianRelativeBoundaryCells B).rlp.llp i) (n : ℕ) :
    (cocartesianRelativeBoundaryCells B).rlp.llp (overParameterPushoutProduct (boundary.{u} n).ι i) := by
  intro E F p hp
  let q := overCotensorComparison (boundary.{u} n).ι p
  have hq : (cocartesianRelativeBoundaryCells B).rlp q := by
    rintro A D f ⟨s⟩
    exact (overParameter_cotensor_lifting_iff _ _ p).mp
      (hp _ (cocartesianRelativeBoundaryCells_boundary s n))
  exact (overParameter_cotensor_lifting_iff _ i p).mpr (hi q hq)

/-- Every native completed left map is genuinely weak and monic in the full intrinsic Cartesian mapping class. -/
theorem cartesianRelativeBoundary_left_le_testing (B : SSet.{u}) [Quasicategory B] :
    (cartesianRelativeBoundaryCells B).rlp.llp ≤ cartesianTestingTrivialCofibrations B := by
  calc
    _ ≤ (cartesianTestingTrivialCofibrations B).rlp.llp :=
      antitone_llp (antitone_rlp (cartesianRelativeBoundaryCells_le_testing B))
    _ = _ := cartesianTestingFibrations_llp B

/-- The entire dual completed native left class has the same full weak-mono conclusion. -/
theorem cocartesianRelativeBoundary_left_le_testing (B : SSet.{u}) [Quasicategory B] :
    (cocartesianRelativeBoundaryCells B).rlp.llp ≤ cocartesianTestingTrivialCofibrations B := by
  calc
    _ ≤ (cocartesianTestingTrivialCofibrations B).rlp.llp :=
      antitone_llp (antitone_rlp (cocartesianRelativeBoundaryCells_le_testing B))
    _ = _ := cocartesianTestingFibrations_llp B

end SSet.Marked
