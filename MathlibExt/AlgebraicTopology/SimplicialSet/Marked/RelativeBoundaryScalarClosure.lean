/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeBoundarySaturation

/-!
# All original scalar-monomorphism corners in the relative left class

The completed family's right maps have the full original simplicial
boundary-right comparison on every generator. Native simplicial
monomorphism generation extends that lifting to every scalar mono.
The same cotensor adjunction then proves closure of the entire generated
left class, retaining arbitrary original marked right codomains.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty
open scoped Simplicial

namespace SSet.Marked

/-- Each whole original retained Cartesian generator lifts every scalar-mono corner into every completed right map. -/
theorem cartesianRelativeBoundary_generator_scalar_mono {B : SSet.{u}} {E F : Over (max B)}
    (p : E ⟶ F) (hp : (cartesianRelativeBoundaryCells B).rlp p)
    (s : RelativeBoundaryCellIndex cartesianCell.{u} B)
    {K L : SSet.{u}} (a : K ⟶ L) [Mono a] :
    HasLiftingProperty (overParameterPushoutProduct a (cartesianRelativeBoundaryCell B s).hom) p := by
  have hI := (overParameterBoundary_lifting_iff (cartesianRelativeBoundaryCell B s).hom p).mp
    (fun n => hp _ (cartesianRelativeBoundaryCells_boundary s n))
  have hm : (monomorphisms SSet.{u}).rlp
      (overParameterMappingComparison (cartesianRelativeBoundaryCell B s).hom p) := by
    rw [SSet.rlp_monomorphisms]
    exact hI
  exact (overParameterPushoutProduct_hasLiftingProperty_iff a _ p).mpr (hm a inferInstance)

/-- The same original dual generators lift every scalar-mono corner without target fibrancy assumptions. -/
theorem cocartesianRelativeBoundary_generator_scalar_mono {B : SSet.{u}} {E F : Over (max B)}
    (p : E ⟶ F) (hp : (cocartesianRelativeBoundaryCells B).rlp p)
    (s : RelativeBoundaryCellIndex cocartesianCell.{u} B)
    {K L : SSet.{u}} (a : K ⟶ L) [Mono a] :
    HasLiftingProperty (overParameterPushoutProduct a (cocartesianRelativeBoundaryCell B s).hom) p := by
  have hI := (overParameterBoundary_lifting_iff (cocartesianRelativeBoundaryCell B s).hom p).mp
    (fun n => hp _ (cocartesianRelativeBoundaryCells_boundary s n))
  have hm : (monomorphisms SSet.{u}).rlp
      (overParameterMappingComparison (cocartesianRelativeBoundaryCell B s).hom p) := by
    rw [SSet.rlp_monomorphisms]
    exact hI
  exact (overParameterPushoutProduct_hasLiftingProperty_iff a _ p).mpr (hm a inferInstance)

/-- Every scalar monomorphism preserves the whole actual generated Cartesian left class. -/
theorem cartesianRelativeBoundary_left_scalar_mono {B : SSet.{u}} {X Y : Over (max B)}
    (i : X ⟶ Y) (hi : (cartesianRelativeBoundaryCells B).rlp.llp i)
    {K L : SSet.{u}} (a : K ⟶ L) [Mono a] :
    (cartesianRelativeBoundaryCells B).rlp.llp (overParameterPushoutProduct a i) := by
  intro E F p hp
  let q := overCotensorComparison a p
  have hq : (cartesianRelativeBoundaryCells B).rlp q := by
    rintro A D f ⟨s⟩
    exact (overParameter_cotensor_lifting_iff a _ p).mp
      (cartesianRelativeBoundary_generator_scalar_mono p hp s a)
  exact (overParameter_cotensor_lifting_iff a i p).mpr (hi q hq)

/-- Every original scalar monomorphism also preserves the full dual native left class. -/
theorem cocartesianRelativeBoundary_left_scalar_mono {B : SSet.{u}} {X Y : Over (max B)}
    (i : X ⟶ Y) (hi : (cocartesianRelativeBoundaryCells B).rlp.llp i)
    {K L : SSet.{u}} (a : K ⟶ L) [Mono a] :
    (cocartesianRelativeBoundaryCells B).rlp.llp (overParameterPushoutProduct a i) := by
  intro E F p hp
  let q := overCotensorComparison a p
  have hq : (cocartesianRelativeBoundaryCells B).rlp q := by
    rintro A D f ⟨s⟩
    exact (overParameter_cotensor_lifting_iff a _ p).mp
      (cocartesianRelativeBoundary_generator_scalar_mono p hp s a)
  exact (overParameter_cotensor_lifting_iff a i p).mpr (hi q hq)

end SSet.Marked
