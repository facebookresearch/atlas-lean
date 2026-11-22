/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CellMarkingCoverage
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.InnerParameterPushout
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianWeakEquivalences

/-!
# Original inner marked cells have full parameter boundary lifting

The actual minimally marked inner horn covers every target mark. Its
monic parameter corner has an inner-anodyne underlying simplicial map
and covers every original corner mark. A native inner-fibration lift
therefore preserves the full marked diagonal. Actual boundary adjunction
then proves the original relative mapping restriction is a boundary-right
map, hence mapping weak, for every intrinsic Cartesian or cocartesian
target. No marked-model recognition equality is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The same original minimally marked inner horn and whole supplied base simplex define a native marked slice cell. -/
def innerCellOver {B : SSet.{u}} (n : ℕ) (i : Fin (n + 3)) (r : (Δ[n + 2] : SSet.{u}) ⟶ B) :
    Over.mk (ofMin (Y := max B) ((horn.{u} (n + 2) i).ι ≫ r)) ⟶ Over.mk (ofMin (Y := max B) r) :=
  Over.homMk (innerCell.{u} n i) (Hom.ext rfl)

/-- Native whole parameter lifting for the original marked inner cell follows from the actual inner-anodyne
  corner and exact mark coverage. -/
theorem innerCellOver_parameter_lifting {A D B : SSet.{u}}
    (a : A ⟶ D) [Mono a] (n : ℕ) (i : Fin (n + 3)) (hi : 0 < i) (hi' : i < Fin.last (n + 2))
    (r : (Δ[n + 2] : SSet.{u}) ⟶ B) {Y Z : Over (max B)} (p : Y ⟶ Z) [InnerFibration p.left.hom] :
    HasLiftingProperty (overParameterPushoutProduct a (innerCellOver n i r)) p := by
  let f := innerCellOver n i r
  let sq := overParameterUnderlyingPushout a f
  have hinner : innerAnodyneExtensions f.left.hom := innerAnodyneExtensions.horn_ι hi hi'
  let _ : HasLiftingProperty sq.ι.hom p.left.hom :=
    innerAnodyneExtensions_pushoutObjObjι (underlyingParameterSquare sq).flip hinner _ InnerFibration.mem
  have hcov : MarkingSurjective sq.ι := parameterSquare_markingSurjective sq (innerCell_markingSurjective n i)
  let _ : HasLiftingProperty (overParameterPushoutProduct a f).left p.left := hcov.hasLiftingProperty p.left
  exact HasLiftingProperty.over _ p

/-- The actual Cartesian relative mapping restriction of every original inner marked horn has all native
  boundary lifts. -/
theorem innerCellOver_cartesian_mapping_rlp {B : SSet.{u}}
    (n : ℕ) (i : Fin (n + 3)) (hi : 0 < i) (hi' : i < Fin.last (n + 2))
    (r : (Δ[n + 2] : SSet.{u}) ⟶ B) (Y : CartesianOver B) :
    modelCategoryQuillen.I.{u}.rlp ((overMappingFunctor .maximal (max B) Y.obj).map (innerCellOver n i r).op) := by
  let p := Over.mkIdTerminal.from Y.obj
  let _ : CartesianFibration Y.obj.hom.hom := Y.property.1
  have hp : p.left = Y.obj.hom := Over.mkIdTerminal_from_left Y.obj
  let _ : InnerFibration p.left.hom := hp.symm ▸ (inferInstanceAs (InnerFibration Y.obj.hom.hom))
  apply (overParameterBoundary_terminal_lifting_iff _ Y.obj).mp
  intro k
  exact innerCellOver_parameter_lifting _ n i hi hi' r p

/-- The same original marked inner-cell mapping boundary lifting holds for every actual cocartesian target. -/
theorem innerCellOver_cocartesian_mapping_rlp {B : SSet.{u}}
    (n : ℕ) (i : Fin (n + 3)) (hi : 0 < i) (hi' : i < Fin.last (n + 2))
    (r : (Δ[n + 2] : SSet.{u}) ⟶ B) (Y : CocartesianOver B) :
    modelCategoryQuillen.I.{u}.rlp ((overMappingFunctor .maximal (max B) Y.obj).map (innerCellOver n i r).op) := by
  let p := Over.mkIdTerminal.from Y.obj
  let _ : CocartesianFibration Y.obj.hom.hom := Y.property.1
  have hp : p.left = Y.obj.hom := Over.mkIdTerminal_from_left Y.obj
  let _ : InnerFibration p.left.hom := hp.symm ▸ (inferInstanceAs (InnerFibration Y.obj.hom.hom))
  apply (overParameterBoundary_terminal_lifting_iff _ Y.obj).mp
  intro k
  exact innerCellOver_parameter_lifting _ n i hi hi' r p

/-- Every original minimally marked inner horn is Cartesian mapping weak over its whole original base simplex. -/
theorem innerCellOver_cartesian_weak {B : SSet.{u}}
    (n : ℕ) (i : Fin (n + 3)) (hi : 0 < i) (hi' : i < Fin.last (n + 2))
    (r : (Δ[n + 2] : SSet.{u}) ⟶ B) : cartesianWeakEquivalences B (innerCellOver n i r) := by
  apply (cartesianWeakEquivalences_iff _).mpr
  intro Y
  exact modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _ (innerCellOver_cartesian_mapping_rlp n i hi hi' r Y)

/-- The same whole original marked inner horn is cocartesian mapping weak. -/
theorem innerCellOver_cocartesian_weak {B : SSet.{u}}
    (n : ℕ) (i : Fin (n + 3)) (hi : 0 < i) (hi' : i < Fin.last (n + 2))
    (r : (Δ[n + 2] : SSet.{u}) ⟶ B) : cocartesianWeakEquivalences B (innerCellOver n i r) := by
  apply (cocartesianWeakEquivalences_iff _).mpr
  intro Y
  exact modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _ (innerCellOver_cocartesian_mapping_rlp n
    i hi hi' r Y)

end SSet.Marked
