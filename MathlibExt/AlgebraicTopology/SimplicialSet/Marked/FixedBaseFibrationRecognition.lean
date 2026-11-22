/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FixedBaseHornCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.IntrinsicParameterLifting

/-!
# Exact intrinsic target recognition for the original fixed-base cell family

The original auxiliary tests already recognize the intrinsic marking and
Cartesian or cocartesian projection. The added constant-base mono/horn
tests lift into every such original target, by the native relative
mapping-fibration theorem. Thus this genuinely small relative family
has precisely the original intrinsic terminal lifting targets, including
arbitrary non-Kan quasicategory bases. This asserts terminal target
recognition, not identification with all marked-model fibrations.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty
open scoped Simplicial

namespace SSet.Marked

/-- The entire original intrinsic cartesian target lifts every actual fixed-base generator. -/
theorem cartesianFixedBaseCells_terminal_rlp_of_intrinsic {B : SSet.{u}} [Quasicategory B]
    (X : Over (max B)) (hX : cartesianObjects B X) :
    (cartesianFixedBaseCells B).rlp (Over.mkIdTerminal.from X) := by
  let target : CartesianOver B := ⟨X, hX⟩
  have haux : (cartesianCellsOver B).rlp (Over.mkIdTerminal.from X) :=
    (cartesianCellsOver_terminal_rlp_iff X).mpr hX
  rintro A D f ⟨s⟩
  cases s with
  | inl s => exact haux _ (ofHoms.mk (f := overCell cartesianCell (max B)) s)
  | inr s =>
    let _ : Mono (fixedBaseMonoCell B s.1).hom := fixedBaseMonoCell_mono B s.1
    exact cartesian_parameterHorn_lifting (fixedBaseMonoCell B s.1).hom target s.2.1 s.2.2

/-- The actual fixed-base terminal right class is exactly the original intrinsic cartesian object class. -/
theorem cartesianFixedBaseCells_terminal_rlp_iff {B : SSet.{u}} [Quasicategory B]
    (X : Over (max B)) :
    (cartesianFixedBaseCells B).rlp (Over.mkIdTerminal.from X) ↔ cartesianObjects B X := by
  constructor
  · intro h
    exact (cartesianCellsOver_terminal_rlp_iff X).mp
      (antitone_rlp (cartesianCellsOver_le_fixedBase B) _ h)
  · exact cartesianFixedBaseCells_terminal_rlp_of_intrinsic X

/-- The entire original intrinsic cocartesian target lifts every actual fixed-base generator. -/
theorem cocartesianFixedBaseCells_terminal_rlp_of_intrinsic {B : SSet.{u}} [Quasicategory B]
    (X : Over (max B)) (hX : cocartesianObjects B X) :
    (cocartesianFixedBaseCells B).rlp (Over.mkIdTerminal.from X) := by
  let target : CocartesianOver B := ⟨X, hX⟩
  have haux : (cocartesianCellsOver B).rlp (Over.mkIdTerminal.from X) :=
    (cocartesianCellsOver_terminal_rlp_iff X).mpr hX
  rintro A D f ⟨s⟩
  cases s with
  | inl s => exact haux _ (ofHoms.mk (f := overCell cocartesianCell (max B)) s)
  | inr s =>
    let _ : Mono (fixedBaseMonoCell B s.1).hom := fixedBaseMonoCell_mono B s.1
    exact cocartesian_parameterHorn_lifting (fixedBaseMonoCell B s.1).hom target s.2.1 s.2.2

/-- The actual fixed-base terminal right class is exactly the original intrinsic cocartesian object class. -/
theorem cocartesianFixedBaseCells_terminal_rlp_iff {B : SSet.{u}} [Quasicategory B]
    (X : Over (max B)) :
    (cocartesianFixedBaseCells B).rlp (Over.mkIdTerminal.from X) ↔ cocartesianObjects B X := by
  constructor
  · intro h
    exact (cocartesianCellsOver_terminal_rlp_iff X).mp
      (antitone_rlp (cocartesianCellsOver_le_fixedBase B) _ h)
  · exact cocartesianFixedBaseCells_terminal_rlp_of_intrinsic X

end SSet.Marked
