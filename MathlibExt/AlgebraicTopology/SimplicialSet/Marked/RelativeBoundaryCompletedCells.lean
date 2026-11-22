/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FixedBaseReplacementWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.WeakMonoParameterClosure
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FullTestingTargetRecognition

/-!
# The actual small constant-base scalar-boundary completion

Start with every original fixed-base auxiliary and mono/horn cell. A
finite word of scalar boundary dimensions forms the same successive
native fixed-base corners. The family is genuinely small in the original
value universe, is monic, and has full mapping weakness by the proved
scalar-mono closure. Its terminal right class is exactly the original
intrinsic target class. This does not assert that its whole saturated
left class equals every weak marked mono.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty
open scoped Simplicial

namespace SSet.Marked

/-- A finite word retains each original scalar boundary operator and its exact order of application. -/
def relativeBoundaryIterate {B : SSet.{u}} (l : List ℕ) (f : Arrow (Over (max B))) : Arrow (Over (max B)) :=
  match l with
  | [] => f
  | n :: l => Arrow.mk (overParameterPushoutProduct (boundary.{u} n).ι (relativeBoundaryIterate l f).hom)

/-- Every actual finite-word corner preserves monicity of its full original source arrow. -/
theorem relativeBoundaryIterate_mono {B : SSet.{u}} (l : List ℕ) (f : Arrow (Over (max B))) [Mono f.hom] :
    Mono (relativeBoundaryIterate l f).hom := by
  induction l with
  | nil =>
    change Mono f.hom
    infer_instance
  | cons n l ih =>
    let _ : Mono (relativeBoundaryIterate l f).hom := ih
    exact overParameterBoundary_mono _ n

/-- Full Cartesian weak marked monos remain weak and monic under every actual original boundary word. -/
theorem relativeBoundaryIterate_cartesian_weak {B : SSet.{u}} [Quasicategory B]
    (l : List ℕ) (f : Arrow (Over (max B))) (hf : cartesianTestingTrivialCofibrations B f.hom) :
    cartesianTestingTrivialCofibrations B (relativeBoundaryIterate l f).hom := by
  induction l with
  | nil => exact hf
  | cons n l ih => exact cartesianWeakMono_parameter_closed _ ih (boundary.{u} n).ι

/-- The original dual full weak-mono class has the same finite-word corner closure. -/
theorem relativeBoundaryIterate_cocartesian_weak {B : SSet.{u}} [Quasicategory B]
    (l : List ℕ) (f : Arrow (Over (max B))) (hf : cocartesianTestingTrivialCofibrations B f.hom) :
    cocartesianTestingTrivialCofibrations B (relativeBoundaryIterate l f).hom := by
  induction l with
  | nil => exact hf
  | cons n l ih => exact cocartesianWeakMono_parameter_closed _ ih (boundary.{u} n).ι

/-- The exact original fixed-base cell index with its finite scalar-boundary operator word. -/
abbrev RelativeBoundaryCellIndex (a : FibrationCellIndex → Arrow Marked.{u}) (B : SSet.{u}) :=
  List ℕ × FixedBaseCellIndex a B

/-- The original Cartesian cell at its supplied index, with the same full scalar-boundary word. -/
def cartesianRelativeBoundaryCell (B : SSet.{u}) (s : RelativeBoundaryCellIndex cartesianCell.{u} B) :
    Arrow (Over (max B)) := relativeBoundaryIterate s.1 (cartesianFixedBaseCell B s.2)

/-- The dual actual boundary-completed cell retains its original arrows, marks and base maps. -/
def cocartesianRelativeBoundaryCell (B : SSet.{u}) (s : RelativeBoundaryCellIndex cocartesianCell.{u} B) :
    Arrow (Over (max B)) := relativeBoundaryIterate s.1 (cocartesianFixedBaseCell B s.2)

/-- The complete original fixed-base boundary-word index is small at the same value universe. -/
theorem relativeBoundaryCellIndex_small (a : FibrationCellIndex → Arrow Marked.{u}) (B : SSet.{u}) :
    Small.{u} (RelativeBoundaryCellIndex a B) := by
  let _ : Small.{u} (FixedBaseCellIndex a B) := fixedBaseCellIndex_small a B
  let _ : Small.{u} (List ℕ) := small_zero _
  infer_instance

/-- The actual Cartesian constant-base boundary-completed family, retaining every original whole cell map. -/
def cartesianRelativeBoundaryCells (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  ofHoms (fun s => (cartesianRelativeBoundaryCell B s).hom)

/-- The actual dual small completed family on the same original carrier. -/
def cocartesianRelativeBoundaryCells (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  ofHoms (fun s => (cocartesianRelativeBoundaryCell B s).hom)

/-- Every actual original completed Cartesian cell is a full weak marked mono. -/
theorem cartesianRelativeBoundaryCells_le_testing (B : SSet.{u}) [Quasicategory B] :
    cartesianRelativeBoundaryCells B ≤ cartesianTestingTrivialCofibrations B := by
  rintro X Y f ⟨s⟩
  exact relativeBoundaryIterate_cartesian_weak s.1 _
    (cartesianFixedBaseCells_le_testing B _ (ofHoms.mk s.2))

/-- The original dual completed family has the same full weak-mono membership. -/
theorem cocartesianRelativeBoundaryCells_le_testing (B : SSet.{u}) [Quasicategory B] :
    cocartesianRelativeBoundaryCells B ≤ cocartesianTestingTrivialCofibrations B := by
  rintro X Y f ⟨s⟩
  exact relativeBoundaryIterate_cocartesian_weak s.1 _
    (cocartesianFixedBaseCells_le_testing B _ (ofHoms.mk s.2))

/-- All original fixed-base Cartesian cells are retained by the empty boundary word. -/
theorem cartesianFixedBaseCells_le_relativeBoundary (B : SSet.{u}) :
    cartesianFixedBaseCells B ≤ cartesianRelativeBoundaryCells B := by
  rintro X Y f ⟨s⟩
  exact ofHoms.mk (f := fun t => (cartesianRelativeBoundaryCell B t).hom) ([], s)

/-- The dual empty-word inclusion keeps every original fixed-base source and operator. -/
theorem cocartesianFixedBaseCells_le_relativeBoundary (B : SSet.{u}) :
    cocartesianFixedBaseCells B ≤ cocartesianRelativeBoundaryCells B := by
  rintro X Y f ⟨s⟩
  exact ofHoms.mk (f := fun t => (cocartesianRelativeBoundaryCell B t).hom) ([], s)

/-- Full original Cartesian intrinsic targets pass exactly the completed constant-base terminal right tests. -/
theorem cartesianRelativeBoundary_terminal_iff_intrinsic {B : SSet.{u}} [Quasicategory B]
    (Y : Over (max B)) :
    (cartesianRelativeBoundaryCells B).rlp (Over.mkIdTerminal.from Y) ↔ cartesianObjects B Y := by
  constructor
  · intro h
    exact (cartesianFixedBaseCells_terminal_rlp_iff Y).mp
      (antitone_rlp (cartesianFixedBaseCells_le_relativeBoundary B) _ h)
  · intro h
    exact antitone_rlp (cartesianRelativeBoundaryCells_le_testing B) _ (cartesianTesting_terminal_of_intrinsic Y h)

/-- The same full original dual terminal recognition holds for this actual constant-base completion. -/
theorem cocartesianRelativeBoundary_terminal_iff_intrinsic {B : SSet.{u}} [Quasicategory B]
    (Y : Over (max B)) :
    (cocartesianRelativeBoundaryCells B).rlp (Over.mkIdTerminal.from Y) ↔ cocartesianObjects B Y := by
  constructor
  · intro h
    exact (cocartesianFixedBaseCells_terminal_rlp_iff Y).mp
      (antitone_rlp (cocartesianFixedBaseCells_le_relativeBoundary B) _ h)
  · intro h
    exact antitone_rlp (cocartesianRelativeBoundaryCells_le_testing B) _ (cocartesianTesting_terminal_of_intrinsic Y h)

end SSet.Marked
