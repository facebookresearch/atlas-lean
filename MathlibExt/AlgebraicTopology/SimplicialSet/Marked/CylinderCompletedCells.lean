/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.IntervalEndpointCorners
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.IntervalBoundaryCorners
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FibrationCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.BoundaryCells

/-!
# An actual small native cylinder completion of the original marked cells

Start with the original Cartesian or cocartesian cells and both original
endpoint corners of the native marked mono generators. Iterate the actual
whole-boundary corner, retaining its original pushout, markings and maps.
This defines a small monic original family, with every generator's next
boundary corner retained. Full left-class corner saturation and equality
with all local-testing weak monos require separate proofs and are not
asserted here.
-/

noncomputable section
universe u
open CategoryTheory MorphismProperty Limits HomotopicalAlgebra

namespace SSet.Marked

/-- The actual auxiliary cells and both native mono-generator endpoint corners. -/
abbrev CylinderSeedIndex := FibrationCellIndex ⊕ (MonoCellIndex × Fin 2)

/-- The original native Cartesian seed arrow, keeping the whole selected endpoint pushout. -/
def cartesianCylinderSeed (s : CylinderSeedIndex) : Arrow Marked.{u} :=
  match s with
  | .inl i => cartesianCell.{u} i
  | .inr i => Arrow.mk (intervalCylinder.{u}.endpointCorner (monoCell.{u} i.1).hom i.2)

/-- The dual seed family retains the same original endpoint corners and dual auxiliary arrows. -/
def cocartesianCylinderSeed (s : CylinderSeedIndex) : Arrow Marked.{u} :=
  match s with
  | .inl i => cocartesianCell.{u} i
  | .inr i => Arrow.mk (intervalCylinder.{u}.endpointCorner (monoCell.{u} i.1).hom i.2)

/-- Iterate the actual whole-boundary corner on the same original marked arrow. -/
def iterateIntervalBoundaryCorner : ℕ → Arrow Marked.{u} → Arrow Marked.{u}
  | 0, f => f
  | n + 1, f => Arrow.mk (intervalCylinder.boundaryCorner (iterateIntervalBoundaryCorner n f).hom)

/-- Each actual native marked mono generator is monic by its proved generating-class equality. -/
theorem monoCell_mono (s : MonoCellIndex) : Mono (monoCell.{u} s).hom := by
  have h : monoCells.{u}.rlp.llp (monoCell.{u} s).hom :=
    monoCells.le_llp_rlp _ (ofHoms.mk (f := fun s => (monoCell.{u} s).hom) s)
  change monomorphisms Marked.{u} (monoCell.{u} s).hom
  rw [← monoCells_generate_monomorphisms]
  exact h

/-- Every original Cartesian seed, including both whole endpoint corners, is monic. -/
theorem cartesianCylinderSeed_mono (s : CylinderSeedIndex) : Mono (cartesianCylinderSeed.{u} s).hom := by
  rcases s with s | ⟨s, ε⟩
  · exact cartesianCell_mono s
  · let _ : Mono (monoCell.{u} s).hom := monoCell_mono s
    exact intervalEndpointCorner_mono _ ε

/-- The corresponding dual original seed family is monic on the same native marked carrier. -/
theorem cocartesianCylinderSeed_mono (s : CylinderSeedIndex) : Mono (cocartesianCylinderSeed.{u} s).hom := by
  rcases s with s | ⟨s, ε⟩
  · exact cocartesianCell_mono s
  · let _ : Mono (monoCell.{u} s).hom := monoCell_mono s
    exact intervalEndpointCorner_mono _ ε

/-- The actual original whole-boundary corner preserves monicity at every iteration. -/
theorem iterateIntervalBoundaryCorner_mono (n : ℕ) (f : Arrow Marked.{u}) [Mono f.hom] :
    Mono (iterateIntervalBoundaryCorner n f).hom := by
  induction n with
  | zero => exact inferInstanceAs (Mono f.hom)
  | succ n ih =>
      let _ : Mono (iterateIntervalBoundaryCorner n f).hom := ih
      exact intervalBoundaryCorner_mono _

/-- The original countable completed Cartesian arrow family. -/
def cartesianCylinderCompletedCell (s : ℕ × CylinderSeedIndex) : Arrow Marked.{u} :=
  iterateIntervalBoundaryCorner s.1 (cartesianCylinderSeed s.2)

/-- The original countable completed cocartesian family. -/
def cocartesianCylinderCompletedCell (s : ℕ × CylinderSeedIndex) : Arrow Marked.{u} :=
  iterateIntervalBoundaryCorner s.1 (cocartesianCylinderSeed s.2)

/-- The genuine original completed Cartesian generator property. -/
def cartesianCylinderCompletedCells : MorphismProperty Marked.{u} :=
  ofHoms (fun s => (cartesianCylinderCompletedCell s).hom)

/-- The genuine dual completed generator property on the same original marked category. -/
def cocartesianCylinderCompletedCells : MorphismProperty Marked.{u} :=
  ofHoms (fun s => (cocartesianCylinderCompletedCell s).hom)

/-- Native index smallness holds in every original working universe. -/
theorem cartesianCylinderCompletedCells_isSmall : IsSmall.{u} cartesianCylinderCompletedCells.{u} := by
  let _ : Small.{u} (ℕ × CylinderSeedIndex) := small_zero _
  exact isSmall_ofHoms _

/-- The same original-universe index bound holds for the dual completed family. -/
theorem cocartesianCylinderCompletedCells_isSmall : IsSmall.{u} cocartesianCylinderCompletedCells.{u} := by
  let _ : Small.{u} (ℕ × CylinderSeedIndex) := small_zero _
  exact isSmall_ofHoms _

/-- Every completed Cartesian generator is an actual original marked monomorphism. -/
theorem cartesianCylinderCompletedCells_le_monomorphisms :
    cartesianCylinderCompletedCells.{u} ≤ monomorphisms Marked.{u} := by
  rintro X Y f ⟨s⟩
  let _ : Mono (cartesianCylinderSeed.{u} s.2).hom := cartesianCylinderSeed_mono _
  exact iterateIntervalBoundaryCorner_mono _ _

/-- Every dual completed generator has the same native original monicity. -/
theorem cocartesianCylinderCompletedCells_le_monomorphisms :
    cocartesianCylinderCompletedCells.{u} ≤ monomorphisms Marked.{u} := by
  rintro X Y f ⟨s⟩
  let _ : Mono (cocartesianCylinderSeed.{u} s.2).hom := cocartesianCylinderSeed_mono _
  exact iterateIntervalBoundaryCorner_mono _ _

/-- The actual Cartesian family contains the next whole original boundary corner of each retained generator. -/
theorem cartesianCylinderCompletedCells_boundary (s : ℕ × CylinderSeedIndex) :
    cartesianCylinderCompletedCells.{u} (intervalCylinder.boundaryCorner (cartesianCylinderCompletedCell.{u} s).hom) :=
  ofHoms.mk (f := fun s => (cartesianCylinderCompletedCell.{u} s).hom) ⟨s.1 + 1, s.2⟩

/-- The actual dual generator family is closed under the same next original boundary corner. -/
theorem cocartesianCylinderCompletedCells_boundary (s : ℕ × CylinderSeedIndex) :
    cocartesianCylinderCompletedCells.{u} (intervalCylinder.boundaryCorner
      (cocartesianCylinderCompletedCell.{u} s).hom) :=
  ofHoms.mk (f := fun s => (cocartesianCylinderCompletedCell.{u} s).hom) ⟨s.1 + 1, s.2⟩

end SSet.Marked
