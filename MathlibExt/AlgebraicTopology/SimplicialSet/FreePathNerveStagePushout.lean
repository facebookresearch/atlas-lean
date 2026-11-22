/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveCellCoordinateRecord

/-!
# The actual original all-word length-stage pushout

The entire native indexed sum of original path-word cells attaches
along its literal old-stage preimage. Complete original raw word and
ordinal recovery prove open-complement injection; all original words
give exhaustive range coverage. The existing native preimage pushout
criterion gives the SAME four original maps.
-/

noncomputable section
universe u v
open CategoryTheory Limits Opposite
open scoped Simplicial
namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

/-- The SAME original next-stage map of every complete indexed word cell. -/
def stageCellToNext (k : ℕ) : stageCells V (k + 1) ⟶ (lengthStage V (k + 1) : SSet.{max u v}) :=
  SSet.Subcomplex.lift (stageCellMap V (k + 1)) (stageCellMap_range_le V (k + 1))

/-- The complete original all-word attaching square is an actual native simplicial pushout. -/
theorem original_stage_isPushout (k : ℕ) :
    IsPushout ((lengthStage V k).fromPreimage (stageCellMap V (k + 1)))
      ((lengthStage V k).preimage (stageCellMap V (k + 1))).ι
      (SSet.Subcomplex.homOfLE (lengthStage_mono V (Nat.le_succ k)))
      (stageCellToNext V k) := by
  have h := SSet.Subcomplex.preimageSupRange_isPushout (lengthStage V k) (stageCellMap V (k + 1))
    (fun q a b ha hb hab => by
      rcases q with ⟨⟨n⟩⟩
      exact stageCellMap_complement_injective V k n a b ha hb hab)
  exact h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (SSet.Subcomplex.eqToIso (lengthStage_sup_range V k))
      (by rfl) (by rfl) (by rfl) (by rfl)

/-- The full original attaching map retains the SAME exact native ambient inclusion. -/
lemma stageCellToNext_ι (k : ℕ) :
    stageCellToNext V k ≫ (lengthStage V (k + 1)).ι = stageCellMap V (k + 1) :=
  SSet.Subcomplex.lift_ι _ _

end CategoryTheory.FreePathNerveCoordinates
