/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeOriginalCriticalHornWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverFibrationCells

/-!
# Every original critical cell and actual native unstraightening lifts

The original critical summand retains every arity and whole original
marked target-to-base map. Its actual physical native image is a weak
projective attachment through the genuine full marked Arrow Iso.
The actual native adjunction then gives critical-cell right lifts for
unstraightening every genuine coherent-model fibration.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The SAME original critically marked horn is the actual original Cartesian critical cell summand. -/
def nativeOriginalCriticalCell (n : ℕ) : Arrow Marked.{u} := cartesianCell (.inr (.inl n))

/-- The entire original critical cell retains precisely its whole original marked horn inclusion. -/
theorem nativeOriginalCriticalCell_hom (n : ℕ) :
    (nativeOriginalCriticalCell.{u} n).hom = cartesianCriticalCell n := rfl

/-- The original critical family retains every supplied original whole marked base projection. -/
def nativeOriginalCriticalCellsOver (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  overCells nativeOriginalCriticalCell.{u} (max B)

/-- Every SAME actual original critical cell over every whole original target-to-base map has its genuine weak
native image. -/
theorem nativeOriginalCriticalOverCell_straightening_projectiveWeakLeft (B : SSet.{u})
    (s : OverCellIndex nativeOriginalCriticalCell.{u} (max B)) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      ((nativeStraightening B).map (overCell nativeOriginalCriticalCell.{u} (max B) s)) :=
  nativeOriginalCriticalCell_straightening_projectiveWeakLeft B s.1 s.2

/-- The SAME entire original critical family, including all original arities and full marked base maps, lies in the
actual native weak projective image class. -/
theorem nativeOriginalCriticalCellsOver_straightening_projectiveWeakLeft (B : SSet.{u}) :
    nativeOriginalCriticalCellsOver B ≤
      ((enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp).inverseImage
        (nativeStraightening B) :=
  (ofHoms_le_iff (overCell nativeOriginalCriticalCell.{u} (max B)) _).mpr
    (nativeOriginalCriticalOverCell_straightening_projectiveWeakLeft B)

/-- Actual native unstraightening of every genuine coherent-model fibration lifts the SAME complete original
critical cells over every original whole marked base map. -/
theorem nativeUnstraightening_map_originalCriticalRlp (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → (nativeOriginalCriticalCellsOver B).rlp ((nativeUnstraightening B).map q) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  let J := enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos
  have hq' : J.rlp q := (fibration_iff q).mp hq
  rintro X Y i ⟨s⟩
  exact ((nativeStraighteningAdjunction B).hasLiftingProperty_iff
    (overCell nativeOriginalCriticalCell.{u} (max B) s) q).mp
      ((nativeOriginalCriticalOverCell_straightening_projectiveWeakLeft B s) q hq')

end SSet.Marked
