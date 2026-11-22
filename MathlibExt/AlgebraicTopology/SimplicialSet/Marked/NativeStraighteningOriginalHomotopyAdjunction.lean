/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningOriginalCylinderWeak

/-!
# The same native adjunction transposes the original whole cylinder homotopies

The original relative interval cylinder retains its source projection
and both original endpoints. Its literal native image retains every
whole map. The ordinary actual native adjunction transposes homotopies
in both directions by its original endpoint naturality. No model weak
map, homotopy comparison or Quillen result is an input.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The same whole native source-projection cylinder homotopy transposes to the original relative marked slice
homotopy, retaining both exact endpoint equations. -/
def nativeOriginalHomotopyCurry (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ)
    {f₀ f₁ : (nativeStraightening B).obj X ⟶ F}
    (H : (nativeStraighteningOriginalPrecylinder B X).LeftHomotopy f₀ f₁) :
    ((relativeIntervalCylinder (max B)).app X).LeftHomotopy
      ((nativeStraighteningAdjunction B).homEquiv X F f₀)
      ((nativeStraighteningAdjunction B).homEquiv X F f₁) := by
  let P := (relativeIntervalCylinder (max B)).app X
  let adj := nativeStraighteningAdjunction B
  refine { h := adj.homEquiv P.I F H.h, h₀ := ?_, h₁ := ?_ }
  · exact (adj.homEquiv_naturality_left P.i₀ H.h).symm.trans
      (congrArg (adj.homEquiv X F) H.h₀)
  · exact (adj.homEquiv_naturality_left P.i₁ H.h).symm.trans
      (congrArg (adj.homEquiv X F) H.h₁)

/-- The original entire marked relative cylinder homotopy transposes back to the same whole actual native cylinder,
with both original endpoint equations. -/
def nativeOriginalHomotopyUncurry (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ)
    {f₀ f₁ : (nativeStraightening B).obj X ⟶ F}
    (H : ((relativeIntervalCylinder (max B)).app X).LeftHomotopy
      ((nativeStraighteningAdjunction B).homEquiv X F f₀)
      ((nativeStraighteningAdjunction B).homEquiv X F f₁)) :
    (nativeStraighteningOriginalPrecylinder B X).LeftHomotopy f₀ f₁ := by
  let P := (relativeIntervalCylinder (max B)).app X
  let adj := nativeStraighteningAdjunction B
  refine { h := (adj.homEquiv P.I F).symm H.h, h₀ := ?_, h₁ := ?_ }
  · exact (adj.homEquiv_naturality_left_symm P.i₀ H.h).symm.trans
      ((congrArg (adj.homEquiv X F).symm H.h₀).trans
        ((adj.homEquiv X F).symm_apply_apply f₀))
  · exact (adj.homEquiv_naturality_left_symm P.i₁ H.h).symm.trans
      ((congrArg (adj.homEquiv X F).symm H.h₁).trans
        ((adj.homEquiv X F).symm_apply_apply f₁))

/-- The original full marked cylinder homotopies and their literal native images are equivalent without any fibrancy
or base hypothesis. -/
theorem nativeOriginalHomotopy_iff (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ)
    (f₀ f₁ : (nativeStraightening B).obj X ⟶ F) :
    Nonempty ((nativeStraighteningOriginalPrecylinder B X).LeftHomotopy f₀ f₁) ↔
      Nonempty (((relativeIntervalCylinder (max B)).app X).LeftHomotopy
        ((nativeStraighteningAdjunction B).homEquiv X F f₀)
        ((nativeStraighteningAdjunction B).homEquiv X F f₁)) :=
  ⟨fun ⟨H⟩ => ⟨nativeOriginalHomotopyCurry B X F H⟩,
    fun ⟨H⟩ => ⟨nativeOriginalHomotopyUncurry B X F H⟩⟩

/-- Transposing the same entire original homotopy in both directions returns its original whole marked slice map. -/
theorem nativeOriginalHomotopyCurry_uncurry_h (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ)
    {f₀ f₁ : (nativeStraightening B).obj X ⟶ F}
    (H : ((relativeIntervalCylinder (max B)).app X).LeftHomotopy
      ((nativeStraighteningAdjunction B).homEquiv X F f₀)
      ((nativeStraighteningAdjunction B).homEquiv X F f₁)) :
    (nativeOriginalHomotopyCurry B X F (nativeOriginalHomotopyUncurry B X F H)).h = H.h :=
  (nativeStraighteningAdjunction B).homEquiv _ F |>.apply_symm_apply H.h

/-- Transposing the same whole native homotopy in both directions returns its entire original coherent diagram map. -/
theorem nativeOriginalHomotopyUncurry_curry_h (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ)
    {f₀ f₁ : (nativeStraightening B).obj X ⟶ F}
    (H : (nativeStraighteningOriginalPrecylinder B X).LeftHomotopy f₀ f₁) :
    (nativeOriginalHomotopyUncurry B X F (nativeOriginalHomotopyCurry B X F H)).h = H.h :=
  (nativeStraighteningAdjunction B).homEquiv _ F |>.symm_apply_apply H.h

end SSet.Marked
