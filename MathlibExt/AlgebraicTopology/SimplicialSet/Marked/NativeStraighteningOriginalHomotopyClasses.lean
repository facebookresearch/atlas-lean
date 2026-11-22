/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningOriginalHomotopyAdjunction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeHomotopyComponents
import Mathlib.AlgebraicTopology.ModelCategory.Homotopy

/-!
# Genuine homotopy classes for the same original native adjunction

The actual native image of the original source-projection cylinder is
good. Every actual coherent-model homotopy into a fibrant diagram can
therefore be represented using that same whole cylinder. The ordinary
native adjunction transposes both original endpoints. Quotient recursion
in both directions retains each original whole representative and gives
an equivalence with the original relative marked homotopy classes.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Actual coherent-model homotopy classes transpose to the same original relative marked homotopy classes, using
the proved good original native cylinder. -/
def nativeOriginalHomotopyClassCurry (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → LeftHomotopyClass ((nativeStraightening B).obj X) F →
      (relativeIntervalCylinder (max B)).HomotopyClass X ((nativeUnstraightening B).obj F) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF
  let _ : IsFibrant F := hF
  let _ : IsCofibrant ((nativeStraightening B).obj X) := nativeStraightening_object_isCofibrant B X
  let Q := nativeStraighteningOriginalCylinder B X
  let _ : Q.IsGood := nativeStraighteningOriginalCylinder_isGood B X
  let P := relativeIntervalCylinder (max B)
  let E := (nativeStraighteningAdjunction B).homEquiv X F
  refine Quot.lift (fun f => P.homotopyQuotientFunctor.map (E f)) ?_
  intro f₀ f₁ h
  exact P.homotopyQuotientFunctor_map_eq
    (nativeOriginalHomotopyCurry B X F (h.leftHomotopy Q))

/-- The same original relative marked homotopy classes transpose back to actual coherent-model classes through their
unchanged whole representatives. -/
def nativeOriginalHomotopyClassUncurry (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    (relativeIntervalCylinder (max B)).HomotopyClass X ((nativeUnstraightening B).obj F) →
      LeftHomotopyClass ((nativeStraightening B).obj X) F := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  let P := relativeIntervalCylinder (max B)
  let E := (nativeStraighteningAdjunction B).homEquiv X F
  change Quot (@HomRel.CompClosure (Over (max B)) _ P.elementaryHomotopyRel
    X ((nativeUnstraightening B).obj F)) → _
  refine Quot.lift (fun f => LeftHomotopyClass.mk (E.symm f)) ?_
  intro f₀ f₁ h
  obtain ⟨H⟩ := (HomRel.compClosure_iff_self (r := P.elementaryHomotopyRel) f₀ f₁).mp h
  have H' : (P.app X).LeftHomotopy (E (E.symm f₀)) (E (E.symm f₁)) := by
    simpa only [Equiv.apply_symm_apply] using H
  have K : (nativeStraighteningOriginalCylinder B X).LeftHomotopy (E.symm f₀) (E.symm f₁) :=
    nativeOriginalHomotopyUncurry B X F H'
  exact LeftHomotopyClass.sound K.leftHomotopyRel

/-- The actual target homotopy-class representative transposes to its same entire original native-adjunction marked
slice representative. -/
theorem nativeOriginalHomotopyClassCurry_mk (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    ∀ (_hF : IsFibrant F) (f : (nativeStraightening B).obj X ⟶ F),
      nativeOriginalHomotopyClassCurry B X F _hF (LeftHomotopyClass.mk f) =
        (relativeIntervalCylinder (max B)).homotopyQuotientFunctor.map
          ((nativeStraighteningAdjunction B).homEquiv X F f) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro _hF f
  rfl

/-- The original whole marked slice representative is read back by the inverse of the same actual native adjunction. -/
theorem nativeOriginalHomotopyClassUncurry_map (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    ∀ f : X ⟶ (nativeUnstraightening B).obj F,
      nativeOriginalHomotopyClassUncurry B X F
        ((relativeIntervalCylinder (max B)).homotopyQuotientFunctor.map f) =
          LeftHomotopyClass.mk ((nativeStraighteningAdjunction B).homEquiv X F |>.symm f) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro f
  rfl

/-- The same actual native adjunction identifies genuine target-model homotopy classes with the original full marked
relative classes into every actual fibrant coherent diagram. -/
def nativeOriginalLeftHomotopyClassEquiv (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → LeftHomotopyClass ((nativeStraightening B).obj X) F ≃
      (relativeIntervalCylinder (max B)).HomotopyClass X ((nativeUnstraightening B).obj F) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF
  refine
    { toFun := nativeOriginalHomotopyClassCurry B X F hF
      invFun := nativeOriginalHomotopyClassUncurry B X F
      left_inv := ?_
      right_inv := ?_ }
  · intro c
    obtain ⟨f, rfl⟩ := LeftHomotopyClass.mk_surjective c
    rw [nativeOriginalHomotopyClassCurry_mk, nativeOriginalHomotopyClassUncurry_map,
      Equiv.symm_apply_apply]
  · intro c
    obtain ⟨f, rfl⟩ := (relativeIntervalCylinder (max B)).homotopyQuotientFunctor.map_surjective c
    rw [nativeOriginalHomotopyClassUncurry_map, nativeOriginalHomotopyClassCurry_mk,
      Equiv.apply_symm_apply]

/-- Actual right homotopy classes have the same original marked relative-class equivalence, retaining the original
whole native representative. -/
def nativeOriginalRightHomotopyClassEquiv (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    IsFibrant F → RightHomotopyClass ((nativeStraightening B).obj X) F ≃
      (relativeIntervalCylinder (max B)).HomotopyClass X ((nativeUnstraightening B).obj F) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF
  let _ : IsFibrant F := hF
  let _ : IsCofibrant ((nativeStraightening B).obj X) := nativeStraightening_object_isCofibrant B X
  exact leftHomotopyClassEquivRightHomotopyClass.symm.trans
    (nativeOriginalLeftHomotopyClassEquiv B X F hF)

/-- The actual right homotopy class of an original native map retains precisely the same whole marked slice
transpose. -/
theorem nativeOriginalRightHomotopyClassEquiv_mk (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    ∀ (_hF : IsFibrant F) (f : (nativeStraightening B).obj X ⟶ F),
      nativeOriginalRightHomotopyClassEquiv B X F _hF (RightHomotopyClass.mk f) =
        (relativeIntervalCylinder (max B)).homotopyQuotientFunctor.map
          ((nativeStraighteningAdjunction B).homEquiv X F f) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro _hF f
  rfl

/-- The genuine homotopy-class equivalence retains precomposition by every original whole marked slice map, through
the same actual native adjunction naturality. -/
theorem nativeOriginalRightHomotopyClassEquiv_pre (B : SSet.{u})
    {X Y : Over (max B)} (i : X ⟶ Y) (F : EnrichedDiagram (realization B)ᵒᵖ) :
    let _ := coherentDiagramModelCategory B
    ∀ (hF : IsFibrant F) (c : RightHomotopyClass ((nativeStraightening B).obj Y) F),
      nativeOriginalRightHomotopyClassEquiv B X F hF (c.precomp ((nativeStraightening B).map i)) =
        (relativeIntervalCylinder (max B)).homotopyClassPrecomp i ((nativeUnstraightening B).obj F)
          (nativeOriginalRightHomotopyClassEquiv B Y F hF c) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hF c
  obtain ⟨f, rfl⟩ := RightHomotopyClass.mk_surjective c
  rw [RightHomotopyClass.precomp_mk, nativeOriginalRightHomotopyClassEquiv_mk,
    nativeOriginalRightHomotopyClassEquiv_mk]
  let P := relativeIntervalCylinder (max B)
  change P.homotopyQuotientFunctor.map
      ((nativeStraighteningAdjunction B).homEquiv X F ((nativeStraightening B).map i ≫ f)) =
    P.homotopyQuotientFunctor.map i ≫
      P.homotopyQuotientFunctor.map ((nativeStraighteningAdjunction B).homEquiv Y F f)
  exact (congrArg P.homotopyQuotientFunctor.map
    ((nativeStraighteningAdjunction B).homEquiv_naturality_left i f)).trans
      (P.homotopyQuotientFunctor.map_comp i _)

end SSet.Marked
