/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.TensorFunctor
import all Mathlib.CategoryTheory.Monoidal.Bimod

/-!
# The universal map from the original bimodule tensor

The original balancing coequalizer represents pairings that preserve the
two outer actions. The construction retains the literal projection,
the original left and right action squares, and both universal maps.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped MonoidalCategory

namespace Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] {A B D : Mon C}

/-- The original tensor projection retains the complete balancing equation. -/
@[reassoc] theorem tensorProjection_balance (M : Bimod A B) (N : Bimod B D) :
    (M.actRight ▷ N.X) ≫ tensorProjection M N =
      (α_ M.X B.X N.X).hom ≫ (M.X ◁ N.actLeft) ≫ tensorProjection M N := by
  exact (coequalizer.condition _ _).trans (Category.assoc _ _ _)

/-- The original projection preserves the left action through its actual source associator. -/
@[reassoc] theorem tensorProjection_leftAction (M : Bimod A B) (N : Bimod B D) :
    (A.X ◁ tensorProjection M N) ≫ (tensorBimod M N).actLeft =
      (α_ A.X M.X N.X).inv ≫ (M.actLeft ▷ N.X) ≫ tensorProjection M N :=
  TensorBimod.whiskerLeft_π_actLeft M N

/-- The original projection preserves the right action through the complete original source word. -/
@[reassoc] theorem tensorProjection_rightAction (M : Bimod A B) (N : Bimod B D) :
    (tensorProjection M N ▷ D.X) ≫ (tensorBimod M N).actRight =
      (α_ M.X N.X D.X).hom ≫ (M.X ◁ N.actRight) ≫ tensorProjection M N :=
  TensorBimod.π_tensor_id_actRight M N

/-- The equivalent original right-linearity word retains the inverse source associator. -/
@[reassoc] theorem tensorProjection_rightLinear (M : Bimod A B) (N : Bimod B D) :
    (M.X ◁ N.actRight) ≫ tensorProjection M N =
      (α_ M.X N.X D.X).inv ≫ (tensorProjection M N ▷ D.X) ≫ (tensorBimod M N).actRight := by
  have h := congrArg (fun t => (α_ M.X N.X D.X).inv ≫ t) (tensorProjection_rightAction M N)
  simp only [Iso.inv_hom_id_assoc] at h
  exact h.symm

/-- The universal underlying map is the descendent of the original balancing coequalizer. -/
def tensorDescRaw (M : Bimod A B) (N : Bimod B D) {X : C} (k : M.X ⊗ N.X ⟶ X)
    (h : (M.actRight ▷ N.X) ≫ k = (α_ M.X B.X N.X).hom ≫ (M.X ◁ N.actLeft) ≫ k) :
    (tensorBimod M N).X ⟶ X := coequalizer.desc k (by simpa only [Category.assoc] using h)

/-- The universal descendent retains the entire original pairing on the actual projection. -/
@[reassoc] theorem tensorProjection_tensorDescRaw (M : Bimod A B) (N : Bimod B D)
    {X : C} (k : M.X ⊗ N.X ⟶ X)
    (h : (M.actRight ▷ N.X) ≫ k = (α_ M.X B.X N.X).hom ≫ (M.X ◁ N.actLeft) ≫ k) :
    tensorProjection M N ≫ tensorDescRaw M N k h = k := coequalizer.π_desc _ _

/-- A pairing preserving the original balancing and outer actions descends to an actual bimodule map. -/
def tensorDesc (M : Bimod A B) (N : Bimod B D) (P : Bimod A D) (k : M.X ⊗ N.X ⟶ P.X)
    (hB : (M.actRight ▷ N.X) ≫ k = (α_ M.X B.X N.X).hom ≫ (M.X ◁ N.actLeft) ≫ k)
    (hA : (α_ A.X M.X N.X).inv ≫ (M.actLeft ▷ N.X) ≫ k = (A.X ◁ k) ≫ P.actLeft)
    (hD : (M.X ◁ N.actRight) ≫ k = (α_ M.X N.X D.X).inv ≫ (k ▷ D.X) ≫ P.actRight) :
    tensorBimod M N ⟶ P where
  hom := tensorDescRaw M N k hB
  left_act_hom := by
    refine (cancel_epi ((tensorLeft A.X).map
      (coequalizer.π (M.actRight ▷ N.X) ((α_ M.X B.X N.X).hom ≫ M.X ◁ N.actLeft)))).mp ?_
    change (A.X ◁ tensorProjection M N) ≫ (tensorBimod M N).actLeft ≫ tensorDescRaw M N k hB =
      (A.X ◁ tensorProjection M N) ≫ (A.X ◁ tensorDescRaw M N k hB) ≫ P.actLeft
    rw [tensorProjection_leftAction_assoc, tensorProjection_tensorDescRaw,
      ← whiskerLeft_comp_assoc, tensorProjection_tensorDescRaw]
    exact hA
  right_act_hom := by
    refine (cancel_epi ((tensorRight D.X).map
      (coequalizer.π (M.actRight ▷ N.X) ((α_ M.X B.X N.X).hom ≫ M.X ◁ N.actLeft)))).mp ?_
    change (tensorProjection M N ▷ D.X) ≫ (tensorBimod M N).actRight ≫ tensorDescRaw M N k hB =
      (tensorProjection M N ▷ D.X) ≫ (tensorDescRaw M N k hB ▷ D.X) ≫ P.actRight
    rw [tensorProjection_rightAction_assoc, tensorProjection_tensorDescRaw,
      ← comp_whiskerRight_assoc, tensorProjection_tensorDescRaw]
    rw [hD, Iso.hom_inv_id_assoc]

/-- The complete tensor universal map retains the original pairing on the actual quotient projection. -/
@[reassoc] theorem tensorProjection_tensorDesc (M : Bimod A B) (N : Bimod B D) (P : Bimod A D)
    (k : M.X ⊗ N.X ⟶ P.X)
    (hB : (M.actRight ▷ N.X) ≫ k = (α_ M.X B.X N.X).hom ≫ (M.X ◁ N.actLeft) ≫ k)
    (hA : (α_ A.X M.X N.X).inv ≫ (M.actLeft ▷ N.X) ≫ k = (A.X ◁ k) ≫ P.actLeft)
    (hD : (M.X ◁ N.actRight) ≫ k = (α_ M.X N.X D.X).inv ≫ (k ▷ D.X) ≫ P.actRight) :
    tensorProjection M N ≫ (tensorDesc M N P k hB hA hD).hom = k :=
  tensorProjection_tensorDescRaw M N k hB

/-- The actual bimodule tensor maps are determined by the complete original quotient projection. -/
theorem tensor_hom_ext (M : Bimod A B) (N : Bimod B D) {P : Bimod A D}
    {f g : tensorBimod M N ⟶ P} (h : tensorProjection M N ≫ f.hom = tensorProjection M N ≫ g.hom) :
    f = g := Bimod.hom_ext _ _ (coequalizer.hom_ext h)

end Bimod
