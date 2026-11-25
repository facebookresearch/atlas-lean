/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedReplacementConstruction
public import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductBrown
public import Mathlib.CategoryTheory.Localization.Bifunctor

/-!
# The actual tensor derived with the original chosen replacements

The tensor bifunctor on the ordinary homotopy category is constructed from
the original `QX ⊗ QY`, all original maps and the canonical localization.
Brown's lemma supplies invariance at those actual cofibrant endpoints.
Ordinary tensor computes this bifunctor when both original endpoints are
cofibrant. No arbitrary-endpoint flatness is assumed or concluded.

Source: Hovey, *Model Categories*, Proposition 4.3.1 and Theorem 4.3.2.
The full derived closed monoidal structure is built in separate modules;
this module supplies its actual tensor and every replacement comparison.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory MorphismProperty Functor
open scoped MonoidalClosed

namespace HomotopicalAlgebra.DerivedTensorConstructions

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]

local notation "Ho" => MorphismProperty.Localization (weakEquivalences C)
local notation "π" => MorphismProperty.Q (weakEquivalences C)

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The actual original replacement tensor bifunctor on objects and all original maps. -/
def replacedTensor (d : GeneratedFunctorialReplacements.Data (C := C)) : C ⥤ C ⥤ C :=
  d.Q ⋙ curriedTensor C ⋙ (whiskeringLeft C C C).obj d.Q

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The raw derived tensor retains the actual canonical projection of `QX ⊗ QY`. -/
def raw (d : GeneratedFunctorialReplacements.Data (C := C)) : C ⥤ C ⥤ Ho :=
  replacedTensor d ⋙ (whiskeringRight C C Ho).obj π

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- Each raw object is the original two-replacement tensor image. -/
theorem raw_obj (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y : C) :
    ((raw d).obj X).obj Y = (π).obj (d.Q.obj X ⊗ d.Q.obj Y) := rfl

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- Every original source-variable map keeps the actual chosen Q-map and tensor whisker. -/
theorem raw_map_left (d : GeneratedFunctorialReplacements.Data (C := C))
    {X X' : C} (f : X ⟶ X') (Y : C) :
    ((raw d).map f).app Y = (π).map (d.Q.map f ▷ d.Q.obj Y) := rfl

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- Every original target-variable map keeps the same Q-map and original tensor whisker. -/
theorem raw_map_right (d : GeneratedFunctorialReplacements.Data (C := C))
    (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    ((raw d).obj X).map g = (π).map (d.Q.obj X ◁ d.Q.map g) := rfl

/-- Both original weak arrows are inverted from their actual cofibrant Q-images and Brown's lemma.
-/
theorem raw_inverts (d : GeneratedFunctorialReplacements.Data (C := C)) :
    MorphismProperty.IsInvertedBy₂ (weakEquivalences C) (weakEquivalences C) (raw d) := by
  rintro ⟨X, Y⟩ ⟨X', Y'⟩ ⟨f, g⟩ ⟨hf, hg⟩
  let _ : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  let _ : IsCofibrant (d.Q.obj X') := d.q_cofibrant X'
  let _ : IsCofibrant (d.Q.obj Y) := d.q_cofibrant Y
  let _ : IsCofibrant (d.Q.obj Y') := d.q_cofibrant Y'
  let _ : WeakEquivalence (d.Q.map f) := (weakEquivalence_iff _).mpr (d.q_map_weak f hf)
  let _ : WeakEquivalence (d.Q.map g) := (weakEquivalence_iff _).mpr (d.q_map_weak g hg)
  let pp := IsClosedSymmetricMonoidalModelCategory.pushoutProductAxiom (C := C)
  let _ : WeakEquivalence (d.Q.map f ▷ d.Q.obj Y) :=
    pp.whiskerRight_weakEquivalence_of_cofibrant (d.Q.map f) (d.Q.obj Y)
  let _ : WeakEquivalence (d.Q.obj X' ◁ d.Q.map g) :=
    pp.whiskerLeft_weakEquivalence_of_cofibrant (d.Q.obj X') (d.Q.map g)
  change IsIso ((π).map (d.Q.map f ▷ d.Q.obj Y) ≫ (π).map (d.Q.obj X' ◁ d.Q.map g))
  rw [← (π).map_comp]
  exact Localization.inverts (π) (weakEquivalences C) _ WeakEquivalence.mem

/-- The actual tensor on both full original homotopy categories is obtained by bifunctor
localization. -/
def tensor (d : GeneratedFunctorialReplacements.Data (C := C)) : Ho ⥤ Ho ⥤ Ho :=
  Localization.lift₂ (raw d) (raw_inverts d) π π

instance tensorLifting (d : GeneratedFunctorialReplacements.Data (C := C)) :
    Localization.Lifting₂ π π (weakEquivalences C) (weakEquivalences C) (raw d) (tensor d) :=
  inferInstanceAs (Localization.Lifting₂ π π _ _ _ (Localization.lift₂ (raw d) (raw_inverts d) π π))

/-- The complete tensor calculation is a natural isomorphism on both original variables. -/
def projectionIso (d : GeneratedFunctorialReplacements.Data (C := C)) :
    (((whiskeringLeft₂ Ho).obj π).obj π).obj (tensor d) ≅ raw d :=
  Localization.Lifting₂.iso π π (weakEquivalences C) (weakEquivalences C) (raw d) (tensor d)

/-- The actual two-variable tensor comparison keeps the same object and map calculation. -/
def comparison (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y : C) :
    ((tensor d).obj ((π).obj X)).obj ((π).obj Y) ≅ (π).obj (d.Q.obj X ⊗ d.Q.obj Y) :=
  ((evaluation C Ho).obj Y).mapIso ((projectionIso d).app X)

/-- Every original source map commutes with the actual derived tensor comparison. -/
theorem comparison_naturality_left (d : GeneratedFunctorialReplacements.Data (C := C))
    {X X' : C} (f : X ⟶ X') (Y : C) :
    ((tensor d).map ((π).map f)).app ((π).obj Y) ≫ (comparison d X' Y).hom =
      (comparison d X Y).hom ≫ (π).map (d.Q.map f ▷ d.Q.obj Y) :=
  congrArg (fun a => a.app Y) ((projectionIso d).hom.naturality f)

/-- Every original target map commutes with the same complete tensor comparison. -/
theorem comparison_naturality_right (d : GeneratedFunctorialReplacements.Data (C := C))
    (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    ((tensor d).obj ((π).obj X)).map ((π).map g) ≫ (comparison d X Y').hom =
      (comparison d X Y).hom ≫ (π).map (d.Q.obj X ◁ d.Q.map g) :=
  ((projectionIso d).hom.app X).naturality g

/-- The inverse source comparison retains the same original Q-map. -/
theorem comparison_inv_naturality_left (d : GeneratedFunctorialReplacements.Data (C := C))
    {X X' : C} (f : X ⟶ X') (Y : C) :
    (π).map (d.Q.map f ▷ d.Q.obj Y) ≫ (comparison d X' Y).inv =
      (comparison d X Y).inv ≫ ((tensor d).map ((π).map f)).app ((π).obj Y) :=
  congrArg (fun a => a.app Y) ((projectionIso d).inv.naturality f)

/-- The inverse target comparison retains the same original Q-map. -/
theorem comparison_inv_naturality_right (d : GeneratedFunctorialReplacements.Data (C := C))
    (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    (π).map (d.Q.obj X ◁ d.Q.map g) ≫ (comparison d X Y').inv =
      (comparison d X Y).inv ≫ ((tensor d).obj ((π).obj X)).map ((π).map g) :=
  ((projectionIso d).inv.app X).naturality g

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The original replacement counits give the actual ordinary tensor computation map. -/
def cofibrantComparisonMap (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y : C) :
    (π).obj (d.Q.obj X ⊗ d.Q.obj Y) ⟶ (π).obj (X ⊗ Y) :=
  (π).map (d.q.app X ⊗ₘ d.q.app Y)

/-- That exact ordinary comparison is invertible when both original endpoints are cofibrant. -/
theorem cofibrantComparisonMap_isIso (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y : C) [IsCofibrant X] [IsCofibrant Y] : IsIso (cofibrantComparisonMap d X Y) := by
  let _ : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  let _ : IsCofibrant (d.Q.obj Y) := d.q_cofibrant Y
  let qX : d.Q.obj X ⟶ X := d.q.app X
  let qY : d.Q.obj Y ⟶ Y := d.q.app Y
  let _ : WeakEquivalence qX := (weakEquivalence_iff _).mpr (d.q_trivialFibration X).2
  let _ : WeakEquivalence qY := (weakEquivalence_iff _).mpr (d.q_trivialFibration Y).2
  let pp := IsClosedSymmetricMonoidalModelCategory.pushoutProductAxiom (C := C)
  let _ : WeakEquivalence (qX ▷ d.Q.obj Y) := pp.whiskerRight_weakEquivalence_of_cofibrant qX
      (d.Q.obj Y)
  let _ : WeakEquivalence (X ◁ qY) := pp.whiskerLeft_weakEquivalence_of_cofibrant X qY
  change IsIso ((π).map (qX ⊗ₘ qY))
  rw [tensorHom_def]
  exact Localization.inverts (π) (weakEquivalences C) _ WeakEquivalence.mem

/-- Ordinary tensor on the same two cofibrant endpoints computes the actual derived tensor. -/
def cofibrantComparison (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y : C) [IsCofibrant X] [IsCofibrant Y] :
    ((tensor d).obj ((π).obj X)).obj ((π).obj Y) ≅ (π).obj (X ⊗ Y) := by
  let _ : IsIso (cofibrantComparisonMap d X Y) := cofibrantComparisonMap_isIso d X Y
  exact comparison d X Y ≪≫ asIso (cofibrantComparisonMap d X Y)

/-- The computation keeps the exact original Q counits on both tensor factors. -/
theorem cofibrantComparison_hom (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y : C) [IsCofibrant X] [IsCofibrant Y] :
    (cofibrantComparison d X Y).hom =
      (comparison d X Y).hom ≫ (π).map (d.q.app X ⊗ₘ d.q.app Y) := rfl

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The actual ordinary comparison commutes with both original arrow maps and both Q counits. -/
theorem cofibrantComparisonMap_naturality (d : GeneratedFunctorialReplacements.Data (C := C))
    {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (π).map (d.Q.map f ⊗ₘ d.Q.map g) ≫ cofibrantComparisonMap d X' Y' =
      cofibrantComparisonMap d X Y ≫ (π).map (f ⊗ₘ g) := by
  unfold cofibrantComparisonMap
  rw [← (π).map_comp, ← (π).map_comp, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  exact (π).congr_map (congrArg₂ (fun a b => a ⊗ₘ b) (d.q.naturality f) (d.q.naturality g))

end HomotopicalAlgebra.DerivedTensorConstructions
