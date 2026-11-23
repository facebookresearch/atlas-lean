/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.OneSided

/-!
# Functorial composition of the original bimodules

The actual bicategory of monoids and bimodules supplies the curried tensor
functor. Its maps are the existing two whiskerings on the original
coequalizers. The projection formulas retain both original module maps.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped MonoidalCategory

namespace Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {A B D : Mon C}

/-- The original composable bimodule tensor, using the existing bicategory composition functor. -/
def tensorCurried (A B D : Mon C) : Bimod A B ⥤ Bimod B D ⥤ Bimod A D :=
  @Bicategory.precomposing (Mon C) (monBicategory (C := C)) A B D

/-- The same original relative tensor with a fixed left bimodule. -/
def tensorLeftFunctor (M : Bimod A B) : Bimod B D ⥤ Bimod A D :=
  (tensorCurried A B D).obj M

/-- The same original relative tensor with a fixed right bimodule. -/
def tensorRightFunctor (N : Bimod B D) : Bimod A B ⥤ Bimod A D :=
  @Bicategory.postcomp (Mon C) (monBicategory (C := C)) B D A N

/-- The complete curried tensor keeps the literal original coequalizer bimodule. -/
theorem tensorCurried_obj (M : Bimod A B) (N : Bimod B D) :
    ((tensorCurried A B D).obj M).obj N = tensorBimod M N := rfl

/-- The complete original map in the first variable is its existing right whiskering. -/
theorem tensorCurried_map_app {M M' : Bimod A B} (f : M ⟶ M') (N : Bimod B D) :
    ((tensorCurried A B D).map f).app N = whiskerRight f N := rfl

/-- The complete original map in the second variable is its existing left whiskering. -/
theorem tensorCurried_obj_map (M : Bimod A B) {N N' : Bimod B D} (g : N ⟶ N') :
    ((tensorCurried A B D).obj M).map g = whiskerLeft M g := rfl

/-- The actual quotient projection, before imposing the original balancing equation. -/
def tensorProjection (M : Bimod A B) (N : Bimod B D) :
    M.X ⊗ N.X ⟶ (tensorBimod M N).X :=
  coequalizer.π (M.actRight ▷ N.X) ((α_ M.X B.X N.X).hom ≫ M.X ◁ N.actLeft)

/-- Every original first-variable map is retained by the quotient square. -/
theorem tensorProjection_whiskerRight {M M' : Bimod A B} (f : M ⟶ M') (N : Bimod B D) :
    tensorProjection M N ≫ (whiskerRight f N).hom =
      (f.hom ▷ N.X) ≫ tensorProjection M' N := by
  simp only [tensorProjection, whiskerRight_hom, coequalizer.π, ι_colimMap,
    parallelPairHom_app_one]

/-- Every original second-variable map is retained by the same quotient square. -/
theorem tensorProjection_whiskerLeft (M : Bimod A B) {N N' : Bimod B D} (g : N ⟶ N') :
    tensorProjection M N ≫ (whiskerLeft M g).hom =
      (M.X ◁ g.hom) ≫ tensorProjection M N' := by
  simp only [tensorProjection, whiskerLeft_hom, coequalizer.π, ι_colimMap,
    parallelPairHom_app_one]

/-- Both original bimodule maps act on the actual relative tensor quotient. -/
def tensorMap {M M' : Bimod A B} {N N' : Bimod B D} (f : M ⟶ M') (g : N ⟶ N') :
    tensorBimod M N ⟶ tensorBimod M' N' :=
  whiskerRight f N ≫ whiskerLeft M' g

/-- The whole tensor-map square keeps both original underlying tensor maps. -/
theorem tensorMap_projection {M M' : Bimod A B} {N N' : Bimod B D}
    (f : M ⟶ M') (g : N ⟶ N') :
    tensorProjection M N ≫ (tensorMap f g).hom =
      (f.hom ⊗ₘ g.hom) ≫ tensorProjection M' N' := by
  rw [tensorMap, comp_hom', ← Category.assoc, tensorProjection_whiskerRight,
    Category.assoc, tensorProjection_whiskerLeft, ← Category.assoc, ← tensorHom_def]

end Bimod
