/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.IdempotentCoequalizerSplit
public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer

/-!
# Identifying the internally split endpoint with an actual original retract

The original inclusion, projection and their actual retract equation
construct the endpoint idempotent. They make the original projection a split
coequalizer of that idempotent and the identity, so Mathlib's uniqueness of
colimits identifies the chosen coequalizer with the original retract. Both
comparison maps are expressed in those same original maps.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe u v

namespace CategoryTheory.SmallObject.OriginalRetractSplitIso

open Limits

variable {C : Type u} [Category.{v} C] {R E : C}
  (i : R ⟶ E) (r : E ⟶ R) (hir : i ≫ r = 𝟙 R)

/-- The actual original retract induces this same endpoint idempotent. -/
abbrev idempotent : E ⟶ E := r ≫ i

include hir in
/-- The original retract equation proves actual idempotence. -/
theorem idempotent_idempotent : idempotent i r ≫ idempotent i r = idempotent i r := by
  change (r ≫ i) ≫ (r ≫ i) = r ≫ i
  rw [Category.assoc, ← Category.assoc i r i, hir, Category.id_comp]

include hir in
/-- The original projection is fixed by the same actual endpoint idempotent. -/
theorem idempotent_projection : idempotent i r ≫ r = r := by
  change (r ≫ i) ≫ r = r
  rw [Category.assoc, hir, Category.comp_id]

include hir in
/-- The original inclusion is fixed by the same actual endpoint idempotent. -/
theorem inclusion_idempotent : i ≫ idempotent i r = i := by
  change i ≫ (r ≫ i) = i
  rw [← Category.assoc, hir, Category.id_comp]

/-- For `i : R ⟶ E` and `r : E ⟶ R` with `i ≫ r = 𝟙 R`, the projection
`r` is a split coequalizer of the ordered parallel pair `(r ≫ i, 𝟙 E)`.
Its right section is `i`, and its left section is `𝟙 E`; the order of the
parallel maps and these two sections is part of the split-coequalizer data. -/
def isSplitCoequalizer : IsSplitCoequalizer (idempotent i r) (𝟙 E) r where
  rightSection := i
  leftSection := 𝟙 E
  condition := by rw [idempotent_projection i r hir, Category.id_comp]
  rightSection_π := hir
  leftSection_bottom := Category.id_comp _
  leftSection_top := Category.id_comp _

variable [HasCoequalizers C]

/-- The chosen coequalizer of the idempotent and the identity is the original retract. -/
def iso : IdempotentCoequalizerSplit.obj (idempotent i r) ≅ R :=
  (coequalizerIsCoequalizer (idempotent i r) (𝟙 E)).coconePointUniqueUpToIso
    (isSplitCoequalizer i r hir).isCoequalizer

/-- The forward comparison retains the original selected projection function. -/
theorem projection_iso_hom :
    IdempotentCoequalizerSplit.projection (idempotent i r) ≫ (iso i r hir).hom = r :=
  (coequalizerIsCoequalizer (idempotent i r) (𝟙 E)).comp_coconePointUniqueUpToIso_hom
    (isSplitCoequalizer i r hir).isCoequalizer WalkingParallelPair.one

/-- The backward comparison is the original inclusion followed by the selected projection. -/
theorem iso_inv :
    (iso i r hir).inv = i ≫ IdempotentCoequalizerSplit.projection (idempotent i r) := by
  apply Cofork.IsColimit.hom_ext (isSplitCoequalizer i r hir).isCoequalizer
  change r ≫ (iso i r hir).inv = r ≫ i ≫ IdempotentCoequalizerSplit.projection (idempotent i r)
  rw [← Category.assoc]
  exact ((coequalizerIsCoequalizer (idempotent i r) (𝟙 E)).comp_coconePointUniqueUpToIso_inv
    (isSplitCoequalizer i r hir).isCoequalizer WalkingParallelPair.one).trans
    ((coequalizer.condition (idempotent i r) (𝟙 E)).trans (Category.id_comp _)).symm

end CategoryTheory.SmallObject.OriginalRetractSplitIso
