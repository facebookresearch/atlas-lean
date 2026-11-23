/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.IdempotentCoequalizerSplit

/-!
# Identifying the internally split endpoint with an actual original retract

The original inclusion, projection and their actual retract equation
construct the endpoint idempotent and its coequalizer comparison Iso.
Every comparison function is expressed in those same original maps.
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

variable [HasCoequalizers C]

/-- The actual forward comparison uses the constructed split inclusion and original projection. -/
def toOriginal : IdempotentCoequalizerSplit.obj (idempotent i r) ⟶ R :=
  IdempotentCoequalizerSplit.inclusion (idempotent i r) (idempotent_idempotent i r hir) ≫ r

/-- The actual backward comparison uses the original inclusion and selected split projection. -/
def fromOriginal : R ⟶ IdempotentCoequalizerSplit.obj (idempotent i r) :=
  i ≫ IdempotentCoequalizerSplit.projection (idempotent i r)

/-- The two actual comparison functions retract onto the original given object. -/
theorem from_to : fromOriginal i r ≫ toOriginal i r hir = 𝟙 R := by
  calc
    _ = i ≫ ((IdempotentCoequalizerSplit.projection (idempotent i r) ≫
        IdempotentCoequalizerSplit.inclusion (idempotent i r)
          (idempotent_idempotent i r hir)) ≫ r) := by
      simp only [fromOriginal, toOriginal, Category.assoc]
    _ = i ≫ (idempotent i r ≫ r) := by
      rw [IdempotentCoequalizerSplit.projection_inclusion]
    _ = i ≫ r := by rw [idempotent_projection i r hir]
    _ = _ := hir

/-- The same two actual functions retract onto the internally chosen split endpoint. -/
theorem to_from : toOriginal i r hir ≫ fromOriginal i r =
    𝟙 (IdempotentCoequalizerSplit.obj (idempotent i r)) := by
  calc
    _ = IdempotentCoequalizerSplit.inclusion (idempotent i r)
        (idempotent_idempotent i r hir) ≫
        (idempotent i r ≫ IdempotentCoequalizerSplit.projection (idempotent i r)) := by
      simp only [toOriginal, fromOriginal, idempotent, Category.assoc]
    _ = IdempotentCoequalizerSplit.inclusion (idempotent i r)
        (idempotent_idempotent i r hir) ≫
        IdempotentCoequalizerSplit.projection (idempotent i r) := by
      rw [IdempotentCoequalizerSplit.idempotent_projection]
    _ = _ := IdempotentCoequalizerSplit.inclusion_projection _ _

/-- The original given retract is identified by the constructed actual comparison maps. -/
def iso : IdempotentCoequalizerSplit.obj (idempotent i r) ≅ R where
  hom := toOriginal i r hir
  inv := fromOriginal i r
  hom_inv_id := to_from i r hir
  inv_hom_id := from_to i r hir

/-- The actual whole forward comparison retains the original selected projection function. -/
theorem projection_toOriginal :
    IdempotentCoequalizerSplit.projection (idempotent i r) ≫ toOriginal i r hir = r := by
  calc
    _ = (IdempotentCoequalizerSplit.projection (idempotent i r) ≫
        IdempotentCoequalizerSplit.inclusion (idempotent i r)
          (idempotent_idempotent i r hir)) ≫ r := (Category.assoc _ _ _).symm
    _ = idempotent i r ≫ r := by rw [IdempotentCoequalizerSplit.projection_inclusion]
    _ = _ := idempotent_projection i r hir

end CategoryTheory.SmallObject.OriginalRetractSplitIso
