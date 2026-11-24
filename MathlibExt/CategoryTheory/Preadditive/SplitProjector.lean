/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Preadditive.SplitKernel
public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

import Mathlib.Tactic.Abel

/-!
# Kernel maps of split projectors

The complementary projector of an idempotent factors through its kernel inclusion. Morphisms
commuting with the projectors induce maps of these kernels, and the split maps form a retract in
the arrow category. The complementary construction gives the cokernel comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits

namespace CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {X : C} (p : X ⟶ X) (hp : p ≫ p = p) [HasKernel p]

/--
The complementary projector factors through the kernel, retaining exactly the original kernel
object and inclusion.
-/
def projectorKernelSplit : SplitMono (kernel.ι p) where
  retraction := kernel.lift p (𝟙 X - p) (by
    rw [Preadditive.sub_comp, Category.id_comp, hp, sub_self])
  id := by
    apply (cancel_mono (kernel.ι p)).1
    rw [Category.assoc, kernel.lift_ι, Preadditive.comp_sub,
      Category.comp_id, kernel.condition, sub_zero, Category.id_comp]

/-- The retraction is the factorization of the original complementary projector. -/
def projectorKernelRetraction : X ⟶ kernel p :=
  (projectorKernelSplit p hp).retraction

/-- Its composite with the original kernel inclusion is exactly 1-p. -/
@[reassoc]
theorem projectorKernelRetraction_ι :
    projectorKernelRetraction p hp ≫ kernel.ι p = 𝟙 X - p := by
  dsimp only [projectorKernelRetraction, projectorKernelSplit]
  exact kernel.lift_ι _ _ _

/-- The splitting earns the split identity. -/
@[reassoc]
theorem ι_projectorKernelRetraction :
    kernel.ι p ≫ projectorKernelRetraction p hp = 𝟙 (kernel p) :=
  (projectorKernelSplit p hp).id

/-- An projector kernel is a retract, with its original inclusion. -/
def projectorKernelRetract : Retract (kernel p) X where
  i := kernel.ι p
  r := projectorKernelRetraction p hp
  retract := ι_projectorKernelRetraction p hp

/-- The existing split-complement cokernel comparison supplies the canonical comparison. -/
def projectorCokernelIsoKernel [HasCokernel p] : cokernel p ≅ kernel p :=
  cokernelSplitComplementIso p (kernel.ι p) (projectorKernelRetraction p hp)
    (ι_projectorKernelRetraction p hp) (by
      rw [projectorKernelRetraction_ι]
      abel)

/-- The original cokernel projection computes the original complementary retraction. -/
@[reassoc]
theorem projectorCokernelIsoKernel_π_hom [HasCokernel p] :
    cokernel.π p ≫ (projectorCokernelIsoKernel p hp).hom =
      projectorKernelRetraction p hp :=
  cokernelSplitComplementIso_π_hom _ _ _ _ _

variable {Y : C} (q : Y ⟶ Y) (hq : q ≫ q = q) [HasKernel q]
  (f : X ⟶ Y) (w : p ≫ f = f ≫ q)

/-- Restriction preserves the original projector complements and map f. -/
@[reassoc]
theorem projectorKernelRetraction_naturality :
    f ≫ projectorKernelRetraction q hq =
      projectorKernelRetraction p hp ≫ kernel.map p q f f w := by
  apply (cancel_mono (kernel.ι q)).1
  have hm : kernel.map p q f f w ≫ kernel.ι q = kernel.ι p ≫ f :=
    kernel.lift_ι _ _ _
  rw [Category.assoc, projectorKernelRetraction_ι, Category.assoc, hm,
    ← Category.assoc, projectorKernelRetraction_ι,
    Preadditive.comp_sub, Preadditive.sub_comp,
    Category.comp_id, Category.id_comp, w]

/-- The induced kernel arrow is a retract of the original arrow, not a comparison premise. -/
def projectorKernelMapRetractArrow : RetractArrow (kernel.map p q f f w) f where
  i := Arrow.homMk (kernel.ι p) (kernel.ι q) (by
    change kernel.ι p ≫ f = kernel.map p q f f w ≫ kernel.ι q
    exact (kernel.lift_ι _ _ _).symm)
  r := Arrow.homMk (projectorKernelRetraction p hp) (projectorKernelRetraction q hq)
    (projectorKernelRetraction_naturality p hp q hq f w).symm
  retract := by
    apply Arrow.hom_ext
    · exact ι_projectorKernelRetraction p hp
    · exact ι_projectorKernelRetraction q hq

end CategoryTheory.Limits

namespace CategoryTheory.Limits

section MappedKernels

universe u₁ u₂ u₃ v₁ v₂ v₃

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (F : C₁ ⥤ D) (G : C₂ ⥤ D) [F.Additive] [G.Additive]
  {X : C₁} {Y : C₂} (p : X ⟶ X) (q : Y ⟶ Y)
  [HasKernel p] [HasKernel q]
  [PreservesLimit (parallelPair p 0) F] [PreservesLimit (parallelPair q 0) G]
  (f : F.obj X ⟶ G.obj Y) (w : F.map p ≫ f = f ≫ G.map q)

/-- A map between two original functor images restricts through the kernel comparisons. -/
def mappedProjectorKernelMap : F.obj (kernel p) ⟶ G.obj (kernel q) :=
  (PreservesKernel.iso F p).hom ≫ kernel.map (F.map p) (G.map q) f f w ≫
    (PreservesKernel.iso G q).inv

/-- Both original mapped inclusions remain the exact coordinate maps. -/
@[reassoc]
theorem mappedProjectorKernelMap_ι :
    mappedProjectorKernelMap F G p q f w ≫ G.map (kernel.ι q) =
      F.map (kernel.ι p) ≫ f := by
  simp only [mappedProjectorKernelMap, Category.assoc, PreservesKernel.iso_inv_ι,
    kernel.map, kernel.lift_ι]
  rw [← Category.assoc, PreservesKernel.iso_hom, kernelComparison_comp_ι]

end MappedKernels

end CategoryTheory.Limits
