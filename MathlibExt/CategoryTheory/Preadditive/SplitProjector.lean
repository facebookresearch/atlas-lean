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
# Kernels and complements of idempotents

In a preadditive category, the complementary idempotent `1-p` of
`p : X → X` factors through `kernel p`, making the kernel a retract
of `X`. This identifies `cokernel p` with `kernel p` when both exist.
Compatible maps of idempotents restrict to their kernels; additive
functors preserving the relevant kernels carry these restriction maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits

namespace CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {X : C} (p : X ⟶ X) (hp : p ≫ p = p) [HasKernel p]

/-- In a preadditive category `C`, let `p : X → X` be idempotent
and suppose its kernel exists. The kernel inclusion
`kernel.ι p : kernel p → X` is a split monomorphism; its retraction
is obtained by factoring `1-p` through the kernel. -/
def projectorKernelSplit : SplitMono (kernel.ι p) where
  retraction := kernel.lift p (𝟙 X - p) (by
    rw [Preadditive.sub_comp, Category.id_comp, hp, sub_self])
  id := by
    apply (cancel_mono (kernel.ι p)).1
    rw [Category.assoc, kernel.lift_ι, Preadditive.comp_sub,
      Category.comp_id, kernel.condition, sub_zero, Category.id_comp]

/-- In a preadditive category `C`, let `p : X → X` be idempotent
and suppose its kernel exists. The complementary
endomorphism `1-p` factors as a map `X → kernel p` followed by
the original kernel inclusion. This defines its canonical retraction. -/
def projectorKernelRetraction : X ⟶ kernel p :=
  (projectorKernelSplit p hp).retraction

/-- In a preadditive category `C`, let `p : X → X` be idempotent
and suppose its kernel exists. The canonical
retraction has composite with the kernel inclusion equal to
`1-p`: `projectorKernelRetraction ≫ kernel.ι p = 𝟙 X-p`. -/
@[reassoc]
theorem projectorKernelRetraction_ι :
    projectorKernelRetraction p hp ≫ kernel.ι p = 𝟙 X - p := by
  dsimp only [projectorKernelRetraction, projectorKernelSplit]
  exact kernel.lift_ι _ _ _

/-- In a preadditive category `C`, let `p : X → X` be idempotent
and suppose its kernel exists. The kernel inclusion
followed by the complementary retraction is the identity of
`kernel p`, so these two maps give a split pair. -/
@[reassoc]
theorem ι_projectorKernelRetraction :
    kernel.ι p ≫ projectorKernelRetraction p hp = 𝟙 (kernel p) :=
  (projectorKernelSplit p hp).id

/-- In a preadditive category `C`, let `p : X → X` be idempotent
and suppose its kernel exists. The inclusion
and complementary retraction exhibit `kernel p` as a retract
of `X`, with the original kernel object and inclusion. -/
def projectorKernelRetract : Retract (kernel p) X where
  i := kernel.ι p
  r := projectorKernelRetraction p hp
  retract := ι_projectorKernelRetraction p hp

/-- In a preadditive category `C`, let `p : X → X` be idempotent
and suppose its kernel exists. If its cokernel
also exists, the split pair gives a canonical isomorphism
`cokernel p ≅ kernel p`. -/
def projectorCokernelIsoKernel [HasCokernel p] : cokernel p ≅ kernel p :=
  cokernelSplitComplementIso p (kernel.ι p) (projectorKernelRetraction p hp)
    (ι_projectorKernelRetraction p hp) (by
      rw [projectorKernelRetraction_ι]
      abel)

/-- In a preadditive category `C`, let `p : X → X` be idempotent
and suppose its kernel exists. If its cokernel
also exists, the cokernel projection followed by
`cokernel p ≅ kernel p` equals the complementary retraction
`X → kernel p`. -/
@[reassoc]
theorem projectorCokernelIsoKernel_π_hom [HasCokernel p] :
    cokernel.π p ≫ (projectorCokernelIsoKernel p hp).hom =
      projectorKernelRetraction p hp :=
  cokernelSplitComplementIso_π_hom _ _ _ _ _

variable {Y : C} (q : Y ⟶ Y) (hq : q ≫ q = q) [HasKernel q]
  (f : X ⟶ Y) (w : p ≫ f = f ≫ q)

/-- In a preadditive category `C`, let `p : X → X`, `q : Y → Y`
be idempotents with kernels and let `f : X → Y` satisfy
`p ≫ f = f ≫ q`. The complementary retractions satisfy
`f ≫ r_q = r_p ≫ kernel.map(p,q,f,f)`. -/
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

/-- In a preadditive category `C`, let `p`, `q` be idempotents with
kernels and `f : X → Y` commute with them. The induced kernel
arrow `kernel p → kernel q` is a retract of the original arrow
`f`, using the two complementary kernel splittings. -/
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

/-- Let `C₁`, `C₂`, `D` be preadditive categories, `F : C₁ → D`,
`G : C₂ → D` additive, and `p : X → X`, `q : Y → Y` have
kernels preserved by `F` and `G`. If `F(p) ≫ f = f ≫ G(q)`,
there is a canonical restriction `F(kernel p) → G(kernel q)`. -/
def mappedProjectorKernelMap : F.obj (kernel p) ⟶ G.obj (kernel q) :=
  (PreservesKernel.iso F p).hom ≫ kernel.map (F.map p) (G.map q) f f w ≫
    (PreservesKernel.iso G q).inv

/-- For additive functors `F : C₁ → D`, `G : C₂ → D` between
preadditive categories, endomorphisms `p`, `q` with preserved
kernels, and `F(p) ≫ f = f ≫ G(q)`, the restricted kernel map
satisfies `restriction ≫ G(kernel.ι q) = F(kernel.ι p) ≫ f`. -/
@[reassoc]
theorem mappedProjectorKernelMap_ι :
    mappedProjectorKernelMap F G p q f w ≫ G.map (kernel.ι q) =
      F.map (kernel.ι p) ≫ f := by
  simp only [mappedProjectorKernelMap, Category.assoc, PreservesKernel.iso_inv_ι,
    kernel.map, kernel.lift_ι]
  rw [← Category.assoc, PreservesKernel.iso_hom, kernelComparison_comp_ι]

end MappedKernels

end CategoryTheory.Limits
