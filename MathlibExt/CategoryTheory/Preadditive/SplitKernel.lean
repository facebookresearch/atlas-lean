/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Preadditive.SplitCokernel
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels

/-!
# Kernels of split complementary projectors

In a preadditive category, a split pair `i : Y → X`, `r : X → Y`
with `i ≫ r = 𝟙 Y` makes `i` a kernel of the complementary endomorphism
`q = 𝟙 X - r ≫ i`. If a kernel object is chosen, it is canonically
isomorphic to `Y`; these comparisons are natural for compatible maps of
the split pairs.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits Opposite

namespace CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {X Y : C} (q : X ⟶ X) (i : Y ⟶ X) (r : X ⟶ Y)
  (hi : i ≫ r = 𝟙 Y) (hq : q = 𝟙 X - r ≫ i)

include hi hq in
/-- In a preadditive category `C`, let `i : Y → X`, `r : X → Y` satisfy
`i ≫ r = 𝟙 Y`, and let `q = 𝟙 X - r ≫ i`. The inclusion is
annihilated by the complement: `i ≫ q = 0`. -/
@[reassoc]
theorem inclusion_comp_splitComplement : i ≫ q = 0 := by
  rw [hq, Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hi,
    Category.id_comp, sub_self]

/-- In a preadditive category `C`, let `i : Y → X`, `r : X → Y` satisfy
`i ≫ r = 𝟙 Y`, and let `q = 𝟙 X - r ≫ i`. The map
`i : Y → X` is a kernel of `q`; its universal property does not
require a separate chosen kernel object. -/
def splitComplementIsKernel :
    IsLimit (KernelFork.ofι i (inclusion_comp_splitComplement q i r hi hq)) := by
  have hiOp : r.op ≫ i.op = 𝟙 (op Y) := by
    rw [← op_comp, hi, op_id]
  have hqOp : q.op = 𝟙 (op X) - i.op ≫ r.op := by
    rw [hq, op_sub, op_id, op_comp]
  exact CokernelCofork.IsColimit.ofπUnop i.op
    (splitComplement_comp_retraction q.op r.op i.op hiOp hqOp)
    (splitComplementIsCokernel q.op r.op i.op hiOp hqOp)

variable [HasKernel q]

/-- In a preadditive category `C`, let `i : Y → X`, `r : X → Y` satisfy
`i ≫ r = 𝟙 Y`, and let `q = 𝟙 X - r ≫ i`. If a kernel
of `q` exists, there is a canonical isomorphism `kernel q ≅ Y`
whose comparison respects the original inclusion. -/
def kernelSplitComplementIso : kernel q ≅ Y :=
  (kernelIsKernel q).conePointUniqueUpToIso (splitComplementIsKernel q i r hi hq)

/-- In a preadditive category `C`, let `i : Y → X`, `r : X → Y` satisfy
`i ≫ r = 𝟙 Y`, and let `q = 𝟙 X - r ≫ i`. If the kernel
of `q` exists, its comparison `e : kernel q ≅ Y` satisfies
`e.hom ≫ i = kernel.ι q`. -/
@[reassoc]
theorem kernelSplitComplementIso_hom_ι :
    (kernelSplitComplementIso q i r hi hq).hom ≫ i = kernel.ι q :=
  IsLimit.conePointUniqueUpToIso_hom_comp (kernelIsKernel q)
    (splitComplementIsKernel q i r hi hq) WalkingParallelPair.zero

/-- In a preadditive category `C`, let `i : Y → X`, `r : X → Y` satisfy
`i ≫ r = 𝟙 Y`, and let `q = 𝟙 X - r ≫ i`. If the kernel
of `q` exists, the inverse comparison satisfies
`e.inv ≫ kernel.ι q = i`. -/
@[reassoc]
theorem kernelSplitComplementIso_inv_ι :
    (kernelSplitComplementIso q i r hi hq).inv ≫ kernel.ι q = i :=
  IsLimit.conePointUniqueUpToIso_inv_comp (kernelIsKernel q)
    (splitComplementIsKernel q i r hi hq) WalkingParallelPair.zero

/-- In a preadditive category `C`, let `i : Y → X`, `r : X → Y` satisfy
`i ≫ r = 𝟙 Y`, and let `q = 𝟙 X - r ≫ i`. If the kernel
of `q` exists, the forward comparison to `Y` is the kernel
inclusion followed by `r`: `e.hom = kernel.ι q ≫ r`. -/
theorem kernelSplitComplementIso_hom :
    (kernelSplitComplementIso q i r hi hq).hom = kernel.ι q ≫ r := by
  calc
    _ = (kernelSplitComplementIso q i r hi hq).hom ≫ (i ≫ r) := by
      rw [hi, Category.comp_id]
    _ = ((kernelSplitComplementIso q i r hi hq).hom ≫ i) ≫ r :=
      (Category.assoc _ _ _).symm
    _ = _ := by rw [kernelSplitComplementIso_hom_ι]

variable {X' Y' : C} (q' : X' ⟶ X') (i' : Y' ⟶ X') (r' : X' ⟶ Y')
  (hi' : i' ≫ r' = 𝟙 Y') (hq' : q' = 𝟙 X' - r' ≫ i') [HasKernel q']

/-- In a preadditive category `C`, take two split pairs `(i,r)` and
`(i′,r′)` with complementary endomorphisms `q`, `q′` and existing
kernels. For `f : X → X′`, `g : Y → Y′` with
`q ≫ f = f ≫ q′` and `i ≫ f = g ≫ i′`, the induced kernel map
commutes with the inverse comparisons from `Y` and `Y′`. -/
@[reassoc]
theorem kernelSplitComplementIso_inv_naturality
    (f : X ⟶ X') (g : Y ⟶ Y') (w : q ≫ f = f ≫ q')
    (hι : i ≫ f = g ≫ i') :
    (kernelSplitComplementIso q i r hi hq).inv ≫ kernel.map q q' f f w =
      g ≫ (kernelSplitComplementIso q' i' r' hi' hq').inv := by
  have hMap : kernel.map q q' f f w ≫ kernel.ι q' = kernel.ι q ≫ f :=
    kernel.lift_ι _ _ _
  apply (cancel_mono (kernel.ι q')).1
  calc
    _ = (kernelSplitComplementIso q i r hi hq).inv ≫ (kernel.ι q ≫ f) := by
      rw [Category.assoc, hMap]
    _ = i ≫ f := by rw [← Category.assoc, kernelSplitComplementIso_inv_ι]
    _ = g ≫ i' := hι
    _ = _ := by rw [Category.assoc, kernelSplitComplementIso_inv_ι]

/-- In a preadditive category `C`, take two split pairs with complements
`q`, `q′` and existing kernels. If `f : X → X′`, `g : Y → Y′`
commute with the complements and inclusions, the induced kernel
map commutes with the canonical forward comparisons to `Y` and `Y′`. -/
@[reassoc]
theorem kernelSplitComplementIso_naturality
    (f : X ⟶ X') (g : Y ⟶ Y') (w : q ≫ f = f ≫ q')
    (hι : i ≫ f = g ≫ i') :
    kernel.map q q' f f w ≫ (kernelSplitComplementIso q' i' r' hi' hq').hom =
      (kernelSplitComplementIso q i r hi hq).hom ≫ g := by
  apply (cancel_epi (kernelSplitComplementIso q i r hi hq).inv).1
  calc
    _ = ((kernelSplitComplementIso q i r hi hq).inv ≫ kernel.map q q' f f w) ≫
        (kernelSplitComplementIso q' i' r' hi' hq').hom :=
      (Category.assoc _ _ _).symm
    _ = (g ≫ (kernelSplitComplementIso q' i' r' hi' hq').inv) ≫
        (kernelSplitComplementIso q' i' r' hi' hq').hom :=
      congrArg (fun m => m ≫ (kernelSplitComplementIso q' i' r' hi' hq').hom)
        (kernelSplitComplementIso_inv_naturality q i r hi hq q' i' r' hi' hq' f g w hι)
    _ = g := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = _ := by rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end CategoryTheory.Limits
