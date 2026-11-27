/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Kernels and cokernels of biproduct maps

In a category with zero morphisms, the biproduct of a family's kernel
inclusions is a kernel of its biproduct map. Dually, the biproduct of its
cokernel projections is a cokernel. The comparisons are characterized by
these inclusions and projections, assuming only the component kernels or
cokernels and the indicated biproducts.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

noncomputable section

universe u v w

namespace CategoryTheory.Limits

section Kernels

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {I : Type w} {X Y : I → C} (f : ∀ i, X i ⟶ Y i)
  [HasBiproduct X] [HasBiproduct Y] [∀ i, HasKernel (f i)]
  [HasBiproduct (fun i => kernel (f i))]

/-- The biproduct of the given kernel inclusions. -/
def biproductKernelInclusion : (⨁ fun i => kernel (f i)) ⟶ ⨁ X :=
  biproduct.map (fun i => kernel.ι (f i))

/-- The given kernel equations hold for the biproduct map. -/
theorem biproductKernelInclusion_comp_map :
    biproductKernelInclusion f ≫ biproduct.map f = 0 := by
  apply biproduct.hom_ext
  intro i
  simp only [biproductKernelInclusion, Category.assoc, biproduct.map_π,
    biproduct.map_π_assoc, kernel.condition, comp_zero, zero_comp]

/-- The given component kernels construct the universal kernel fork. -/
def biproductKernelForkIsLimit :
    IsLimit (KernelFork.ofι (biproductKernelInclusion f)
      (biproductKernelInclusion_comp_map f)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {_} g hg => biproduct.lift (fun i =>
      kernel.lift (f i) (g ≫ biproduct.π X i) (by
        have h := congrArg (fun k => k ≫ biproduct.π Y i) hg
        simpa only [Category.assoc, biproduct.map_π, zero_comp] using h)))
    (fun {_} g hg => by
      apply biproduct.hom_ext
      intro i
      simp only [biproductKernelInclusion, Category.assoc, biproduct.map_π,
        biproduct.lift_π_assoc, kernel.lift_ι])
    (fun {_} g hg m hm => by
      apply biproduct.hom_ext
      intro i
      apply (cancel_mono (kernel.ι (f i))).mp
      simp only [Category.assoc, biproduct.lift_π, kernel.lift_ι]
      have h := congrArg (fun k => k ≫ biproduct.π X i) hm
      simpa only [biproductKernelInclusion, Category.assoc, biproduct.map_π] using h)

variable [HasKernel (biproduct.map f)]

/-- The given kernel of the finite biproduct map is its kernel biproduct. -/
def biproductKernelIso : (⨁ fun i => kernel (f i)) ≅ kernel (biproduct.map f) :=
  IsLimit.conePointUniqueUpToIso (biproductKernelForkIsLimit f) (limit.isLimit _)

/-- The comparison preserves the given kernel inclusions. -/
theorem biproductKernelIso_hom_comp_ι :
    (biproductKernelIso f).hom ≫ kernel.ι (biproduct.map f) =
      biproductKernelInclusion f :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

end Kernels

section Cokernels

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {I : Type w} {X Y : I → C} (f : ∀ i, X i ⟶ Y i)
  [HasBiproduct X] [HasBiproduct Y] [∀ i, HasCokernel (f i)]
  [HasBiproduct (fun i => cokernel (f i))]

/-- The biproduct of the given cokernel quotients. -/
def biproductCokernelQuotient : (⨁ Y) ⟶ ⨁ fun i => cokernel (f i) :=
  biproduct.map (fun i => cokernel.π (f i))

/-- The given cokernel equations hold for the biproduct map. -/
theorem map_comp_biproductCokernelQuotient :
    biproduct.map f ≫ biproductCokernelQuotient f = 0 := by
  apply biproduct.hom_ext'
  intro i
  simp only [biproductCokernelQuotient, biproduct.ι_map_assoc,
    biproduct.ι_map, comp_zero]
  rw [← Category.assoc, cokernel.condition, zero_comp]

/-- The given component cokernels construct the universal cokernel cofork. -/
def biproductCokernelCoforkIsColimit :
    IsColimit (CokernelCofork.ofπ (biproductCokernelQuotient f)
      (map_comp_biproductCokernelQuotient f)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun {_} g hg => biproduct.desc (fun i =>
      cokernel.desc (f i) (biproduct.ι Y i ≫ g) (by
        have h := congrArg (fun k => biproduct.ι X i ≫ k) hg
        simpa only [biproduct.ι_map_assoc, Category.assoc, comp_zero] using h)))
    (fun {_} g hg => by
      apply biproduct.hom_ext'
      intro i
      simp only [biproductCokernelQuotient, biproduct.ι_map_assoc,
        biproduct.ι_desc, cokernel.π_desc])
    (fun {_} g hg m hm => by
      apply biproduct.hom_ext'
      intro i
      apply (cancel_epi (cokernel.π (f i))).mp
      simp only [← Category.assoc, biproduct.ι_desc, cokernel.π_desc]
      have h := congrArg (fun k => biproduct.ι Y i ≫ k) hm
      simpa only [biproductCokernelQuotient, biproduct.ι_map_assoc,
        Category.assoc] using h)

variable [HasCokernel (biproduct.map f)]

/-- The given cokernel of the biproduct map is its cokernel biproduct. -/
def biproductCokernelIso : cokernel (biproduct.map f) ≅ ⨁ fun i => cokernel (f i) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (biproductCokernelCoforkIsColimit f)

/-- The comparison preserves the given cokernel quotients. -/
theorem π_comp_biproductCokernelIso_hom :
    cokernel.π (biproduct.map f) ≫ (biproductCokernelIso f).hom =
      biproductCokernelQuotient f :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one

end Cokernels

end CategoryTheory.Limits
