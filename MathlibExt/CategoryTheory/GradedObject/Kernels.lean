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

public import MathlibExt.CategoryTheory.GradedObject.Preadditive
public import MathlibExt.CategoryTheory.GradedObject.Evaluation
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Kernels of graded objects and their components

Let C be a preadditive category with kernels and I an arbitrary grading type. The category of
I-graded objects has kernels. Evaluation at i ∈ I identifies the component of the graded
kernel of f with the kernel of f_i in C.

Each component of the kernel inclusion is monic, and it is an isomorphism wherever f_i=0. The
grading type and the object and morphism universes of C are independent.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.GradedObject

variable {I : Type w} {C : Type u} [Category.{v} C] [Preadditive C] [HasKernels C]

local instance evaluationAdditive (i : I) : (eval (C := C) i).Additive where
  map_add := by intros; rfl

local instance coefficientEqualizers : HasEqualizers C := Preadditive.hasEqualizers_of_hasKernels

/-- Let I be an arbitrary type and C a preadditive category with kernels. Then the category
GradedObject I C has kernels. The equivalence with functors on the discrete category of I
gives their existence, and evaluation at each i preserves them. No relation between the
grading, object, and morphism universes is required. -/
instance hasKernels : HasKernels (GradedObject I C) := by
  letI : HasLimitsOfShape WalkingParallelPair (GradedObject I C) :=
    Adjunction.hasLimitsOfShape_of_equivalence (piEquivalenceFunctorDiscrete I C).functor
  infer_instance

/-- Let C be a preadditive category with kernels, I a grading type, and f : X → Y a morphism of
I-graded objects. For each i ∈ I there is a canonical isomorphism (ker f)_i ≅ ker(f_i),
obtained from preservation of kernels by evaluation at i. It compares the chosen graded kernel
component with the chosen kernel of the component morphism in C. -/
def kernelComponentIso {X Y : GradedObject I C} (f : X ⟶ Y) (i : I) :
    (kernel f) i ≅ kernel (f i) := by
  letI : PreservesLimitsOfShape WalkingParallelPair (eval (C := C) i) :=
    evaluation_preservesLimitsOfShape WalkingParallelPair i
  exact PreservesKernel.iso (eval i) f

@[reassoc (attr := simp)]
theorem kernelComponentIso_hom_ι {X Y : GradedObject I C} (f : X ⟶ Y) (i : I) :
    (kernelComponentIso f i).hom ≫ kernel.ι (f i) = (kernel.ι f) i := by
  rw [kernelComponentIso, PreservesKernel.iso_hom]
  exact kernelComparison_comp_ι f (eval i)

/-- Let C be a preadditive category with kernels, I an arbitrary type, and f : X → Y a graded
morphism. For every i ∈ I, the component (kernel.ι(f))_i : (ker f)_i → X_i is a monomorphism
in C. Under the component kernel isomorphism, it is the inclusion of ker(f_i). -/
instance mono_kernel_component {X Y : GradedObject I C} (f : X ⟶ Y) (i : I) :
    Mono ((kernel.ι f) i) := by
  rw [← kernelComponentIso_hom_ι f i]
  infer_instance

/-- Let C be a preadditive category with kernels, I a grading type, f : X → Y an I-graded
morphism, and i ∈ I. If f_i=0, then (kernel.ι(f))_i : (ker f)_i → X_i is an isomorphism. This
concerns the component of the graded kernel inclusion; evaluation identifies it with the
kernel inclusion of the zero morphism f_i. -/
theorem isIso_kernel_component_of_eq_zero {X Y : GradedObject I C}
    (f : X ⟶ Y) (i : I) (h : f i = 0) : IsIso ((kernel.ι f) i) := by
  letI : IsIso (kernel.ι (f i)) := KernelFork.IsLimit.isIso_ι
    (KernelFork.ofι (kernel.ι (f i)) (kernel.condition (f i))) (kernelIsKernel (f i)) h
  rw [← kernelComponentIso_hom_ι f i]
  infer_instance

end CategoryTheory.GradedObject
