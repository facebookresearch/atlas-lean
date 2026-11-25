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
# Actual kernel components of native graded objects

The existing discrete-diagram equivalence supplies kernel existence. The
existing evaluation preservation theorem and native `PreservesKernel.iso`
identify each actual chosen graded kernel component with the actual native
kernel of the component map. No new kernel construction engine is used.
Object, Hom and grading worlds remain independent.
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

/-- Kernel existence follows from the existing equivalence with discrete
diagrams and native functor-category limits. -/
instance hasKernels : HasKernels (GradedObject I C) := by
  letI : HasLimitsOfShape WalkingParallelPair (GradedObject I C) :=
    Adjunction.hasLimitsOfShape_of_equivalence (piEquivalenceFunctorDiscrete I C).functor
  infer_instance

/-- Evaluation of the actual chosen graded kernel is canonically the
actual component kernel. -/
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

/-- The actual component of a graded kernel inclusion is monic. -/
instance mono_kernel_component {X Y : GradedObject I C} (f : X ⟶ Y) (i : I) :
    Mono ((kernel.ι f) i) := by
  rw [← kernelComponentIso_hom_ι f i]
  infer_instance

/-- A zero component equation has an isomorphic actual kernel inclusion
in that component. This is a native kernel fact, not a homology interchange. -/
theorem isIso_kernel_component_of_eq_zero {X Y : GradedObject I C}
    (f : X ⟶ Y) (i : I) (h : f i = 0) : IsIso ((kernel.ι f) i) := by
  letI : IsIso (kernel.ι (f i)) := KernelFork.IsLimit.isIso_ι
    (KernelFork.ofι (kernel.ι (f i)) (kernel.condition (f i))) (kernelIsKernel (f i)) h
  rw [← kernelComponentIso_hom_ι f i]
  infer_instance

end CategoryTheory.GradedObject
