/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.ExactCategory.FiniteResolving
public import Mathlib.CategoryTheory.EssentialImage

/-!
# Actual represented kernels from ambient image closure

Kernel-of-epimorphism closure of the original essential image supplies a
representative of the actual ambient kernel. The original fully faithful
additive functor lifts its inclusion and earns its universal property.
The result uses the existing `KernelLift` and `KernelResolvingData` carriers.

This constructor is the neutral home of the kernel-lifting body used by
the bounded ambient-acyclic top-kernel construction. It exposes the original
choice, complete mapped inclusion and both source universal properties.
No finite resolution, projectivity, source homology, global source kernels,
or comparison outcome is assumed. All four object and Hom universes remain
independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

namespace CategoryTheory.Functor

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive]
variable (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
  F.essImage U → F.essImage V → F.essImage (Limits.kernel f))

include hKernelClosure

omit [Preadditive E] [F.Additive] in
/-- The original essential-image closure applies to every actual mapped epimorphism. -/
theorem kernelOfEpi_mem_essImage {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    F.essImage (Limits.kernel (F.map f)) :=
  hKernelClosure _ ⟨_, ⟨Iso.refl _⟩⟩ ⟨_, ⟨Iso.refl _⟩⟩

variable [F.Full] [F.Faithful]

/-- Lift the actual ambient kernel through the original fully faithful additive functor. -/
def kernelLiftOfEpi {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] : KernelLift F f := by
  let hImage := kernelOfEpi_mem_essImage F hKernelClosure f
  let e := hImage.getIso
  let i : hImage.witness ⟶ P := F.preimage (e.hom ≫ Limits.kernel.ι (F.map f))
  have hi : i ≫ f = 0 := by
    apply F.map_injective
    simp only [i, F.map_comp, F.map_preimage, F.map_zero, Category.assoc,
      Limits.kernel.condition, comp_zero]
  refine
    { K := hImage.witness
      ι := i
      zero := hi
      mappedIsLimit := ?_ }
  exact (kernelIsKernel (F.map f)).ofIsoLimit
    (Fork.ext e.symm (by
      change e.inv ≫ F.map i = Limits.kernel.ι (F.map f)
      simp only [i, F.map_preimage, Iso.inv_hom_id_assoc]))

/-- The whole family satisfies the original kernel-resolving carrier without a resolution input. -/
theorem kernelResolvingDataOfKernelImageClosure : KernelResolvingData F where
  kernelOfEpi f hf := by
    let _ := hf
    exact ⟨kernelLiftOfEpi F hKernelClosure f⟩

/-- Every source representative is the witness of the same earned essential-image statement. -/
theorem kernelLiftOfEpi_K {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    (kernelLiftOfEpi F hKernelClosure f).K =
      (kernelOfEpi_mem_essImage F hKernelClosure f).witness := rfl

/-- The whole original source inclusion is the preimage of the actual ambient kernel inclusion. -/
theorem kernelLiftOfEpi_ι {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    (kernelLiftOfEpi F hKernelClosure f).ι =
      F.preimage ((kernelOfEpi_mem_essImage F hKernelClosure f).getIso.hom ≫
        Limits.kernel.ι (F.map f)) := rfl

/-- The complete mapped inclusion retains the same chosen representative chart and ambient kernel.
-/
theorem kernelLiftOfEpi_map_ι {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    F.map (kernelLiftOfEpi F hKernelClosure f).ι =
      (kernelOfEpi_mem_essImage F hKernelClosure f).getIso.hom ≫ Limits.kernel.ι (F.map f) :=
  F.map_preimage _

/-- The original lifted inclusion is killed by the same original morphism. -/
theorem kernelLiftOfEpi_zero {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    (kernelLiftOfEpi F hKernelClosure f).ι ≫ f = 0 :=
  (kernelLiftOfEpi F hKernelClosure f).zero

/-- Every original mapped row has the actual ambient kernel universal property. -/
def kernelLiftOfEpiMappedIsLimit {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    IsLimit (KernelFork.ofι (f := F.map f) (F.map (kernelLiftOfEpi F hKernelClosure f).ι)
      (by rw [← F.map_comp, kernelLiftOfEpi_zero, F.map_zero])) :=
  (kernelLiftOfEpi F hKernelClosure f).mappedIsLimit

/-- The same actual kernel row is short exact in the ambient abelian category. -/
theorem kernelLiftOfEpi_mappedShortExact {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    ((kernelLiftOfEpi F hKernelClosure f).shortComplex.map F).ShortExact :=
  (kernelLiftOfEpi F hKernelClosure f).mappedShortExact

variable [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
  [F.ReflectsAdmissibleExact]

/-- Reflection of the same actual ambient row earns the original source conflation. -/
theorem kernelLiftOfEpi_isAdmissibleExact {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    IsAdmissibleExact (kernelLiftOfEpi F hKernelClosure f).shortComplex :=
  (kernelLiftOfEpi F hKernelClosure f).isAdmissibleExact

/-- The represented source inclusion has its actual kernel universal property in E. -/
def kernelLiftOfEpiIsLimit {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    IsLimit (KernelFork.ofι (f := f) (kernelLiftOfEpi F hKernelClosure f).ι
      (kernelLiftOfEpi_zero F hKernelClosure f)) :=
  isLimit_kernelFork_of_isAdmissibleExact
    (kernelLiftOfEpi_isAdmissibleExact F hKernelClosure f)

/-- The same original morphism is the actual source cokernel of the represented inclusion. -/
def kernelLiftOfEpiIsColimit {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    IsColimit (CokernelCofork.ofπ (f := (kernelLiftOfEpi F hKernelClosure f).ι) f
      (kernelLiftOfEpi_zero F hKernelClosure f)) :=
  isColimit_cokernelCofork_of_isAdmissibleExact
    (kernelLiftOfEpi_isAdmissibleExact F hKernelClosure f)

end CategoryTheory.Functor

end
