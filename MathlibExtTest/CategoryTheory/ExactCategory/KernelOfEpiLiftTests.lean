/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.ExactCategory.KernelOfEpiLift

/-! Direct clients retain the whole kernel family, actual mapped inclusion and both source UPs. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

namespace MathlibExtTest.KernelOfEpiLift

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive] [F.Full] [F.Faithful]
variable (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
  F.essImage U → F.essImage V → F.essImage (kernel f))

example : Functor.KernelResolvingData F :=
  F.kernelResolvingDataOfKernelImageClosure hKernelClosure

example {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    F.map (F.kernelLiftOfEpi hKernelClosure f).ι =
      (F.kernelOfEpi_mem_essImage hKernelClosure f).getIso.hom ≫ kernel.ι (F.map f) :=
  F.kernelLiftOfEpi_map_ι hKernelClosure f

variable [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
  [F.ReflectsAdmissibleExact]

example {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    IsAdmissibleExact (F.kernelLiftOfEpi hKernelClosure f).shortComplex :=
  F.kernelLiftOfEpi_isAdmissibleExact hKernelClosure f

example {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    IsLimit (KernelFork.ofι (f := f) (F.kernelLiftOfEpi hKernelClosure f).ι
      (F.kernelLiftOfEpi_zero hKernelClosure f)) :=
  F.kernelLiftOfEpiIsLimit hKernelClosure f

example {P Q : E} (f : P ⟶ Q) [Epi (F.map f)] :
    IsColimit (CokernelCofork.ofπ (f := (F.kernelLiftOfEpi hKernelClosure f).ι) f
      (F.kernelLiftOfEpi_zero hKernelClosure f)) :=
  F.kernelLiftOfEpiIsColimit hKernelClosure f

end MathlibExtTest.KernelOfEpiLift

end
