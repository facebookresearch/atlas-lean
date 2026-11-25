/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.ExactCategory.AdmissiblePresentationFunctor

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uC vC uD vD uE vE

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]
variable {A B : C} {p : A ⟶ B} (K : AdmissibleEpiKernelPresentation p)

example : (K.map F).kernel = F.obj K.kernel :=
  AdmissibleEpiKernelPresentation.map_kernel F K

example : (K.map F).ι = F.map K.ι :=
  AdmissibleEpiKernelPresentation.map_ι F K

-- The literal mapped row retains its target-category kernel universal property.
example :
    IsLimit (KernelFork.ofι (f := F.map p) (F.map K.ι) (by
      rw [← CategoryTheory.Functor.map_comp, K.zero, CategoryTheory.Functor.map_zero])) :=
  (K.map F).kernelIsLimit

example :
    IsColimit (CokernelCofork.ofπ (f := F.map K.ι) (F.map p) (by
      rw [← CategoryTheory.Functor.map_comp, K.zero, CategoryTheory.Functor.map_zero])) :=
  (K.map F).cokernelIsColimit

example : K.map (𝟭 C) = K :=
  AdmissibleEpiKernelPresentation.map_id K

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable (G : D ⥤ E) [G.Additive] [G.IsExact]

example : K.map (F ⋙ G) = (K.map F).map G :=
  AdmissibleEpiKernelPresentation.map_comp F G K

end
