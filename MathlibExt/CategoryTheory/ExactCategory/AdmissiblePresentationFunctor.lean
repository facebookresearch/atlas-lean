/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.ExactCategory.AdmissibleEpiKernelComposition
public import MathlibExt.CategoryTheory.ExactCategory.Functor

/-!
# Exact-functor transport of actual admissible kernel presentations

An exact additive functor maps the stored original kernel object, inclusion
and epimorphism to an admissible kernel presentation. The mapped kernel is
the literal image of the original kernel. Its universal properties follow
from the mapped admissible exact row in the original target exact category.

Identity and composition retain the entire stored presentation. Object and
morphism universes in the source and target remain independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uC vC uD vD uE vE

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.AdmissibleEpiKernelPresentation

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

variable (F : C ⥤ D) [F.Additive] [F.IsExact]
variable {A B : C} {p : A ⟶ B}

/-- Map the original stored kernel object and row through an exact additive functor. -/
def map (K : AdmissibleEpiKernelPresentation p) :
    AdmissibleEpiKernelPresentation (F.map p) where
  kernel := F.obj K.kernel
  ι := F.map K.ι
  zero := by
    rw [← CategoryTheory.Functor.map_comp, K.zero, CategoryTheory.Functor.map_zero]
  exact := F.map_admissibleExact (ShortComplex.mk K.ι p K.zero) K.exact

/-- The mapped kernel is exactly the original functor image of the stored kernel. -/
theorem map_kernel (K : AdmissibleEpiKernelPresentation p) :
    (K.map F).kernel = F.obj K.kernel :=
  rfl

/-- The mapped inclusion is the literal original mapped inclusion. -/
theorem map_ι (K : AdmissibleEpiKernelPresentation p) :
    (K.map F).ι = F.map K.ι :=
  rfl

/-- Identity transport retains the entire original stored kernel presentation. -/
theorem map_id (K : AdmissibleEpiKernelPresentation p) :
    K.map (𝟭 C) = K := by
  cases K
  rfl

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- Composition transport uses the same kernel object, inclusion and exact row
as the two successive original functor transports. -/
theorem map_comp (G : D ⥤ E) [G.Additive] [G.IsExact]
    (K : AdmissibleEpiKernelPresentation p) :
    K.map (F ⋙ G) = (K.map F).map G := by
  cases K
  rfl

end CategoryTheory.ExactCategory.AdmissibleEpiKernelPresentation

end
