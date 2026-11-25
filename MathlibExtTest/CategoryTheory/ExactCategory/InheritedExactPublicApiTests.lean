/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.ExactCategory.ExtensionClosedFullSubcategory

/-!
# Independent clients of generic inherited exact structures

Only generic exact-category modules are imported. The ambient object and
morphism universes are independent, and closure is the actual admissible
row condition. Cokernel presentations and full-subcategory exact data are
derived without any Resolution hypothesis or K-theory import.
-/

public section

noncomputable section

open CategoryTheory Limits ExactCategory

universe u v

namespace CategoryTheory.ExactCategory.InheritedExactPublicApiTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

example {A B : C} (i : A ⟶ B) (hi : IsAdmissibleMono i) :
    Nonempty (AdmissibleMonoCokernelPresentation i) :=
  AdmissibleMonoCokernelPresentation.nonempty hi

example {A B D : C} {i : A ⟶ B} {j : B ⟶ D}
    (K : AdmissibleMonoCokernelPresentation i)
    (L : AdmissibleMonoCokernelPresentation j) :
    IsAdmissibleExact (K.compositeCokernelSequence L) :=
  K.compositeCokernelSequence_exact L

example {A B D : C} {i : A ⟶ B} {j : B ⟶ D}
    (K : AdmissibleMonoCokernelPresentation i)
    (L : AdmissibleMonoCokernelPresentation j) :
    (K.compositeCokernelSequence L).X₁ = K.cokernel ∧
      (K.compositeCokernelSequence L).X₂ = (K.composite L).cokernel ∧
      (K.compositeCokernelSequence L).X₃ = L.cokernel :=
  ⟨K.compositeCokernelSequence_X₁ L,
    K.compositeCokernelSequence_X₂ L, K.compositeCokernelSequence_X₃ L⟩

example (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (hP : ExtensionClosed P) : ExactFullSubcategoryData P :=
  extensionClosedExactData P hP

example (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (hP : ExtensionClosed P) (S : ShortComplex P.FullSubcategory) :
    letI : HasBinaryBiproducts P.FullSubcategory := InheritedExact.binaryBiproducts P hP
    letI : ExactCategory P.FullSubcategory := InheritedExact.exactCategory P hP
    IsAdmissibleExact S ↔ IsAdmissibleExact (S.map P.ι) :=
  InheritedExact.admissible_iff P hP S

example (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (hP : ExtensionClosed P) :
    letI : HasBinaryBiproducts P.FullSubcategory := InheritedExact.binaryBiproducts P hP
    letI : ExactCategory P.FullSubcategory := InheritedExact.exactCategory P hP
    P.ι.IsExact :=
  InheritedExact.inclusion_exact P hP

end CategoryTheory.ExactCategory.InheritedExactPublicApiTests

end
