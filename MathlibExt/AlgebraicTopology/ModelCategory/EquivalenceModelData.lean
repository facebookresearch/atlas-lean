/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.Equivalence
import MathlibExt.CategoryTheory.MorphismProperty.InverseImage

/-!
# Complete model data under the original equivalence transport

The existing model transport is used throughout. Its entire model record is
determined by its actual morphism classes. Identity, composition and the
original unit/counit roundtrips therefore identify full model records on the
unchanged categories. The generating families retain their unsaturated
strict images, including the original intermediate categories and inverses.

These statements compare model data. The supplied chosen factor algorithms
remain separate data and are not replaced by getters for transported families.
-/

set_option autoImplicit false
noncomputable section
universe w uC vC uD vD uE vE

open CategoryTheory CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.ModelCategory

variable {C : Type uC} [Category.{vC} C]

/-- The three complete morphism classes determine the actual whole model record. -/
theorem eq_of_classes (M N : ModelCategory C)
    (hF : M.categoryWithFibrations.fibrations = N.categoryWithFibrations.fibrations)
    (hC : M.categoryWithCofibrations.cofibrations = N.categoryWithCofibrations.cofibrations)
    (hW : M.categoryWithWeakEquivalences.weakEquivalences =
      N.categoryWithWeakEquivalences.weakEquivalences) : M = N := by
  have hF' : M.categoryWithFibrations = N.categoryWithFibrations :=
    congrArg (fun P : MorphismProperty C => (⟨P⟩ : CategoryWithFibrations C)) hF
  have hC' : M.categoryWithCofibrations = N.categoryWithCofibrations :=
    congrArg (fun P : MorphismProperty C => (⟨P⟩ : CategoryWithCofibrations C)) hC
  have hW' : M.categoryWithWeakEquivalences = N.categoryWithWeakEquivalences :=
    congrArg (fun P : MorphismProperty C => (⟨P⟩ : CategoryWithWeakEquivalences C)) hW
  cases M
  cases N
  cases hF'
  cases hC'
  cases hW'
  rfl

/-- The full cofibration and weak classes recognize the whole model via its actual WFS. -/
theorem eq_of_cofibrations_and_weakEquivalences (M N : ModelCategory C)
    (hC : M.categoryWithCofibrations.cofibrations = N.categoryWithCofibrations.cofibrations)
    (hW : M.categoryWithWeakEquivalences.weakEquivalences =
      N.categoryWithWeakEquivalences.weakEquivalences) : M = N := by
  apply eq_of_classes M N _ hC hW
  have hM : (M.categoryWithCofibrations.cofibrations ⊓
      M.categoryWithWeakEquivalences.weakEquivalences).rlp =
      M.categoryWithFibrations.fibrations := by
    let : ModelCategory C := M
    exact trivialCofibrations_rlp C
  have hN : (N.categoryWithCofibrations.cofibrations ⊓
      N.categoryWithWeakEquivalences.weakEquivalences).rlp =
      N.categoryWithFibrations.fibrations := by
    let : ModelCategory C := N
    exact trivialCofibrations_rlp C
  rw [← hM, ← hN, hC, hW]

/-- The full fibration and weak classes recognize the whole model by the other actual WFS. -/
theorem eq_of_fibrations_and_weakEquivalences (M N : ModelCategory C)
    (hF : M.categoryWithFibrations.fibrations = N.categoryWithFibrations.fibrations)
    (hW : M.categoryWithWeakEquivalences.weakEquivalences =
      N.categoryWithWeakEquivalences.weakEquivalences) : M = N := by
  apply eq_of_classes M N hF _ hW
  have hM : (M.categoryWithFibrations.fibrations ⊓
      M.categoryWithWeakEquivalences.weakEquivalences).llp =
      M.categoryWithCofibrations.cofibrations := by
    let : ModelCategory C := M
    exact trivialFibrations_llp C
  have hN : (N.categoryWithFibrations.fibrations ⊓
      N.categoryWithWeakEquivalences.weakEquivalences).llp =
      N.categoryWithCofibrations.cofibrations := by
    let : ModelCategory C := N
    exact trivialFibrations_llp C
  rw [← hM, ← hN, hF, hW]

end HomotopicalAlgebra.ModelCategory


namespace HomotopicalAlgebra.CofibrantGenerationData.Equivalence

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E]

/-- The existing transport through the actual identity retains the complete original model. -/
theorem modelCategory_refl [M : ModelCategory C] :
    modelCategory (CategoryTheory.Equivalence.refl (C := C)) = M := by
  apply ModelCategory.eq_of_classes <;> rfl

/-- Direct and iterated original equivalence transport give the same whole model record. -/
theorem modelCategory_trans [ModelCategory E] (e : C ≌ D) (f : D ≌ E) :
    (letI : ModelCategory D := modelCategory f;
      modelCategory e) = modelCategory (e.trans f) := by
  apply ModelCategory.eq_of_classes <;> rfl

/-- The actual counit identifies the complete roundtrip model with its original target record. -/
theorem modelCategory_roundtrip [M : ModelCategory D] (e : C ≌ D) :
    (letI : ModelCategory C := modelCategory e;
      modelCategory e.symm) = M := by
  apply ModelCategory.eq_of_classes
  · exact inverseImage_equivalence_roundtrip (fibrations D) e
  · exact inverseImage_equivalence_roundtrip (cofibrations D) e
  · exact inverseImage_equivalence_roundtrip (weakEquivalences D) e

/-- The original unit likewise identifies the full reverse roundtrip source model. -/
theorem modelCategory_reverse_roundtrip [M : ModelCategory C] (e : C ≌ D) :
    (letI : ModelCategory D := modelCategory e.symm;
      modelCategory e) = M := by
  apply ModelCategory.eq_of_classes
  · exact inverseImage_equivalence_reverse_roundtrip (fibrations C) e
  · exact inverseImage_equivalence_reverse_roundtrip (cofibrations C) e
  · exact inverseImage_equivalence_reverse_roundtrip (weakEquivalences C) e

/-- Isomorphic forward functors identify full transported models without a class premise. -/
theorem modelCategory_eq_of_functor_iso [ModelCategory D] (e e' : C ≌ D)
    (h : e.functor ≅ e'.functor) : modelCategory e = modelCategory e' := by
  apply ModelCategory.eq_of_classes
  · exact inverseImage_eq_of_natIso (fibrations D) h
  · exact inverseImage_eq_of_natIso (cofibrations D) h
  · exact inverseImage_eq_of_natIso (weakEquivalences D) h

/-- The two original inverses compose on the unsaturated family, retaining all actual labels. -/
theorem family_trans (e : C ≌ D) (f : D ≌ E) (P : MorphismProperty E) :
    family e (family f P) = family (e.trans f) P :=
  strictMap_strictMap P f.inverse e.inverse

variable [ModelCategory E] {κ : Cardinal.{w}} [Fact κ.IsRegular]
  [OrderBot κ.ord.ToType] (e : C ≌ D) (f : D ≌ E) (d : CofibrantGenerationData E κ)

/-- Both routes retain the entire literal original I family at the unchanged cardinal. -/
theorem generationData_trans_I :
    letI : ModelCategory D := modelCategory f
    letI : ModelCategory C := modelCategory e
    (generationData e (generationData f d)).I = (generationData (e.trans f) d).I :=
  family_trans e f d.I

/-- Both routes retain the entire literal original J family at the unchanged cardinal. -/
theorem generationData_trans_J :
    letI : ModelCategory D := modelCategory f
    letI : ModelCategory C := modelCategory e
    (generationData e (generationData f d)).J = (generationData (e.trans f) d).J :=
  family_trans e f d.J

end HomotopicalAlgebra.CofibrantGenerationData.Equivalence
