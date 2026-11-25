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

public import Mathlib.Algebra.Homology.Single
public import MathlibExt.Algebra.Homology.CochainComplex.Bounded

/-!
# Single complexes in the bounded category

The cochain complex concentrated in degree `j` has support window `[j,j]`
and defines a functor to bounded cochain complexes. Evaluation in degree
`j` recovers the coefficient object through the canonical single-complex
isomorphism; all other terms are zero.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable (E : Type uE) [Category.{vE} E] [HasZeroMorphisms E] [HasZeroObject E]

/-- The single complex in degree `j` has support window `[j,j]`. -/
theorem bounded_single (j : ℤ) (X : E) :
    CochainComplex.bounded E ((HomologicalComplex.single E (.up ℤ) j).obj X) := by
  refine ⟨j, j, ?_⟩
  intro i hi
  exact HomologicalComplex.isZero_single_obj_X (.up ℤ) j X i (by omega)

namespace Bounded

/-- Single-complex functor with codomain the bounded cochain category. -/
def single (j : ℤ) : E ⥤ Bounded E :=
  ObjectProperty.lift (CochainComplex.bounded E)
    (HomologicalComplex.single E (.up ℤ) j) (bounded_single E j)

/-- The underlying functor is the single-complex functor. -/
theorem single_comp_ι (j : ℤ) :
    single E j ⋙ ι E = HomologicalComplex.single E (.up ℤ) j := rfl

/-- Underlying complex of a bounded single object. -/
theorem single_obj_obj (j : ℤ) (X : E) :
    ((single E j).obj X).obj = (HomologicalComplex.single E (.up ℤ) j).obj X := rfl

/-- Underlying map between bounded single objects. -/
theorem single_map_hom (j : ℤ) {X Y : E} (f : X ⟶ Y) :
    ((single E j).map f).hom = (HomologicalComplex.single E (.up ℤ) j).map f := rfl

/-- Canonical evaluation isomorphism in the support degree. -/
def singleObjXSelf (j : ℤ) (X : E) : ((single E j).obj X).obj.X j ≅ X :=
  HomologicalComplex.singleObjXSelf (.up ℤ) j X

/-- The evaluation chart is the canonical single-object chart. -/
theorem singleObjXSelf_eq (j : ℤ) (X : E) :
    singleObjXSelf E j X = HomologicalComplex.singleObjXSelf (.up ℤ) j X := rfl

/-- A single-complex map expressed through its source and target evaluation charts. -/
theorem single_map_f_self (j : ℤ) {X Y : E} (f : X ⟶ Y) :
    ((single E j).map f).hom.f j =
      (singleObjXSelf E j X).hom ≫ f ≫ (singleObjXSelf E j Y).inv :=
  HomologicalComplex.single_map_f_self (.up ℤ) j f

/-- The single-complex term is zero outside the support degree. -/
theorem single_isZero_X (j : ℤ) (X : E) (i : ℤ) (hi : i ≠ j) :
    IsZero (((single E j).obj X).obj.X i) :=
  HomologicalComplex.isZero_single_obj_X (.up ℤ) j X i hi

/-- Natural evaluation isomorphism for the bounded single-complex functor. -/
def singleCompEvalIsoSelf (j : ℤ) : single E j ⋙ eval E j ≅ 𝟭 E :=
  HomologicalComplex.singleCompEvalIsoSelf E (.up ℤ) j

/-- Forward map of the bounded single-evaluation comparison. -/
theorem singleCompEvalIsoSelf_hom (j : ℤ) :
    (singleCompEvalIsoSelf E j).hom =
      (HomologicalComplex.singleCompEvalIsoSelf E (.up ℤ) j).hom := rfl

/-- Inverse map of the bounded single-evaluation comparison. -/
theorem singleCompEvalIsoSelf_inv (j : ℤ) :
    (singleCompEvalIsoSelf E j).inv =
      (HomologicalComplex.singleCompEvalIsoSelf E (.up ℤ) j).inv := rfl

end Bounded

end CochainComplex

end
