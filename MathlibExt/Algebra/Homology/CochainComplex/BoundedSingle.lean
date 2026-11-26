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
# Single cochain complexes in the bounded category

Let E be a category with zero morphisms and a zero object. For an integer j,
the single cochain complex Sⱼ(X) places X in degree j and zero objects in
every other degree, with zero differentials. Its support is [j,j], so
X ↦ Sⱼ(X) defines a functor from E to bounded integer-indexed cochain
complexes.

Evaluation at j is naturally isomorphic to the identity of E. If εⱼ(X)
is the evaluation isomorphism Sⱼ(X)ʲ ≅ X, the j-th component of Sⱼ(f) is
εⱼ(Y)⁻¹ ∘ f ∘ εⱼ(X). All terms in degrees i≠j are zero.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable (E : Type uE) [Category.{vE} E] [HasZeroMorphisms E] [HasZeroObject E]

/-- Let E be a category with zero morphisms and a zero object. For an
integer j and an object X, the single cochain complex Sⱼ(X), equal to X
in degree j and zero in other degrees, is bounded with support [j,j]. -/
theorem bounded_single (j : ℤ) (X : E) :
    CochainComplex.bounded E ((HomologicalComplex.single E (.up ℤ) j).obj X) := by
  refine ⟨j, j, ?_⟩
  intro i hi
  exact HomologicalComplex.isZero_single_obj_X (.up ℤ) j X i (by omega)

namespace Bounded

/-- For a category E with zero morphisms and a zero object and an integer j,
the functor E → Bounded(E) sending X to the cochain complex concentrated
at X in degree j, and sending a morphism f to its single-complex map. -/
def single (j : ℤ) : E ⥤ Bounded E :=
  ObjectProperty.lift (CochainComplex.bounded E)
    (HomologicalComplex.single E (.up ℤ) j) (bounded_single E j)

/-- For a category E with zero morphisms and a zero object, the single
functor in degree j followed by the inclusion of bounded complexes into all
integer-indexed cochain complexes equals the single-complex functor with
codomain the full cochain category. -/
theorem single_comp_ι (j : ℤ) :
    single E j ⋙ ι E = HomologicalComplex.single E (.up ℤ) j := rfl

/-- In a category E with zero morphisms and a zero object, the underlying
cochain complex of the bounded single object Sⱼ(X) is the single cochain
complex concentrated at X in degree j. -/
theorem single_obj_obj (j : ℤ) (X : E) :
    ((single E j).obj X).obj = (HomologicalComplex.single E (.up ℤ) j).obj X := rfl

/-- For a morphism f:X → Y in a category E with zero morphisms and a zero
object, the underlying cochain map between the bounded single objects in
degree j is the single-complex map induced by f. -/
theorem single_map_hom (j : ℤ) {X Y : E} (f : X ⟶ Y) :
    ((single E j).map f).hom = (HomologicalComplex.single E (.up ℤ) j).map f := rfl

/-- For a category E with zero morphisms and a zero object, an integer j
and an object X, the canonical evaluation isomorphism εⱼ(X):Sⱼ(X)ʲ ≅ X
for the bounded single cochain complex in degree j. -/
def singleObjXSelf (j : ℤ) (X : E) : ((single E j).obj X).obj.X j ≅ X :=
  HomologicalComplex.singleObjXSelf (.up ℤ) j X

/-- In a category E with zero morphisms and a zero object, the evaluation
isomorphism Sⱼ(X)ʲ ≅ X in the bounded category equals the canonical
evaluation isomorphism for the same single complex in the full cochain
category. -/
theorem singleObjXSelf_eq (j : ℤ) (X : E) :
    singleObjXSelf E j X = HomologicalComplex.singleObjXSelf (.up ℤ) j X := rfl

/-- Let E have zero morphisms and a zero object, and let f:X → Y.
If εⱼ(X):Sⱼ(X)ʲ ≅ X and εⱼ(Y):Sⱼ(Y)ʲ ≅ Y are the canonical evaluation
isomorphisms, then the degree-j component of the bounded single map is
εⱼ(Y)⁻¹ ∘ f ∘ εⱼ(X). -/
theorem single_map_f_self (j : ℤ) {X Y : E} (f : X ⟶ Y) :
    ((single E j).map f).hom.f j =
      (singleObjXSelf E j X).hom ≫ f ≫ (singleObjXSelf E j Y).inv :=
  HomologicalComplex.single_map_f_self (.up ℤ) j f

/-- For a category E with zero morphisms and a zero object, the i-th term
of the bounded single cochain complex Sⱼ(X) is a zero object whenever
i≠j. -/
theorem single_isZero_X (j : ℤ) (X : E) (i : ℤ) (hi : i ≠ j) :
    IsZero (((single E j).obj X).obj.X i) :=
  HomologicalComplex.isZero_single_obj_X (.up ℤ) j X i hi

/-- For a category E with zero morphisms and a zero object, evaluating
the bounded single functor in its support degree j gives a functor naturally
isomorphic to the identity of E. The component at X is the canonical
isomorphism Sⱼ(X)ʲ ≅ X. -/
def singleCompEvalIsoSelf (j : ℤ) : single E j ⋙ eval E j ≅ 𝟭 E :=
  HomologicalComplex.singleCompEvalIsoSelf E (.up ℤ) j

/-- In a category E with zero morphisms and a zero object, the forward
natural transformation from evaluation in degree j of the bounded single
functor to the identity has components εⱼ(X):Sⱼ(X)ʲ → X. It is the same
transformation as for single complexes in the full cochain category. -/
theorem singleCompEvalIsoSelf_hom (j : ℤ) :
    (singleCompEvalIsoSelf E j).hom =
      (HomologicalComplex.singleCompEvalIsoSelf E (.up ℤ) j).hom := rfl

/-- In a category E with zero morphisms and a zero object, the inverse
natural transformation from the identity to evaluation in degree j of the
bounded single functor has components εⱼ(X)⁻¹:X → Sⱼ(X)ʲ. It agrees
with the inverse single-evaluation transformation in the full cochain
category. -/
theorem singleCompEvalIsoSelf_inv (j : ℤ) :
    (singleCompEvalIsoSelf E j).inv =
      (HomologicalComplex.singleCompEvalIsoSelf E (.up ℤ) j).inv := rfl

end Bounded

end CochainComplex

end
