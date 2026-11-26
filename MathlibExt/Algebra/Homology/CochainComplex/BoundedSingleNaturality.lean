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

public import Mathlib.Algebra.Homology.Additive
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedSingle

/-!
# Single complexes and zero-preserving functors

Let C and D be categories with zero morphisms and zero objects, and let
F:C → D preserve zero morphisms. Termwise application of F to bounded
integer-indexed cochain complexes has a natural comparison
c_F(X):F(Sⱼ(X)) ≅ Sⱼ(F(X)). In the support degree j its forward
component is εⱼ(F(X))⁻¹ ∘ F(εⱼ(X)); its inverse is
F(εⱼ(X)⁻¹) ∘ εⱼ(F(X)). Both maps have zero components in every degree i≠j.

The comparisons agree with the canonical identification for the identity
functor and compose for zero-preserving functors F and G, using the
canonical comparison between termwise application of G∘F and successive
termwise application of F and G. The categories C, D and the target of G
have independent object and morphism universes.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uC vC uD vD uE vE

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.Bounded

variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C] [HasZeroObject C]
variable {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D] [HasZeroObject D]
variable (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- For categories C and D with zero morphisms and zero objects, a functor
F:C → D preserving zero morphisms and an integer j, the natural isomorphism
F(Sⱼ(X)) ≅ Sⱼ(F(X)) in the bounded cochain category. Here Sⱼ places
an object in degree j and zero in the other degrees. -/
def singleMapCochainComplexBounded (j : ℤ) :
    single C j ⋙ F.mapCochainComplexBounded ≅ F ⋙ single D j :=
  NatIso.ofComponents
    (fun X => (CochainComplex.bounded D).isoMk
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) j).app X))
    (fun f => by
      apply ObjectProperty.hom_ext
      exact (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) j).hom.naturality f)

/-- Let F:C → D preserve zero morphisms, with C and D having zero morphisms
and zero objects. For an object X and an integer j, the underlying cochain
map of the forward bounded comparison F(Sⱼ(X)) → Sⱼ(F(X)) is the
canonical single-complex comparison in the full cochain category. -/
theorem singleMapCochainComplexBounded_hom_app_hom (j : ℤ) (X : C) :
    ((singleMapCochainComplexBounded F j).hom.app X).hom =
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) j).hom.app X := rfl

/-- Let F:C → D preserve zero morphisms, with C and D having zero morphisms
and zero objects. For an object X and an integer j, the underlying cochain
map of the inverse bounded comparison Sⱼ(F(X)) → F(Sⱼ(X)) is the inverse
canonical single-complex comparison in the full cochain category. -/
theorem singleMapCochainComplexBounded_inv_app_hom (j : ℤ) (X : C) :
    ((singleMapCochainComplexBounded F j).inv.app X).hom =
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) j).inv.app X := rfl

/-- Let F:C → D preserve zero morphisms, with C and D having zero morphisms
and zero objects. For X in C, write εⱼ(X):Sⱼ(X)ʲ ≅ X and
εⱼ(F(X)):Sⱼ(F(X))ʲ ≅ F(X) for the evaluation isomorphisms.
The degree-j component of F(Sⱼ(X)) → Sⱼ(F(X)) is
εⱼ(F(X))⁻¹ ∘ F(εⱼ(X)). -/
@[simp]
theorem singleMapCochainComplexBounded_hom_app_self (j : ℤ) (X : C) :
    ((singleMapCochainComplexBounded F j).hom.app X).hom.f j =
      F.map (singleObjXSelf C j X).hom ≫ (singleObjXSelf D j (F.obj X)).inv :=
  HomologicalComplex.singleMapHomologicalComplex_hom_app_self F (.up ℤ) j X

/-- For a zero-morphism-preserving functor F:C → D between categories with
zero morphisms and zero objects, the forward bounded comparison
F(Sⱼ(X)) → Sⱼ(F(X)) has zero i-th component whenever i≠j. -/
@[simp]
theorem singleMapCochainComplexBounded_hom_app_ne {i j : ℤ} (h : i ≠ j) (X : C) :
    ((singleMapCochainComplexBounded F j).hom.app X).hom.f i = 0 :=
  HomologicalComplex.singleMapHomologicalComplex_hom_app_ne F (.up ℤ) h X

/-- Let F:C → D preserve zero morphisms, with C and D having zero morphisms
and zero objects. For the evaluation isomorphisms εⱼ(X) and εⱼ(F(X)),
the degree-j component of the inverse comparison
Sⱼ(F(X)) → F(Sⱼ(X)) is F(εⱼ(X)⁻¹) ∘ εⱼ(F(X)). -/
@[simp]
theorem singleMapCochainComplexBounded_inv_app_self (j : ℤ) (X : C) :
    ((singleMapCochainComplexBounded F j).inv.app X).hom.f j =
      (singleObjXSelf D j (F.obj X)).hom ≫ F.map (singleObjXSelf C j X).inv :=
  HomologicalComplex.singleMapHomologicalComplex_inv_app_self F (.up ℤ) j X

/-- For a zero-morphism-preserving functor F:C → D between categories with
zero morphisms and zero objects, the inverse bounded comparison
Sⱼ(F(X)) → F(Sⱼ(X)) has zero i-th component whenever i≠j. -/
@[simp]
theorem singleMapCochainComplexBounded_inv_app_ne {i j : ℤ} (h : i ≠ j) (X : C) :
    ((singleMapCochainComplexBounded F j).inv.app X).hom.f i = 0 :=
  HomologicalComplex.singleMapHomologicalComplex_inv_app_ne F (.up ℤ) h X

omit [HasZeroObject D] in
/-- Let C have zero morphisms and a zero object, let D have zero morphisms,
and let F:C → D preserve zero morphisms. For the single complex Sⱼ(X),
every term of its termwise image F(Sⱼ(X)) in degree i≠j is a zero object
in D. -/
theorem singleMapCochainComplexBounded_source_isZero_X (j : ℤ) (X : C)
    (i : ℤ) (h : i ≠ j) :
    IsZero (((single C j ⋙ F.mapCochainComplexBounded).obj X).obj.X i) :=
  F.map_isZero (single_isZero_X C j X i h)

/-- In a category C with zero morphisms and a zero object, the forward
single-complex comparison for the identity functor, evaluated at X and j,
equals the canonical cochain identification of termwise identity applied
to Sⱼ(X) with Sⱼ(X). -/
theorem singleMapCochainComplexBounded_id_hom_app (j : ℤ) (X : C) :
    ((singleMapCochainComplexBounded (𝟭 C) j).hom.app X).hom =
      (Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom.app ((single C j).obj X).obj :=
  HomologicalComplex.singleMapHomologicalComplex_id_hom_app (.up ℤ) j X

/-- In a category C with zero morphisms and a zero object, the inverse
single-complex comparison for the identity functor, evaluated at X and j,
equals the inverse canonical cochain identification between termwise
identity applied to Sⱼ(X) and Sⱼ(X). -/
theorem singleMapCochainComplexBounded_id_inv_app (j : ℤ) (X : C) :
    ((singleMapCochainComplexBounded (𝟭 C) j).inv.app X).hom =
      (Functor.mapHomologicalComplexIdIso C (.up ℤ)).inv.app ((single C j).obj X).obj :=
  HomologicalComplex.singleMapHomologicalComplex_id_inv_app (.up ℤ) j X

variable {E : Type uE} [Category.{vE} E] [HasZeroMorphisms E] [HasZeroObject E]
variable (G : D ⥤ E) [G.PreservesZeroMorphisms]

/-- Let C, D and E have zero morphisms and zero objects, and let F:C → D
and G:D → E preserve zero morphisms. The forward comparison
(G∘F)(Sⱼ(X)) → Sⱼ(G(F(X))) is the canonical identification with
G(F(Sⱼ(X))), followed by G applied to the forward comparison for F
and then the forward comparison for G at F(X). -/
theorem singleMapCochainComplexBounded_comp_hom_app (j : ℤ) (X : C) :
    ((singleMapCochainComplexBounded (F ⋙ G) j).hom.app X).hom =
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app
          ((single C j).obj X).obj ≫
        (G.mapHomologicalComplex (.up ℤ)).map
          ((singleMapCochainComplexBounded F j).hom.app X).hom ≫
        ((singleMapCochainComplexBounded G j).hom.app (F.obj X)).hom :=
  HomologicalComplex.singleMapHomologicalComplex_comp_hom_app F G (.up ℤ) j X

/-- Let C, D and E have zero morphisms and zero objects, and let F:C → D
and G:D → E preserve zero morphisms. As underlying cochain maps, the
inverse single-complex comparison for G∘F at X is the inverse comparison
for G at F(X), followed by G applied to the inverse comparison for F at X. -/
theorem singleMapCochainComplexBounded_comp_inv_app (j : ℤ) (X : C) :
    ((singleMapCochainComplexBounded (F ⋙ G) j).inv.app X).hom =
      ((singleMapCochainComplexBounded G j).inv.app (F.obj X)).hom ≫
        (G.mapHomologicalComplex (.up ℤ)).map
          ((singleMapCochainComplexBounded F j).inv.app X).hom :=
  HomologicalComplex.singleMapHomologicalComplex_comp_inv_app F G (.up ℤ) j X

end CochainComplex.Bounded

end
