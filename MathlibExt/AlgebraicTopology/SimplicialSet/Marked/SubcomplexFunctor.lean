/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ColimitCriterion
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MarkingCoverage
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# Original marked subcomplex diagrams

Pull back the supplied marking to every original simplicial subcomplex.
The actual inclusions form a functor and cocone. If every original mark
already lies in a designated source subcomplex, all later inclusions
cover their target marks and the native underlying colimit is the same
marked colimit. This retains every simplex, mark and original inclusion.
-/

noncomputable section
universe u v w
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Inherit the original marking on each actual simplicial subcomplex and keep the native inclusion maps. -/
def subcomplexFunctor (X : Marked.{u}) : X.toSSet.Subcomplex ⥤ Marked.{u} where
  obj S := comap X S.ι
  map f :=
    { hom := Subcomplex.toSSetFunctor.map f
      preserve {e} he := by
        exact he }
  map_id S := Hom.ext (Subcomplex.toSSetFunctor.map_id S)
  map_comp f g := Hom.ext (Subcomplex.toSSetFunctor.map_comp f g)

/-- Forgetting this actual marking recovers precisely the original subcomplex diagram. -/
@[simp]
theorem subcomplexFunctor_forget (X : Marked.{u}) :
    subcomplexFunctor X ⋙ forget = Subcomplex.toSSetFunctor := rfl

/-- The original subcomplex inclusions give the actual marked cocone into the supplied object. -/
def subcomplexCocone (X : Marked.{u}) {J : Type w} [Category.{v} J]
    (F : J ⥤ X.toSSet.Subcomplex) : Cocone (F ⋙ subcomplexFunctor X) where
  pt := X
  ι :=
    { app j := comapHom X (F.obj j).ι
      naturality j j' f := by
        apply Hom.ext
        apply NatTrans.ext
        funext n
        apply ConcreteCategory.hom_ext
        intro e
        rfl }

/-- When original marks lie in an old subcomplex, every later native marked inclusion covers all target marks. -/
theorem subcomplexFunctor_map_markingSurjective (X : Marked.{u}) (A : X.toSSet.Subcomplex)
    (hA : ∀ e : X.toSSet _⦋1⦌, e ∈ X.marking → e ∈ A.obj (op ⦋1⦌))
    {S T : X.toSSet.Subcomplex} (f : S ⟶ T) (hS : A ≤ S) :
    MarkingSurjective ((subcomplexFunctor X).map f) := by
  intro e he
  let a : S.toSSet _⦋1⦌ := ⟨e.val, hS _ (hA e.val he)⟩
  exact ⟨a, he, by apply Subtype.ext; rfl⟩

/-- Original marked-edge coverage also retains every original vertex in that same source subcomplex. -/
theorem vertices_mem_of_marks_mem (X : Marked.{u}) (A : X.toSSet.Subcomplex)
    (hA : ∀ e : X.toSSet _⦋1⦌, e ∈ X.marking → e ∈ A.obj (op ⦋1⦌))
    (x : X.toSSet _⦋0⦌) : x ∈ A.obj (op ⦋0⦌) := by
  have h := A.map (SimplexCategory.δ (0 : Fin 2)).op (hA _ (X.degenerate_mem x))
  change X.toSSet.δ (0 : Fin 2) (X.toSSet.σ (0 : Fin 1) x) ∈ A.obj (op ⦋0⦌) at h
  exact (δ_comp_σ_self_apply (0 : Fin 1) x) ▸ h

/-- An original underlying subcomplex colimit is the same marked colimit when all original marks already
  occur at the designated stage. -/
def subcomplexCoconeIsColimit (X : Marked.{u}) {J : Type w} [Category.{v} J]
    (F : J ⥤ X.toSSet.Subcomplex) (j₀ : J)
    (h₀ : ∀ e : X.toSSet _⦋1⦌, e ∈ X.marking → e ∈ (F.obj j₀).obj (op ⦋1⦌))
    (hc : IsColimit (forget.mapCocone (subcomplexCocone X F))) :
    IsColimit (subcomplexCocone X F) :=
  isColimitOfUnderlyingMarking hc (by
    intro e he
    exact ⟨j₀, ⟨e, h₀ e he⟩, he, rfl⟩)

end SSet.Marked
