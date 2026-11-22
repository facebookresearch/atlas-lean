/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidSimplexFaces
public import MathlibExt.AlgebraicTopology.SimplicialSet.CocontinuousSetMonomorphisms
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# The actual full-J left Kan functor preserves monomorphisms

In each original output degree, the actual k adjunction supplies cocontinuity.
The preserved endpoint coproduct supplies the original boundary-one test:
same-endpoint images cancel through the represented full-J coface, while
distinct endpoint images avoid distinct vertices in the same full-J tuple.
The Set-valued one-boundary criterion then applies to each actual evaluation.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.FreeGroupoidSimplex

private abbrev evaluatedK (d : SimplexCategoryᵒᵖ) : SSet.{u} ⥤ Type u :=
  kFunctor.{u} ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj d

private instance evaluatedK_preservesColimits (d : SimplexCategoryᵒᵖ) :
    PreservesColimitsOfSize.{u, u} (evaluatedK.{u} d) := by
  let : PreservesColimitsOfSize.{u, u} kFunctor.{u} :=
    kAdjunction.leftAdjoint_preservesColimits
  infer_instance

private theorem boundaryOne_cover (d : SimplexCategoryᵒᵖ)
    (x : (evaluatedK.{u} d).obj (boundary 1 : SSet.{u})) :
    ∃ (i : Fin 2) (a : (evaluatedK.{u} d).obj (Δ[0] : SSet.{u})),
      (evaluatedK d).map (boundary.ι i) a = x := by
  let : PreservesFiniteColimits (evaluatedK.{u} d) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  obtain ⟨j, a, ha⟩ := Types.jointly_surjective_of_isColimit
    (mappedBoundaryOneIsColimit (evaluatedK.{u} d)) x
  rcases j with ⟨j⟩
  cases j with
  | left => exact ⟨0, a, ha⟩
  | right => exact ⟨1, a, ha⟩

private theorem representedEndpoint (d : SimplexCategoryᵒᵖ) (i : Fin 2)
    (a : (evaluatedK.{u} d).obj (Δ[0] : SSet.{u})) :
    (kRepresentableIso.{u}.hom.app ⦋1⦌).app d
        ((evaluatedK d).map (stdSimplex.δ i) a) =
      (J.{u}.map (SimplexCategory.δ i)).app d
        ((kRepresentableIso.hom.app ⦋0⦌).app d a) := by
  exact congrArg
    (fun f : kFunctor.obj (Δ[0] : SSet.{u}) ⟶ J.obj ⦋1⦌ => f.app d a)
    (kRepresentableIso_hom_naturality (SimplexCategory.δ i))

private theorem representedEndpoint_injective (d : SimplexCategoryᵒᵖ) (i : Fin 2) :
    Function.Injective ((evaluatedK.{u} d).map (stdSimplex.δ i)) := by
  have hJ : Function.Injective ((J.{u}.map (SimplexCategory.δ i)).app d) :=
    (mono_iff_injective _).1 inferInstance
  have hIso : Function.Injective ((kRepresentableIso.{u}.hom.app ⦋0⦌).app d) :=
    (mono_iff_injective _).1 inferInstance
  intro a b h
  apply hIso
  apply hJ
  rw [← representedEndpoint d i a, ← representedEndpoint d i b]
  exact congrArg ((kRepresentableIso.hom.app ⦋1⦌).app d) h

private theorem differentEndpointImages (d : SimplexCategoryᵒᵖ) (i j : Fin 2)
    (hne : i ≠ j) (a b : (J.{u}.obj ⦋0⦌).obj d) :
    (J.{u}.map (SimplexCategory.δ i)).app d a ≠
      (J.{u}.map (SimplexCategory.δ j)).app d b := by
  intro h
  let z := (J.{u}.map (SimplexCategory.δ i)).app d a
  have hi : ∀ k, simplexVertexEquiv.{u} ⦋1⦌ d.unop.len z k ≠ i :=
    (J_coface_range_iff 0 i d.unop.len z).1 ⟨a, rfl⟩
  have hj : ∀ k, simplexVertexEquiv.{u} ⦋1⦌ d.unop.len z k ≠ j :=
    (J_coface_range_iff 0 j d.unop.len z).1 ⟨b, h.symm⟩
  have exhaust : ∀ i j v : Fin 2, i ≠ j → v = i ∨ v = j := by decide
  obtain hv | hv := exhaust i j (simplexVertexEquiv ⦋1⦌ d.unop.len z 0) hne
  · exact hi 0 hv
  · exact hj 0 hv

private theorem boundaryOne_mono (d : SimplexCategoryᵒᵖ) :
    Mono ((evaluatedK.{u} d).map ((boundary.{u} 1).ι)) := by
  apply (mono_iff_injective _).2
  intro x y h
  obtain ⟨i, a, rfl⟩ := boundaryOne_cover d x
  obtain ⟨j, b, rfl⟩ := boundaryOne_cover d y
  have hFaces := h
  change (((evaluatedK d).map (boundary.ι i) ≫
      (evaluatedK d).map ((boundary.{u} 1).ι)) a) =
    (((evaluatedK d).map (boundary.ι j) ≫
      (evaluatedK d).map ((boundary.{u} 1).ι)) b) at hFaces
  rw [mappedBoundary_ι_comp (evaluatedK d) i,
    mappedBoundary_ι_comp (evaluatedK d) j] at hFaces
  by_cases hij : i = j
  · subst j
    exact congrArg ((evaluatedK d).map (boundary.ι i))
      (representedEndpoint_injective d i hFaces)
  · exfalso
    apply differentEndpointImages d i j hij
      ((kRepresentableIso.hom.app ⦋0⦌).app d a)
      ((kRepresentableIso.hom.app ⦋0⦌).app d b)
    rw [← representedEndpoint d i a, ← representedEndpoint d j b]
    exact congrArg ((kRepresentableIso.hom.app ⦋1⦌).app d) hFaces

/-- The actual full-J left Kan extension preserves every original monomorphism. -/
@[instance]
theorem kFunctor_preservesMonomorphisms : kFunctor.{u}.PreservesMonomorphisms := by
  constructor
  intro X Y f hf
  rw [NatTrans.mono_iff_mono_app]
  intro d
  exact (cocontinuous_preservesMonomorphisms_of_boundaryOne
    (evaluatedK.{u} d) (boundaryOne_mono d)).preserves f

end SSet.FreeGroupoidSimplex
