/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Interval
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Products

/-!
# Marked simplicial sets on the interval

The identity edge of `Δ[1]` is not degenerate: it is marked in the maximal marking but not in the
minimal one, so no marked map from the maximally to the minimally marked interval lies over the
identity. The interval classifier sends the identity edge of the maximally marked interval to the
identity map, and an edge of a marked product is marked exactly when both of its components are.
-/

set_option autoImplicit false

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.MarkedBasicTests

open SSet SSet.stdSimplex

/-- The identity edge of the interval. -/
abbrev idEdge : (Δ[1] : SSet.{u}) _⦋1⦌ :=
  objMk₁ (1 : Fin 3)

/-- The identity edge is the Yoneda image of the identity map. -/
theorem idEdge_eq : idEdge.{u} = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
  ext i
  fin_cases i <;> rfl

/-- Every degenerate edge of the interval is one of the two constant edges. -/
theorem degenerate_edge (x : (Δ[1] : SSet.{u}) _⦋0⦌) :
    (Δ[1] : SSet.{u}).σ (0 : Fin 1) x = objMk₁ (0 : Fin 3) ∨
      (Δ[1] : SSet.{u}).σ (0 : Fin 1) x = objMk₁ (2 : Fin 3) := by
  obtain ⟨i, rfl⟩ := objMk₁_surjective x
  fin_cases i
  · exact Or.inl (σ_objMk₁_of_le (0 : Fin 2) (0 : Fin 1) (by decide))
  · exact Or.inr (σ_objMk₁_of_lt (1 : Fin 2) (0 : Fin 1) (by decide))

/-- The identity edge is not marked in the minimal marking. -/
theorem idEdge_not_mem_min : idEdge.{u} ∉ (Marked.min (Δ[1] : SSet.{u})).marking := by
  rintro ⟨x, hx⟩
  rcases degenerate_edge x with h | h
  · exact absurd (objMk₁_injective (h.symm.trans hx)) (by decide)
  · exact absurd (objMk₁_injective (h.symm.trans hx)) (by decide)

/-- The identity edge is marked in the maximal marking. -/
theorem idEdge_mem_max : idEdge.{u} ∈ (Marked.max (Δ[1] : SSet.{u})).marking :=
  Set.mem_univ _

/-- No marked map from the maximally to the minimally marked interval lies over the identity. -/
theorem no_marked_identity :
    ¬ ∃ f : Marked.max (Δ[1] : SSet.{u}) ⟶ Marked.min (Δ[1] : SSet.{u}), f.hom = 𝟙 _ := by
  rintro ⟨f, hf⟩
  have h := f.preserve idEdge_mem_max.{u}
  rw [hf] at h
  exact idEdge_not_mem_min h

/-- From the minimal to the maximal marking, the identity is a marked map. -/
example : (Marked.toMax (X := Marked.min (Δ[1] : SSet.{u})) (𝟙 (Δ[1] : SSet.{u}))).hom = 𝟙 _ :=
  rfl

/-- The minimal-marking adjunction keeps the underlying map, and its inverse marks it minimally. -/
example (X : SSet.{u}) (Y : Marked.{u}) (f : Marked.minimal.obj X ⟶ Y) :
    Marked.minimalHomEquiv X Y f = f.hom :=
  rfl

example (X : SSet.{u}) (Y : Marked.{u}) (g : X ⟶ Marked.forget.obj Y) :
    ((Marked.minimalHomEquiv X Y).symm g).hom = g :=
  rfl

/-- The interval classifier returns the marked edge it started from. -/
example (Y : Marked.{u}) (e : Y.toSSet _⦋1⦌) (he : e ∈ Y.marking) :
    Marked.maxIntervalHomEquiv Y (Marked.intervalMapOfMarkedEdge e he) = ⟨e, he⟩ :=
  Subtype.ext (SSet.yonedaEquiv.apply_symm_apply e)

/-- On the identity edge of the maximally marked interval, the classifier gives the identity map. -/
theorem intervalMap_idEdge :
    Marked.intervalMapOfMarkedEdge (Y := Marked.max (Δ[1] : SSet.{u})) idEdge.{u}
      idEdge_mem_max = 𝟙 _ :=
  Marked.Hom.ext
    ((congrArg SSet.yonedaEquiv.symm idEdge_eq).trans (SSet.yonedaEquiv.symm_apply_apply _))

/-- A product edge whose second component is the identity edge is not marked. -/
theorem prod_idEdge_not_mem :
    ((idEdge.{u}, idEdge.{u}) :
        (Marked.prod (Marked.max (Δ[1] : SSet.{u})) (Marked.min Δ[1])).toSSet _⦋1⦌) ∉
      (Marked.prod (Marked.max (Δ[1] : SSet.{u})) (Marked.min Δ[1])).marking :=
  fun h => idEdge_not_mem_min h.2

/-- A product edge whose second component is degenerate is marked. -/
theorem prod_degenerate_mem (v : (Δ[1] : SSet.{u}) _⦋0⦌) :
    ((idEdge.{u}, (Δ[1] : SSet.{u}).σ (0 : Fin 1) v) :
        (Marked.prod (Marked.max (Δ[1] : SSet.{u})) (Marked.min Δ[1])).toSSet _⦋1⦌) ∈
      (Marked.prod (Marked.max (Δ[1] : SSet.{u})) (Marked.min Δ[1])).marking :=
  ⟨Set.mem_univ _, ⟨v, rfl⟩⟩

/-- The product universal property is given by the projections and the simultaneous lift. -/
example (T X Y : Marked.{u}) (f : T ⟶ Marked.prod X Y) :
    Marked.prodHomEquiv T X Y f = (f ≫ Marked.prodFst X Y, f ≫ Marked.prodSnd X Y) :=
  rfl

example (T X Y : Marked.{u}) (f : T ⟶ X) (g : T ⟶ Y) :
    ((Marked.prodHomEquiv T X Y).symm (f, g)).hom = CartesianMonoidalCategory.lift f.hom g.hom :=
  rfl

end MathlibExtTest.AlgebraicTopology.SimplicialSet.MarkedBasicTests
