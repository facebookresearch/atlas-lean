/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
# Exact original vertex lifts in a specified component of a Kan fibration

Both one-dimensional horn lifts retain the entire original edge and its
prescribed endpoint. Their reverse and transitive component steps lift
every original component relation, without Kan source or target. Thus a
specified target vertex in the image component has an exact original
vertex preimage in that same specified source component.
This is the representative correction needed in Bergner's actual F2
condition; it does not assume scalar weakness or target fibrancy.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

variable {X Y : SSet.{u}} (p : X ⟶ Y) [Fibration p]

/-- Lift the SAME whole original edge with its actual source vertex prescribed. -/
theorem fibration_exists_edge_lift_source (x : X _⦋0⦌) {y : Y _⦋0⦌}
    (e : Edge (p.app _ x) y) :
    ∃ (x' : X _⦋0⦌) (e' : Edge x x'), p.app _ x' = y ∧ (e'.map p).edge = e.edge := by
  let faces : ∀ (j : Fin 2) (_ : j ≠ 0), (Δ[0] : SSet.{u}) ⟶ X :=
    fun _ _ => yonedaEquiv.symm x
  have compatible : horn.IsCompatible faces := True.intro
  obtain ⟨l, hl, hlp⟩ := compatible.exists_lift p (yonedaEquiv.symm e.edge) (by
    intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, stdSimplex.yonedaEquiv_δ_comp]
      simp only [faces, Equiv.apply_symm_apply]
      exact e.src_eq.symm)
  have hsource : X.δ 1 (yonedaEquiv l) = x := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hl 1 (by decide), Equiv.apply_symm_apply]
  have hmap : p.app _ (yonedaEquiv l) = e.edge := by
    rw [← yonedaEquiv_comp, hlp, Equiv.apply_symm_apply]
  refine ⟨X.δ 0 (yonedaEquiv l), Edge.mk (yonedaEquiv l) hsource rfl, ?_, ?_⟩
  · rw [δ_naturality_apply p 0, hmap]
    exact e.tgt_eq
  · exact hmap

/-- Lift the SAME whole original edge with its actual target vertex prescribed. -/
theorem fibration_exists_edge_lift_target (x : X _⦋0⦌) {y : Y _⦋0⦌}
    (e : Edge y (p.app _ x)) :
    ∃ (x' : X _⦋0⦌) (e' : Edge x' x), p.app _ x' = y ∧ (e'.map p).edge = e.edge := by
  let faces : ∀ (j : Fin 2) (_ : j ≠ 1), (Δ[0] : SSet.{u}) ⟶ X :=
    fun _ _ => yonedaEquiv.symm x
  have compatible : horn.IsCompatible faces := True.intro
  obtain ⟨l, hl, hlp⟩ := compatible.exists_lift p (yonedaEquiv.symm e.edge) (by
    intro j hj
    fin_cases j
    · apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, stdSimplex.yonedaEquiv_δ_comp]
      simp only [faces, Equiv.apply_symm_apply]
      exact e.tgt_eq.symm
    · exact (hj rfl).elim)
  have htarget : X.δ 0 (yonedaEquiv l) = x := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hl 0 (by decide), Equiv.apply_symm_apply]
  have hmap : p.app _ (yonedaEquiv l) = e.edge := by
    rw [← yonedaEquiv_comp, hlp, Equiv.apply_symm_apply]
  refine ⟨X.δ 1 (yonedaEquiv l), Edge.mk (yonedaEquiv l) rfl htarget, ?_, ?_⟩
  · rw [δ_naturality_apply p 1, hmap]
    exact e.src_eq
  · exact hmap

/-- Every actual target component relation lifts to an exact vertex without changing the original source component. -/
theorem fibration_exists_vertex_in_same_component (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (h : π₀.mk (p.app _ x) = π₀.mk y) :
    ∃ x' : X _⦋0⦌, p.app _ x' = y ∧ π₀.mk x' = π₀.mk x := by
  let transport (a b : Y _⦋0⦌) : Prop :=
    ∀ z : X _⦋0⦌, p.app _ z = a →
      ∃ z' : X _⦋0⦌, p.app _ z' = b ∧ π₀.mk z' = π₀.mk z
  have lift_chain (a b : Y _⦋0⦌) (hab : Relation.EqvGen (π₀Rel (X := Y)) a b) :
      transport a b ∧ transport b a := by
    induction hab with
    | rel a b hab =>
      obtain ⟨e⟩ := hab
      constructor
      · intro z hz
        subst a
        obtain ⟨z', e', hmap, _⟩ := fibration_exists_edge_lift_source p z e
        exact ⟨z', hmap, (π₀.sound e').symm⟩
      · intro z hz
        subst b
        obtain ⟨z', e', hmap, _⟩ := fibration_exists_edge_lift_target p z e
        exact ⟨z', hmap, π₀.sound e'⟩
    | refl a =>
      exact ⟨fun z hz => ⟨z, hz, rfl⟩, fun z hz => ⟨z, hz, rfl⟩⟩
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ =>
      constructor
      · intro z hz
        obtain ⟨z', hz', hclass⟩ := ih₁.1 z hz
        obtain ⟨z'', hz'', hclass'⟩ := ih₂.1 z' hz'
        exact ⟨z'', hz'', hclass'.trans hclass⟩
      · intro z hz
        obtain ⟨z', hz', hclass⟩ := ih₂.2 z hz
        obtain ⟨z'', hz'', hclass'⟩ := ih₁.2 z' hz'
        exact ⟨z'', hz'', hclass'.trans hclass⟩
  exact (lift_chain _ _ ((π₀.mk_eq_mk_iff _ _).mp h)).1 x rfl

/-- A target vertex in the image of a specified original component lifts exactly in that SAME component. -/
theorem fibration_exists_vertex_lift_of_component (a : π₀ X) (y : Y _⦋0⦌)
    (h : mapπ₀ p a = π₀.mk y) :
    ∃ x : X _⦋0⦌, p.app _ x = y ∧ π₀.mk x = a := by
  obtain ⟨x, rfl⟩ := π₀.mk_surjective a
  exact fibration_exists_vertex_in_same_component p x y h

end SSet
