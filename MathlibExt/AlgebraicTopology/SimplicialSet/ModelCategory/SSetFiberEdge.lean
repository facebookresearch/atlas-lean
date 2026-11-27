/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Fiber
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetAnodyneLifting
public import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexCompat

/-!
# Strict-fiber nonemptiness along a base edge

Let p:E→B be a Kan fibration and e:b₀→b₁ an edge of an arbitrary simplicial base B. The
strict-fiber subcomplex over b₀ is nonbottom exactly when the strict fiber over b₁ is nonbottom.

The edge's source is face δ₁ and target is face δ₀. Forward vertex transport fills the horn
Λ⁰[1], while backward transport fills Λ¹[1]. Only horn lifting of p is required, in any universe
u.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial SSet Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Subcomplex

private lemma subcomplex_ne_bot_iff_exists_zero {X : SSet.{u}} (A : X.Subcomplex) :
    A ≠ ⊥ ↔ ∃ x : X _⦋0⦌, x ∈ A.obj (op ⦋0⦌) := by
  constructor
  · intro hA
    by_contra hnone
    push Not at hnone
    have h_le : A ≤ ⊥ := by
      intro n x hx
      have h0 : X.map (SimplexCategory.const ⦋0⦌ n.unop 0).op x ∈ A.obj (op ⦋0⦌) :=
        A.map _ hx
      exact (hnone _ h0).elim
    have h_eq : A = ⊥ := le_antisymm h_le bot_le
    exact hA h_eq
  · rintro ⟨x, hx⟩ rfl
    simp only [Subfunctor.bot_obj] at hx
    exact hx

private lemma fiber_ne_bot_iff_exists_vertex {E B : SSet.{u}} (p : E ⟶ B)
    (b : B _⦋0⦌) : fiber p b ≠ ⊥ ↔ ∃ x : E _⦋0⦌, p.app _ x = b := by
  rw [subcomplex_ne_bot_iff_exists_zero]
  constructor
  · rintro ⟨x, hx⟩
    rw [mem_fiber_obj_zero_iff] at hx
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, (mem_fiber_obj_zero_iff _ _).mpr rfl⟩

private lemma horn_one_zero_eq : SSet.horn (n := 1) (0 : Fin 2) =
    SSet.stdSimplex.face (n := 1) {0} := by
  have h0 : SSet.horn (n := 1) (0 : Fin 2) =
      SSet.stdSimplex.face (n := 1) ({1}ᶜ : Finset (Fin 2)) := by
    ext m x
    simp [SSet.horn_eq_iSup]
  have h1 : ({1}ᶜ : Finset (Fin 2)) = {0} := by decide
  rw [h0, h1]

private lemma horn_one_one_eq : SSet.horn (n := 1) (1 : Fin 2) =
    SSet.stdSimplex.face (n := 1) {1} := by
  have h0 : SSet.horn (n := 1) (1 : Fin 2) =
      SSet.stdSimplex.face (n := 1) ({0}ᶜ : Finset (Fin 2)) := by
    ext m x
    simp [SSet.horn_eq_iSup]
  have h1 : ({0}ᶜ : Finset (Fin 2)) = {1} := by decide
  rw [h0, h1]

private lemma yoneda_symm_comp_fibration_eq {E B : SSet.{u}} (p : E ⟶ B)
    {x : E _⦋0⦌} {b : B _⦋0⦌} (h : p.app _ x = b) :
    SSet.yonedaEquiv.symm x ≫ p = SSet.yonedaEquiv.symm b := by
  rw [SSet.yonedaEquiv_symm_comp, h]

private lemma exists_of_source {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    {b₀ b₁ : B _⦋0⦌} (e : B.Edge b₀ b₁) {x₀ : E _⦋0⦌} (hx₀ : p.app _ x₀ = b₀) :
    ∃ x₁ : E _⦋0⦌, p.app _ x₁ = b₁ := by
  let edgeMap : Δ[1] ⟶ B := SSet.yonedaEquiv.symm e.edge
  let iso0 : Δ[0] ≅ (SSet.stdSimplex.face (n := 1) {0} : SSet.{u}) :=
    SSet.stdSimplex.faceSingletonIso.{u} (0 : Fin 2)
  let top0 : (SSet.stdSimplex.face (n := 1) {0} : SSet.{u}) ⟶ E :=
    iso0.inv ≫ SSet.yonedaEquiv.symm x₀
  have h_an0 : SSet.anodyneExtensions (SSet.horn 1 (0 : Fin 2)).ι :=
    SSet.anodyneExtensions.horn_ι (0 : Fin 2)
  have h_an_face0 : SSet.anodyneExtensions (SSet.stdSimplex.face (n := 1) {0}).ι := by
    rw [← horn_one_zero_eq]
    exact h_an0
  have hlp : HasLiftingProperty (SSet.stdSimplex.face (n := 1) {0}).ι p :=
    SSet.anodyneExtensions.hasLeftLiftingProperty h_an_face0 p
  have h_top_p : top0 ≫ p = iso0.inv ≫ SSet.yonedaEquiv.symm b₀ := by
    calc top0 ≫ p = iso0.inv ≫ (SSet.yonedaEquiv.symm x₀ ≫ p) := by
          rw [Category.assoc]
      _ = iso0.inv ≫ SSet.yonedaEquiv.symm b₀ := by
          rw [yoneda_symm_comp_fibration_eq p hx₀]
  have h_face_edge : (SSet.stdSimplex.face (n := 1) {0}).ι ≫ edgeMap =
      iso0.inv ≫ SSet.yonedaEquiv.symm b₀ := by
    calc (SSet.stdSimplex.face (n := 1) {0}).ι ≫ edgeMap =
        iso0.inv ≫ (iso0.hom ≫ (SSet.stdSimplex.face (n := 1) {0}).ι) ≫ edgeMap := by
          simp [Iso.inv_hom_id_assoc]
      _ = iso0.inv ≫ (SSet.stdSimplex.{u}.δ (1 : Fin 2) ≫ edgeMap) := by
          rw [SSet.stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ]
      _ = iso0.inv ≫ SSet.yonedaEquiv.symm b₀ := by
          have hδ : SSet.stdSimplex.{u}.δ (1 : Fin 2) ≫ edgeMap =
              SSet.yonedaEquiv.symm b₀ := by
            have := e.δ_one_yonedaEquiv_symm
            simp [edgeMap]
          rw [hδ]
  have sq : CommSq top0 (SSet.stdSimplex.face (n := 1) {0}).ι p edgeMap :=
    ⟨by rw [h_top_p, h_face_edge]⟩
  have hl : sq.HasLift := hlp.sq_hasLift sq
  let l : Δ[1] ⟶ E := sq.lift
  have hl2 : l ≫ p = edgeMap := sq.fac_right
  let x₁ : E _⦋0⦌ := SSet.yonedaEquiv (SSet.stdSimplex.{u}.δ (0 : Fin 2) ≫ l)
  have h_symm_x₁ : SSet.yonedaEquiv.symm x₁ = SSet.stdSimplex.{u}.δ (0 : Fin 2) ≫ l := by
    simp [x₁]
  have h_x₁ : p.app _ x₁ = b₁ := by
    have h_eq : SSet.yonedaEquiv.symm x₁ ≫ p = SSet.yonedaEquiv.symm b₁ := by
      calc SSet.yonedaEquiv.symm x₁ ≫ p
          = (SSet.stdSimplex.{u}.δ (0 : Fin 2) ≫ l) ≫ p := by rw [h_symm_x₁]
        _ = SSet.stdSimplex.{u}.δ (0 : Fin 2) ≫ (l ≫ p) := by rw [Category.assoc]
        _ = SSet.stdSimplex.{u}.δ (0 : Fin 2) ≫ edgeMap := by rw [hl2]
        _ = SSet.yonedaEquiv.symm b₁ := by
          have := e.δ_zero_yonedaEquiv_symm
          simp [edgeMap]
    have h1 := congrArg SSet.yonedaEquiv h_eq
    simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h1
    exact h1
  exact ⟨x₁, h_x₁⟩

private lemma exists_of_target {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    {b₀ b₁ : B _⦋0⦌} (e : B.Edge b₀ b₁) {x₁ : E _⦋0⦌} (hx₁ : p.app _ x₁ = b₁) :
    ∃ x₀ : E _⦋0⦌, p.app _ x₀ = b₀ := by
  let edgeMap : Δ[1] ⟶ B := SSet.yonedaEquiv.symm e.edge
  let iso1 : Δ[0] ≅ (SSet.stdSimplex.face (n := 1) {1} : SSet.{u}) :=
    SSet.stdSimplex.faceSingletonIso.{u} (1 : Fin 2)
  let top1 : (SSet.stdSimplex.face (n := 1) {1} : SSet.{u}) ⟶ E :=
    iso1.inv ≫ SSet.yonedaEquiv.symm x₁
  have h_an1 : SSet.anodyneExtensions (SSet.horn 1 (1 : Fin 2)).ι :=
    SSet.anodyneExtensions.horn_ι (1 : Fin 2)
  have h_an_face1 : SSet.anodyneExtensions (SSet.stdSimplex.face (n := 1) {1}).ι := by
    rw [← horn_one_one_eq]
    exact h_an1
  have hlp : HasLiftingProperty (SSet.stdSimplex.face (n := 1) {1}).ι p :=
    SSet.anodyneExtensions.hasLeftLiftingProperty h_an_face1 p
  have h_top_p : top1 ≫ p = iso1.inv ≫ SSet.yonedaEquiv.symm b₁ := by
    calc top1 ≫ p = iso1.inv ≫ (SSet.yonedaEquiv.symm x₁ ≫ p) := by
          rw [Category.assoc]
      _ = iso1.inv ≫ SSet.yonedaEquiv.symm b₁ := by
          rw [yoneda_symm_comp_fibration_eq p hx₁]
  have h_face_edge : (SSet.stdSimplex.face (n := 1) {1}).ι ≫ edgeMap =
      iso1.inv ≫ SSet.yonedaEquiv.symm b₁ := by
    calc (SSet.stdSimplex.face (n := 1) {1}).ι ≫ edgeMap =
        iso1.inv ≫ (iso1.hom ≫ (SSet.stdSimplex.face (n := 1) {1}).ι) ≫ edgeMap := by
          simp [Iso.inv_hom_id_assoc]
      _ = iso1.inv ≫ (SSet.stdSimplex.{u}.δ (0 : Fin 2) ≫ edgeMap) := by
          rw [SSet.stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ]
      _ = iso1.inv ≫ SSet.yonedaEquiv.symm b₁ := by
          have hδ : SSet.stdSimplex.{u}.δ (0 : Fin 2) ≫ edgeMap =
              SSet.yonedaEquiv.symm b₁ := by
            have := e.δ_zero_yonedaEquiv_symm
            simp [edgeMap]
          rw [hδ]
  have sq : CommSq top1 (SSet.stdSimplex.face (n := 1) {1}).ι p edgeMap :=
    ⟨by rw [h_top_p, h_face_edge]⟩
  have hl : sq.HasLift := hlp.sq_hasLift sq
  let l : Δ[1] ⟶ E := sq.lift
  have hl2 : l ≫ p = edgeMap := sq.fac_right
  let x₀ : E _⦋0⦌ := SSet.yonedaEquiv (SSet.stdSimplex.{u}.δ (1 : Fin 2) ≫ l)
  have h_symm_x₀ : SSet.yonedaEquiv.symm x₀ = SSet.stdSimplex.{u}.δ (1 : Fin 2) ≫ l := by
    simp [x₀]
  have h_x₀ : p.app _ x₀ = b₀ := by
    have h_eq : SSet.yonedaEquiv.symm x₀ ≫ p = SSet.yonedaEquiv.symm b₀ := by
      calc SSet.yonedaEquiv.symm x₀ ≫ p
          = (SSet.stdSimplex.{u}.δ (1 : Fin 2) ≫ l) ≫ p := by rw [h_symm_x₀]
        _ = SSet.stdSimplex.{u}.δ (1 : Fin 2) ≫ (l ≫ p) := by rw [Category.assoc]
        _ = SSet.stdSimplex.{u}.δ (1 : Fin 2) ≫ edgeMap := by rw [hl2]
        _ = SSet.yonedaEquiv.symm b₀ := by
          have := e.δ_one_yonedaEquiv_symm
          simp [edgeMap]
    have h1 := congrArg SSet.yonedaEquiv h_eq
    simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h1
    exact h1
  exact ⟨x₀, h_x₀⟩

/-- For a Kan fibration p:E→B and a directed edge b₀→b₁ in B, the strict-fiber subcomplex over b₀ is
nonbottom if and only if the one over b₁ is nonbottom. Equivalently, their fibers are nonempty
simultaneously. -/
theorem fiber_neq_bot_iff_of_edge {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    {b₀ b₁ : B _⦋0⦌} (e : B.Edge b₀ b₁) :
    fiber p b₀ ≠ ⊥ ↔ fiber p b₁ ≠ ⊥ := by
  rw [fiber_ne_bot_iff_exists_vertex, fiber_ne_bot_iff_exists_vertex]
  constructor
  · rintro ⟨x₀, hx₀⟩
    exact exists_of_source p e hx₀
  · rintro ⟨x₁, hx₁⟩
    exact exists_of_target p e hx₁

end SSet.Subcomplex
