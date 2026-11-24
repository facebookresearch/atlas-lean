/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomPrism
public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalence
import MathlibExt.AlgebraicTopology.Quasicategory.Core
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# Vertical edges of simplicial prisms

The vertical edge at a vertex of `B` is the pair of its degenerate edge
and the fundamental edge of `Δ[1]`. This module records equivalence of
all vertical edges, restriction and degenerate prisms, naturality of the
endpoint sections, and the boundary facts used for prism attachments.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace SSet

/-- Two simplices of `Δ[m]` whose order maps agree at every index are
equal. -/
private lemma stdSimplex_ext_asOrderHom {m : ℕ} {Δ : SimplexCategoryᵒᵖ}
    {x y : (Δ[m] : SSet.{u}).obj Δ}
    (h : ∀ k : Fin (Δ.unop.len + 1),
      (stdSimplex.asOrderHom x) k = (stdSimplex.asOrderHom y) k) :
    x = y := by
  apply stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  exact OrderHom.ext _ _ (funext fun k => h k)

section PrismOneVerticals

variable {A B C : SSet.{u}}

/-- The vertical `1`-simplex of `B ⊗ Δ[1]` at a vertex `x`:
the pair of the degenerate simplex at `x` and the fundamental
simplex of `Δ[1]`. -/
noncomputable def verticalOneSimplex (x : B _⦋0⦌) :
    (B ⊗ Δ[1]) _⦋1⦌ :=
  (B.σ 0 x, yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))

/-- Every vertical edge of the prism `F` is an equivalence. -/
def PrismOneVerticalsEquivalences (F : B ⊗ Δ[1] ⟶ C) : Prop :=
  ∀ x : B _⦋0⦌,
    (Edge.mk' (F.app _ (verticalOneSimplex x))).IsEquivalence

lemma verticalOneSimplex_fst (x : B _⦋0⦌) :
    (verticalOneSimplex x).1 = B.σ 0 x :=
  rfl

lemma verticalOneSimplex_snd (x : B _⦋0⦌) :
    (verticalOneSimplex x).2 = yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) :=
  rfl

/-- Whiskering sends vertical simplices to vertical simplices:
componentwise by `σ`-naturality in the first factor. -/
lemma whiskerRight_app_verticalOneSimplex (f : A ⟶ B)
    (x : A _⦋0⦌) :
    (f ▷ Δ[1]).app _ (verticalOneSimplex x) =
      verticalOneSimplex (f.app _ x) := by
  apply Prod.ext
  · change f.app _ (A.σ 0 x) = B.σ 0 (f.app _ x)
    exact σ_naturality_apply f 0 x
  · rfl

/-- Verticals of a restricted prism are verticals of the
original prism at the image vertices. -/
lemma prismOneVerticalsEquivalences_whiskerRight_comp
    (f : A ⟶ B) (F : B ⊗ Δ[1] ⟶ C)
    (hF : PrismOneVerticalsEquivalences F) :
    PrismOneVerticalsEquivalences ((f ▷ Δ[1]) ≫ F) := by
  intro x
  refine (Edge.isEquivalence_iff_of_edge_eq ?_).2 (hF (f.app _ x))
  change ((f ▷ Δ[1]) ≫ F).app _ (verticalOneSimplex x) =
    F.app _ (verticalOneSimplex (f.app _ x))
  simp only [NatTrans.comp_app, types_comp_apply,
    whiskerRight_app_verticalOneSimplex]

/-- Verticals of a degenerate (first-projection) prism are
degenerate edges, hence equivalences. -/
lemma prismOneVerticalsEquivalences_fst_comp (g : B ⟶ C) :
    PrismOneVerticalsEquivalences
      (CartesianMonoidalCategory.fst B Δ[1] ≫ g) := by
  intro x
  have hval : (CartesianMonoidalCategory.fst B Δ[1] ≫ g).app _
        (verticalOneSimplex x) = C.σ 0 (g.app _ x) := by
    change g.app _
        ((CartesianMonoidalCategory.fst B Δ[1]).app _
          (verticalOneSimplex x)) = _
    change g.app _ (B.σ 0 x) = _
    exact σ_naturality_apply g 0 x
  refine (Edge.isEquivalence_iff_of_edge_eq ?_).2
    (Edge.isEquivalence_id (g.app _ x))
  change (CartesianMonoidalCategory.fst B Δ[1] ≫ g).app _
      (verticalOneSimplex x) = (Edge.id (g.app _ x)).edge
  rw [Edge.id_edge]
  exact hval

/-- Naturality of the prism sections in the base, pointwise:
both composites send a simplex `s` to the pair
`(i.app _ s, constant κ)`. -/
lemma prismSectionAt_comp_whiskerRight (i : A ⟶ B) {m : ℕ}
    (κ : Fin (m + 1)) :
    prismSectionAt A κ ≫ (i ▷ Δ[m]) = i ≫ prismSectionAt B κ := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro s
  apply Prod.ext
  · simp only [NatTrans.comp_app, types_comp_apply,
      whiskerRight_app_apply_fst, prismSectionAt_app_fst]
  · apply stdSimplex_ext_asOrderHom
    intro k
    simp only [NatTrans.comp_app, types_comp_apply,
      whiskerRight_app_apply_snd, asOrderHom_prismSectionAt_app_snd]

end PrismOneVerticals

section PrismOneCellPrelims

variable {n : ℕ}

/-- The section at any vertex is a section of the first
projection, pointwise by `prismSectionAt_app_fst`. -/
lemma prismSectionAt_comp_fst (X : SSet.{u}) {m : ℕ}
    (κ : Fin (m + 1)) :
    prismSectionAt X κ ≫ CartesianMonoidalCategory.fst X Δ[m] =
      𝟙 X := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro s
  exact prismSectionAt_app_fst X κ s

/-- Whiskering the inclusion of the face `{0}` is the first
projection followed by the section at `0`: pointwise, a
simplex of the face is constant `0`
(`stdSimplex.mem_face_iff`), as is the second component of
the section (`asOrderHom_prismSectionAt_app_snd`). -/
lemma whiskerLeft_faceZero_ι (A : SSet.{u}) :
    A ◁ (stdSimplex.face {0}).ι =
      CartesianMonoidalCategory.fst A
          ((stdSimplex.face {0} :
            (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ≫
        prismSectionAt A 0 := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext
  · rfl
  · apply stdSimplex_ext_asOrderHom
    intro k
    have h2 : Finset.image
          (stdSimplex.objEquiv z.2.val).toOrderHom ⊤ ≤
        ({0} : Finset (Fin 2)) := z.2.2
    have hz0 : (stdSimplex.asOrderHom z.2.val) k = 0 :=
      Finset.mem_singleton.1
        (h2 (Finset.mem_image.2 ⟨k, Finset.mem_univ k, rfl⟩))
    simp only [NatTrans.comp_app, types_comp_apply,
      asOrderHom_prismSectionAt_app_snd]
    exact hz0

/-- Whiskering the inclusion of the face `{1}` is the first
projection followed by the section at `1` (the mirror). -/
lemma whiskerLeft_faceOne_ι (A : SSet.{u}) :
    A ◁ (stdSimplex.face {1}).ι =
      CartesianMonoidalCategory.fst A
          ((stdSimplex.face {1} :
            (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ≫
        prismSectionAt A 1 := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext
  · rfl
  · apply stdSimplex_ext_asOrderHom
    intro k
    have h2 : Finset.image
          (stdSimplex.objEquiv z.2.val).toOrderHom ⊤ ≤
        ({1} : Finset (Fin 2)) := z.2.2
    have hz1 : (stdSimplex.asOrderHom z.2.val) k = 1 :=
      Finset.mem_singleton.1
        (h2 (Finset.mem_image.2 ⟨k, Finset.mem_univ k, rfl⟩))
    simp only [NatTrans.comp_app, types_comp_apply,
      asOrderHom_prismSectionAt_app_snd]
    exact hz1

/-- For `n ≥ 1` every vertex of `Δ[n]` lies in `∂Δ[n]`: its
single value misses any other vertex
(`mem_boundary_iff_notMem_range`). -/
lemma vertex_mem_boundary_of_one_le (hn : 1 ≤ n)
    (x : Δ[n] _⦋0⦌) : x ∈ (∂Δ[n]).obj _ := by
  by_cases hx : x 0 = 0
  · refine (mem_boundary_iff_notMem_range x).2 ⟨⟨1, by omega⟩, ?_⟩
    rintro ⟨t, ht⟩
    have ht0 : t = 0 := by
      apply Fin.ext
      have h2 := t.2
      omega
    subst ht0
    rw [hx] at ht
    exact absurd ht (by simp)
  · refine (mem_boundary_iff_notMem_range x).2 ⟨0, ?_⟩
    rintro ⟨t, ht⟩
    have ht0 : t = 0 := by
      apply Fin.ext
      have h2 := t.2
      omega
    subst ht0
    exact hx ht

/-- For `n ≥ 1` the degenerate simplex at any vertex of
`Δ[n]` lies in `∂Δ[n]`, by closure of a subcomplex under
simplicial maps. -/
lemma sigma_zero_mem_boundary_of_one_le (hn : 1 ≤ n)
    (x : Δ[n] _⦋0⦌) : Δ[n].σ 0 x ∈ (∂Δ[n]).obj _ :=
  (∂Δ[n]).map _ (vertex_mem_boundary_of_one_le hn x)

/-- Maps out of `(∂Δ[0] : SSet) ⊗ W` are unique, since
`∂Δ[0] = ⊥` has no simplices in any degree. -/
lemma eq_of_boundaryZero_tensor {W C : SSet.{u}}
    (F G : (∂Δ[0] : SSet.{u}) ⊗ W ⟶ C) : F = G := by
  apply NatTrans.ext
  funext Δ
  apply ConcreteCategory.hom_ext
  intro z
  have h := z.1.2
  simp only [boundary_zero, Subfunctor.bot_obj,
    Set.mem_empty_iff_false] at h

end PrismOneCellPrelims

end SSet
