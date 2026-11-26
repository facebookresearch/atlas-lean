/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Split

/-!
# Two-summand coproduct coordinates in simplicial degree one

For a simplicial splitting s of X in an arbitrary category C, a summand index in degree one is
an epimorphism [1] → [k]. There are exactly two indices: the identity of [1] and the
degeneracy σ₀ : [1] → [0]. Their cofan maps are ι₁ : N₁ → X₁ and ι₀ ≫ X.σ₀ : N₀ → X₁.

Given old : N₀ → Z and new : N₁ → Z, the splitting coproduct property defines a descendant X₁
→ Z with these two component values. Conversely, two maps out of X₁ are equal if they agree on
both summands. The object and morphism universes of C are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject.Splitting

/-- Degenerate summand index in simplicial degree one.

The index oneDegenerate in IndexSet(op [1]) is the epimorphism σ₀ : [1] → [0], corresponding
to the degree-zero summand of a splitting. -/
abbrev oneDegenerate : IndexSet (op ⦋1⦌) := IndexSet.mk (SimplexCategory.σ (0 : Fin 1))

/-- Classification of splitting indices in degree one.

Every index in IndexSet(op [1]) is either the identity epimorphism of [1] or oneDegenerate,
the unique epimorphism σ₀ to [0]. -/
theorem oneIndex_cases (a : IndexSet (op ⦋1⦌)) : a = IndexSet.id _ ∨ a = oneDegenerate := by
  by_cases h : a.EqId
  · exact Or.inl h
  · right
    have hd : a.1.unop.len = 0 := by
      have hn := (a.eqId_iff_len_le).not.mp h
      change ¬ 1 ≤ a.1.unop.len at hn
      omega
    rcases a with ⟨⟨⟨m⟩⟩, ⟨e, he⟩⟩
    change m = 0 at hd
    subst m
    have heq : e = SimplexCategory.σ (0 : Fin 1) := SimplexCategory.isTerminalZero.hom_ext _ _
    subst e
    rfl

private theorem identity_ne_degenerate : IndexSet.id (op ⦋1⦌) ≠ oneDegenerate := by
  intro h
  have hn := congrArg (fun a : IndexSet (op ⦋1⦌) => a.1.unop.len) h
  change 1 = 0 at hn
  exact Nat.one_ne_zero hn

variable {C : Type u} [Category.{v} C] {X : SimplicialObject C} (s : Splitting X) {Z : C}

/-- Component family for a degree-one splitting descendant.

For a splitting s and maps old : N₀ → Z, new : N₁ → Z, assign new to the identity index and
old to the σ₀ index. The equality of each index with its representative supplies the domain
identification. -/
def oneFamily (old : s.N 0 ⟶ Z) (new : s.N 1 ⟶ Z) (a : IndexSet (op ⦋1⦌)) :
    s.N a.1.unop.len ⟶ Z := by
  classical
  exact if h : a = IndexSet.id _ then
      eqToHom (congrArg (fun b => s.N b.1.unop.len) h) ≫ new
    else
      eqToHom (congrArg (fun b => s.N b.1.unop.len) ((oneIndex_cases a).resolve_left h)) ≫ old

/-- Descendant from the two degree-one summands.

For a splitting s of X, maps old : N₀ → Z and new : N₁ → Z determine oneDesc : X₁ → Z by the
splitting's degree-one coproduct universal property. -/
def oneDesc (old : s.N 0 ⟶ Z) (new : s.N 1 ⟶ Z) : X.obj (op ⦋1⦌) ⟶ Z :=
  s.desc (op ⦋1⦌) (oneFamily s old new)

/-- Nondegenerate component of a degree-one descendant.

For the map oneDesc(old,new) : X₁ → Z, its composite with ι₁ : N₁ → X₁ is new. -/
@[reassoc]
theorem oneDesc_new (old : s.N 0 ⟶ Z) (new : s.N 1 ⟶ Z) : s.ι 1 ≫ s.oneDesc old new = new := by
  classical
  have h := s.ι_desc (op ⦋1⦌) (oneFamily s old new) (IndexSet.id _)
  rw [s.cofan_inj_id 1] at h
  have hf : oneFamily s old new (IndexSet.id (op ⦋1⦌)) = new := by
    dsimp only [oneFamily]
    rw [dif_pos rfl]
    dsimp only [IndexSet.id]
    exact Category.id_comp _
  exact h.trans hf

/-- Degenerate component of a degree-one descendant.

For oneDesc(old,new), the composite (ι₀ ≫ X.σ₀) ≫ oneDesc is old : N₀ → Z. This is the
component indexed by σ₀ : [1] → [0]. -/
@[reassoc]
theorem oneDesc_old (old : s.N 0 ⟶ Z) (new : s.N 1 ⟶ Z) :
    (s.ι 0 ≫ X.σ (0 : Fin 1)) ≫ s.oneDesc old new = old := by
  classical
  have h := s.ι_desc (op ⦋1⦌) (oneFamily s old new) oneDegenerate
  rw [s.cofan_inj_eq] at h
  change (s.ι 0 ≫ X.σ (0 : Fin 1)) ≫ s.oneDesc old new =
    oneFamily s old new oneDegenerate at h
  have hf : oneFamily s old new oneDegenerate = old := by
    dsimp only [oneFamily]
    rw [dif_neg (Ne.symm identity_ne_degenerate)]
    dsimp only [oneDegenerate, IndexSet.mk]
    exact Category.id_comp _
  exact h.trans hf

/-- Two-summand extensionality in simplicial degree one.

For a splitting s of X, maps f,g : X₁ → Z are equal when ι₁ ≫ f = ι₁ ≫ g and (ι₀ ≫ X.σ₀) ≫ f =
(ι₀ ≫ X.σ₀) ≫ g. These are the two coproduct summands in degree one. -/
theorem one_hom_ext {f g : X.obj (op ⦋1⦌) ⟶ Z}
    (hnew : s.ι 1 ≫ f = s.ι 1 ≫ g)
    (hold : (s.ι 0 ≫ X.σ (0 : Fin 1)) ≫ f = (s.ι 0 ≫ X.σ (0 : Fin 1)) ≫ g) : f = g := by
  apply s.hom_ext'
  intro a
  rcases oneIndex_cases a with rfl | rfl
  · rw [s.cofan_inj_id 1]
    exact hnew
  · rw [s.cofan_inj_eq]
    change (s.ι 0 ≫ X.σ (0 : Fin 1)) ≫ f =
      (s.ι 0 ≫ X.σ (0 : Fin 1)) ≫ g
    exact hold

end CategoryTheory.SimplicialObject.Splitting

end
