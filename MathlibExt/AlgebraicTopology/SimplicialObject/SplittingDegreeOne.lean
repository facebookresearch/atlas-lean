/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Split

/-!
# Actual degree-one coproduct coordinates in a native splitting

There are exactly two original epi indices over [1]: identity and the
zeroth degeneracy to [0]. Native coproduct descent therefore assembles
maps from the new nondegenerate summand and the old degenerate summand,
without assuming a global coproduct structure or a desired IsIso.
This canonical general provider is needed by relative-prism degree extension.
Source UNEXECUTED.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject.Splitting

abbrev oneDegenerate : IndexSet (op ⦋1⦌) := IndexSet.mk (SimplexCategory.σ (0 : Fin 1))

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

/-- The actual two-summand family, with original zero and one components. -/
def oneFamily (old : s.N 0 ⟶ Z) (new : s.N 1 ⟶ Z) (a : IndexSet (op ⦋1⦌)) :
    s.N a.1.unop.len ⟶ Z := by
  classical
  exact if h : a = IndexSet.id _ then
      eqToHom (congrArg (fun b => s.N b.1.unop.len) h) ≫ new
    else
      eqToHom (congrArg (fun b => s.N b.1.unop.len) ((oneIndex_cases a).resolve_left h)) ≫ old

def oneDesc (old : s.N 0 ⟶ Z) (new : s.N 1 ⟶ Z) : X.obj (op ⦋1⦌) ⟶ Z :=
  s.desc (op ⦋1⦌) (oneFamily s old new)

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
