/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

/-!
# Eventually constant inverse sequences

If the successor maps of an inverse sequence are isomorphisms from a stage
onward, the sequence is eventually constant. Its limit exists and is
canonically isomorphic to any chosen stable stage. The forward comparison is
the limit projection to that stage.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor

universe v u

variable {C : Type u} [Category.{v} C]

/-- If the successor maps of an inverse sequence are isomorphisms from stage `N` onward, then the
sequence is eventually constant to stage `N`. -/
theorem isEventuallyConstantTo_op_of_eventually_transition_iso
    (A : ℕᵒᵖ ⥤ C) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n →
      IsIso (A.map (homOfLE (Nat.le_succ n)).op)) :
    A.IsEventuallyConstantTo (op N) := by
  have key : ∀ k : ℕ,
      IsIso (A.map (homOfLE (Nat.le_add_right N k)).op) := by
    intro k
    induction k with
    | zero =>
        have h0 : (homOfLE (Nat.le_add_right N 0)).op =
            𝟙 (op N) :=
          Subsingleton.elim _ _
        rw [h0]
        infer_instance
    | succ k ih =>
        have hdecomp :
            (homOfLE (Nat.le_add_right N (k + 1))).op =
              (homOfLE (Nat.le_add_right (N + k) 1)).op ≫
                (homOfLE (Nat.le_add_right N k)).op :=
          Subsingleton.elim _ _
        rw [hdecomp, A.map_comp]
        have hstep : IsIso
            (A.map (homOfLE (Nat.le_add_right (N + k) 1)).op) := by
          have hs := h (N + k) (Nat.le_add_right N k)
          exact hs
        exact IsIso.comp_isIso' hstep ih
  intro i f
  obtain ⟨m⟩ := i
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom f.unop)
  have hf : f = (homOfLE (Nat.le_add_right N k)).op :=
    Subsingleton.elim _ _
  rw [hf]
  exact key k

/-- An inverse sequence whose successor maps are eventually isomorphisms has a limit, without
requiring ambient countable limits. -/
theorem hasLimit_of_eventually_transition_iso
    (A : ℕᵒᵖ ⥤ C) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n →
      IsIso (A.map (homOfLE (Nat.le_succ n)).op)) :
    HasLimit A :=
  (isEventuallyConstantTo_op_of_eventually_transition_iso A N h).hasLimit

/-- The chosen limit of an eventually constant inverse sequence is canonically isomorphic to a
stable stage, with forward map the corresponding limit projection. -/
noncomputable def sequentialLimitIsoAtOfEventuallyTransitionIso
    (A : ℕᵒᵖ ⥤ C) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n →
      IsIso (A.map (homOfLE (Nat.le_succ n)).op))
    [HasLimit A] :
    limit A ≅ A.obj (op N) := by
  let hA := isEventuallyConstantTo_op_of_eventually_transition_iso A N h
  letI : IsIso (limit.π A (op N)) :=
    hA.isIso_π_of_isLimit (limit.isLimit A)
  exact asIso (limit.π A (op N))

/-- The comparison of an eventually constant inverse sequence’s limit with a stable stage has
forward map equal to the limit projection at that stage. -/
@[simp]
theorem sequentialLimitIsoAtOfEventuallyTransitionIso_hom
    (A : ℕᵒᵖ ⥤ C) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n →
      IsIso (A.map (homOfLE (Nat.le_succ n)).op))
    [HasLimit A] :
    (sequentialLimitIsoAtOfEventuallyTransitionIso A N h).hom =
      limit.π A (op N) :=
  rfl

end CategoryTheory.Functor

end
