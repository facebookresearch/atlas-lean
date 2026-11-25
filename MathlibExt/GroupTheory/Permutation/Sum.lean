/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Permutations supported on the first summand

Extending a permutation by the identity on the second summand gives exactly
its pointwise stabilizer. The two summands have independent universes and
need no finiteness assumptions.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Equiv.Perm

/-- Extend a permutation by the identity on the second summand. -/
def sumInlHom (A : Type u) (B : Type v) : Perm A →* Perm (A ⊕ B) :=
  (sumCongrHom A B).comp
    { toFun := fun a => (a, 1)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

@[simp]
theorem sumInlHom_apply_inl (A : Type u) (B : Type v) (p : Perm A) (a : A) :
    sumInlHom A B p (Sum.inl a) = Sum.inl (p a) := rfl

@[simp]
theorem sumInlHom_apply_inr (A : Type u) (B : Type v) (p : Perm A) (b : B) :
    sumInlHom A B p (Sum.inr b) = Sum.inr b := rfl

/-- First-summand extension preserves distinct permutations. -/
theorem sumInlHom_injective (A : Type u) (B : Type v) :
    Function.Injective (sumInlHom A B) := by
  intro p q h
  ext a
  exact Sum.inl.inj (congrArg (fun r : Perm (A ⊕ B) => r (Sum.inl a)) h)

/-- Its image is exactly the permutations fixing every point of the second summand. -/
theorem mem_sumInlHom_range_iff (A : Type u) (B : Type v) (s : Perm (A ⊕ B)) :
    s ∈ (sumInlHom A B).range ↔ ∀ b : B, s (Sum.inr b) = Sum.inr b := by
  classical
  constructor
  · rintro ⟨p, rfl⟩ b
    rfl
  · intro hfix
    have hleft : ∀ a : A, ∃ a' : A, s (Sum.inl a) = Sum.inl a' := by
      intro a
      cases hs : s (Sum.inl a) with
      | inl a' => exact ⟨a', rfl⟩
      | inr b =>
        have h := s.injective (hs.trans (hfix b).symm)
        cases h
    let f : A → A := fun a => Classical.choose (hleft a)
    have hf (a : A) : s (Sum.inl a) = Sum.inl (f a) :=
      Classical.choose_spec (hleft a)
    have hinj : Function.Injective f := by
      intro a a' h
      apply Sum.inl.inj
      apply s.injective
      exact (hf a).trans ((congrArg Sum.inl h).trans (hf a').symm)
    have hsurj : Function.Surjective f := by
      intro a
      obtain ⟨x, hx⟩ := s.surjective (Sum.inl a)
      cases x with
      | inl a' => exact ⟨a', Sum.inl.inj ((hf a').symm.trans hx)⟩
      | inr b =>
        have h : Sum.inr b = Sum.inl a := (hfix b).symm.trans hx
        cases h
    let p : Perm A := Equiv.ofBijective f ⟨hinj, hsurj⟩
    refine ⟨p, ?_⟩
    ext x
    cases x with
    | inl a => exact (hf a).symm
    | inr b => exact (hfix b).symm

end Equiv.Perm
