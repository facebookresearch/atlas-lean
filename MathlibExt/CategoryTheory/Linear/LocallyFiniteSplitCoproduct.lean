/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# A finite-sum inverse for a countable split coproduct

Let `C` be preadditive and suppose a family `F : ℕ → C` has a coproduct. Given maps `i_j : F_j
→ X` and `p_j : X → F_j`, assume `i_j ≫ p_j = id`, distinct cross terms `i_j ≫ p_k` vanish,
and `p_j = 0` for `j>N` at a fixed cutoff `N`.

If `∑_(j=0)^N p_j ≫ i_j = id_X`, the coproduct descent of the `i_j` is an isomorphism. Its
inverse is the finite sum `∑_(j=0)^N p_j ≫ ι_j`. The splitting and finite-support hypotheses
prove the inverse identity on the whole coproduct.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u v

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The finite-sum map into a countable coproduct.

For maps `p_j : X → F_j` and cutoff `N`, sum `p_j` followed by the coproduct inclusion over `0
≤ j ≤ N`. -/
def finiteSplitCoproductInverse (F : ℕ → C) [HasCoproduct F] {X : C}
    (p : ∀ i : ℕ, X ⟶ F i) (N : ℕ) : X ⟶ ∐ F :=
  ∑ j : Fin (N + 1), p j.val ≫ Sigma.ι F j.val

/-- The finite projector-sum identity for coproduct descent.

If `∑_(j=0)^N p_j ≫ i_j = id_X`, the finite-sum map into the coproduct followed by the descent
of the `i_j` is the identity on `X`. -/
@[reassoc]
theorem finiteSplitCoproductInverse_desc (F : ℕ → C) [HasCoproduct F] {X : C}
    (i : ∀ j : ℕ, F j ⟶ X) (p : ∀ j : ℕ, X ⟶ F j) (N : ℕ)
    (hsum : (∑ j : Fin (N + 1), p j.val ≫ i j.val) = 𝟙 X) :
    finiteSplitCoproductInverse F p N ≫ Sigma.desc i = 𝟙 X := by
  rw [finiteSplitCoproductInverse, Preadditive.sum_comp]
  simp only [Category.assoc, Sigma.ι_desc]
  exact hsum

/-- The coproduct inverse identity from split orthogonal projections.

If each `i_j` splits `p_j`, cross terms vanish for distinct indices, and all `p_j` above `N`
are zero, the inclusion descent followed by the finite-sum inverse is the identity on the
coproduct. -/
@[reassoc]
theorem desc_finiteSplitCoproductInverse (F : ℕ → C) [HasCoproduct F] {X : C}
    (i : ∀ j : ℕ, F j ⟶ X) (p : ∀ j : ℕ, X ⟶ F j) (N : ℕ)
    (hsplit : ∀ j : ℕ, i j ≫ p j = 𝟙 (F j))
    (hcross : ∀ j k : ℕ, j ≠ k → i j ≫ p k = 0)
    (hsupport : ∀ j : ℕ, N < j → p j = 0) :
    Sigma.desc i ≫ finiteSplitCoproductInverse F p N = 𝟙 (∐ F) := by
  apply Sigma.hom_ext
  intro j
  rw [Sigma.ι_desc_assoc, finiteSplitCoproductInverse, Preadditive.comp_sum]
  by_cases hj : j ≤ N
  · let j₀ : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    rw [Finset.sum_eq_single j₀]
    · simp only [j₀, ← Category.assoc, hsplit, Category.id_comp, Category.comp_id]
    · intro k hk hne
      have hjk : j ≠ k.val := fun h => hne (Fin.ext h.symm)
      rw [← Category.assoc, hcross j k.val hjk, zero_comp]
    · simp
  · have hj' : N < j := by omega
    have hid : 𝟙 (F j) = 0 := by rw [← hsplit j, hsupport j hj', comp_zero]
    have hi : Sigma.ι F j = 0 := by
      rw [← Category.id_comp (Sigma.ι F j), hid, zero_comp]
    rw [Category.comp_id, hi]
    apply Finset.sum_eq_zero
    intro k hk
    have hjk : j ≠ k.val := by have hkn := k.isLt; omega
    rw [← Category.assoc, hcross j k.val hjk, zero_comp]

/-- The isomorphism given by finitely supported split coproduct data.

The split, cross-vanishing, support, and projector-sum equations identify `∐ F` with `X`, with
forward map the inclusion descent and inverse the finite sum of projections into coproduct
inclusions. -/
def finiteSplitCoproductIso (F : ℕ → C) [HasCoproduct F] {X : C}
    (i : ∀ j : ℕ, F j ⟶ X) (p : ∀ j : ℕ, X ⟶ F j) (N : ℕ)
    (hsplit : ∀ j : ℕ, i j ≫ p j = 𝟙 (F j))
    (hcross : ∀ j k : ℕ, j ≠ k → i j ≫ p k = 0)
    (hsupport : ∀ j : ℕ, N < j → p j = 0)
    (hsum : (∑ j : Fin (N + 1), p j.val ≫ i j.val) = 𝟙 X) : (∐ F) ≅ X where
  hom := Sigma.desc i
  inv := finiteSplitCoproductInverse F p N
  hom_inv_id := desc_finiteSplitCoproductInverse F i p N hsplit hcross hsupport
  inv_hom_id := finiteSplitCoproductInverse_desc F i p N hsum

end CategoryTheory.Limits
