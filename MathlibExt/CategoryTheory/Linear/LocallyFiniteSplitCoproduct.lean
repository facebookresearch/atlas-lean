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
# Actual locally finite split-image coproduct inverses

For an original countable family of split images, the actual forward map is
the native coproduct descent of the image inclusions. When the original
projections have finite support and their actual projector sum is identity,
the inverse is the finite native sum of projections followed by coproduct
inclusions. Cross-image identities and the actual splits prove both inverse
laws. No coproduct isomorphism certificate, exactness or global AB5
assumption is supplied.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u v

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The actual finite sum of the original projections into the original countable coproduct. -/
def finiteSplitCoproductInverse (F : ℕ → C) [HasCoproduct F] {X : C}
    (p : ∀ i : ℕ, X ⟶ F i) (N : ℕ) : X ⟶ ∐ F :=
  ∑ j : Fin (N + 1), p j.val ≫ Sigma.ι F j.val

/-- The actual finite projector sum proves the exact right inverse to the original inclusion descent. -/
@[reassoc]
theorem finiteSplitCoproductInverse_desc (F : ℕ → C) [HasCoproduct F] {X : C}
    (i : ∀ j : ℕ, F j ⟶ X) (p : ∀ j : ℕ, X ⟶ F j) (N : ℕ)
    (hsum : (∑ j : Fin (N + 1), p j.val ≫ i j.val) = 𝟙 X) :
    finiteSplitCoproductInverse F p N ≫ Sigma.desc i = 𝟙 X := by
  rw [finiteSplitCoproductInverse, Preadditive.sum_comp]
  simp only [Category.assoc, Sigma.ι_desc]
  exact hsum

/-- Actual cross-image and split identities prove the original descent followed by its finite inverse is identity. -/
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

/-- The original countable split-image descent has its actual finite-sum inverse. -/
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
