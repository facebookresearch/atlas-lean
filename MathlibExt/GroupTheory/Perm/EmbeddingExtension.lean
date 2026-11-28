/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

module

public import MathlibExt.GroupTheory.Perm.ViaEmbedding
public import Mathlib.Data.Fin.Basic
import Lean.Elab.Tactic.Omega

/-!
# Permutations carrying one finite embedding to another

Starting with the identity, successively swap the current image of each
source label with its target image. The complete construction commutes with
every embedding of the ambient type. This supplies compatible permutation
representatives for the symmetric free-smash argument in MMSS Proposition 12.3.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
namespace Equiv.Perm
variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

/-- Apply the successive swaps for the displayed prefix of the finite domain. -/
def alignFiniteEmbeddingsAux {n : ℕ} (a b : Fin n ↪ α) : ℕ → Perm α
  | 0 => 1
  | k + 1 => if hk : k < n then
      Equiv.swap (alignFiniteEmbeddingsAux a b k (a ⟨k, hk⟩)) (b ⟨k, hk⟩) *
        alignFiniteEmbeddingsAux a b k
    else alignFiniteEmbeddingsAux a b k

/-- Every source label inside any completed prefix is carried to its displayed target image. -/
theorem alignFiniteEmbeddingsAux_apply {n : ℕ} (a b : Fin n ↪ α)
    (k : ℕ) (j : Fin n) (hj : j.val < k) :
    alignFiniteEmbeddingsAux a b k (a j) = b j := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    by_cases hk : k < n
    · simp only [alignFiniteEmbeddingsAux, dite_eq_left hk, mul_apply]
      by_cases hjk : j.val = k
      · have he : j = ⟨k, hk⟩ := Fin.ext hjk
        rw [he]
        exact Equiv.swap_apply_left _ _
      · have hlt : j.val < k := by omega
        have hp := ih j hlt
        rw [hp]
        have hji : j ≠ ⟨k, hk⟩ := by
          intro he
          exact hjk (congrArg Fin.val he)
        have h₁ : b j ≠ alignFiniteEmbeddingsAux a b k (a ⟨k, hk⟩) := by
          intro he
          exact hji (a.injective ((alignFiniteEmbeddingsAux a b k).injective (hp.trans he)))
        have h₂ : b j ≠ b ⟨k, hk⟩ := b.injective.ne hji
        exact Equiv.swap_apply_of_ne_of_ne h₁ h₂
    · simp only [alignFiniteEmbeddingsAux, dite_eq_right hk]
      exact ih j (by omega)

/-- Every entire prefix of the actual swap construction commutes with every ambient embedding. -/
theorem alignFiniteEmbeddingsAux_viaEmbedding {n : ℕ}
    (a b : Fin n ↪ α) (ι : α ↪ β) (k : ℕ) :
    (alignFiniteEmbeddingsAux a b k).viaEmbedding ι =
      alignFiniteEmbeddingsAux (a.trans ι) (b.trans ι) k := by
  induction k with
  | zero =>
    change (viaEmbeddingHom ι) 1 = 1
    exact (viaEmbeddingHom ι).map_one
  | succ k ih =>
    by_cases hk : k < n
    · simp only [alignFiniteEmbeddingsAux, dite_eq_left hk]
      rw [← viaEmbeddingHom_apply, MonoidHom.map_mul, viaEmbeddingHom_swap,
        viaEmbeddingHom_apply, ih]
      rw [← ih]
      simp only [Function.Embedding.trans_apply, viaEmbedding_apply]
    · simp only [alignFiniteEmbeddingsAux, dite_eq_right hk]
      exact ih

/-- A permutation carrying one finite embedding to the other, constructed by successive swaps. -/
def alignFiniteEmbeddings {n : ℕ} (a b : Fin n ↪ α) : Perm α :=
  alignFiniteEmbeddingsAux a b n

/-- The constructed permutation carries every displayed source image to the corresponding target. -/
theorem alignFiniteEmbeddings_apply {n : ℕ} (a b : Fin n ↪ α) (j : Fin n) :
    alignFiniteEmbeddings a b (a j) = b j :=
  alignFiniteEmbeddingsAux_apply a b n j j.isLt

/-- An empty finite domain produces the actual identity permutation. -/
theorem alignFiniteEmbeddings_zero (a b : Fin 0 ↪ α) : alignFiniteEmbeddings a b = 1 := rfl

/-- The same complete swap construction commutes with every ambient embedding. -/
theorem alignFiniteEmbeddings_viaEmbedding {n : ℕ}
    (a b : Fin n ↪ α) (ι : α ↪ β) :
    (alignFiniteEmbeddings a b).viaEmbedding ι =
      alignFiniteEmbeddings (a.trans ι) (b.trans ι) :=
  alignFiniteEmbeddingsAux_viaEmbedding a b ι n

end Equiv.Perm
