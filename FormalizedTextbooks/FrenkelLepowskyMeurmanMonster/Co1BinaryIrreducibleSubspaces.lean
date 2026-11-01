/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryIrreducibleAlgebra

/-! The checked cyclic vector and functional bases force binary irreducibility. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- An invariant subspace containing the rank-one image vector contains the full cyclic basis. -/
theorem co1Irreducible_column_mem_top
    (W : Submodule (ZMod 2) (Fin 24 → ZMod 2))
    (hG : ∀ k : Fin 5, co1IrreduciblePreserves W (omegaOrbitBinaryMatrices k))
    (hcol : co1IrreducibleColumn ∈ W) : W = ⊤ := by
  have hc : ∀ n : ℕ, ∀ hn : n < 24,
      co1IrreducibleColumnMatrix.col ⟨n, hn⟩ ∈ W := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hz : n = 0
      · subst n
        have he : (⟨0, hn⟩ : Fin 24) = 0 := Fin.ext rfl
        rw [he, co1Irreducible_cyclic_starts.1]
        exact hcol
      let j : Fin 24 := ⟨n, hn⟩
      have hj : j ≠ 0 := by
        intro he
        exact hz (congrArg Fin.val he)
      have hp := (co1Irreducible_cyclic_parents j hj).1
      have hm := hG (co1IrreducibleColumnLetters j) _
        (ih (co1IrreducibleColumnParents j).val hp
          (co1IrreducibleColumnParents j).isLt)
      rw [co1Irreducible_cyclic_columns j hj] at hm
      exact hm
  apply top_unique
  intro v _
  have he : co1IrreducibleColumnMatrix *ᵥ (co1IrreducibleColumnInverse *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, co1Irreducible_basis_inverses.1, Matrix.one_mulVec]
  have hsum : co1IrreducibleColumnMatrix *ᵥ (co1IrreducibleColumnInverse *ᵥ v) =
      ∑ j, (co1IrreducibleColumnInverse *ᵥ v) j • co1IrreducibleColumnMatrix.col j := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  rw [← he, hsum]
  exact W.sum_mem fun j _ => W.smul_mem _ (hc j.val j.isLt)

/-- A generator-invariant subspace annihilated by the cyclic functional is zero. -/
theorem co1Irreducible_row_annihilates_bot
    (W : Submodule (ZMod 2) (Fin 24 → ZMod 2))
    (hG : ∀ k : Fin 5, co1IrreduciblePreserves W (omegaOrbitBinaryMatrices k))
    (hrow : ∀ x, x ∈ W → co1IrreducibleRow ⬝ᵥ x = 0) : W = ⊥ := by
  have hr : ∀ n : ℕ, ∀ hn : n < 24, ∀ x, x ∈ W →
      co1IrreducibleRowMatrix.row ⟨n, hn⟩ ⬝ᵥ x = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn x hx
      by_cases hz : n = 0
      · subst n
        have he : (⟨0, hn⟩ : Fin 24) = 0 := Fin.ext rfl
        rw [he, co1Irreducible_cyclic_starts.2]
        exact hrow x hx
      let j : Fin 24 := ⟨n, hn⟩
      have hj : j ≠ 0 := by
        intro he
        exact hz (congrArg Fin.val he)
      rw [← co1Irreducible_cyclic_rows j hj, ← Matrix.dotProduct_mulVec]
      exact ih (co1IrreducibleRowParents j).val
        (co1Irreducible_cyclic_parents j hj).2 (co1IrreducibleRowParents j).isLt _
          (hG (co1IrreducibleRowLetters j) x hx)
  apply bot_unique
  intro x hx
  have he : co1IrreducibleRowMatrix *ᵥ x = 0 := by
    funext i
    exact hr i.val i.isLt x hx
  change x = 0
  have hi := congrArg (fun v => co1IrreducibleRowInverse *ᵥ v) he
  rwa [Matrix.mulVec_mulVec, co1Irreducible_basis_inverses.2,
    Matrix.one_mulVec, Matrix.mulVec_zero] at hi

/-- Every subspace invariant under the five genuine Conway generators is zero or whole. -/
theorem co1Irreducible_generator_subspace_dichotomy
    (W : Submodule (ZMod 2) (Fin 24 → ZMod 2))
    (hG : ∀ k : Fin 5, co1IrreduciblePreserves W (omegaOrbitBinaryMatrices k)) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hrow : ∀ x, x ∈ W → co1IrreducibleRow ⬝ᵥ x = 0
  · exact Or.inl (co1Irreducible_row_annihilates_bot W hG hrow)
  · push Not at hrow
    obtain ⟨x, hx, hne⟩ := hrow
    have hbits : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
    have hone : co1IrreducibleRow ⬝ᵥ x = 1 := (hbits _).resolve_left hne
    have hcol : co1IrreducibleColumn ∈ W := by
      have hm := co1Irreducible_rank_one_preserves W hG x hx
      have he : co1IrreducibleStage 28 *ᵥ x = co1IrreducibleColumn := by
        have hmat : co1IrreducibleStage 28 =
            Matrix.vecMulVec co1IrreducibleColumn co1IrreducibleRow :=
          Matrix.ext co1Irreducible_rank_one
        rw [hmat, Matrix.vecMulVec_mulVec, hone]
        simp
      rwa [he] at hm
    exact Or.inr (co1Irreducible_column_mem_top W hG hcol)

/-- The actual faithful binary Conway representation is irreducible. -/
theorem co1BinaryAction_invariant_subspace_dichotomy
    (W : Submodule (ZMod 2) (Fin 24 → ZMod 2))
    (hW : ∀ g : Co1, ∀ v, v ∈ W → co1BinaryAction g v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  apply co1Irreducible_generator_subspace_dichotomy W
  intro k x hx
  have h := hW (QuotientGroup.mk' signsSubgroup (omegaOrbitIsometry k)) x hx
  change leechBinaryAction (omegaOrbitIsometry k) x ∈ W at h
  rwa [omegaOrbitIsometry_binary] at h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
