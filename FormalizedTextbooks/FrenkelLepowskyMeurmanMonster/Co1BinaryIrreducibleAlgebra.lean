/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryIrreducibleRankOne
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryIrreducibleCyclic
public import Mathlib.Data.Matrix.Basic

/-! The checked rank-one operator preserves every genuine invariant binary subspace. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A binary matrix sends every vector of a subspace back into that subspace. -/
def co1IrreduciblePreserves (W : Submodule (ZMod 2) (Fin 24 → ZMod 2))
    (A : Matrix (Fin 24) (Fin 24) (ZMod 2)) : Prop :=
  ∀ x, x ∈ W → A *ᵥ x ∈ W

/-- Preservation is closed under actual matrix composition. -/
theorem co1Irreducible_preserves_mul (W : Submodule (ZMod 2) (Fin 24 → ZMod 2))
    (A B : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hA : co1IrreduciblePreserves W A) (hB : co1IrreduciblePreserves W B) :
    co1IrreduciblePreserves W (A * B) := by
  intro x hx
  rw [← Matrix.mulVec_mulVec]
  exact hA _ (hB x hx)

/-- Preservation is closed under finite sums of actual matrices. -/
theorem co1Irreducible_preserves_sum {ι : Type*} [Fintype ι]
    (W : Submodule (ZMod 2) (Fin 24 → ZMod 2))
    (A : ι → Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hA : ∀ i, co1IrreduciblePreserves W (A i)) :
    co1IrreduciblePreserves W (∑ i, A i) := by
  intro x hx
  rw [Matrix.sum_mulVec]
  exact W.sum_mem fun i _ => hA i x hx

/-- Every word and power stage preserves any subspace invariant under the five actual generators. -/
theorem co1Irreducible_word_power_preserves
    (W : Submodule (ZMod 2) (Fin 24 → ZMod 2))
    (hG : ∀ k : Fin 5, co1IrreduciblePreserves W (omegaOrbitBinaryMatrices k))
    (n : ℕ) (hn : n < 26) :
    co1IrreduciblePreserves W (co1IrreducibleStage ⟨n, by omega⟩) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hzero : n = 0
    · subst n
      have he : (⟨0, by omega⟩ : Fin 29) = 0 := Fin.ext rfl
      rw [he, co1Irreducible_stage_zero]
      intro x hx
      simpa only [Matrix.one_mulVec] using hx
    by_cases hword : n ≤ 12
    · let k : Fin 12 := ⟨n - 1, by omega⟩
      have hnext : (⟨k.val + 1, by omega⟩ : Fin 29) = ⟨n, by omega⟩ :=
        Fin.ext (by dsimp [k]; omega)
      have hs : co1IrreducibleStage ⟨n, by omega⟩ =
          omegaOrbitBinaryMatrices (co1IrreducibleWordLetters k) *
            co1IrreducibleStage ⟨n - 1, by omega⟩ := by
        rw [← hnext]
        exact Matrix.ext fun i j => (co1Irreducible_word_steps k i j).symm
      rw [hs]
      exact co1Irreducible_preserves_mul W _ _ (hG _)
        (ih (n - 1) (by omega) (by omega))
    · let k : Fin 13 := ⟨n - 13, by omega⟩
      have hprev : (⟨k.val + 12, by omega⟩ : Fin 29) = ⟨n - 1, by omega⟩ :=
        Fin.ext (by dsimp [k]; omega)
      have hnext : (⟨k.val + 13, by omega⟩ : Fin 29) = ⟨n, by omega⟩ :=
        Fin.ext (by dsimp [k]; omega)
      have hs : co1IrreducibleStage ⟨n, by omega⟩ =
          co1IrreducibleStage 12 * co1IrreducibleStage ⟨n - 1, by omega⟩ := by
        rw [← hnext, ← hprev]
        exact Matrix.ext fun i j => (co1Irreducible_power_steps k i j).symm
      rw [hs]
      exact co1Irreducible_preserves_mul W _ _
        (ih 12 (by omega) (by omega)) (ih (n - 1) (by omega) (by omega))

/-- The genuine rank-one composition preserves every subspace invariant under its generators. -/
theorem co1Irreducible_rank_one_preserves
    (W : Submodule (ZMod 2) (Fin 24 → ZMod 2))
    (hG : ∀ k : Fin 5, co1IrreduciblePreserves W (omegaOrbitBinaryMatrices k)) :
    co1IrreduciblePreserves W (co1IrreducibleStage 28) := by
  have hp : co1IrreduciblePreserves W (co1IrreducibleStage 26) := by
    have he : co1IrreducibleStage 26 =
        ∑ n : Fin 15, co1IrreducibleStage (co1IrreduciblePowerStage n) :=
      Matrix.ext fun i j => (co1Irreducible_projector_sum i j).symm
    rw [he]
    apply co1Irreducible_preserves_sum
    intro n
    exact co1Irreducible_word_power_preserves W hG
      (co1IrreduciblePowerStage n).val (by
        unfold co1IrreduciblePowerStage
        split_ifs <;> simp only [Fin.val_zero] <;> omega)
  have h27 : co1IrreducibleStage 27 = omegaOrbitBinaryMatrices 0 * co1IrreducibleStage 26 :=
    Matrix.ext fun i j => (co1Irreducible_projector_middle i j).symm
  have h28 : co1IrreducibleStage 28 = co1IrreducibleStage 26 * co1IrreducibleStage 27 :=
    Matrix.ext fun i j => (co1Irreducible_projector_product i j).symm
  rw [h28, h27]
  exact co1Irreducible_preserves_mul W _ _ hp
    (co1Irreducible_preserves_mul W _ _ (hG 0) hp)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
