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

/-! Every equivariant linear map commutes with the genuine rank-one Conway operator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A linear endomorphism commutes with the complete action of a binary matrix. -/
def co1BinaryCommutes (T : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (A : Matrix (Fin 24) (Fin 24) (ZMod 2)) : Prop :=
  ∀ x, T (A *ᵥ x) = A *ᵥ T x

/-- Commutation is closed under actual matrix composition. -/
theorem co1Binary_commutes_mul (T : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (A B : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hA : co1BinaryCommutes T A) (hB : co1BinaryCommutes T B) :
    co1BinaryCommutes T (A * B) := by
  intro x
  rw [← Matrix.mulVec_mulVec, hA (B *ᵥ x), hB x, ← Matrix.mulVec_mulVec]

/-- Commutation is closed under finite sums of actual matrices. -/
theorem co1Binary_commutes_sum {ι : Type*} [Fintype ι]
    (T : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (A : ι → Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hA : ∀ i, co1BinaryCommutes T (A i)) :
    co1BinaryCommutes T (∑ i, A i) := by
  intro x
  rw [Matrix.sum_mulVec, map_sum, Matrix.sum_mulVec]
  exact Finset.sum_congr rfl (fun i _ => hA i x)

/-- Every checked word and power stage commutes with an endomorphism commuting
with the five actual generators. -/
theorem co1Binary_word_power_commutes
    (T : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (hG : ∀ k : Fin 5, co1BinaryCommutes T (omegaOrbitBinaryMatrices k))
    (n : ℕ) (hn : n < 26) :
    co1BinaryCommutes T (co1IrreducibleStage ⟨n, by omega⟩) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hzero : n = 0
    · subst n
      have he : (⟨0, by omega⟩ : Fin 29) = 0 := Fin.ext rfl
      rw [he, co1Irreducible_stage_zero]
      intro x
      simp only [Matrix.one_mulVec]
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
      exact co1Binary_commutes_mul T _ _ (hG _)
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
      exact co1Binary_commutes_mul T _ _
        (ih 12 (by omega) (by omega)) (ih (n - 1) (by omega) (by omega))

/-- The genuine rank-one composition commutes with every endomorphism commuting
with its generators. -/
theorem co1Binary_rank_one_commutes
    (T : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (hG : ∀ k : Fin 5, co1BinaryCommutes T (omegaOrbitBinaryMatrices k)) :
    co1BinaryCommutes T (co1IrreducibleStage 28) := by
  have hp : co1BinaryCommutes T (co1IrreducibleStage 26) := by
    have he : co1IrreducibleStage 26 =
        ∑ n : Fin 15, co1IrreducibleStage (co1IrreduciblePowerStage n) :=
      Matrix.ext fun i j => (co1Irreducible_projector_sum i j).symm
    rw [he]
    apply co1Binary_commutes_sum
    intro n
    exact co1Binary_word_power_commutes T hG
      (co1IrreduciblePowerStage n).val (by
        unfold co1IrreduciblePowerStage
        split_ifs <;> simp only [Fin.val_zero] <;> omega)
  have h27 : co1IrreducibleStage 27 = omegaOrbitBinaryMatrices 0 * co1IrreducibleStage 26 :=
    Matrix.ext fun i j => (co1Irreducible_projector_middle i j).symm
  have h28 : co1IrreducibleStage 28 = co1IrreducibleStage 26 * co1IrreducibleStage 27 :=
    Matrix.ext fun i j => (co1Irreducible_projector_product i j).symm
  rw [h28, h27]
  exact co1Binary_commutes_mul T _ _ hp
    (co1Binary_commutes_mul T _ _ (hG 0) hp)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
