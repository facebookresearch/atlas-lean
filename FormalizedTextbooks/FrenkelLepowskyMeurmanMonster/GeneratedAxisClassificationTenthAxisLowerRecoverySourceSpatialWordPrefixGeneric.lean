/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSpatialWordPrefixData

/-! Ungated symbolic source formulas and linear seven-prefix matrix transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Each original stage retains all24 forward, inverse, and signed physical coordinates. -/
def GeneratedTenthSourceSpatialWordPrefixMetadata (j : Fin 7) : Prop :=
  generatedTenthSourceSpatialWordPrefixXi j = generatedAxisGlobalFifthShortNormalizationXi 2 j ∧
    ∀ i : Fin 24,
      generatedTenthSourceSpatialWordPrefixForward j i =
        (generatedAxisGlobalFifthShortNormalizationPermutation 2 j).val i ∧
      generatedTenthSourceSpatialWordPrefixInverse j i =
        (generatedAxisGlobalFifthShortNormalizationPermutation 2 j).val.symm i ∧
      generatedTenthSourceSpatialWordPrefixSign j i =
        if (sourceGeneratedSignCode
          (generatedAxisGlobalFifthShortNormalizationSigns 2 j)).val i = 0 then 1 else -1

/-- The complete stage uses one original physical column, after collapsing both sparse sums. -/
def generatedTenthSourceSpatialWordPrefixStage (j : Fin 7) : Matrix (Fin 24) (Fin 24) ℚ :=
  fun i k =>
    (if generatedTenthSourceSpatialWordPrefixXi j then
      co1XiMatrixQ i (generatedTenthSourceSpatialWordPrefixForward j k)
    else if i = generatedTenthSourceSpatialWordPrefixForward j k then 1 else 0) *
      (generatedTenthSourceSpatialWordPrefixSign j
        (generatedTenthSourceSpatialWordPrefixForward j k) : ℚ)

/-- A single24-term product certifies each full576-entry next prefix independently. -/
def GeneratedTenthSourceSpatialWordPrefixStep (j : Fin 7) : Prop :=
  ∀ i k : Fin 24,
    generatedTenthSourceSpatialWordPrefix j.succ i k =
      ∑ l : Fin 24, generatedTenthSourceSpatialWordPrefixStage j i l *
        generatedTenthSourceSpatialWordPrefix j.castSucc l k

/-- Algebraically collapse a genuine sign diagonal and inverse-coordinate permutation. -/
theorem generatedTenth_source_spatial_word_prefix_collapse
    (X : Matrix (Fin 24) (Fin 24) ℚ) (d : golayCode) (p : Equiv.Perm (Fin 24))
    (i k : Fin 24) :
    (X * (generatedAxisGlobalSpatialSignMatrix d *
      generatedAxisGlobalSpatialPermutationMatrix p)) i k =
      X i (p k) * (if d.val (p k) = 0 then 1 else -1) := by
  rw [Matrix.mul_apply]
  simp_rw [generatedAxisGlobalSpatialSignMatrix, Matrix.diagonal_mul,
    generatedAxisGlobalSpatialPermutationMatrix]
  rw [Finset.sum_eq_single (p k)]
  · simp
  · intro b _ hb
    have he : p.symm b ≠ k := by
      intro he
      exact hb ((p.symm_apply_eq).mp he)
    simp [he]
  · simp

/-- The actual source stage has this primitive Xi-row/sign/permutation formula. -/
theorem generatedTenth_source_spatial_word_prefix_actual_formula
    (j : Fin 7) (i k : Fin 24) :
    generatedAxisGlobalFifthSpatialStageMatrix 2 j i k =
      (if generatedAxisGlobalFifthShortNormalizationXi 2 j then
        co1XiMatrixQ i ((generatedAxisGlobalFifthShortNormalizationPermutation 2 j).val k)
      else if i = (generatedAxisGlobalFifthShortNormalizationPermutation 2 j).val k
        then 1 else 0) *
      (if (sourceGeneratedSignCode (generatedAxisGlobalFifthShortNormalizationSigns 2 j)).val
        ((generatedAxisGlobalFifthShortNormalizationPermutation 2 j).val k) = 0
        then 1 else -1) := by
  unfold generatedAxisGlobalFifthSpatialStageMatrix
  rw [generatedTenth_source_spatial_word_prefix_collapse]
  cases hx : generatedAxisGlobalFifthShortNormalizationXi 2 j <;>
    simp [Matrix.one_apply]

/-- Exact original metadata binds every complete literal stage to the genuine source stage. -/
theorem generatedTenth_source_spatial_word_prefix_stage_eq (j : Fin 7)
    (h : GeneratedTenthSourceSpatialWordPrefixMetadata j) :
    generatedTenthSourceSpatialWordPrefixStage j = generatedAxisGlobalFifthSpatialStageMatrix 2 j :=
    by
  ext i k
  rw [generatedTenth_source_spatial_word_prefix_actual_formula]
  unfold generatedTenthSourceSpatialWordPrefixStage
  rw [h.1, (h.2 k).1, (h.2 _).2.2]
  split_ifs <;> rfl

/-- Checked single-stage prefix products give the exact source recurrence as matrix equalities. -/
theorem generatedTenth_source_spatial_word_prefix_recurrence (j : Fin 7)
    (hm : GeneratedTenthSourceSpatialWordPrefixMetadata j)
    (hs : GeneratedTenthSourceSpatialWordPrefixStep j) :
    generatedAxisGlobalFifthSpatialStageMatrix 2 j *
      generatedTenthSourceSpatialWordPrefix j.castSucc =
        generatedTenthSourceSpatialWordPrefix j.succ := by
  rw [← generatedTenth_source_spatial_word_prefix_stage_eq j hm]
  ext i k
  exact (hs i k).symm

/-- The exact chronological source word follows by seven symbolic matrix steps. -/
theorem generatedTenth_source_spatial_word_prefix_word
    (hm : ∀ j, GeneratedTenthSourceSpatialWordPrefixMetadata j)
    (hs : ∀ j, GeneratedTenthSourceSpatialWordPrefixStep j) :
    generatedAxisGlobalFifthSpatialWordMatrix 2 = generatedTenthSourceSpatialWordLiteral := by
  have hstep : ∀ n : ℕ, (hn : n ≤ 7) →
      generatedAxisGlobalWordChain (fun j => generatedAxisGlobalFifthSpatialStageMatrix 2
        ⟨j % 7, Nat.mod_lt _ (by decide)⟩) n =
      generatedTenthSourceSpatialWordPrefix ⟨n, by omega⟩ := by
    intro n
    induction n with
    | zero => intro hn; simp [generatedAxisGlobalWordChain,
        generatedTenthSourceSpatialWordPrefix]
    | succ n ih =>
      intro hn
      rw [generatedAxisGlobalWordChain, ih (by omega)]
      have he : n % 7 = n := Nat.mod_eq_of_lt (by omega)
      have hr := generatedTenth_source_spatial_word_prefix_recurrence
        ⟨n, by omega⟩ (hm ⟨n, by omega⟩) (hs ⟨n, by omega⟩)
      have hc : (⟨n, by omega⟩ : Fin 7).castSucc =
          (⟨n, by omega⟩ : Fin 8) := Fin.ext rfl
      have hn' : (⟨n, by omega⟩ : Fin 7).succ =
          (⟨n + 1, by omega⟩ : Fin 8) := Fin.ext rfl
      rw [hc, hn'] at hr
      simpa only [he] using hr
  exact hstep 7 (by omega)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
