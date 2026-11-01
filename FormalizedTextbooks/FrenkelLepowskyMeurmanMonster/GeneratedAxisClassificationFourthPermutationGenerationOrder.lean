/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthPermutationGenerationOrbits

/-! Exact order of the genuine Golay code14 and unordered-pair permutation stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The next actual prefix subgroup is exactly the stabilizer of the next base coordinate. -/
noncomputable def generatedFourthPermutationNextStabilizerEquiv (k : Fin 7) :
    MulAction.stabilizer (generatedFourthPermutationPointStabilizer k.val) (golayBasePoints k) ≃
      generatedFourthPermutationPointStabilizer (k.val + 1) where
  toFun p := ⟨p.val.val, p.val.property.1, by
    intro j hj
    by_cases hjk : j.val < k.val
    · exact p.val.property.2 j hjk
    · have hjeq : j = k := Fin.ext (by omega)
      subst j
      exact p.property⟩
  invFun p := ⟨⟨p.val, p.property.1, fun j hj => p.property.2 j (by omega)⟩,
    p.property.2 k (by omega)⟩
  left_inv p := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv p := Subtype.ext rfl

/-- Actual orbit-stabilizer gives the exact seven-step cardinal recurrence. -/
theorem generatedFourth_permutation_card_step (k : Fin 7) :
    Nat.card (generatedFourthPermutationPointStabilizer k.val) =
      generatedFourthPermutationOrbitSizes k *
        Nat.card (generatedFourthPermutationPointStabilizer (k.val + 1)) := by
  have h := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup
      (generatedFourthPermutationPointStabilizer k.val) (golayBasePoints k))
  rw [Nat.card_prod, generatedFourth_permutation_orbit_card,
    Nat.card_congr (generatedFourthPermutationNextStabilizerEquiv k)] at h
  exact h.symm

/-- The faithful actual seven-point base makes the terminal prefix stabilizer trivial. -/
theorem generatedFourth_permutation_stabilizer_seven :
    generatedFourthPermutationPointStabilizer 7 = ⊥ := by
  apply le_antisymm
  · intro p hp
    exact Subgroup.mem_bot.mpr
      (golayAutomorphism_eq_one_of_fix_base p (fun j => hp.2 j j.isLt))
  · exact bot_le

/-- Prefix zero is precisely the actual code14 and unordered-pair stabilizer. -/
theorem generatedFourth_permutation_stabilizer_zero :
    generatedFourthPermutationPointStabilizer 0 = generatedFourthPermutationFlagStabilizer := by
  ext p
  change (p ∈ generatedFourthPermutationFlagStabilizer ∧
    ∀ j : Fin 7, j.val < 0 → p.val (golayBasePoints j) = golayBasePoints j) ↔ _
  simp

/-- The genuine Golay permutation stabilizer of code14 and unordered pair 8,11 has order 11520. -/
theorem generatedFourth_permutation_flag_card :
    Nat.card generatedFourthPermutationFlagStabilizer = 11520 := by
  have h0 := generatedFourth_permutation_card_step (0 : Fin 7)
  have h1 := generatedFourth_permutation_card_step (1 : Fin 7)
  have h2 := generatedFourth_permutation_card_step (2 : Fin 7)
  have h3 := generatedFourth_permutation_card_step (3 : Fin 7)
  have h4 := generatedFourth_permutation_card_step (4 : Fin 7)
  have h5 := generatedFourth_permutation_card_step (5 : Fin 7)
  have h6 := generatedFourth_permutation_card_step (6 : Fin 7)
  change Nat.card (generatedFourthPermutationPointStabilizer 0) =
    16 * Nat.card (generatedFourthPermutationPointStabilizer 1) at h0
  change Nat.card (generatedFourthPermutationPointStabilizer 1) =
    15 * Nat.card (generatedFourthPermutationPointStabilizer 2) at h1
  change Nat.card (generatedFourthPermutationPointStabilizer 2) =
    6 * Nat.card (generatedFourthPermutationPointStabilizer 3) at h2
  change Nat.card (generatedFourthPermutationPointStabilizer 3) =
    1 * Nat.card (generatedFourthPermutationPointStabilizer 4) at h3
  change Nat.card (generatedFourthPermutationPointStabilizer 4) =
    4 * Nat.card (generatedFourthPermutationPointStabilizer 5) at h4
  change Nat.card (generatedFourthPermutationPointStabilizer 5) =
    2 * Nat.card (generatedFourthPermutationPointStabilizer 6) at h5
  change Nat.card (generatedFourthPermutationPointStabilizer 6) =
    1 * Nat.card (generatedFourthPermutationPointStabilizer 7) at h6
  rw [← generatedFourth_permutation_stabilizer_zero, h0, h1, h2, h3, h4, h5, h6,
    generatedFourth_permutation_stabilizer_seven, Subgroup.card_bot]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
