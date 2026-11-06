/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadPointwiseData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismOrder

/-! The genuine five-point stabilizer has a three-point orbit inside its unique actual octad. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original five-point stabilizer has its exact order forty-eight. -/
theorem generatedNinth_golay_five_stabilizer_card : Nat.card (golayPointStabilizer 5) = 48 := by
  have h₆ := golayPointStabilizer_card_step (6 : Fin 7)
  change Nat.card (golayPointStabilizer 6) = 3 * Nat.card (golayPointStabilizer 7) at h₆
  rw [golayPointStabilizer_seven, Subgroup.card_bot, mul_one] at h₆
  have h₅ := golayPointStabilizer_card_step (5 : Fin 7)
  change Nat.card (golayPointStabilizer 5) = 16 * Nat.card (golayPointStabilizer 6) at h₅
  rw [h₆] at h₅
  exact h₅

/-- Original five-point stabilizer elements fix the first five physical coordinates. -/
theorem generatedNinth_golay_five_fixes_initial (p : golayPointStabilizer 5)
    (i : Fin 24) (hi : i.val < 5) : p.val.val i = i := by
  let j : Fin 5 := ⟨i.val, hi⟩
  have h := p.property (Fin.castAdd 2 j) hi
  rw [golayBasePoints_firstFive] at h
  have he : Fin.castAdd 19 j = i := Fin.ext rfl
  rwa [he] at h

/-- The actual orbit of the next octad coordinate is exactly its three remaining coordinates. -/
theorem generatedNinth_golay_five_octad_orbit :
    MulAction.orbit (golayPointStabilizer 5) (5 : Fin 24) =
      {i : Fin 24 | 5 ≤ i.val ∧ i.val < 8} := by
  ext i
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨p, rfl⟩
    change 5 ≤ (p.val.val 5).val ∧ (p.val.val 5).val < 8
    have hfirst := generatedNinth_golay_five_fixes_initial p
    have ho := golayAutomorphism_standardOctad_points p.val hfirst 5
    have h8 : (p.val.val 5).val < 8 := ho.mpr (by decide)
    refine ⟨?_, h8⟩
    by_contra h
    have hv : (p.val.val 5).val < 5 := by omega
    have hf := hfirst (p.val.val 5) hv
    have he : p.val.val 5 = 5 := p.val.val.injective hf
    have := congrArg Fin.val he
    omega
  · intro hi
    change 5 ≤ i.val ∧ i.val < 8 at hi
    have he : golayStabilizerOrbitEligible (6 : Fin 7) i := by
      change i = 5 ∨ i = 6 ∨ i = 7
      have hv : i.val = 5 ∨ i.val = 6 ∨ i.val = 7 := by omega
      rcases hv with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    obtain ⟨p, hp⟩ := golayPointStabilizer_reaches (6 : Fin 7) i he
    let p' : golayPointStabilizer 5 := ⟨p.val, fun j hj => p.property j (by omega)⟩
    refine ⟨p', ?_⟩
    change p.val.val 5 = i
    change p.val.val 5 = i at hp
    exact hp

/-- The actual five-point group's octad orbit has precisely three elements. -/
theorem generatedNinth_golay_five_octad_orbit_card :
    Nat.card (MulAction.orbit (golayPointStabilizer 5) (5 : Fin 24)) = 3 := by
  rw [generatedNinth_golay_five_octad_orbit, Nat.card_eq_fintype_card]
  decide +kernel

/-- Fixing the sixth actual octad coordinate leaves exactly sixteen actual permutations. -/
theorem generatedNinth_golay_five_octad_stabilizer_card :
    Nat.card (MulAction.stabilizer (golayPointStabilizer 5) (5 : Fin 24)) = 16 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    (golayPointStabilizer 5) (5 : Fin 24))
  rw [Nat.card_prod, generatedNinth_golay_five_octad_orbit_card,
    generatedNinth_golay_five_stabilizer_card] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
