/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismTransitivity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismOctads
public import Mathlib.GroupTheory.GroupAction.Quotient

/-! Exact order of the actual permutation automorphism group of the Golay code.
The checked representatives establish all orbit lower bounds; uniqueness of the
standard octad gives the last orbit upper bounds. The seven-point base supplies
the trivial endpoint, so orbit-stabilizer counts the original subgroup. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Sizes of the seven successive orbits. -/
def golayStabilizerOrbitLengths : Fin 7 → ℕ := ![24, 23, 22, 21, 20, 16, 3]

private theorem golayPointStabilizer_fixes_initial (k : ℕ) (p : golayPointStabilizer k)
    (i : Fin 24) (hi5 : i.val < 5) (hik : i.val < k) : p.val.val i = i := by
  let j : Fin 5 := ⟨i.val, hi5⟩
  have hji : Fin.castAdd 19 j = i := Fin.ext rfl
  have h := p.property (Fin.castAdd 2 j) hik
  rw [golayBasePoints_firstFive, hji] at h
  exact h

private theorem golayPointStabilizer_image_ge (k : ℕ) (hk : k ≤ 5)
    (p : golayPointStabilizer k) (i : Fin 24) (hi : k ≤ i.val) : k ≤ (p.val.val i).val := by
  by_contra h
  have himg : (p.val.val i).val < k := by omega
  have hfix := golayPointStabilizer_fixes_initial k p (p.val.val i) (by omega) himg
  have heq := p.val.val.injective hfix.symm
  have hval := congrArg Fin.val heq
  omega

/-- Actual stabilizer images obey precisely the certified eligible-point restrictions. -/
theorem golayPointStabilizer_image_eligible (k : Fin 7) (p : golayPointStabilizer k.val) :
    golayStabilizerOrbitEligible k (p.val.val (golayBasePoints k)) := by
  by_cases hk5 : k.val < 5
  · have hbase : (golayBasePoints k).val = k.val := by
      have h : ∀ k : Fin 7, k.val < 5 → (golayBasePoints k).val = k.val := by decide
      exact h k hk5
    simp only [golayStabilizerOrbitEligible, hk5, ite_true]
    apply golayPointStabilizer_image_ge k.val (by omega) p
    omega
  · have hfirst : ∀ i : Fin 24, i.val < 5 → p.val.val i = i := by
      intro i hi
      exact golayPointStabilizer_fixes_initial k.val p i hi (by omega)
    by_cases hk : k.val = 5
    · have hkeq : k = 5 := Fin.ext hk
      subst k
      have h := golayAutomorphism_standardOctad_points p.val hfirst 8
      change (p.val.val 8).val < 8 ↔ (8 : Fin 24).val < 8 at h
      change 8 ≤ (p.val.val 8).val
      omega
    · have hkeq : k = 6 := Fin.ext (by omega)
      subst k
      have h := golayAutomorphism_standardOctad_points p.val hfirst 5
      have hi8 : (p.val.val 5).val < 8 := h.mpr (by decide)
      let p5 : golayPointStabilizer 5 := ⟨p.val, fun j hj => p.property j (by omega)⟩
      have hi5 := golayPointStabilizer_image_ge 5 (by omega) p5 5 (by decide)
      change 5 ≤ (p.val.val 5).val at hi5
      change (p.val.val 5) = 5 ∨ (p.val.val 5) = 6 ∨ (p.val.val 5) = 7
      have hv : (p.val.val 5).val = 5 ∨ (p.val.val 5).val = 6 ∨ (p.val.val 5).val = 7 := by omega
      rcases hv with hv | hv | hv
      · exact Or.inl (Fin.ext hv)
      · exact Or.inr (Or.inl (Fin.ext hv))
      · exact Or.inr (Or.inr (Fin.ext hv))

/-- The actual orbit equals its explicitly certified eligible point set. -/
theorem golayPointStabilizer_orbit (k : Fin 7) :
    MulAction.orbit (golayPointStabilizer k.val) (golayBasePoints k) =
      {i | golayStabilizerOrbitEligible k i} := by
  ext i
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨p, rfl⟩
    exact golayPointStabilizer_image_eligible k p
  · intro hi
    obtain ⟨p, hp⟩ := golayPointStabilizer_reaches k i hi
    exact ⟨p, hp⟩

/-- Count each eligible set directly in the physical 24 coordinates. -/
theorem golayPointStabilizer_orbit_card (k : Fin 7) :
    Nat.card (MulAction.orbit (golayPointStabilizer k.val) (golayBasePoints k)) =
      golayStabilizerOrbitLengths k := by
  rw [golayPointStabilizer_orbit, Nat.card_eq_fintype_card]
  have h : ∀ k : Fin 7,
      Fintype.card {i : Fin 24 // golayStabilizerOrbitEligible k i} =
        golayStabilizerOrbitLengths k := by decide +kernel
  exact h k

private noncomputable def golayNextStabilizerEquiv (k : Fin 7) :
    MulAction.stabilizer (golayPointStabilizer k.val) (golayBasePoints k) ≃
      golayPointStabilizer (k.val + 1) where
  toFun p := ⟨p.val.val, by
    intro j hj
    by_cases hjk : j.val < k.val
    · exact p.val.property j hjk
    · have hjeq : j = k := Fin.ext (by omega)
      subst j
      exact p.property⟩
  invFun p := ⟨⟨p.val, fun j hj => p.property j (by omega)⟩, p.property k (by omega)⟩
  left_inv p := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv p := Subtype.ext rfl

/-- Orbit-stabilizer recurrence for the genuine nested stabilizers. -/
theorem golayPointStabilizer_card_step (k : Fin 7) :
    Nat.card (golayPointStabilizer k.val) =
      golayStabilizerOrbitLengths k * Nat.card (golayPointStabilizer (k.val + 1)) := by
  have h := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup (golayPointStabilizer k.val) (golayBasePoints k))
  rw [Nat.card_prod, golayPointStabilizer_orbit_card,
    Nat.card_congr (golayNextStabilizerEquiv k)] at h
  exact h.symm

/-- The original actual Golay permutation group has order 244823040. -/
theorem golayAutomorphism_card : Nat.card golayAutomorphismSubgroup = 244823040 := by
  have hzero : golayPointStabilizer 0 = ⊤ := by
    ext p
    change (∀ j : Fin 7, j.val < 0 → p.val (golayBasePoints j) = golayBasePoints j) ↔ True
    constructor
    · intro _; trivial
    · intro _ j hj; omega
  have hcard : Nat.card (golayPointStabilizer 0) = Nat.card golayAutomorphismSubgroup := by
    rw [hzero, Subgroup.card_top]
  have h0 := golayPointStabilizer_card_step (0 : Fin 7)
  change Nat.card (golayPointStabilizer 0) =
    24 * Nat.card (golayPointStabilizer 1) at h0
  have h1 := golayPointStabilizer_card_step (1 : Fin 7)
  change Nat.card (golayPointStabilizer 1) =
    23 * Nat.card (golayPointStabilizer 2) at h1
  have h2 := golayPointStabilizer_card_step (2 : Fin 7)
  change Nat.card (golayPointStabilizer 2) =
    22 * Nat.card (golayPointStabilizer 3) at h2
  have h3 := golayPointStabilizer_card_step (3 : Fin 7)
  change Nat.card (golayPointStabilizer 3) =
    21 * Nat.card (golayPointStabilizer 4) at h3
  have h4 := golayPointStabilizer_card_step (4 : Fin 7)
  change Nat.card (golayPointStabilizer 4) =
    20 * Nat.card (golayPointStabilizer 5) at h4
  have h5 := golayPointStabilizer_card_step (5 : Fin 7)
  change Nat.card (golayPointStabilizer 5) =
    16 * Nat.card (golayPointStabilizer 6) at h5
  have h6 := golayPointStabilizer_card_step (6 : Fin 7)
  change Nat.card (golayPointStabilizer 6) =
    3 * Nat.card (golayPointStabilizer 7) at h6
  rw [← hcard, h0, h1, h2, h3, h4, h5, h6, golayPointStabilizer_seven]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
