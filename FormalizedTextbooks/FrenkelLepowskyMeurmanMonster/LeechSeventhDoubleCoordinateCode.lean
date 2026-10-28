/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhFourCoordinateLattice

/-! The genuine Golay obstruction to identifying distinct four-coordinate frame classes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

private theorem double_odd_impossible : ∀ x : ZMod 4, ∀ c : ZMod 2,
    2 * x ≠ 1 + 2 * (c.val : ZMod 4) := by decide +kernel

private theorem double_binary_injective : ∀ a b : ZMod 2,
    (2 : ZMod 4) * (a.val : ZMod 4) = 2 * (b.val : ZMod 4) → a = b := by
  decide +kernel

/-- Twice a coordinate vector lies in the actual lattice only if its parity is a Golay word. -/
theorem leechSeventh_double_coordinate_code (v : Fin 24 → ℤ)
    (hv : (2 : ℤ) • v ∈ leechIntegral) : integerParity v ∈ golayCode := by
  obtain ⟨m, hm, c, hcm, hc, _⟩ := (mem_leechIntegral_iff_source _).mp hv
  have hm0 : m = 0 := by
    rcases hm with h0 | h1
    · exact h0
    · have h := hc 0
      rw [h1] at h
      norm_num [Pi.smul_apply, smul_eq_mul] at h
      exact False.elim (double_odd_impossible (v 0 : ZMod 4) (c 0) h)
  have he : integerParity v = c := by
    funext i
    have h := hc i
    rw [hm0] at h
    norm_num [Pi.smul_apply, smul_eq_mul] at h
    rw [← golay_double_lift] at h
    exact double_binary_injective (v i : ZMod 2) (c i) h
  exact he.symm ▸ hcm

/-- The actual binary word with ones at two stated physical coordinates. -/
def leechSeventhPairParity (t u : Fin 24) : Fin 24 → ZMod 2 :=
  Pi.single t 1 + Pi.single u 1

private theorem pair_weight : ∀ t u : Fin 24, t ≠ u →
    (∑ i, (leechSeventhPairParity t u i).val) = 2 := by
  unfold leechSeventhPairParity
  decide +kernel

/-- A genuine two-coordinate parity word cannot belong to the Golay code. -/
theorem leechSeventh_pair_parity_not_code (t u : Fin 24) (htu : t ≠ u) :
    leechSeventhPairParity t u ∉ golayCode := by
  intro hc
  have h0 : leechSeventhPairParity t u ≠ 0 := by
    intro h
    have he := congrArg (fun x : Fin 24 → ZMod 2 => x t) h
    simp [leechSeventhPairParity, htu] at he
  have hw := golayCode_weight_ge_eight _ hc h0
  rw [pair_weight t u htu] at hw
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
