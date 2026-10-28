/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE8PointwiseMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE8AffineCoverage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SignFixing

/-! Exact unsigned norm-twelve kernel of the full genuine positive pointwise E8 subgroup. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The entire nonzero support of the actual distinguished vector is the stated six coordinates. -/
theorem generatedTenth_e8_line_nonzero_iff : ∀ i : Fin 24,
    generatedTenthE7DistinguishedVector i ≠ 0 ↔ i ∈ generatedTenthE7LineSupport := by
  decide +kernel

/-- The genuine integral signed-permutation action at every transported source coordinate. -/
theorem generatedTenth_e8_monomial_line_coordinate (c : golayCode)
    (p : golayAutomorphismSubgroup) (i : Fin 24) :
    (leechIntegralAction (golaySignIsometry c * golayPermutationIsometry p)
      generatedTenthE7NormTwelveLine).val (p.val i) =
      if c.val (p.val i) = 0 then generatedTenthE7DistinguishedVector i
        else -generatedTenthE7DistinguishedVector i := by
  rw [map_mul]
  change (leechIntegralAction (golaySignIsometry c)
    (leechIntegralAction (golayPermutationIsometry p) generatedTenthE7NormTwelveLine)).val
      (p.val i) = _
  rw [leechIntegralAction_golaySign]
  change golayIntegerSign c.val
    (leechIntegralAction (golayPermutationIsometry p) generatedTenthE7NormTwelveLine).val
      (p.val i) = _
  rw [leechIntegralAction_golayPermutation]
  simp only [golayIntegerSign, golayIntegerPermute, p.val.symm_apply_apply]
  rfl

/-- Actual unsigned fixation forces preservation of the entire original six-coordinate support. -/
theorem generatedTenth_e8_monomial_line_support (c : golayCode)
    (p : golayAutomorphismSubgroup)
    (h : leechIntegralAction (golaySignIsometry c * golayPermutationIsometry p)
      generatedTenthE7NormTwelveLine = generatedTenthE7NormTwelveLine ∨
      leechIntegralAction (golaySignIsometry c * golayPermutationIsometry p)
        generatedTenthE7NormTwelveLine = -generatedTenthE7NormTwelveLine) :
    ∀ i ∈ generatedTenthE7LineSupport, p.val i ∈ generatedTenthE7LineSupport := by
  intro i hi
  have hnonzero := (generatedTenth_e8_line_nonzero_iff i).mpr hi
  by_contra hn
  have hz : generatedTenthE7DistinguishedVector (p.val i) = 0 := by
    by_contra hz
    exact hn ((generatedTenth_e8_line_nonzero_iff _).mp hz)
  rcases h with h | h
  · have hh := congrArg (fun u : leechIntegral => u.val (p.val i)) h
    rw [generatedTenth_e8_monomial_line_coordinate] at hh
    change (if c.val (p.val i) = 0 then generatedTenthE7DistinguishedVector i
      else -generatedTenthE7DistinguishedVector i) =
        generatedTenthE7DistinguishedVector (p.val i) at hh
    rw [hz] at hh
    split_ifs at hh <;> omega
  · have hh := congrArg (fun u : leechIntegral => u.val (p.val i)) h
    rw [generatedTenth_e8_monomial_line_coordinate] at hh
    change (if c.val (p.val i) = 0 then generatedTenthE7DistinguishedVector i
      else -generatedTenthE7DistinguishedVector i) =
        -generatedTenthE7DistinguishedVector (p.val i) at hh
    rw [hz] at hh
    split_ifs at hh <;> omega

/-- The full actual pointwise E8 group has exactly the same two unsigned-line fixers
as its Golay-sign subgroup: identity and the genuine complement-octad sign. -/
theorem generatedTenth_e8_full_unsigned_line_kernel (g : leechIsomSubgroup)
    (hg : g ∈ generatedTenthE8PointwiseSpatial) :
    (leechIntegralAction g generatedTenthE7NormTwelveLine = generatedTenthE7NormTwelveLine ∨
      leechIntegralAction g generatedTenthE7NormTwelveLine = -generatedTenthE7NormTwelveLine) ↔
        g = 1 ∨ g = generatedTenthE7ComplementSign := by
  constructor
  · intro h
    obtain ⟨c, p, hp, hcp⟩ := generatedTenth_e8_pointwise_decomposition g hg
    have hs := generatedTenth_e8_monomial_line_support c.val p (hcp ▸ h)
    have hp1 := generatedTenth_e8_affine_line_kernel p hp hs
    have hperm : golayPermutationIsometry (1 : golayAutomorphismSubgroup) = 1 :=
      golayPermutationHom.map_one
    rw [hp1, hperm, mul_one] at hcp
    rw [hcp] at h
    rcases (generatedTenth_e7_sign_unsigned_iff c.val c.property).mp h with hc | hc
    · left
      rw [hcp, hc]
      exact golaySignHom.map_one
    · right
      rw [hcp, hc]
      rfl
  · rintro (rfl | rfl)
    · left
      rw [map_one]
      rfl
    · exact Or.inr generatedTenth_e7_complement_negates_norm_twelve

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
