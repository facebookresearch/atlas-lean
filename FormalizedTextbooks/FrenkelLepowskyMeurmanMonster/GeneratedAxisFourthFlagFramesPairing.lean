/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationE8Sections

/-! Pairing actual norm-eight frame witnesses incident with an actual short vector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Integral pairing before the physical normalization by the square root of eight. -/
def generatedFourthFlagIntegralPairing (x y : leechIntegral) : ℤ :=
  ∑ i, x.val i * y.val i

/-- Actual section vectors of norm eight pairing to four with the selected short vector. -/
def GeneratedFourthFlagIncidentVectors (S : Submodule ℤ leechIntegral)
    (r : leechIntegral) :=
  {x : leechIntegral // x ∈ S ∧ leechSquareSum x.val = 64 ∧
    generatedFourthFlagIntegralPairing x r = 32}

/-- The second frame witness obtained by reflection across the selected short vector. -/
def generatedFourthFlagFramePartner (r x : leechIntegral) : leechIntegral :=
  (2 : ℤ) • r - x

/-- Partnering preserves the actual norm-eight and incidence equations. -/
theorem generatedFourthFlagFramePartner_incident
    (S : Submodule ℤ leechIntegral) (r : leechIntegral)
    (hr : r ∈ S) (hnr : leechSquareSum r.val = 32)
    (x : GeneratedFourthFlagIncidentVectors S r) :
    generatedFourthFlagFramePartner r x.val ∈ S ∧
      leechSquareSum (generatedFourthFlagFramePartner r x.val).val = 64 ∧
      generatedFourthFlagIntegralPairing (generatedFourthFlagFramePartner r x.val) r =
        32 := by
  refine ⟨S.sub_mem (S.smul_mem 2 hr) x.property.1, ?_, ?_⟩
  · have h : leechSquareSum (generatedFourthFlagFramePartner r x.val).val =
        4 * leechSquareSum r.val - 4 * generatedFourthFlagIntegralPairing x.val r +
          leechSquareSum x.val.val := by
      unfold leechSquareSum generatedFourthFlagIntegralPairing
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change (2 * r.val i - x.val.val i) ^ 2 =
        4 * r.val i ^ 2 - 4 * (x.val.val i * r.val i) + x.val.val i ^ 2
      ring
    rw [h, hnr, x.property.2.1, x.property.2.2]
    norm_num
  · have h : generatedFourthFlagIntegralPairing
        (generatedFourthFlagFramePartner r x.val) r =
        2 * leechSquareSum r.val - generatedFourthFlagIntegralPairing x.val r := by
      unfold generatedFourthFlagIntegralPairing leechSquareSum
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change (2 * r.val i - x.val.val i) * r.val i =
        2 * r.val i ^ 2 - x.val.val i * r.val i
      ring
    rw [h, hnr, x.property.2.2]
    norm_num

/-- Partnering twice returns the original genuine lattice vector. -/
theorem generatedFourthFlagFramePartner_involution (r x : leechIntegral) :
    generatedFourthFlagFramePartner r (generatedFourthFlagFramePartner r x) = x := by
  simp [generatedFourthFlagFramePartner]

/-- Both partner witnesses represent the same actual lattice class modulo twice Λ. -/
theorem generatedFourthFlagFramePartner_reduction (r x : leechIntegral) :
    leechReduction (generatedFourthFlagFramePartner r x) = leechReduction x := by
  rw [generatedFourthFlagFramePartner, two_smul ℤ r]
  rw [map_sub, map_add, ZModModule.add_self, zero_sub]
  exact (eq_neg_of_add_eq_zero_left (ZModModule.add_self (leechReduction x))).symm

/-- The incidence pairing has no fixed point among actual norm-eight witnesses. -/
theorem generatedFourthFlagFramePartner_ne
    (S : Submodule ℤ leechIntegral) (r : leechIntegral)
    (hnr : leechSquareSum r.val = 32)
    (x : GeneratedFourthFlagIncidentVectors S r) :
    generatedFourthFlagFramePartner r x.val ≠ x.val := by
  intro h
  have he : r = x.val := by
    apply Subtype.ext
    ext i
    have hi := congrArg (fun u : leechIntegral => u.val i) h
    change 2 * r.val i - x.val.val i = x.val.val i at hi
    omega
  have hx := x.property.2.1
  rw [← he, hnr] at hx
  norm_num at hx

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
