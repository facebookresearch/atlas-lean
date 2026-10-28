/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2PlaneGeometry
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightPreparationMonomial

/-! Genuine monomial isometries preserving the standard root line. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The standard root as a genuine integral Leech vector. -/
def leechRootedA2Root : leechIntegral :=
  ⟨leechRootedA2RootIntegral, leechRootedA2RootIntegral_mem⟩

/-- Actual root-line preservation, with its two possible lattice signs. -/
def leechRootedA2PreservesRootLine (e : leechIsomSubgroup) : Prop :=
  leechIntegralAction e leechRootedA2Root = leechRootedA2Root ∨
    leechIntegralAction e leechRootedA2Root = -leechRootedA2Root

/-- The root-line condition is closed under genuine isometry multiplication. -/
theorem leechRootedA2PreservesRootLine_mul (e f : leechIsomSubgroup)
    (he : leechRootedA2PreservesRootLine e) (hf : leechRootedA2PreservesRootLine f) :
    leechRootedA2PreservesRootLine (e * f) := by
  rcases he with he | he <;> rcases hf with hf | hf
  · left
    rw [map_mul, LinearEquiv.mul_apply, hf, he]
  · right
    rw [map_mul, LinearEquiv.mul_apply, hf, map_neg, he]
  · right
    rw [map_mul, LinearEquiv.mul_apply, hf, he]
  · left
    rw [map_mul, LinearEquiv.mul_apply, hf, map_neg, he, neg_neg]

/-- Inversion preserves the actual root line. -/
theorem leechRootedA2PreservesRootLine_inv (e : leechIsomSubgroup)
    (he : leechRootedA2PreservesRootLine e) : leechRootedA2PreservesRootLine e⁻¹ := by
  rcases he with he | he
  · left
    apply (leechIntegralAction e).injective
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    simpa using he.symm
  · right
    apply (leechIntegralAction e).injective
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, map_neg, he, neg_neg]
    rfl

/-- A genuine Golay permutation fixing both root coordinates fixes the actual root vector. -/
theorem leechRootedA2Root_permutation (p : golayAutomorphismSubgroup)
    (h0 : p.val 0 = 0) (h1 : p.val 1 = 1) :
    leechIntegralAction (golayPermutationIsometry p) leechRootedA2Root =
      leechRootedA2Root := by
  apply Subtype.ext
  rw [leechIntegralAction_golayPermutation]
  funext i
  have hp0 : p.val.symm i = 0 ↔ i = 0 := by rw [p.val.symm_apply_eq, h0]
  have hp1 : p.val.symm i = 1 ↔ i = 1 := by rw [p.val.symm_apply_eq, h1]
  simp only [golayIntegerPermute, leechRootedA2Root, leechRootedA2RootIntegral, hp0, hp1]

/-- Equal signs at the two root coordinates preserve the genuine root line. -/
theorem leechRootedA2Root_sign (d : golayCode) (hd : d.val 0 = d.val 1) :
    leechRootedA2PreservesRootLine (golaySignIsometry d) := by
  have he : ∀ i, (leechIntegralAction (golaySignIsometry d) leechRootedA2Root).val i =
      if d.val i = 0 then leechRootedA2RootIntegral i else -leechRootedA2RootIntegral i := by
    intro i
    rw [leechIntegralAction_golaySign]
    rfl
  by_cases h0 : d.val 0 = 0
  · left
    apply Subtype.ext
    funext i
    rw [he]
    by_cases hi0 : i = 0
    · subst i
      simp [h0, leechRootedA2Root]
    · by_cases hi1 : i = 1
      · subst i
        simp [← hd, h0, leechRootedA2Root]
      · simp [leechRootedA2Root, leechRootedA2RootIntegral, hi0, hi1]
  · right
    apply Subtype.ext
    funext i
    rw [he]
    by_cases hi0 : i = 0
    · subst i
      simp [h0, leechRootedA2Root]
    · by_cases hi1 : i = 1
      · subst i
        simp [← hd, h0, leechRootedA2Root]
      · simp [leechRootedA2Root, leechRootedA2RootIntegral, hi0, hi1]

/-- Swapping the root coordinates also fixes their positive sum. -/
theorem leechRootedA2Root_permutation_swap (p : golayAutomorphismSubgroup)
    (h0 : p.val 0 = 1) (h1 : p.val 1 = 0) :
    leechIntegralAction (golayPermutationIsometry p) leechRootedA2Root =
      leechRootedA2Root := by
  apply Subtype.ext
  rw [leechIntegralAction_golayPermutation]
  funext i
  have hp0 : p.val.symm i = 0 ↔ i = 1 := by rw [p.val.symm_apply_eq, h0]
  have hp1 : p.val.symm i = 1 ↔ i = 0 := by rw [p.val.symm_apply_eq, h1]
  simp only [golayIntegerPermute, leechRootedA2Root, leechRootedA2RootIntegral, hp0, hp1]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
