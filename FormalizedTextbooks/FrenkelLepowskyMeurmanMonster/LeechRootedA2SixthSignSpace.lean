/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialSignGeneration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthPermutationTransport

/-! The original equal-sign code subgroup and its genuine flag-permutation action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual Golay codewords with equal signs on all three sixth-root coordinates. -/
def leechRootedA2SixthSignSpace : Submodule (ZMod 2) golayCode where
  carrier := {c | c.val 17 = c.val 16 ∧ c.val 19 = c.val 16}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro c d ⟨hc17, hc19⟩ ⟨hd17, hd19⟩
    exact ⟨congrArg₂ (· + ·) hc17 hd17, congrArg₂ (· + ·) hc19 hd19⟩
  smul_mem' := by
    rintro a c ⟨hc17, hc19⟩
    exact ⟨congrArg (a * ·) hc17, congrArg (a * ·) hc19⟩

/-- The source coefficient kernel maps to precisely these actual Golay codewords. -/
def leechRootedA2SixthSignEncode (t : generatedSixthSignCoefficientSpace) :
    leechRootedA2SixthSignSpace :=
  ⟨generatedSixthSignCoefficientCode t, (generatedSixth_sign_coefficient_mem t.val).mp t.property⟩

/-- The original encoder is bijective on the genuine equal-three-coordinate sign space. -/
theorem leechRootedA2SixthSignEncode_bijective :
    Function.Bijective leechRootedA2SixthSignEncode := by
  constructor
  · intro t u h
    apply Subtype.ext
    apply golayEncoder_injective
    exact congrArg (fun c : leechRootedA2SixthSignSpace => c.val.val) h
  · intro c
    obtain ⟨a, ha⟩ := c.val.property
    have hc : golayEncoder a 17 = golayEncoder a 16 ∧
        golayEncoder a 19 = golayEncoder a 16 := by
      rw [ha]
      exact c.property
    let t : generatedSixthSignCoefficientSpace :=
      ⟨a, (generatedSixth_sign_coefficient_mem a).mpr hc⟩
    refine ⟨t, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact ha

/-- The genuine equal-three-coordinate Golay sign group has exactly 1024 elements. -/
theorem leechRootedA2SixthSignSpace_card : Nat.card leechRootedA2SixthSignSpace = 1024 := by
  rw [← Nat.card_congr (Equiv.ofBijective leechRootedA2SixthSignEncode
    leechRootedA2SixthSignEncode_bijective), generatedSixthSignCoefficientSpace_card]

/-- Genuine flag permutations preserve the original equal-sign code space. -/
theorem leechRootedA2SixthSignSpace_permutation (p : golayAutomorphismSubgroup)
    (hp : p ∈ leechRootedA2SixthPermutationFlag) (c : leechRootedA2SixthSignSpace) :
    golayCodePermutation p c.val ∈ leechRootedA2SixthSignSpace := by
  have h19 : p.val.symm 19 = 19 := p.val.symm_apply_eq.mpr hp.2.symm
  change c.val.val (p.val.symm 17) = c.val.val (p.val.symm 16) ∧
    c.val.val (p.val.symm 19) = c.val.val (p.val.symm 16)
  rcases hp.1 with hp | hp
  · have h16 : p.val.symm 16 = 16 := p.val.symm_apply_eq.mpr hp.1.symm
    have h17 : p.val.symm 17 = 17 := p.val.symm_apply_eq.mpr hp.2.symm
    rw [h16, h17, h19]
    exact c.property
  · have h16 : p.val.symm 16 = 17 := p.val.symm_apply_eq.mpr hp.2.symm
    have h17 : p.val.symm 17 = 16 := p.val.symm_apply_eq.mpr hp.1.symm
    rw [h16, h17, h19]
    exact ⟨c.property.1.symm, c.property.2.trans c.property.1.symm⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
