/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SignCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SignKernelCount
public import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-! The actual unsigned norm-twelve orbit under the positively E8-fixing Golay signs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false

/-- The entire actual E8-positive Golay-sign group in multiplicative notation. -/
abbrev generatedTenthE7SignGroup := Multiplicative generatedTenthE7OctadSigns

/-- These original words give genuine original lattice isometries. -/
def generatedTenthE7SignGroupHom : generatedTenthE7SignGroup →* leechIsomSubgroup where
  toFun c := golaySignIsometry c.toAdd.val
  map_one' := golaySignHom.map_one
  map_mul' c d := golaySignHom.map_mul
    (Multiplicative.ofAdd c.toAdd.val) (Multiplicative.ofAdd d.toAdd.val)

/-- The group acts through the original genuine integral lattice action. -/
instance generatedTenthE7SignIntegralAction : MulAction generatedTenthE7SignGroup leechIntegral :=
  MulAction.compHom leechIntegral (leechIntegralAction.comp generatedTenthE7SignGroupHom)

/-- The complete unsigned line represented by both actual integral orientations. -/
def generatedTenthE7UnsignedLine : Finset leechIntegral :=
  {generatedTenthE7NormTwelveLine, -generatedTenthE7NormTwelveLine}

/-- The unordered pair stabilizer is exactly genuine fixation in either orientation. -/
theorem generatedTenth_e7_sign_pair_stabilizer (c : generatedTenthE7SignGroup) :
    c ∈ MulAction.stabilizer generatedTenthE7SignGroup generatedTenthE7UnsignedLine ↔
      leechIntegralAction (golaySignIsometry c.toAdd.val) generatedTenthE7NormTwelveLine =
        generatedTenthE7NormTwelveLine ∨
      leechIntegralAction (golaySignIsometry c.toAdd.val) generatedTenthE7NormTwelveLine =
        -generatedTenthE7NormTwelveLine := by
  change c • generatedTenthE7UnsignedLine = generatedTenthE7UnsignedLine ↔ _
  constructor
  · intro h
    have hm : c • generatedTenthE7NormTwelveLine ∈ c • generatedTenthE7UnsignedLine := by
      exact Finset.smul_mem_smul_finset (by simp [generatedTenthE7UnsignedLine])
    rw [h] at hm
    have hh : c • generatedTenthE7NormTwelveLine = generatedTenthE7NormTwelveLine ∨
        c • generatedTenthE7NormTwelveLine = -generatedTenthE7NormTwelveLine := by
      simpa only [generatedTenthE7UnsignedLine, Finset.mem_insert, Finset.mem_singleton] using hm
    change leechIntegralAction (golaySignIsometry c.toAdd.val) generatedTenthE7NormTwelveLine =
        generatedTenthE7NormTwelveLine ∨
      leechIntegralAction (golaySignIsometry c.toAdd.val) generatedTenthE7NormTwelveLine =
        -generatedTenthE7NormTwelveLine at hh
    exact hh
  · intro h
    have hn : c • (-generatedTenthE7NormTwelveLine) =
        -(c • generatedTenthE7NormTwelveLine) := by
      exact map_neg (leechIntegralAction (golaySignIsometry c.toAdd.val)) _
    change c • generatedTenthE7NormTwelveLine = generatedTenthE7NormTwelveLine ∨
      c • generatedTenthE7NormTwelveLine = -generatedTenthE7NormTwelveLine at h
    change Finset.image (fun u : leechIntegral => c • u)
      {generatedTenthE7NormTwelveLine, -generatedTenthE7NormTwelveLine} =
        {generatedTenthE7NormTwelveLine, -generatedTenthE7NormTwelveLine}
    rw [Finset.image_insert, Finset.image_singleton, hn]
    rcases h with h | h
    · rw [h]
    · rw [h, neg_neg, Finset.pair_comm]


/-- The stabilizer is in bijection with the fully classified actual original sign kernel. -/
def generatedTenthE7SignStabilizerEquiv :
    MulAction.stabilizer generatedTenthE7SignGroup generatedTenthE7UnsignedLine ≃
      generatedTenthE7UnsignedSignKernel where
  toFun c := ⟨c.val.toAdd.val, c.val.toAdd.property,
    (generatedTenth_e7_sign_pair_stabilizer c.val).mp c.property⟩
  invFun c := ⟨Multiplicative.ofAdd ⟨c.val, c.property.1⟩,
    (generatedTenth_e7_sign_pair_stabilizer _).mpr c.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The entire actual unsigned-line stabilizer in the positive Golay signs has order two. -/
theorem generatedTenth_e7_sign_stabilizer_card :
    Nat.card (MulAction.stabilizer generatedTenthE7SignGroup generatedTenthE7UnsignedLine) = 2 := by
  rw [Nat.card_congr generatedTenthE7SignStabilizerEquiv,
    generatedTenth_e7_unsigned_sign_kernel_card]

/-- The actual unsigned norm-twelve orbit under the whole positive Golay-sign group
has size sixteen. -/
theorem generatedTenth_e7_sign_unsigned_orbit_card :
    Nat.card (MulAction.orbit generatedTenthE7SignGroup generatedTenthE7UnsignedLine) = 16 := by
  let _ := Fintype.ofFinite generatedTenthE7SignGroup
  let _ := Fintype.ofFinite
    (MulAction.stabilizer generatedTenthE7SignGroup generatedTenthE7UnsignedLine)
  let f : generatedTenthE7SignGroup →
      MulAction.orbit generatedTenthE7SignGroup generatedTenthE7UnsignedLine :=
    fun c => ⟨c • generatedTenthE7UnsignedLine, ⟨c, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨s, c, hc⟩
    exact ⟨c, Subtype.ext hc⟩
  let : Finite (MulAction.orbit generatedTenthE7SignGroup generatedTenthE7UnsignedLine) :=
    Finite.of_surjective f hf
  let _ := Fintype.ofFinite
    (MulAction.orbit generatedTenthE7SignGroup generatedTenthE7UnsignedLine)
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    generatedTenthE7SignGroup generatedTenthE7UnsignedLine
  simp only [← Nat.card_eq_fintype_card] at h
  rw [generatedTenth_e7_sign_stabilizer_card] at h
  have hg : Nat.card generatedTenthE7SignGroup = 32 := by
    exact generatedTenth_e7_octad_sign_space_card
  rw [hg] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
