/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE8FullLineKernel
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE8PointwiseActions
public import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-! Actual unsigned norm-twelve orbit under the full 512-element positive pointwise E8 group. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
/-- Classical equality is used only for the two-element stabilizer equivalence. -/
local instance : DecidableEq leechIsomSubgroup := Classical.decEq _

/-- The full genuine positive pointwise subgroup acts by the original integral lattice action. -/
instance generatedTenthE8PointwiseIntegralAction :
    MulAction generatedTenthE8PointwiseSpatial leechIntegral :=
  MulAction.compHom leechIntegral
    (leechIntegralAction.comp generatedTenthE8PointwiseSpatial.subtype)

/-- Both original actual orientations represent the entire unsigned norm-twelve line. -/
def generatedTenthE8UnsignedLine : Finset leechIntegral :=
  {generatedTenthE7NormTwelveLine, -generatedTenthE7NormTwelveLine}

/-- Actual pair stabilization is precisely positive or negative fixation of the original vector. -/
theorem generatedTenth_e8_pair_stabilizer (g : generatedTenthE8PointwiseSpatial) :
    g ∈ MulAction.stabilizer generatedTenthE8PointwiseSpatial generatedTenthE8UnsignedLine ↔
      leechIntegralAction g.val generatedTenthE7NormTwelveLine = generatedTenthE7NormTwelveLine ∨
      leechIntegralAction g.val generatedTenthE7NormTwelveLine =
        -generatedTenthE7NormTwelveLine := by
  change g • generatedTenthE8UnsignedLine = generatedTenthE8UnsignedLine ↔ _
  constructor
  · intro h
    have hm : g • generatedTenthE7NormTwelveLine ∈ g • generatedTenthE8UnsignedLine :=
      Finset.smul_mem_smul_finset (by simp [generatedTenthE8UnsignedLine])
    rw [h] at hm
    have hh : g • generatedTenthE7NormTwelveLine = generatedTenthE7NormTwelveLine ∨
        g • generatedTenthE7NormTwelveLine = -generatedTenthE7NormTwelveLine := by
      simpa only [generatedTenthE8UnsignedLine, Finset.mem_insert, Finset.mem_singleton] using hm
    change leechIntegralAction g.val generatedTenthE7NormTwelveLine =
        generatedTenthE7NormTwelveLine ∨
      leechIntegralAction g.val generatedTenthE7NormTwelveLine =
        -generatedTenthE7NormTwelveLine at hh
    exact hh
  · intro h
    have hn : g • (-generatedTenthE7NormTwelveLine) = -(g • generatedTenthE7NormTwelveLine) :=
      map_neg (leechIntegralAction g.val) _
    change g • generatedTenthE7NormTwelveLine = generatedTenthE7NormTwelveLine ∨
      g • generatedTenthE7NormTwelveLine = -generatedTenthE7NormTwelveLine at h
    change Finset.image (fun u : leechIntegral => g • u)
      {generatedTenthE7NormTwelveLine, -generatedTenthE7NormTwelveLine} =
        {generatedTenthE7NormTwelveLine, -generatedTenthE7NormTwelveLine}
    rw [Finset.image_insert, Finset.image_singleton, hn]
    rcases h with h | h
    · rw [h]
    · rw [h, neg_neg, Finset.pair_comm]

/-- The genuine complement sign lies in the full actual pointwise E8 group. -/
theorem generatedTenth_e8_complement_mem_pointwise :
    generatedTenthE7ComplementSign ∈ generatedTenthE8PointwiseSpatial :=
  (generatedTenth_e8_pointwise_mem_iff _).mpr generatedTenth_e7_complement_fixes_section

/-- The actual complementary sign is not identity. -/
theorem generatedTenth_e8_complement_sign_ne_one : generatedTenthE7ComplementSign ≠ 1 := by
  intro h
  have hh := generatedTenth_e7_complement_not_positive_point
  rw [h, map_one] at hh
  exact hh rfl

/-- Exactly two genuine isometries occur in the full actual unsigned-line stabilizer. -/
def generatedTenthE8FullLineStabilizerEquiv : Bool ≃
    MulAction.stabilizer generatedTenthE8PointwiseSpatial generatedTenthE8UnsignedLine where
  toFun b := if b then
    ⟨⟨generatedTenthE7ComplementSign, generatedTenth_e8_complement_mem_pointwise⟩,
      (generatedTenth_e8_pair_stabilizer _).mpr
        (Or.inr generatedTenth_e7_complement_negates_norm_twelve)⟩
    else ⟨1, (generatedTenth_e8_pair_stabilizer _).mpr
      ((generatedTenth_e8_full_unsigned_line_kernel 1
        generatedTenthE8PointwiseSpatial.one_mem).mpr (Or.inl rfl))⟩
  invFun g := if g.val.val = 1 then false else true
  left_inv b := by
    cases b <;> simp [generatedTenth_e8_complement_sign_ne_one]
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    rcases (generatedTenth_e8_full_unsigned_line_kernel g.val.val g.val.property).mp
      ((generatedTenth_e8_pair_stabilizer _).mp g.property) with h | h
    · simp [h]
    · simp [h, generatedTenth_e8_complement_sign_ne_one]

/-- The entire actual unsigned norm-twelve line stabilizer
in the full pointwise group has order 2. -/
theorem generatedTenth_e8_full_line_stabilizer_card :
    Nat.card (MulAction.stabilizer generatedTenthE8PointwiseSpatial
      generatedTenthE8UnsignedLine) = 2 := by
  rw [← Nat.card_congr generatedTenthE8FullLineStabilizerEquiv]
  simp

/-- The full actual 512-element group has an actual 256-element unsigned norm-twelve orbit. -/
theorem generatedTenth_e8_full_line_orbit_card :
    Nat.card (MulAction.orbit generatedTenthE8PointwiseSpatial
      generatedTenthE8UnsignedLine) = 256 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let _ := Fintype.ofFinite generatedTenthE8PointwiseSpatial
  let _ := Fintype.ofFinite
    (MulAction.stabilizer generatedTenthE8PointwiseSpatial generatedTenthE8UnsignedLine)
  let f : generatedTenthE8PointwiseSpatial →
      MulAction.orbit generatedTenthE8PointwiseSpatial generatedTenthE8UnsignedLine :=
    fun g => ⟨g • generatedTenthE8UnsignedLine, ⟨g, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨s, g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
  let : Finite (MulAction.orbit generatedTenthE8PointwiseSpatial generatedTenthE8UnsignedLine) :=
    Finite.of_surjective f hf
  let _ := Fintype.ofFinite
    (MulAction.orbit generatedTenthE8PointwiseSpatial generatedTenthE8UnsignedLine)
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    generatedTenthE8PointwiseSpatial generatedTenthE8UnsignedLine
  simp only [← Nat.card_eq_fintype_card] at h
  rw [generatedTenth_e8_full_line_stabilizer_card, generatedTenth_e8_pointwise_spatial_card] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
