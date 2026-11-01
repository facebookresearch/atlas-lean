/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact triality transport for every actual even source cocode. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityReflection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SourceQGenerators

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open Multiplicative

private theorem cocode_add (a b : SpinIndex) : cocodeQ (a + b) = cocodeQ a * cocodeQ b := by
  apply spinRepresentation_injective
  rw [map_mul]
  apply LinearEquiv.ext
  intro x
  ext t
  simp only [LinearEquiv.mul_apply, cocodeQ_spin, spinDot_add_left, qSign_add]
  ring

private theorem commute_product_of_inversions {K : Type*} [Group K] (a b t : K)
    (ha : a * t * a⁻¹ = t⁻¹) (hb : b * t * b⁻¹ = t⁻¹) : Commute (a * b) t := by
  have hc : (a * b) * t * (a * b)⁻¹ = t := by
    calc
      (a * b) * t * (a * b)⁻¹ = a * (b * t * b⁻¹) * a⁻¹ := by group
      _ = a * t⁻¹ * a⁻¹ := by rw [hb]
      _ = (a * t * a⁻¹)⁻¹ := by group
      _ = t := by rw [ha, inv_inv]
  change (a * b) * t = t * (a * b)
  calc
    (a * b) * t = ((a * b) * t * (a * b)⁻¹) * (a * b) := by group
    _ = t * (a * b) := by rw [hc]

/-- Every actual even cocode operator commutes with the genuine dictionary triality. -/
theorem monsterNortonEvenCocode_commute_extra (h : SpinIndex) (hh : h 11 = 0) :
    Commute (rhoLocal (inclQ (cocodeQ h))) sExtra := by
  let e : SpinIndex := Pi.single 11 1
  have he : e 11 = 1 := by simp [e]
  have hodd : (h + e) 11 = 1 := by simp only [Pi.add_apply, hh, he, zero_add]
  have hee : e + e = 0 := by
    ext j
    exact CharTwo.add_self_eq_zero (e j)
  have hadd : (h + e) + e = h := by rw [add_assoc, hee, add_zero]
  have hc := commute_product_of_inversions
    (rhoLocal (inclQ (cocodeQ (h + e)))) (rhoLocal (inclQ (cocodeQ e))) sExtra
      (cocodeQ_conjugates_sExtra_inverse (h + e) hodd)
      (cocodeQ_conjugates_sExtra_inverse e he)
  rw [← map_mul, ← map_mul, ← cocode_add, hadd] at hc
  exact hc

/-- The source cocode word in named G commutes with actual extra whenever its parity is even. -/
theorem monsterNortonEvenCocode_generated_commute_extra (h : SpinIndex) (hh : h 11 = 0) :
    Commute (qIntoGenerated (sourceQCocode h)) extraIntoGenerated := by
  change qIntoGenerated (sourceQCocode h) * extraIntoGenerated =
    extraIntoGenerated * qIntoGenerated (sourceQCocode h)
  apply Subtype.ext
  change rhoLocal (inclQ (cocodeQ h)) * sExtra = sExtra * rhoLocal (inclQ (cocodeQ h))
  exact (monsterNortonEvenCocode_commute_extra h hh).eq

/-- The literal Norton cocode factor 1807 commutes with the actual triality generator. -/
theorem monsterNortonCocode1807_commute_extra :
    Commute (qIntoGenerated (sourceQCocode (golayLabelCoefficients 1807))) extraIntoGenerated :=
  monsterNortonEvenCocode_generated_commute_extra _ (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
