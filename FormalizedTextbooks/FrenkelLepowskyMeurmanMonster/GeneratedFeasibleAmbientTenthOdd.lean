/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthStageCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorOddShortTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthRepresentative

/-! Every odd row of the Tenth prototype has absolute value at most `3/32`.

The odd rows are the Omega-symmetric combinations of the incoming tensor, which is the sum of the
eight certified root-two factors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The integer odd-row numerator (over 128) of the Tenth prototype. -/
def generatedFeasibleAmbientTenthOddNumerator (d : Fin 2048) (i : Fin 24) : ℤ :=
  ∑ r : Fin 8, (generatedFeasibleAmbientTenthSpin 7 r ⟨d.val, by omega⟩ +
      generatedFeasibleAmbientTenthSpin 7 r ⟨d.val + 2048, by omega⟩) *
    generatedFeasibleAmbientTenthSpatial 7 r i

/-- The code with block `q` and offset `e`. -/
private def oddLabel (q : Fin 16) (e : Fin 128) : Fin 2048 :=
  ⟨q.val * 128 + e.val, by have := q.isLt; have := e.isLt; omega⟩

private theorem oddBlocks {P : Fin 2048 → Prop} (h : ∀ q : Fin 16, ∀ e : Fin 128, P (oddLabel q e))
    (d : Fin 2048) : P d := by
  have h' := h ⟨d.val / 128, by have := d.isLt; omega⟩ ⟨d.val % 128, Nat.mod_lt _ (by decide)⟩
  have he : oddLabel ⟨d.val / 128, by have := d.isLt; omega⟩
      ⟨d.val % 128, Nat.mod_lt _ (by decide)⟩ = d := by
    apply Fin.ext
    change d.val / 128 * 128 + d.val % 128 = d.val
    omega
  rw [he] at h'
  exact h'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Codes 0 to 127 are checked at all 24 coordinates.
private theorem odd0 : ∀ e : Fin 128, ∀ i : Fin 24,
    |generatedFeasibleAmbientTenthOddNumerator (oddLabel 0 e) i| ≤ 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Codes 128 to 255 are checked at all 24 coordinates.
private theorem odd1 : ∀ e : Fin 128, ∀ i : Fin 24,
    |generatedFeasibleAmbientTenthOddNumerator (oddLabel 1 e) i| ≤ 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Codes 256 to 383 are checked at all 24 coordinates.
private theorem odd2 : ∀ e : Fin 128, ∀ i : Fin 24,
    |generatedFeasibleAmbientTenthOddNumerator (oddLabel 2 e) i| ≤ 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Codes 384 to 511 are checked at all 24 coordinates.
private theorem odd3 : ∀ e : Fin 128, ∀ i : Fin 24,
    |generatedFeasibleAmbientTenthOddNumerator (oddLabel 3 e) i| ≤ 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Codes 512 to 639 are checked at all 24 coordinates.
private theorem odd4 : ∀ e : Fin 128, ∀ i : Fin 24,
    |generatedFeasibleAmbientTenthOddNumerator (oddLabel 4 e) i| ≤ 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Codes 640 to 767 are checked at all 24 coordinates.
private theorem odd5 : ∀ e : Fin 128, ∀ i : Fin 24,
    |generatedFeasibleAmbientTenthOddNumerator (oddLabel 5 e) i| ≤ 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Codes 768 to 895 are checked at all 24 coordinates.
private theorem odd6 : ∀ e : Fin 128, ∀ i : Fin 24,
    |generatedFeasibleAmbientTenthOddNumerator (oddLabel 6 e) i| ≤ 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Codes 896 to 1023 are checked at all 24 coordinates.
private theorem odd7 : ∀ e : Fin 128, ∀ i : Fin 24,
    |generatedFeasibleAmbientTenthOddNumerator (oddLabel 7 e) i| ≤ 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Codes 1024 to 1151 are checked at all 24 coordinates.
private theorem odd8 : ∀ e : Fin 128, ∀ i : Fin 24,
    |generatedFeasibleAmbientTenthOddNumerator (oddLabel 8 e) i| ≤ 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Codes 1152 to 1279 are checked at all 24 coordinates.
private theorem odd9 : ∀ e : Fin 128, ∀ i : Fin 24,
    |generatedFeasibleAmbientTenthOddNumerator (oddLabel 9 e) i| ≤ 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Codes 1280 to 1407 are checked at all 24 coordinates.
private theorem odd10 : ∀ e : Fin 128, ∀ i : Fin 24,
    |generatedFeasibleAmbientTenthOddNumerator (oddLabel 10 e) i| ≤ 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Codes 1408 to 1535 are checked at all 24 coordinates.
private theorem odd11 : ∀ e : Fin 128, ∀ i : Fin 24,
    |generatedFeasibleAmbientTenthOddNumerator (oddLabel 11 e) i| ≤ 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Codes 1536 to 1663 are checked at all 24 coordinates.
private theorem odd12 : ∀ e : Fin 128, ∀ i : Fin 24,
    |generatedFeasibleAmbientTenthOddNumerator (oddLabel 12 e) i| ≤ 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Codes 1664 to 1791 are checked at all 24 coordinates.
private theorem odd13 : ∀ e : Fin 128, ∀ i : Fin 24,
    |generatedFeasibleAmbientTenthOddNumerator (oddLabel 13 e) i| ≤ 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Codes 1792 to 1919 are checked at all 24 coordinates.
private theorem odd14 : ∀ e : Fin 128, ∀ i : Fin 24,
    |generatedFeasibleAmbientTenthOddNumerator (oddLabel 14 e) i| ≤ 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Codes 1920 to 2047 are checked at all 24 coordinates.
private theorem odd15 : ∀ e : Fin 128, ∀ i : Fin 24,
    |generatedFeasibleAmbientTenthOddNumerator (oddLabel 15 e) i| ≤ 12 := by
  decide +kernel

/-- Every odd-row numerator has absolute value at most 12. -/
theorem generatedFeasibleAmbientTenth_odd_numerator_abs (d : Fin 2048) (i : Fin 24) :
    |generatedFeasibleAmbientTenthOddNumerator d i| ≤ 12 := by
  revert i
  apply oddBlocks (P := fun d => ∀ i : Fin 24, |generatedFeasibleAmbientTenthOddNumerator d i| ≤ 12)
  intro q
  fin_cases q
  · exact odd0
  · exact odd1
  · exact odd2
  · exact odd3
  · exact odd4
  · exact odd5
  · exact odd6
  · exact odd7
  · exact odd8
  · exact odd9
  · exact odd10
  · exact odd11
  · exact odd12
  · exact odd13
  · exact odd14
  · exact odd15

/-- One root-two factor of the incoming tensor at a spin label. -/
private theorem factor_value (r : Fin 8) (k : Fin 4096) (i : Fin 24) :
    generatedTenthTensorFactor r 7 (golayLabelCoefficients k) i =
      ((generatedFeasibleAmbientTenthSpin 7 r k * generatedFeasibleAmbientTenthSpatial 7 r i : ℤ)
          : ℝ) / (64 * Real.sqrt 2) := by
  obtain ⟨h1, h2, h3, h4⟩ := generatedFeasibleAmbientTenth_factor_data r
  change generatedAxisGlobalTensorIntegerPacket
    (generatedAxisGlobalOddTensorFactor (generatedTenthTensorFactorData r 7).1
      (generatedTenthTensorFactorData r 7).2.1)
    ((generatedTenthTensorFactorData r 7).2.2.1 * (generatedTenthTensorFactorData r 7).2.2.2)
    (golayLabelCoefficients k) i = _
  rw [generatedAxisGlobalTensorIntegerPacket_coefficient, h1, h2, h3, h4]
  simp only [generatedAxisGlobalOddTensorFactor]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Every odd row of the Tenth prototype, from the certified factor numerators. -/
theorem generatedFeasibleAmbientTenth_odd_short (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode generatedTenthAxis).2.1 (Sum.inr (Sum.inr (d, i))) =
      qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        (generatedFeasibleAmbientTenthOddNumerator d i : ℝ) / 128 := by
  rw [generatedTenthAxis_local_expression, monsterNortonTensor_extra_odd_short_coordinates]
  have hT : (griessConwayEncode (rhoLocal generatedTenthLocal generatedFifthAxis)).2.2 =
      ∑ r : Fin 8, generatedTenthTensorFactor r 7 := by
    rw [generatedTenthLocal, generatedAxisGlobalFifthRoot02Packet_actual]
    exact generatedTenth_incoming_tensor_factors
  rw [hT]
  simp only [Finset.sum_apply, factor_value]
  unfold generatedFeasibleAmbientTenthOddNumerator
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hr : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  push_cast
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.sum_div]
  field_simp
  rw [hr]
  ring

/-- Every odd row of the Tenth prototype has absolute value at most `3/32`. -/
theorem generatedFeasibleAmbientTenth_odd_abs (d : Fin 2048) (i : Fin 24) :
    |(griessConwayEncode generatedTenthAxis).2.1 (Sum.inr (Sum.inr (d, i)))| ≤ 3 / 32 := by
  rw [generatedFeasibleAmbientTenth_odd_short]
  have hq : |qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)| = 1 := by
    unfold qSign
    split_ifs <;> simp
  have hn := generatedFeasibleAmbientTenth_odd_numerator_abs d i
  have hn' : |(generatedFeasibleAmbientTenthOddNumerator d i : ℝ)| ≤ 12 := by exact_mod_cast hn
  rw [abs_div, abs_mul, hq, one_mul, abs_of_pos (by norm_num : (0 : ℝ) < 128)]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 128)]
  linarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
