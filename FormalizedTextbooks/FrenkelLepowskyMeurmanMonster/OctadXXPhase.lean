/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ConwayFrobenius
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadTensorCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadProductSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadProductPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadCodeSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadIntersection

/-! Actual OXX central phases. The three short preferred lifts are
involutions, so their central product coefficient cycles. The octad
modulation has zero all-one coordinate; consequently the output odd
vector's Omega correction contributes no sign. What remains is exactly
the Parker theta character times the negative-position character. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative

lemma octadXX_preferred_product_coeff (r s : GriessShortIndex) :
    toAdd (griessShortQ r * griessShortQ s).coeff =
      spinDot (spinModulation (griessShortQ s)) (spinTranslation (griessShortQ r)) := by
  change (0 + 0) + (∑ k : Fin 12,
    spinTranslation (griessShortQ r) k * spinModulation (griessShortQ s) k) = _
  simp only [zero_add, spinDot, mul_comm]

lemma octadXX_modulation_dot_omega (o : Fin 759) (e : Fin 64) :
    spinDot (spinModulation (griessShortQ (Sum.inr (Sum.inl (o, e)))))
      (Pi.single 11 1) = 0 := by
  have h : spinDot (spinModulation (griessShortQ (Sum.inr (Sum.inl (o, e)))))
      (Pi.single 11 1) = spinModulation (griessShortQ (Sum.inr (Sum.inl (o, e)))) 11 := by
    simp [spinDot, Pi.single_apply]
  rw [h, griessOctad_modulation_last]

/-- The actual OXX coefficient factors into its code-theta and negative-position signs. -/
theorem griessOctadOdd_product_phase (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24)
    (hb : (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))).base =
        (griessShortQ (Sum.inr (Sum.inr (f, j)))).base) :
    qSign (toAdd (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))).coeff) =
      qSign (spinDot (sourceWordTheta (golayOctadLabel o)) (octadSpinLow f)) *
        octadNegativeCharacter o e f := by
  have hb' := (griessShortQ_product_base_cycle _ _ _).mp hb
  rw [griessShortQ_product_phase_cycle _ _ _ hb,
    griessShortQ_product_phase_cycle _ _ _ hb', octadXX_preferred_product_coeff,
    griessOdd_translation, spinDot_add_right, spinDot_smul_right,
    octadXX_modulation_dot_omega, mul_zero, add_zero,
    griessOctad_modulation, spinDot_add_left, qSign_add]
  rfl

/-- The physical syndrome selector determines the negative-position character
without choosing a normalized octad character label. -/
theorem octadNegativeCharacter_of_syndrome (o : Fin 759) (e : Fin 64)
    (f : Fin 2048) (i j : Fin 24)
    (hs : golaySyndrome (integerParity (griessOctadNegativeInteger o e) +
      (fun k => golayOctadWord o k * golayEncoder (octadSpinLow f) k) +
      Pi.single i 1 + Pi.single j 1) = 0) :
    octadNegativeCharacter o e f =
      qSign (golayEncoder (octadSpinLow f) i) * qSign (golayEncoder (octadSpinLow f) j) := by
  have hI : spinDot (golaySyndrome
      (fun k => golayOctadWord o k * golayEncoder (octadSpinLow f) k)) (octadSpinLow f) = 0 := by
    rw [golaySyndrome_spinDot]
    have hf : ∀ x : ZMod 2, x * x = x := by decide +kernel
    calc
      _ = ∑ k, golayOctadWord o k * golayEncoder (octadSpinLow f) k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [mul_assoc, hf]
      _ = 0 := by
        rw [← golaySyndrome_spinDot]
        change spinDot (golaySyndrome (golayEncoder (golayLabelCoefficients (golayOctadLabel o))))
          (octadSpinLow f) = 0
        rw [golaySyndrome_encoder, spinDot_zero_left]
  have hp (k : Fin 24) : spinDot (golaySyndrome (Pi.single k 1)) (octadSpinLow f) =
      golayEncoder (octadSpinLow f) k := by
    rw [golaySyndrome_spinDot]
    simp [Pi.single_apply]
  have h := congrArg (fun v => spinDot v (octadSpinLow f)) hs
  simp only [map_add, spinDot_add_left, hI, hp, spinDot_zero_left, add_zero] at h
  have he : spinDot (golaySyndrome (integerParity (griessOctadNegativeInteger o e)))
      (octadSpinLow f) = golayEncoder (octadSpinLow f) i + golayEncoder (octadSpinLow f) j := by
    apply add_right_cancel (b := golayEncoder (octadSpinLow f) i + golayEncoder (octadSpinLow f) j)
    rw [add_assoc] at h
    exact h.trans (ZModModule.add_self _).symm
  unfold octadNegativeCharacter
  rw [he, qSign_add]

/-- The actual Y coefficient expressed in physical signs of the output code. -/
theorem octadYSpinConstant_code_transport (o : Fin 759) (d f : Fin 2048) (i j : Fin 24)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d) :
    octadYSpinConstant o d f i j =
      qSign (spinDot (sourceWordTheta (golayOctadLabel o)) (octadSpinLow f)) *
      qSign (golayEncoder (octadSpinLow f) i) * qSign (golayOctadWord o i) *
      qSign (golayEncoder (octadSpinLow f) j) := by
  have ht := octadCodeSign_transport o d f i hd
  have hO : qSign (golayOctadWord o i) =
      if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then -1 else 1 :=
    qSign_golayEncoder_label (golayOctadLabel o) i
  have hf (k : Fin 24) : qSign (golayEncoder (octadSpinLow f) k) =
      if (golayEncodedMask f.val).testBit k.val then -1 else 1 :=
    qSign_golayEncoder_label ⟨f.val, by omega⟩ k
  rw [hO, hf i, hf j]
  unfold octadYSpinConstant octadSpinSelector
  rw [ite_eq_left hd]
  calc
    _ = qSign (spinDot (sourceWordTheta (golayOctadLabel o)) (octadSpinLow f)) *
      (qSign ((octadSpinLow f + octadSpinCode o) 11) *
        (if (golayEncodedMask d.val).testBit i.val then -1 else 1)) *
      (if (golayEncodedMask f.val).testBit j.val then -1 else 1) := by ring
    _ = _ := by rw [ht]; ring

lemma octadXX_word_outside (o : Fin 759) (i : Fin 24) (hi : i ∉ golayOctadSupport o) :
    golayOctadWord o i = 0 := by
  by_contra h
  exact hi ((golayOctadWord_ne_zero_iff o i).mp h)

lemma octadXX_word_inside (o : Fin 759) (i : Fin 24) (hi : i ∈ golayOctadSupport o) :
    golayOctadWord o i = 1 := by
  have hf : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide +kernel
  exact hf _ ((golayOctadWord_ne_zero_iff o i).mpr hi)

/-- The diagonal Y coefficient outside the octad is its theta sign. -/
theorem octadYSpinConstant_outside (o : Fin 759) (d f : Fin 2048) (i : Fin 24)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d)
    (hi : i ∉ golayOctadSupport o) :
    octadYSpinConstant o d f i i =
      qSign (spinDot (sourceWordTheta (golayOctadLabel o)) (octadSpinLow f)) := by
  rw [octadYSpinConstant_code_transport o d f i i hd, octadXX_word_outside o i hi,
    qSign_zero, mul_one, mul_assoc, qSign_sq, mul_one]

/-- Inside the octad, the Y coefficient has the opposite physical code-sign product. -/
theorem octadYSpinConstant_inside (o : Fin 759) (d f : Fin 2048) (i j : Fin 24)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d)
    (hi : i ∈ golayOctadSupport o) :
    octadYSpinConstant o d f i j =
      -(qSign (spinDot (sourceWordTheta (golayOctadLabel o)) (octadSpinLow f)) *
        qSign (golayEncoder (octadSpinLow f) i) * qSign (golayEncoder (octadSpinLow f) j)) := by
  rw [octadYSpinConstant_code_transport o d f i j hd, octadXX_word_inside o i hi, qSign_one]
  ring

/-- Under the actual source selectors, the outside diagonal OXX phase
is the actual Y spin coefficient. -/
theorem griessOctadOdd_phase_eq_YConstant (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i : Fin 24)
    (hb : (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))).base =
        (griessShortQ (Sum.inr (Sum.inr (f, i)))).base)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d)
    (hs : golaySyndrome (integerParity (griessOctadNegativeInteger o e) +
      (fun k => golayOctadWord o k * golayEncoder (octadSpinLow f) k) +
      Pi.single i 1 + Pi.single i 1) = 0)
    (hi : i ∉ golayOctadSupport o) :
    qSign (toAdd (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))).coeff) = octadYSpinConstant o d f i i := by
  rw [griessOctadOdd_product_phase o e d f i i hb,
    octadNegativeCharacter_of_syndrome o e f i i hs, qSign_sq, mul_one,
    octadYSpinConstant_outside o d f i hd hi]

/-- Under the actual source selectors, the OXX phase inside the octad
is the negative of the actual Y spin coefficient. -/
theorem griessOctadOdd_phase_eq_neg_YConstant (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24)
    (hb : (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))).base =
        (griessShortQ (Sum.inr (Sum.inr (f, j)))).base)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d)
    (hs : golaySyndrome (integerParity (griessOctadNegativeInteger o e) +
      (fun k => golayOctadWord o k * golayEncoder (octadSpinLow f) k) +
      Pi.single i 1 + Pi.single j 1) = 0)
    (hi : i ∈ golayOctadSupport o) :
    qSign (toAdd (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))).coeff) = -octadYSpinConstant o d f i j := by
  rw [griessOctadOdd_product_phase o e d f i j hb,
    octadNegativeCharacter_of_syndrome o e f i j hs,
    octadYSpinConstant_inside o d f i j hd hi, neg_neg]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
