/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual quarter-weight phases for octad code translations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadTensorCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ParkerCyclicPhase

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The integer source characteristic function is the encoder's binary value. -/
theorem sourceCodeInteger_eq_encoder_val (d : Fin 4096) (i : Fin 24) :
    sourceCodeInteger d i = (golayEncoder (golayLabelCoefficients d) i).val := by
  rw [golayLabelEncoder_match]
  simp only [sourceCodeInteger]
  cases (golayEncodedMask d.val).testBit i.val <;> norm_num

private theorem binary_complement_val (a : ZMod 2) :
    (a + 1).val + a.val = 1 := by
  fin_cases a <;> decide +kernel

/-- Complementation changes a Golay quarter-weight by an even integer. -/
theorem sourceCodeQuarterWeight_complement (d e : Fin 4096)
    (h : golayEncoder (golayLabelCoefficients d) =
      golayEncoder (golayLabelCoefficients e) + (fun _ => 1)) :
    ((golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ZMod 2) =
      (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) := by
  have hs : (∑ i, sourceCodeInteger d i) + (∑ i, sourceCodeInteger e i) = 24 := by
    rw [← Finset.sum_add_distrib]
    simp only [sourceCodeInteger_eq_encoder_val, h, Pi.add_apply, ← Nat.cast_add]
    simp_rw [binary_complement_val]
    norm_num
  rw [sourceCodeInteger_sum, sourceCodeInteger_sum] at hs
  have hq : ((golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ℤ) +
      ((golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) : ℤ) = 6 := by
    linarith
  have hc := congrArg (fun z : ℤ => (z : ZMod 2)) hq
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat,
    show (6 : ZMod 2) = 0 by decide] at hc
  have hh := congrArg (fun z : ZMod 2 =>
    z + (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ)) hc
  simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using hh

/-- The full source label and its selected low representative have equal
quarter-weight signs, including when they differ by Ω. -/
theorem spinDictionaryCode_quarterWeight (s : Fin 4096) (d : Fin 2048)
    (hd : spinDictionaryCode (golayLabelCoefficients s) = d) :
    ((golayMaskWeight (golayEncodedMask s.val) / 4 : ℕ) : ZMod 2) =
      (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) := by
  rcases spinDictionaryIndex_cases (golayLabelCoefficients s) with hlo | hhi
  · have hs : s = (⟨d.val, by omega⟩ : Fin 4096) :=
      golayLabelCoefficients_bijective.1 (by simpa only [hd] using hlo)
    rw [hs]
  · have he : golayEncoder (golayLabelCoefficients s) =
        golayEncoder (golayLabelCoefficients (⟨d.val, by omega⟩ : Fin 4096)) +
        (fun _ => 1) := by
      have hhi' : golayLabelCoefficients s =
          golayLabelCoefficients (⟨d.val + 2048, by omega⟩ : Fin 4096) := by
        simpa only [hd] using hhi
      rw [hhi', ← golayLabel_low_add_omega, map_add, golay_all_one]
    exact sourceCodeQuarterWeight_complement s ⟨d.val, by omega⟩ he

/-- Intersection with the actual octad is exactly the eight-coordinate
restriction weight of the second word. -/
theorem sourceCodeIntersection_octad_sum (o : Fin 759) (f : Fin 4096) :
    (∑ i, sourceCodeIntersection (golayOctadLabel o) f i) =
      (∑ k : Fin 8, (golayEncoder (golayLabelCoefficients f)
        (golayOctadCoordinate o k)).val : ℕ) := by
  classical
  have hp (i : Fin 24) : sourceCodeIntersection (golayOctadLabel o) f i =
      if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then
        sourceCodeInteger f i else 0 := by
    simp only [sourceCodeIntersection, sourceCodeInteger]
    cases (golayEncodedMask (golayOctadLabel o).val).testBit i.val <;> simp
  simp_rw [hp]
  rw [← Finset.sum_filter]
  change (∑ i ∈ golayMaskSupport (golayEncodedMask (golayOctadLabel o).val),
    sourceCodeInteger f i) = _
  let E := (golayMaskSupport (golayEncodedMask (golayOctadLabel o).val)).orderIsoOfFin
    (golayOctad_support_card o)
  rw [Finset.sum_subtype _ (fun _ => Iff.rfl), ← Equiv.sum_comp E.toEquiv]
  simp only [sourceCodeInteger_eq_encoder_val, Nat.cast_sum]
  rfl

/-- Translating by an octad changes the selected quarter-weight sign by
one half of the restriction weight, even if the full sum has a high label. -/
theorem octadSpinCode_weight_phase (o : Fin 759) (d f : Fin 2048)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d) :
    qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
      qSign (golayMaskWeight (golayEncodedMask f.val) / 4 : ℕ) =
        qSign ((∑ k : Fin 8, (golayEncoder (octadSpinLow f)
          (golayOctadCoordinate o k)).val) / 2 : ℕ) := by
  let s := spinDictionaryLabel (octadSpinCode o + octadSpinLow f)
  have hs : golayLabelCoefficients s = octadSpinCode o + octadSpinLow f :=
    (Equiv.ofBijective golayLabelCoefficients golayLabelCoefficients_bijective).apply_symm_apply _
  have hsd : spinDictionaryCode (golayLabelCoefficients s) = d := by
    rw [hs, add_comm]
    exact hd
  have hq := spinDictionaryCode_quarterWeight s d hsd
  have hi := sourceCodeIntersection_half_parity (golayOctadLabel o)
    (⟨f.val, by omega⟩ : Fin 4096) s hs
  rw [sourceCodeIntersection_octad_sum] at hi
  let n : ℕ := ∑ k : Fin 8, (golayEncoder (octadSpinLow f)
    (golayOctadCoordinate o k)).val
  have hdiv : ((n / 2 : ℕ) : ZMod 2) = (((n : ℤ) / 2 : ℤ) : ZMod 2) := by
    simpa only [Int.cast_natCast, Nat.cast_ofNat] using congrArg (fun z : ℤ => (z : ZMod 2))
      (Int.natCast_ediv n 2)
  have ho : golayMaskWeight (golayEncodedMask (golayOctadLabel o).val) = 8 := by
    rw [← golayMaskSupport_card]
    exact golayOctad_support_card o
  rw [ho, hq] at hi
  norm_num only [Nat.cast_ofNat, show (8 / 4 : ℕ) = 2 by decide, show (2 : ZMod 2) = 0 by decide,
    zero_add, sub_eq_add_neg, ZModModule.neg_eq_self] at hi
  simp only [show (2 : ZMod 2) = 0 by decide, zero_add] at hi
  rw [← qSign_add]
  apply congrArg qSign
  exact (add_comm _ _).trans (hi.symm.trans hdiv.symm)

/-- A selector value of one is the same concrete code condition. -/
theorem octadSpinSelector_weight_phase (o : Fin 759) (d f : Fin 2048)
    (hd : octadSpinSelector o d f = 1) :
    qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
      qSign (golayMaskWeight (golayEncodedMask f.val) / 4 : ℕ) =
        qSign ((∑ k : Fin 8, (golayEncoder (octadSpinLow f)
          (golayOctadCoordinate o k)).val) / 2 : ℕ) := by
  apply octadSpinCode_weight_phase
  unfold octadSpinSelector at hd
  split_ifs at hd with h
  · exact h
  · norm_num at hd

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
