/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Physical code signs transported through the actual spin dictionary selector. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadTensorCoefficients

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every actual spin index is its dictionary's low representative plus its Ω bit. -/
theorem spinDictionaryIndex_low_omega (t : SpinIndex) :
    t = octadSpinLow (spinDictionaryCode t) + t 11 • Pi.single 11 1 := by
  rcases spinDictionaryIndex_cases t with h | h
  · have hl : t 11 = 0 := by rw [h]; exact golayLabel_low_last _
    rw [hl, zero_smul, add_zero]
    exact h
  · have hl : t 11 = 1 := by rw [h]; exact golayLabel_high_last _
    rw [hl, one_smul]
    exact h.trans (golayLabel_low_add_omega _).symm

/-- A physical Golay bit gives the actual real coordinate sign. -/
theorem qSign_golayEncoder_label (d : Fin 4096) (i : Fin 24) :
    qSign (golayEncoder (golayLabelCoefficients d) i) =
      if (golayEncodedMask d.val).testBit i.val then -1 else 1 := by
  rw [golayLabelEncoder_boolean]
  cases (golayEncodedMask d.val).testBit i.val <;>
    simp [golayBooleanCast, qSign_one, qSign_zero]

/-- Under the actual dictionary selector, the source Ω sign transports
the input code's physical sign to the output code and octad signs. -/
theorem octadCodeSign_transport (o : Fin 759) (d f : Fin 2048) (i : Fin 24)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d) :
    qSign ((octadSpinLow f + octadSpinCode o) 11) *
      (if (golayEncodedMask d.val).testBit i.val then -1 else 1) =
      (if (golayEncodedMask f.val).testBit i.val then -1 else 1) *
        (if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then -1 else 1) := by
  let t := octadSpinLow f + octadSpinCode o
  have ht : t = octadSpinLow d + t 11 • Pi.single 11 1 := by
    have hdt : spinDictionaryCode t = d := hd
    simpa only [hdt] using spinDictionaryIndex_low_omega t
  have he : golayEncoder t i = golayEncoder (octadSpinLow d) i + t 11 := by
    have h := congrArg (fun v : SpinIndex => golayEncoder v i) ht
    simpa only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, golay_all_one,
      smul_eq_mul, mul_one] using h
  have hs : qSign (t 11) * qSign (golayEncoder (octadSpinLow d) i) =
      qSign (golayEncoder t i) := by rw [he, qSign_add, mul_comm]
  have ha : golayEncoder t i = golayEncoder (octadSpinLow f) i +
      golayEncoder (octadSpinCode o) i := by
    simp only [t, map_add, Pi.add_apply]
  rw [ha, qSign_add] at hs
  simpa only [t, octadSpinLow, octadSpinCode, qSign_golayEncoder_label] using hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
