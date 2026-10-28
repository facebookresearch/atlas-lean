/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Source Y/Z spin columns split into two genuine basis vectors before compact Norton transport. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSpinBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOctadXYZCoefficients

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem dictionary_support (d : Fin 2048) (t : SpinIndex)
    (hl : t ≠ golayLabelCoefficients ⟨d.val, by omega⟩)
    (hh : t ≠ golayLabelCoefficients ⟨d.val + 2048, by omega⟩) :
    spinDictionaryCode t ≠ d := by
  intro hd
  rcases spinDictionaryIndex_cases t with h | h
  · apply hl
    simpa only [hd] using h
  · apply hh
    simpa only [hd] using h

private theorem low_ne_high (d : Fin 2048) :
    golayLabelCoefficients ⟨d.val, by omega⟩ ≠
      golayLabelCoefficients ⟨d.val + 2048, by omega⟩ := by
  intro h
  have h11 := congrFun h 11
  rw [golayLabel_low_last, golayLabel_high_last] at h11
  exact zero_ne_one h11

/-- The exact source Y spin column is the difference of its low and high dictionary deltas. -/
theorem monsterNortonSourceYSpin_basis (d : Fin 2048) (j : Fin 24) :
    trialityYSpin d j =
      ((if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) / Real.sqrt 2) •
        ((Pi.single (golayLabelCoefficients ⟨d.val, by omega⟩) 1 : SpinSpace) -
          Pi.single (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) 1) := by
  ext t
  by_cases hl : t = golayLabelCoefficients ⟨d.val, by omega⟩
  · subst t
    simp only [trialityYSpin, golayLabel_low_last, qSign_zero, one_mul,
      spinDictionaryCode_low, ite_true, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same,
      Pi.single_apply, low_ne_high d, ite_false, sub_zero, smul_eq_mul, mul_one]
  · by_cases hh : t = golayLabelCoefficients ⟨d.val + 2048, by omega⟩
    · subst t
      simp only [trialityYSpin, golayLabel_high_last, qSign_one, neg_one_mul,
        spinDictionaryCode_high, ite_true, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same,
        Pi.single_apply, Ne.symm (low_ne_high d), ite_false, zero_sub, smul_eq_mul]
      ring
    · simp [trialityYSpin, dictionary_support d t hl hh, hl, hh]

/-- The exact source Z spin column is the sum of its low and high dictionary deltas. -/
theorem monsterNortonSourceZSpin_basis (d : Fin 2048) :
    trialityZSpin d =
      (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) / Real.sqrt 2) •
        ((Pi.single (golayLabelCoefficients ⟨d.val, by omega⟩) 1 : SpinSpace) +
          Pi.single (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) 1) := by
  ext t
  by_cases hl : t = golayLabelCoefficients ⟨d.val, by omega⟩
  · subst t
    simp [trialityZSpin, low_ne_high d]
  · by_cases hh : t = golayLabelCoefficients ⟨d.val + 2048, by omega⟩
    · subst t
      simp [trialityZSpin, Ne.symm (low_ne_high d)]
    · simp [trialityZSpin, dictionary_support d t hl hh, hl, hh]

/-- The proved sixty-four-term actual Norton image of a single spin delta. -/
noncomputable def monsterNortonUCompactBasisExpansion (u : SpinIndex) : SpinSpace :=
  (1 / 8 : ℝ) • ∑ a : XiGrayIndex,
    (monsterNortonUCompactBasisSign u a : ℝ) •
      (Pi.single (monsterNortonUCompactBasisIndex u a) 1 : SpinSpace)

/-- The actual source Y column therefore transports through two explicit sixty-four-term sums. -/
theorem monsterNortonUCompactSourceYSpin (d : Fin 2048) (j : Fin 24) :
    monsterNortonUFiber.val.1.val (trialityYSpin d j) =
      ((if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) / Real.sqrt 2) •
        (monsterNortonUCompactBasisExpansion (golayLabelCoefficients ⟨d.val, by omega⟩) -
          monsterNortonUCompactBasisExpansion
            (golayLabelCoefficients ⟨d.val + 2048, by omega⟩)) := by
  rw [monsterNortonSourceYSpin_basis, map_smul, map_sub,
    monsterNortonUCompactSpin_actual_basis, monsterNortonUCompactSpin_actual_basis]
  rfl

/-- The actual source Z column transports through the sum of the same exact basis expansions. -/
theorem monsterNortonUCompactSourceZSpin (d : Fin 2048) :
    monsterNortonUFiber.val.1.val (trialityZSpin d) =
      (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) / Real.sqrt 2) •
        (monsterNortonUCompactBasisExpansion (golayLabelCoefficients ⟨d.val, by omega⟩) +
          monsterNortonUCompactBasisExpansion
            (golayLabelCoefficients ⟨d.val + 2048, by omega⟩)) := by
  rw [monsterNortonSourceZSpin_basis, map_smul, map_add,
    monsterNortonUCompactSpin_actual_basis, monsterNortonUCompactSpin_actual_basis]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
