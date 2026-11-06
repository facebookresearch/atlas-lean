/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddGeometry
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddCode0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddCode1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddCode2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddCode3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddSupport0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddSupport1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddSupport2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddSupport3

/-! Complete bounded source-code, preferred-phase and support certificates bind actual odd
labels. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every displayed source family is the genuine original code transform modulo all-one. -/
theorem generatedSixth_monomial_odd_source (k : Fin 4) (f : Fin 512) :
    (generatedSixthMonomialOddCode (generatedSixthMonomialOddSourceFamily k f)).val =
      (generatedSixthMonomialOddFullSourceCode k f).val % 2048 := by
  fin_cases k
  · exact generatedSixth_monomial_odd_source0 f
  · exact generatedSixth_monomial_odd_source1 f
  · exact generatedSixth_monomial_odd_source2 f
  · exact generatedSixth_monomial_odd_source3 f

/-- The entire original constant preferred phase equals its checked cache. -/
theorem generatedSixth_monomial_odd_phase_base (k : Fin 4) (f : Fin 512) :
    monsterMonomialQuadratic (representativeMatrix (generatedSixthMonomialMaskPhaseRows k))
      (golayLabelCoefficients ⟨(generatedSixthMonomialOddCode f).val, by omega⟩) +
    spinDot (golayLabelCoefficients (generatedSixthMonomialMaskTranslation k))
      (sourceWordTheta ⟨(generatedSixthMonomialOddCode f).val, by omega⟩) +
    spinDot (golayLabelCoefficients (generatedSixthMonomialMaskModulation k))
      (golayLabelCoefficients ⟨(generatedSixthMonomialOddCode f).val, by omega⟩) =
    generatedSixthMonomialOddPhaseBase k f := by
  fin_cases k
  · exact generatedSixth_monomial_odd_phase_base0 f
  · exact generatedSixth_monomial_odd_phase_base1 f
  · exact generatedSixth_monomial_odd_phase_base2 f
  · exact generatedSixth_monomial_odd_phase_base3 f

/-- Every actual original odd output has the genuine signed source-line permutation. -/
theorem generatedSixth_monomial_odd_permutation (k : Fin 4) (f : Fin 512) (j : Fin 24) :
    griessShortPermutation (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2
      (Sum.inr (Sum.inr
        (generatedSixthMonomialOddCode (generatedSixthMonomialOddSourceFamily k f),
          generatedSixthMonomialPairInput k j))) =
      Sum.inr (Sum.inr (generatedSixthMonomialOddCode f, j)) :=
  generatedSixth_monomial_odd_source_permutation k f
    (generatedSixth_monomial_odd_source k f) j

/-- Every nonzero original spin-pair sum has its genuine displayed code owner. -/
theorem generatedSixth_monomial_odd_owner (d : Fin 2048) :
    generatedSixthPackedSpinPhase ⟨d.val, by omega⟩ +
      generatedSixthPackedSpinPhase ⟨d.val + 2048, by omega⟩ = 0 ∨
    generatedSixthMonomialOddCode (generatedSixthMonomialOddOwner d) = d := by
  have h : ∀ b : Fin 4, ∀ a : Fin 512,
      generatedSixthPackedSpinPhase (Fin.ofNat 4096 (b.val * 512 + a.val)) +
        generatedSixthPackedSpinPhase (Fin.ofNat 4096 (b.val * 512 + a.val + 2048)) = 0 ∨
      generatedSixthMonomialOddCode
        (generatedSixthMonomialOddOwner (Fin.ofNat 2048 (b.val * 512 + a.val))) =
          Fin.ofNat 2048 (b.val * 512 + a.val) := by
    intro b a
    fin_cases b
    · exact generatedSixth_monomial_odd_owner0 a
    · exact generatedSixth_monomial_odd_owner1 a
    · exact generatedSixth_monomial_odd_owner2 a
    · exact generatedSixth_monomial_odd_owner3 a
  let b : Fin 4 := ⟨d.val / 512, by omega⟩
  let a : Fin 512 := ⟨d.val % 512, by omega⟩
  have he : b.val * 512 + a.val = d.val := by dsimp [b, a]; omega
  have hl : Fin.ofNat 4096 (b.val * 512 + a.val) = ⟨d.val, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_ofNat, he]
    omega
  have hu : Fin.ofNat 4096 (b.val * 512 + a.val + 2048) =
      ⟨d.val + 2048, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_ofNat, he]
    omega
  have hd : Fin.ofNat 2048 (b.val * 512 + a.val) = d := by
    apply Fin.ext
    simp only [Fin.val_ofNat, he]
    omega
  simpa only [hl, hu, hd] using h b a

/-- Every actual nonzero odd coefficient lies in the completely checked displayed code support. -/
theorem generatedSixth_monomial_odd_support (d : Fin 2048) (j : Fin 24)
    (h : (griessConwayEncode generatedSixthAxis).2.1 (Sum.inr (Sum.inr (d, j))) ≠ 0) :
    generatedSixthMonomialOddCode (generatedSixthMonomialOddOwner d) = d := by
  rcases generatedSixth_monomial_odd_owner d with hz | hd
  · exfalso
    apply h
    rw [generatedSixth_final_odd_coordinate]
    simp only [generatedSixthFinalOddNumerator, hz, mul_zero, Int.cast_zero, zero_div]
  · exact hd

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
