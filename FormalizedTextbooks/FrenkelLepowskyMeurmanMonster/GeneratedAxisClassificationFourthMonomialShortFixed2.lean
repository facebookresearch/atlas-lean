/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate2Block0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate2Block1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate2Block2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate2Block3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate2Block4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate2Block5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate2Block6
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate2Block7
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate2Block8
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortPairCertificate2Sign0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortPairCertificate2Sign1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortCertificateSoundness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialMatrixFixed

/-! Complete original signed short-coordinate fixation of corrected monomial word 2. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All63 actual families retain all64 intrinsic preferred signs and central coefficients. -/
theorem generatedFourth_monomial_short_octad_complete_2 (j : Fin 63) (e : Fin 64) :
    generatedFourthMonomialShortMatch 2 (generatedFourthLiftShortSourceQ j e)
      (generatedFourthLiftShortOctadNumerator j e)
        (generatedFourthMonomialShortOctadTargets2 j e) := by
  have hb : ∀ b : Fin 9, ∀ z : Fin 7, ∀ f : Fin 64,
      let i : Fin 63 := ⟨7 * b.val + z.val, by omega⟩
      generatedFourthMonomialShortMatch 2 (generatedFourthLiftShortSourceQ i f)
        (generatedFourthLiftShortOctadNumerator i f)
          (generatedFourthMonomialShortOctadTargets2 i f) := by
    intro b
    fin_cases b
    · exact generatedFourth_monomial_short_octad_certificate_2_0
    · exact generatedFourth_monomial_short_octad_certificate_2_1
    · exact generatedFourth_monomial_short_octad_certificate_2_2
    · exact generatedFourth_monomial_short_octad_certificate_2_3
    · exact generatedFourth_monomial_short_octad_certificate_2_4
    · exact generatedFourth_monomial_short_octad_certificate_2_5
    · exact generatedFourth_monomial_short_octad_certificate_2_6
    · exact generatedFourth_monomial_short_octad_certificate_2_7
    · exact generatedFourth_monomial_short_octad_certificate_2_8
  have he : (⟨7 * (j.val / 7) + j.val % 7, by omega⟩ : Fin 63) = j := by
    apply Fin.ext
    dsimp
    omega
  simpa only [he] using hb (⟨j.val / 7, by omega⟩ : Fin 9)
    (⟨j.val % 7, Nat.mod_lt _ (by decide)⟩ : Fin 7) e

/-- All increasing physical pairs retain both actual preferred signs and central phases. -/
theorem generatedFourth_monomial_short_pair_complete_2
    (sg : Fin 2) (a b : Fin 24) (hab : a < b) :
    generatedFourthMonomialShortMatch 2 (generatedFourthLiftShortPairQ sg a b)
      (generatedFourthLiftShortPairNumerator sg a b)
      (generatedFourthMonomialShortPairTargets2 sg a b) := by
  fin_cases sg
  · exact generatedFourth_monomial_short_pair_certificate_2_0 a b hab
  · exact generatedFourth_monomial_short_pair_certificate_2_1 a b hab

/-- The entire original fourth-axis short block is fixed by this actual corrected word. -/
theorem generatedFourth_monomial_short_fixed_2 :
    localShortOperator (generatedFourthMonomialCorrectedFiber 2)
      (griessConwayEncode generatedFourthAxis).2.1 =
        (griessConwayEncode generatedFourthAxis).2.1 :=
  generatedFourth_monomial_short_certificate_soundness 2
    generatedFourthMonomialShortOctadTargets2 generatedFourthMonomialShortPairTargets2
    generatedFourth_monomial_short_octad_complete_2
    generatedFourth_monomial_short_pair_complete_2

/-- This original corrected monomial word fixes the entire genuine fourth axis. -/
theorem generatedFourth_monomial_axis_fixed_2 :
    rhoLocal (localFiberIntoH (generatedFourthMonomialCorrectedFiber 2))
      generatedFourthAxis = generatedFourthAxis :=
  generatedFourth_monomial_axis_fixed_of_short 2
    generatedFourth_monomial_short_fixed_2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
