/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate3Block0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate3Block1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate3Block2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate3Block3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate3Block4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate3Block5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate3Block6
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate3Block7
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate3Block8
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortPairCertificate3Sign0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortPairCertificate3Sign1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortCertificateSoundness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialMatrixFixed

/-! Complete original signed short-coordinate fixation of corrected monomial word 3. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All63 actual families retain all64 intrinsic preferred signs and central coefficients. -/
theorem generatedFourth_monomial_short_octad_complete_3 (j : Fin 63) (e : Fin 64) :
    generatedFourthMonomialShortMatch 3 (generatedFourthLiftShortSourceQ j e)
      (generatedFourthLiftShortOctadNumerator j e)
        (generatedFourthMonomialShortOctadTargets3 j e) := by
  have hb : ∀ b : Fin 9, ∀ z : Fin 7, ∀ f : Fin 64,
      let i : Fin 63 := ⟨7 * b.val + z.val, by omega⟩
      generatedFourthMonomialShortMatch 3 (generatedFourthLiftShortSourceQ i f)
        (generatedFourthLiftShortOctadNumerator i f)
          (generatedFourthMonomialShortOctadTargets3 i f) := by
    intro b
    fin_cases b
    · exact generatedFourth_monomial_short_octad_certificate_3_0
    · exact generatedFourth_monomial_short_octad_certificate_3_1
    · exact generatedFourth_monomial_short_octad_certificate_3_2
    · exact generatedFourth_monomial_short_octad_certificate_3_3
    · exact generatedFourth_monomial_short_octad_certificate_3_4
    · exact generatedFourth_monomial_short_octad_certificate_3_5
    · exact generatedFourth_monomial_short_octad_certificate_3_6
    · exact generatedFourth_monomial_short_octad_certificate_3_7
    · exact generatedFourth_monomial_short_octad_certificate_3_8
  have he : (⟨7 * (j.val / 7) + j.val % 7, by omega⟩ : Fin 63) = j := by
    apply Fin.ext
    dsimp
    omega
  simpa only [he] using hb (⟨j.val / 7, by omega⟩ : Fin 9)
    (⟨j.val % 7, Nat.mod_lt _ (by decide)⟩ : Fin 7) e

/-- All increasing physical pairs retain both actual preferred signs and central phases. -/
theorem generatedFourth_monomial_short_pair_complete_3
    (sg : Fin 2) (a b : Fin 24) (hab : a < b) :
    generatedFourthMonomialShortMatch 3 (generatedFourthLiftShortPairQ sg a b)
      (generatedFourthLiftShortPairNumerator sg a b)
      (generatedFourthMonomialShortPairTargets3 sg a b) := by
  fin_cases sg
  · exact generatedFourth_monomial_short_pair_certificate_3_0 a b hab
  · exact generatedFourth_monomial_short_pair_certificate_3_1 a b hab

/-- The entire original fourth-axis short block is fixed by this actual corrected word. -/
theorem generatedFourth_monomial_short_fixed_3 :
    localShortOperator (generatedFourthMonomialCorrectedFiber 3)
      (griessConwayEncode generatedFourthAxis).2.1 =
        (griessConwayEncode generatedFourthAxis).2.1 :=
  generatedFourth_monomial_short_certificate_soundness 3
    generatedFourthMonomialShortOctadTargets3 generatedFourthMonomialShortPairTargets3
    generatedFourth_monomial_short_octad_complete_3
    generatedFourth_monomial_short_pair_complete_3

/-- This original corrected monomial word fixes the entire genuine fourth axis. -/
theorem generatedFourth_monomial_axis_fixed_3 :
    rhoLocal (localFiberIntoH (generatedFourthMonomialCorrectedFiber 3))
      generatedFourthAxis = generatedFourthAxis :=
  generatedFourth_monomial_axis_fixed_of_short 3
    generatedFourth_monomial_short_fixed_3

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
