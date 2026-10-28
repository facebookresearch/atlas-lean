/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate0Block0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate0Block1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate0Block2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate0Block3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate0Block4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate0Block5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate0Block6
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate0Block7
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortOctadCertificate0Block8
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortPairCertificate0Sign0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortPairCertificate0Sign1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialShortCertificateSoundness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialMatrixFixed

/-! Complete original signed short-coordinate fixation of corrected monomial word 0. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All63 actual families retain all64 intrinsic preferred signs and central coefficients. -/
theorem generatedFourth_monomial_short_octad_complete_0 (j : Fin 63) (e : Fin 64) :
    generatedFourthMonomialShortMatch 0 (generatedFourthLiftShortSourceQ j e)
      (generatedFourthLiftShortOctadNumerator j e)
        (generatedFourthMonomialShortOctadTargets0 j e) := by
  have hb : ∀ b : Fin 9, ∀ z : Fin 7, ∀ f : Fin 64,
      let i : Fin 63 := ⟨7 * b.val + z.val, by omega⟩
      generatedFourthMonomialShortMatch 0 (generatedFourthLiftShortSourceQ i f)
        (generatedFourthLiftShortOctadNumerator i f)
          (generatedFourthMonomialShortOctadTargets0 i f) := by
    intro b
    fin_cases b
    · exact generatedFourth_monomial_short_octad_certificate_0_0
    · exact generatedFourth_monomial_short_octad_certificate_0_1
    · exact generatedFourth_monomial_short_octad_certificate_0_2
    · exact generatedFourth_monomial_short_octad_certificate_0_3
    · exact generatedFourth_monomial_short_octad_certificate_0_4
    · exact generatedFourth_monomial_short_octad_certificate_0_5
    · exact generatedFourth_monomial_short_octad_certificate_0_6
    · exact generatedFourth_monomial_short_octad_certificate_0_7
    · exact generatedFourth_monomial_short_octad_certificate_0_8
  have he : (⟨7 * (j.val / 7) + j.val % 7, by omega⟩ : Fin 63) = j := by
    apply Fin.ext
    dsimp
    omega
  simpa only [he] using hb (⟨j.val / 7, by omega⟩ : Fin 9)
    (⟨j.val % 7, Nat.mod_lt _ (by decide)⟩ : Fin 7) e

/-- All increasing physical pairs retain both actual preferred signs and central phases. -/
theorem generatedFourth_monomial_short_pair_complete_0
    (sg : Fin 2) (a b : Fin 24) (hab : a < b) :
    generatedFourthMonomialShortMatch 0 (generatedFourthLiftShortPairQ sg a b)
      (generatedFourthLiftShortPairNumerator sg a b)
      (generatedFourthMonomialShortPairTargets0 sg a b) := by
  fin_cases sg
  · exact generatedFourth_monomial_short_pair_certificate_0_0 a b hab
  · exact generatedFourth_monomial_short_pair_certificate_0_1 a b hab

/-- The entire original fourth-axis short block is fixed by this actual corrected word. -/
theorem generatedFourth_monomial_short_fixed_0 :
    localShortOperator (generatedFourthMonomialCorrectedFiber 0)
      (griessConwayEncode generatedFourthAxis).2.1 =
        (griessConwayEncode generatedFourthAxis).2.1 :=
  generatedFourth_monomial_short_certificate_soundness 0
    generatedFourthMonomialShortOctadTargets0 generatedFourthMonomialShortPairTargets0
    generatedFourth_monomial_short_octad_complete_0
    generatedFourth_monomial_short_pair_complete_0

/-- This original corrected monomial word fixes the entire genuine fourth axis. -/
theorem generatedFourth_monomial_axis_fixed_0 :
    rhoLocal (localFiberIntoH (generatedFourthMonomialCorrectedFiber 0))
      generatedFourthAxis = generatedFourthAxis :=
  generatedFourth_monomial_axis_fixed_of_short 0
    generatedFourth_monomial_short_fixed_0

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
