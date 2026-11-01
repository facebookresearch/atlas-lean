/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortOctadCertificate0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortOctadCertificate1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortOctadCertificate2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortOctadCertificate3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortOctadCertificate4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortOctadCertificate5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortOctadCertificate6
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortOctadCertificate7
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortOctadCertificate8
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortPairCertificate0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortPairCertificate1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortCertificateSoundness

/-! Complete original short-coordinate fixation of the actual corrected fourth flag lift. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Complete full preferred-Q and original-coefficient matching for all listed octad signs. -/
theorem generatedFourth_lift_short_octad_certificate (j : Fin 63) (e : Fin 64) :
    generatedFourthLiftShortFiniteMatch (generatedFourthLiftShortSourceQ j e)
      (generatedFourthLiftShortOctadNumerator j e) (generatedFourthLiftShortOctadTargets j e) := by
  have hb : ∀ b : Fin 9, ∀ k : Fin 7, ∀ f : Fin 64,
      let i : Fin 63 := ⟨7 * b.val + k.val, by omega⟩
      generatedFourthLiftShortFiniteMatch (generatedFourthLiftShortSourceQ i f)
        (generatedFourthLiftShortOctadNumerator i f)
        (generatedFourthLiftShortOctadTargets i f) := by
    intro b
    fin_cases b
    · exact generatedFourth_lift_short_octad_certificate_0
    · exact generatedFourth_lift_short_octad_certificate_1
    · exact generatedFourth_lift_short_octad_certificate_2
    · exact generatedFourth_lift_short_octad_certificate_3
    · exact generatedFourth_lift_short_octad_certificate_4
    · exact generatedFourth_lift_short_octad_certificate_5
    · exact generatedFourth_lift_short_octad_certificate_6
    · exact generatedFourth_lift_short_octad_certificate_7
    · exact generatedFourth_lift_short_octad_certificate_8
  have he : (⟨7 * (j.val / 7) + j.val % 7, by omega⟩ : Fin 63) = j := by
    apply Fin.ext
    dsimp
    omega
  simpa only [he] using hb (⟨j.val / 7, by omega⟩ : Fin 9)
    (⟨j.val % 7, Nat.mod_lt _ (by decide)⟩ : Fin 7) e

/-- Complete full preferred-Q and original-coefficient matching for every actual pair row. -/
theorem generatedFourth_lift_short_pair_certificate (s : Fin 2) (a b : Fin 24) (hab : a < b) :
    generatedFourthLiftShortFiniteMatch (generatedFourthLiftShortPairQ s a b)
      (generatedFourthLiftShortPairNumerator s a b)
      (generatedFourthLiftShortPairTargets s a b) := by
  have hs : s = 0 ∨ s = 1 := by
    fin_cases s
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hs with rfl | rfl
  · exact generatedFourth_lift_short_pair_certificate_0 a b hab
  · exact generatedFourth_lift_short_pair_certificate_1 a b hab

/-- The corrected actual local lift fixes the entire original fourth-axis short component. -/
theorem generatedFourth_flag_corrected_lift_short_fixed :
    localShortOperator generatedFourthFlagCorrectedLift
      (griessConwayEncode generatedFourthAxis).2.1 =
        (griessConwayEncode generatedFourthAxis).2.1 :=
  generatedFourth_lift_short_certificate_soundness generatedFourth_lift_short_octad_certificate
    generatedFourth_lift_short_pair_certificate

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
