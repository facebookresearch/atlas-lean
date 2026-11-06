/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign20
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign21
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign22
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign23
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign24
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign25
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign26
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign30
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign31
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign32
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign33
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign34
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign35
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSign36

/-! Bounded checked packets cover every genuine occurring octad family and preferred sign. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- All original local signs pull back with the certified preferred global normalization. -/
theorem generatedSixth_monomial_octad_sign_certificate (k : Fin 4) (f : Fin 231)
    (e : Fin 64) (a : Fin 8) :
      (if (trialityEvenMask (generatedSixthMonomialOctadSourceSign k f e)).testBit
        (generatedSixthMonomialOctadSourceCoordinate k f a).val then (-1 : ℤ) else 1) =
      generatedSixthMonomialOctadPhysicalSign k f e *
        (if (trialityEvenMask e).testBit a.val then (-1 : ℤ) else 1) := by
  have h : ∀ k : Fin 4, ∀ p : Fin 7, ∀ r : Fin 33,
      (if (trialityEvenMask (generatedSixthMonomialOctadSourceSign k
        (Fin.ofNat 231 (p.val * 33 + r.val)) e)).testBit
          (generatedSixthMonomialOctadSourceCoordinate k
            (Fin.ofNat 231 (p.val * 33 + r.val)) a).val then (-1 : ℤ) else 1) =
      generatedSixthMonomialOctadPhysicalSign k (Fin.ofNat 231 (p.val * 33 + r.val)) e *
        (if (trialityEvenMask e).testBit a.val then (-1 : ℤ) else 1) := by
    intro k p r
    fin_cases k <;> fin_cases p
    · exact generatedSixth_monomial_octad_sign00 r e a
    · exact generatedSixth_monomial_octad_sign01 r e a
    · exact generatedSixth_monomial_octad_sign02 r e a
    · exact generatedSixth_monomial_octad_sign03 r e a
    · exact generatedSixth_monomial_octad_sign04 r e a
    · exact generatedSixth_monomial_octad_sign05 r e a
    · exact generatedSixth_monomial_octad_sign06 r e a
    · exact generatedSixth_monomial_octad_sign10 r e a
    · exact generatedSixth_monomial_octad_sign11 r e a
    · exact generatedSixth_monomial_octad_sign12 r e a
    · exact generatedSixth_monomial_octad_sign13 r e a
    · exact generatedSixth_monomial_octad_sign14 r e a
    · exact generatedSixth_monomial_octad_sign15 r e a
    · exact generatedSixth_monomial_octad_sign16 r e a
    · exact generatedSixth_monomial_octad_sign20 r e a
    · exact generatedSixth_monomial_octad_sign21 r e a
    · exact generatedSixth_monomial_octad_sign22 r e a
    · exact generatedSixth_monomial_octad_sign23 r e a
    · exact generatedSixth_monomial_octad_sign24 r e a
    · exact generatedSixth_monomial_octad_sign25 r e a
    · exact generatedSixth_monomial_octad_sign26 r e a
    · exact generatedSixth_monomial_octad_sign30 r e a
    · exact generatedSixth_monomial_octad_sign31 r e a
    · exact generatedSixth_monomial_octad_sign32 r e a
    · exact generatedSixth_monomial_octad_sign33 r e a
    · exact generatedSixth_monomial_octad_sign34 r e a
    · exact generatedSixth_monomial_octad_sign35 r e a
    · exact generatedSixth_monomial_octad_sign36 r e a
  let p : Fin 7 := ⟨f.val / 33, by omega⟩
  let r : Fin 33 := ⟨f.val % 33, by omega⟩
  have hf : Fin.ofNat 231 (p.val * 33 + r.val) = f := by
    apply Fin.ext
    simp only [Fin.val_ofNat, p, r]
    omega
  rw [← hf]
  exact h k p r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
