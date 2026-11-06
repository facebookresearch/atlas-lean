/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator20
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator21
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator22
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator23
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator24
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator25
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator26
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator30
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator31
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator32
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator33
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator34
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator35
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadNumerator36

/-! Bounded checked packets cover every genuine occurring octad family and preferred sign. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every actual occurring source coefficient transports with its complete preferred phase. -/
theorem generatedSixth_monomial_octad_numerator_certificate (k : Fin 4) (f : Fin 231)
    (e : Fin 64) :
      nortonUIntegerSign (generatedSixthMonomialOctadPhase k f e) *
      generatedSixthFinalOctadCachedNumerator (generatedSixthMonomialOctadSourceFamily k f)
        (generatedSixthMonomialOctadSourceSign k f e) =
      generatedSixthFinalOctadCachedNumerator f e := by
  have h : ∀ k : Fin 4, ∀ p : Fin 7, ∀ r : Fin 33,
      nortonUIntegerSign (generatedSixthMonomialOctadPhase k
        (Fin.ofNat 231 (p.val * 33 + r.val)) e) *
      generatedSixthFinalOctadCachedNumerator
        (generatedSixthMonomialOctadSourceFamily k (Fin.ofNat 231 (p.val * 33 + r.val)))
        (generatedSixthMonomialOctadSourceSign k (Fin.ofNat 231 (p.val * 33 + r.val)) e) =
      generatedSixthFinalOctadCachedNumerator (Fin.ofNat 231 (p.val * 33 + r.val)) e := by
    intro k p r
    fin_cases k <;> fin_cases p
    · exact generatedSixth_monomial_octad_numerator00 r e
    · exact generatedSixth_monomial_octad_numerator01 r e
    · exact generatedSixth_monomial_octad_numerator02 r e
    · exact generatedSixth_monomial_octad_numerator03 r e
    · exact generatedSixth_monomial_octad_numerator04 r e
    · exact generatedSixth_monomial_octad_numerator05 r e
    · exact generatedSixth_monomial_octad_numerator06 r e
    · exact generatedSixth_monomial_octad_numerator10 r e
    · exact generatedSixth_monomial_octad_numerator11 r e
    · exact generatedSixth_monomial_octad_numerator12 r e
    · exact generatedSixth_monomial_octad_numerator13 r e
    · exact generatedSixth_monomial_octad_numerator14 r e
    · exact generatedSixth_monomial_octad_numerator15 r e
    · exact generatedSixth_monomial_octad_numerator16 r e
    · exact generatedSixth_monomial_octad_numerator20 r e
    · exact generatedSixth_monomial_octad_numerator21 r e
    · exact generatedSixth_monomial_octad_numerator22 r e
    · exact generatedSixth_monomial_octad_numerator23 r e
    · exact generatedSixth_monomial_octad_numerator24 r e
    · exact generatedSixth_monomial_octad_numerator25 r e
    · exact generatedSixth_monomial_octad_numerator26 r e
    · exact generatedSixth_monomial_octad_numerator30 r e
    · exact generatedSixth_monomial_octad_numerator31 r e
    · exact generatedSixth_monomial_octad_numerator32 r e
    · exact generatedSixth_monomial_octad_numerator33 r e
    · exact generatedSixth_monomial_octad_numerator34 r e
    · exact generatedSixth_monomial_octad_numerator35 r e
    · exact generatedSixth_monomial_octad_numerator36 r e
  let p : Fin 7 := ⟨f.val / 33, by omega⟩
  let r : Fin 33 := ⟨f.val % 33, by omega⟩
  have hf : Fin.ofNat 231 (p.val * 33 + r.val) = f := by
    apply Fin.ext
    simp only [Fin.val_ofNat, p, r]
    omega
  rw [← hf]
  exact h k p r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
