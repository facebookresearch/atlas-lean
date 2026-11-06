/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator20
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator21
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator22
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator23
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator24
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator25
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator26
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator27
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator30
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator31
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator32
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator33
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator34
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator35
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator36
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddNumerator37

/-! Bounded preferred-phase checks cover the whole displayed actual odd support. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every genuine displayed odd coefficient has its complete signed original transport. -/
theorem generatedSixth_monomial_odd_numerator_certificate (k : Fin 4) (f : Fin 512)
    (i : Fin 24) :
    nortonUIntegerSign (generatedSixthMonomialOddPhase k f i) *
      generatedSixthFinalOddNumerator
        (generatedSixthMonomialOddCode (generatedSixthMonomialOddSourceFamily k f))
        (generatedSixthMonomialPairInput k i) =
      generatedSixthFinalOddNumerator (generatedSixthMonomialOddCode f) i := by
  have h : ∀ k : Fin 4, ∀ b : Fin 8, ∀ d : Fin 64,
      let f : Fin 512 := Fin.ofNat 512 (b.val * 64 + d.val)
      nortonUIntegerSign (generatedSixthMonomialOddPhase k f i) *
        generatedSixthFinalOddNumerator
          (generatedSixthMonomialOddCode (generatedSixthMonomialOddSourceFamily k f))
          (generatedSixthMonomialPairInput k i) =
        generatedSixthFinalOddNumerator (generatedSixthMonomialOddCode f) i := by
    intro k b d
    fin_cases k <;> fin_cases b
    · exact generatedSixth_monomial_odd_numerator00 d i
    · exact generatedSixth_monomial_odd_numerator01 d i
    · exact generatedSixth_monomial_odd_numerator02 d i
    · exact generatedSixth_monomial_odd_numerator03 d i
    · exact generatedSixth_monomial_odd_numerator04 d i
    · exact generatedSixth_monomial_odd_numerator05 d i
    · exact generatedSixth_monomial_odd_numerator06 d i
    · exact generatedSixth_monomial_odd_numerator07 d i
    · exact generatedSixth_monomial_odd_numerator10 d i
    · exact generatedSixth_monomial_odd_numerator11 d i
    · exact generatedSixth_monomial_odd_numerator12 d i
    · exact generatedSixth_monomial_odd_numerator13 d i
    · exact generatedSixth_monomial_odd_numerator14 d i
    · exact generatedSixth_monomial_odd_numerator15 d i
    · exact generatedSixth_monomial_odd_numerator16 d i
    · exact generatedSixth_monomial_odd_numerator17 d i
    · exact generatedSixth_monomial_odd_numerator20 d i
    · exact generatedSixth_monomial_odd_numerator21 d i
    · exact generatedSixth_monomial_odd_numerator22 d i
    · exact generatedSixth_monomial_odd_numerator23 d i
    · exact generatedSixth_monomial_odd_numerator24 d i
    · exact generatedSixth_monomial_odd_numerator25 d i
    · exact generatedSixth_monomial_odd_numerator26 d i
    · exact generatedSixth_monomial_odd_numerator27 d i
    · exact generatedSixth_monomial_odd_numerator30 d i
    · exact generatedSixth_monomial_odd_numerator31 d i
    · exact generatedSixth_monomial_odd_numerator32 d i
    · exact generatedSixth_monomial_odd_numerator33 d i
    · exact generatedSixth_monomial_odd_numerator34 d i
    · exact generatedSixth_monomial_odd_numerator35 d i
    · exact generatedSixth_monomial_odd_numerator36 d i
    · exact generatedSixth_monomial_odd_numerator37 d i
  let b : Fin 8 := ⟨f.val / 64, by omega⟩
  let d : Fin 64 := ⟨f.val % 64, by omega⟩
  have hf : Fin.ofNat 512 (b.val * 64 + d.val) = f := by
    apply Fin.ext
    simp only [Fin.val_ofNat, b, d]
    omega
  rw [← hf]
  exact h k b d

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
