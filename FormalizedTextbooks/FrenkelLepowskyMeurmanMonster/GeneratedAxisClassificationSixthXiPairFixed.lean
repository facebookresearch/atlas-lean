/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed18
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed19
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed20
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed21
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed22
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed23
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed24
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed25
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed26
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed27
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed28
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed29
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed30
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed31
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed32
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed33
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairFixed34

/-! Every original pair-source output coordinate is fixed with its complete preferred phase. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All 552 genuine pair-source output coordinates are fixed by the corrected Xi lift. -/
theorem generatedSixth_xi_pair_fixed (j : Fin 552) :
    localShortOperator (generatedSixthCorrectedGenerator 4)
        (griessConwayEncode generatedSixthAxis).2.1 (generatedSixthXiPairOutput j) =
      (griessConwayEncode generatedSixthAxis).2.1 (generatedSixthXiPairOutput j) := by
  have hj := j.isLt
  have hb : j.val / 16 ≤ 34 := by omega
  interval_cases h : j.val / 16
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed00 ⟨j.val % 16, ha⟩
    have he : (⟨j.val % 16, by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change j.val % 16 = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed01 ⟨j.val % 16, ha⟩
    have he : (⟨16 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 16 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed02 ⟨j.val % 16, ha⟩
    have he : (⟨32 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 32 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed03 ⟨j.val % 16, ha⟩
    have he : (⟨48 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 48 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed04 ⟨j.val % 16, ha⟩
    have he : (⟨64 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 64 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed05 ⟨j.val % 16, ha⟩
    have he : (⟨80 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 80 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed06 ⟨j.val % 16, ha⟩
    have he : (⟨96 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 96 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed07 ⟨j.val % 16, ha⟩
    have he : (⟨112 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 112 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed08 ⟨j.val % 16, ha⟩
    have he : (⟨128 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 128 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed09 ⟨j.val % 16, ha⟩
    have he : (⟨144 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 144 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed10 ⟨j.val % 16, ha⟩
    have he : (⟨160 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 160 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed11 ⟨j.val % 16, ha⟩
    have he : (⟨176 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 176 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed12 ⟨j.val % 16, ha⟩
    have he : (⟨192 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 192 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed13 ⟨j.val % 16, ha⟩
    have he : (⟨208 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 208 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed14 ⟨j.val % 16, ha⟩
    have he : (⟨224 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 224 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed15 ⟨j.val % 16, ha⟩
    have he : (⟨240 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 240 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed16 ⟨j.val % 16, ha⟩
    have he : (⟨256 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 256 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed17 ⟨j.val % 16, ha⟩
    have he : (⟨272 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 272 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed18 ⟨j.val % 16, ha⟩
    have he : (⟨288 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 288 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed19 ⟨j.val % 16, ha⟩
    have he : (⟨304 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 304 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed20 ⟨j.val % 16, ha⟩
    have he : (⟨320 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 320 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed21 ⟨j.val % 16, ha⟩
    have he : (⟨336 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 336 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed22 ⟨j.val % 16, ha⟩
    have he : (⟨352 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 352 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed23 ⟨j.val % 16, ha⟩
    have he : (⟨368 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 368 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed24 ⟨j.val % 16, ha⟩
    have he : (⟨384 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 384 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed25 ⟨j.val % 16, ha⟩
    have he : (⟨400 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 400 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed26 ⟨j.val % 16, ha⟩
    have he : (⟨416 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 416 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed27 ⟨j.val % 16, ha⟩
    have he : (⟨432 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 432 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed28 ⟨j.val % 16, ha⟩
    have he : (⟨448 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 448 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed29 ⟨j.val % 16, ha⟩
    have he : (⟨464 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 464 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed30 ⟨j.val % 16, ha⟩
    have he : (⟨480 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 480 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed31 ⟨j.val % 16, ha⟩
    have he : (⟨496 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 496 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed32 ⟨j.val % 16, ha⟩
    have he : (⟨512 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 512 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val % 16 < 16 := by omega
    have hf := generatedSixth_xi_pair_fixed33 ⟨j.val % 16, ha⟩
    have he : (⟨528 + (j.val % 16), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 528 + (j.val % 16) = j.val
      omega
    simpa only [he] using hf
  · have ha : j.val - 544 < 8 := by omega
    have hf := generatedSixth_xi_pair_fixed34 ⟨j.val - 544, ha⟩
    have he : (⟨544 + (j.val - 544), by omega⟩ : Fin 552) = j := by
      apply Fin.ext
      change 544 + (j.val - 544) = j.val
      omega
    simpa only [he] using hf

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
