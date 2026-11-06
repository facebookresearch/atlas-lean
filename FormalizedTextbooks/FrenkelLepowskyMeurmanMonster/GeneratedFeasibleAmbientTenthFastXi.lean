/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaCertified
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthBlocks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthPack

/-! The cached integer Gaussian with its Gray-code, sign and diagonal tables packed into single
natural numbers. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

set_option maxRecDepth 100000 in
/-- The 64 Gray-code labels in 12-bit fields. -/
def generatedFeasibleAmbientTenthGrayNat : ℕ := generatedFeasibleAmbientTenthPack
    [0x1c0180fc0f400000, 0xd802c0240e00e80, 0x80cc0c40300340d0, 0x500540b00b804c04,
    0x940600680ac0a40, 0x408008807c07809c, 0x9009407007808c08, 0x540a00a806c0640,
    0x40400480bc0b805c, 0xdc0d803c0340c00c, 0x180ec0e40200280, 0x800c0040f00f4010]

/-- The 64 Gray-code signs (bit set for `-1`). -/
def generatedFeasibleAmbientTenthGraySignNat : ℕ := 0x8117177e177e7ee8

set_option maxRecDepth 100000 in
/-- The diagonal Gaussian signs at all 4096 spin labels (bit set for `+1`). -/
def generatedFeasibleAmbientTenthGammaNat : ℕ := generatedFeasibleAmbientTenthPack
    [0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
    0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
    0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
    0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
    0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
    0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8]

/-- The Gray-code label `a`. -/
def generatedFeasibleAmbientTenthGrayLabelF (a : Fin 64) : Fin 4096 :=
  ⟨(generatedFeasibleAmbientTenthGrayNat >>> (12 * a.val)) % 4096, Nat.mod_lt _ (by decide)⟩

/-- The Gray-code sign `a`. -/
def generatedFeasibleAmbientTenthGraySignF (a : Fin 64) : ℤ := 1 - 2 *
    (((generatedFeasibleAmbientTenthGraySignNat >>> a.val) % 2 : ℕ) : ℤ)

/-- The diagonal Gaussian sign at a spin label. -/
def generatedFeasibleAmbientTenthGammaF (n : Fin 4096) : ℤ := 2 *
    (((generatedFeasibleAmbientTenthGammaNat >>> n.val) % 2 : ℕ) : ℤ) - 1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- All 64 Gray-code labels are compared.
theorem generatedFeasibleAmbientTenth_gray_label_fast : ∀ a : Fin 64,
    generatedFeasibleAmbientTenthGrayLabelF a = generatedSixthGrayCodeLabel a := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- All 64 Gray-code signs are compared.
theorem generatedFeasibleAmbientTenth_gray_sign_fast : ∀ a : Fin 64,
    generatedFeasibleAmbientTenthGraySignF a = generatedSixthGraySign a := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 0 to 511 are compared.
private theorem gamma0 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthGammaF (generatedFeasibleAmbientTenthBlockLabel 0 a) =
        generatedSixthSpinGammaFast (generatedFeasibleAmbientTenthBlockLabel 0 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 512 to 1023 are compared.
private theorem gamma1 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthGammaF (generatedFeasibleAmbientTenthBlockLabel 1 a) =
        generatedSixthSpinGammaFast (generatedFeasibleAmbientTenthBlockLabel 1 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1024 to 1535 are compared.
private theorem gamma2 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthGammaF (generatedFeasibleAmbientTenthBlockLabel 2 a) =
        generatedSixthSpinGammaFast (generatedFeasibleAmbientTenthBlockLabel 2 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1536 to 2047 are compared.
private theorem gamma3 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthGammaF (generatedFeasibleAmbientTenthBlockLabel 3 a) =
        generatedSixthSpinGammaFast (generatedFeasibleAmbientTenthBlockLabel 3 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2048 to 2559 are compared.
private theorem gamma4 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthGammaF (generatedFeasibleAmbientTenthBlockLabel 4 a) =
        generatedSixthSpinGammaFast (generatedFeasibleAmbientTenthBlockLabel 4 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2560 to 3071 are compared.
private theorem gamma5 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthGammaF (generatedFeasibleAmbientTenthBlockLabel 5 a) =
        generatedSixthSpinGammaFast (generatedFeasibleAmbientTenthBlockLabel 5 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3072 to 3583 are compared.
private theorem gamma6 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthGammaF (generatedFeasibleAmbientTenthBlockLabel 6 a) =
        generatedSixthSpinGammaFast (generatedFeasibleAmbientTenthBlockLabel 6 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3584 to 4095 are compared.
private theorem gamma7 : ∀ a : Fin 512,
    generatedFeasibleAmbientTenthGammaF (generatedFeasibleAmbientTenthBlockLabel 7 a) =
        generatedSixthSpinGammaFast (generatedFeasibleAmbientTenthBlockLabel 7 a) := by
  decide +kernel

/-- The packed diagonal signs agree with the certified diagonal signs. -/
theorem generatedFeasibleAmbientTenth_gamma_fast (n : Fin 4096) :
    generatedFeasibleAmbientTenthGammaF n = generatedSixthSpinGammaFast n := by
  revert n
  apply generatedFeasibleAmbientTenth_fin4096_blocks
  intro q
  fin_cases q
  · exact gamma0
  · exact gamma1
  · exact gamma2
  · exact gamma3
  · exact gamma4
  · exact gamma5
  · exact gamma6
  · exact gamma7

/-- The integer Gaussian with packed tables. -/
def generatedFeasibleAmbientTenthXi (v : Fin 4096 → ℤ) (n : Fin 4096) : ℤ :=
  ∑ a : Fin 64,
    let m := generatedSixthSpinLabelXor n (generatedFeasibleAmbientTenthGrayLabelF a)
    let z := v m
    if z = 0 then 0 else generatedFeasibleAmbientTenthGraySignF a *
        generatedFeasibleAmbientTenthGammaF m * z

/-- The packed Gaussian is the cached integer Gaussian. -/
theorem generatedFeasibleAmbientTenth_xi_fast (v : Fin 4096 → ℤ) : generatedFeasibleAmbientTenthXi
    v = generatedSixthIntegerXiCached v := by
  funext n
  unfold generatedFeasibleAmbientTenthXi generatedSixthIntegerXiCached
  simp only [generatedFeasibleAmbientTenth_gray_label_fast,
      generatedFeasibleAmbientTenth_gray_sign_fast, generatedFeasibleAmbientTenth_gamma_fast]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
