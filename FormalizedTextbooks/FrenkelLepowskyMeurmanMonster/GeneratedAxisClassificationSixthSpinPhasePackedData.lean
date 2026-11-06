/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinAnchor

/-! Compact original signed spin phases, checked against the genuine affine Pauli formula. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
open scoped Matrix

/-- Positive coordinates of the genuine normalized original spin phase vector. -/
def generatedSixthSpinPositiveMask : ℕ :=
  (0x2929 +
    (0x686800000000 <<< 64) +
    (0x808000000000000 <<< 128) +
    (0x20200000 <<< 192) +
    (0x6108000000000000 <<< 256) +
    (0x49200000 <<< 320) +
    (0x4029 <<< 384) +
    (0x16800000000 <<< 448) +
    (0x1680000 <<< 512) +
    (0x4029000000000000 <<< 576) +
    (0x204900000000 <<< 640) +
    (0x861 <<< 704) +
    (0x494900000000 <<< 768) +
    (0x6161 <<< 832) +
    (0x68680000 <<< 896) +
    (0x2929000000000000 <<< 960) +
    (0x108600000000 <<< 1024) +
    (0x9204 <<< 1088) +
    (0x2940000 <<< 1152) +
    (0x1680000000000000 <<< 1216) +
    (0x94940000 <<< 1280) +
    (0x8080000000000000 <<< 1344) +
    (0x868600000000 <<< 1408) +
    (0x404 <<< 1472) +
    (0x9292000000000000 <<< 1536) +
    (0x10100000 <<< 1600) +
    (0x8080 <<< 1664) +
    (0x949400000000 <<< 1728) +
    (0x1680 <<< 1792) +
    (0x29400000000 <<< 1856) +
    (0x492000000000000 <<< 1920) +
    (0x86100000 <<< 1984) +
    (0x9402 <<< 2048) +
    (0x801600000000 <<< 2112) +
    (0x8610000000000000 <<< 2176) +
    (0x4920000 <<< 2240) +
    (0x8686000000000000 <<< 2304) +
    (0x4040000 <<< 2368) +
    (0x9494 <<< 2432) +
    (0x808000000000 <<< 2496) +
    (0x80800000 <<< 2560) +
    (0x9494000000000000 <<< 2624) +
    (0x929200000000 <<< 2688) +
    (0x1010 <<< 2752) +
    (0x920400000000 <<< 2816) +
    (0x1086 <<< 2880) +
    (0x80160000 <<< 2944) +
    (0x9402000000000000 <<< 3008) +
    (0x80800000000 <<< 3072) +
    (0x2020 <<< 3136) +
    (0x29290000 <<< 3200) +
    (0x6868000000000000 <<< 3264) +
    (0x29400000 <<< 3328) +
    (0x6801000000000000 <<< 3392) +
    (0x86100000000 <<< 3456) +
    (0x2049 <<< 3520) +
    (0x4920000000000000 <<< 3584) +
    (0x61080000 <<< 3648) +
    (0x6801 <<< 3712) +
    (0x294000000000 <<< 3776) +
    (0x6868 <<< 3840) +
    (0x292900000000 <<< 3904) +
    (0x4949000000000000 <<< 3968) +
    (0x61610000 <<< 4032))

/-- Negative coordinates of the genuine normalized original spin phase vector. -/
def generatedSixthSpinNegativeMask : ℕ :=
  (0x4040 +
    (0x10100000000 <<< 64) +
    (0x6161000000000000 <<< 128) +
    (0x49490000 <<< 192) +
    (0x861000000000000 <<< 256) +
    (0x20490000 <<< 320) +
    (0x2940 <<< 384) +
    (0x680100000000 <<< 448) +
    (0x68010000 <<< 512) +
    (0x2940000000000000 <<< 576) +
    (0x492000000000 <<< 640) +
    (0x6108 <<< 704) +
    (0x202000000000 <<< 768) +
    (0x808 <<< 832) +
    (0x1010000 <<< 896) +
    (0x4040000000000000 <<< 960) +
    (0x861000000000 <<< 1024) +
    (0x492 <<< 1088) +
    (0x94020000 <<< 1152) +
    (0x8016000000000000 <<< 1216) +
    (0x2020000 <<< 1280) +
    (0x1616000000000000 <<< 1344) +
    (0x101000000000 <<< 1408) +
    (0x9292 <<< 1472) +
    (0x404000000000000 <<< 1536) +
    (0x86860000 <<< 1600) +
    (0x1616 <<< 1664) +
    (0x20200000000 <<< 1728) +
    (0x8016 <<< 1792) +
    (0x940200000000 <<< 1856) +
    (0x9204000000000000 <<< 1920) +
    (0x10860000 <<< 1984) +
    (0x294 <<< 2048) +
    (0x168000000000 <<< 2112) +
    (0x1086000000000000 <<< 2176) +
    (0x92040000 <<< 2240) +
    (0x1010000000000000 <<< 2304) +
    (0x92920000 <<< 2368) +
    (0x202 <<< 2432) +
    (0x161600000000 <<< 2496) +
    (0x16160000 <<< 2560) +
    (0x202000000000000 <<< 2624) +
    (0x40400000000 <<< 2688) +
    (0x8686 <<< 2752) +
    (0x49200000000 <<< 2816) +
    (0x8610 <<< 2880) +
    (0x16800000 <<< 2944) +
    (0x294000000000000 <<< 3008) +
    (0x616100000000 <<< 3072) +
    (0x4949 <<< 3136) +
    (0x40400000 <<< 3200) +
    (0x101000000000000 <<< 3264) +
    (0x40290000 <<< 3328) +
    (0x168000000000000 <<< 3392) +
    (0x610800000000 <<< 3456) +
    (0x4920 <<< 3520) +
    (0x2049000000000000 <<< 3584) +
    (0x8610000 <<< 3648) +
    (0x168 <<< 3712) +
    (0x402900000000 <<< 3776) +
    (0x101 <<< 3840) +
    (0x404000000000 <<< 3904) +
    (0x2020000000000000 <<< 3968) +
    (0x8080000 <<< 4032))

/-- The compact signed phase at each of the original 4096 spin addresses. -/
def generatedSixthPackedSpinPhase (n : Fin 4096) : ℤ :=
  (if generatedSixthSpinPositiveMask.testBit n.val then 1 else 0) -
    (if generatedSixthSpinNegativeMask.testBit n.val then 1 else 0)

/-- The genuine support matrix has the checked three nonzero ordinary modulation rows. -/
def generatedSixthPackedSupportMatrix : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  fun j i => golayLabelCoefficients
    (![1504, 3079, 912, 0, 0, 0, 0, 0, 0, 0, 0, 0] j) i

/-- Constant matrix evaluation is checked once, retaining its actual Pauli-product origin. -/
theorem generatedSixth_packed_support_matrix :
    generatedSixthAffineModulationMatrix (generatedSixthPartialPure 8) =
      generatedSixthPackedSupportMatrix := by
  decide +kernel

/-- A finite phase formula with the proved ordinary support rows already evaluated. -/
def generatedSixthPackedPhaseFormula (n : Fin 4096) : ℤ :=
  if generatedSixthPackedSupportMatrix *ᵥ golayLabelCoefficients n = 0 then
    nortonUIntegerSign (spinPhase (generatedSixthAffinePauliProduct
      (fun j => generatedSixthSpinPauliCache j 8)
      (generatedSixthPartialProjection 8 *ᵥ golayLabelCoefficients n)) 0) else 0

/-- Evaluating the original constant support matrix preserves the genuine complete phase formula. -/
theorem generatedSixth_packed_phase_formula (n : Fin 4096) :
    generatedSixthPartialPhaseInteger 8 n = generatedSixthPackedPhaseFormula n := by
  unfold generatedSixthPartialPhaseInteger generatedSixthPackedPhaseFormula
  have hz : golayLabelCoefficients (generatedSixthPartialAnchor 8) = 0 := by decide +kernel
  rw [hz, add_zero, generatedSixth_packed_support_matrix]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
