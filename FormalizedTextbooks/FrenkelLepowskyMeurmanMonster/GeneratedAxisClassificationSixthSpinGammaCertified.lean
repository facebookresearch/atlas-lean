/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinEncoding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaPacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaPacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaPacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaPacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaPacket15

/-! The executable diagonal signs and Gaussian sum are genuine original operators. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem gamma_blocks (k : Fin 16) (m : Fin 256) :
    generatedSixthSpinGammaFast ⟨256 * k.val + m.val, by omega⟩ =
      nortonUIntegerGammaSign (golayLabelCoefficients ⟨256 * k.val + m.val, by omega⟩) := by
  fin_cases k
  · exact generatedSixth_spin_gamma_packet_00 m
  · exact generatedSixth_spin_gamma_packet_01 m
  · exact generatedSixth_spin_gamma_packet_02 m
  · exact generatedSixth_spin_gamma_packet_03 m
  · exact generatedSixth_spin_gamma_packet_04 m
  · exact generatedSixth_spin_gamma_packet_05 m
  · exact generatedSixth_spin_gamma_packet_06 m
  · exact generatedSixth_spin_gamma_packet_07 m
  · exact generatedSixth_spin_gamma_packet_08 m
  · exact generatedSixth_spin_gamma_packet_09 m
  · exact generatedSixth_spin_gamma_packet_10 m
  · exact generatedSixth_spin_gamma_packet_11 m
  · exact generatedSixth_spin_gamma_packet_12 m
  · exact generatedSixth_spin_gamma_packet_13 m
  · exact generatedSixth_spin_gamma_packet_14 m
  · exact generatedSixth_spin_gamma_packet_15 m

/-- Every executable diagonal sign is the exact original Gaussian sign. -/
theorem generatedSixth_spin_gamma_fast (n : Fin 4096) :
    generatedSixthSpinGammaFast n = nortonUIntegerGammaSign (golayLabelCoefficients n) := by
  let k : Fin 16 := ⟨n.val / 256, by omega⟩
  let m : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have hi : (⟨256 * k.val + m.val, by omega⟩ : Fin 4096) = n := by
    apply Fin.ext
    dsimp [k, m]
    omega
  simpa only [hi] using gamma_blocks k m

/-- A finite binary-address numerator with every diagonal sign already certified. -/
def generatedSixthIntegerXiCached (v : NortonUIntegerVector) (n : Fin 4096) : ℤ :=
  ∑ a : Fin 64,
    let m := generatedSixthSpinLabelXor n (generatedSixthGrayCodeLabel a)
    let z := v m
    if z = 0 then 0 else generatedSixthGraySign a * generatedSixthSpinGammaFast m * z

/-- The bounded executable Gaussian is the actual original integer Gaussian. -/
theorem generatedSixth_integer_xi_cached (v : NortonUIntegerVector) :
    nortonUIntegerXi v = generatedSixthIntegerXiCached v := by
  rw [generatedSixth_integer_xi_fast]
  funext n
  unfold generatedSixthIntegerXiFast generatedSixthIntegerXiCached
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  by_cases hz : v (generatedSixthSpinLabelXor n (generatedSixthGrayCodeLabel a)) = 0
  · simp only [hz, ite_true, mul_zero]
  · simp only [hz, ite_false, generatedSixth_spin_gamma_fast]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
