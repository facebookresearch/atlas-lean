/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmeticPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmeticPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmeticPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmeticPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmeticPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmeticPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmeticPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmeticPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmeticPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmeticPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmeticPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmeticPacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmeticPacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmeticPacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmeticPacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnArithmeticPacket15

/-! The complete final-column cache has the exact original XYZ source arithmetic. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem blocks (k : Fin 16) (m : Fin 256) :
    generatedNinthFinalColumnArithmetic ⟨256 * k.val + m.val, by omega⟩ =
      generatedNinthFinalColumnInteger ⟨256 * k.val + m.val, by omega⟩ := by
  fin_cases k
  · exact generatedNinth_final_column_arithmetic_packet_00 m
  · exact generatedNinth_final_column_arithmetic_packet_01 m
  · exact generatedNinth_final_column_arithmetic_packet_02 m
  · exact generatedNinth_final_column_arithmetic_packet_03 m
  · exact generatedNinth_final_column_arithmetic_packet_04 m
  · exact generatedNinth_final_column_arithmetic_packet_05 m
  · exact generatedNinth_final_column_arithmetic_packet_06 m
  · exact generatedNinth_final_column_arithmetic_packet_07 m
  · exact generatedNinth_final_column_arithmetic_packet_08 m
  · exact generatedNinth_final_column_arithmetic_packet_09 m
  · exact generatedNinth_final_column_arithmetic_packet_10 m
  · exact generatedNinth_final_column_arithmetic_packet_11 m
  · exact generatedNinth_final_column_arithmetic_packet_12 m
  · exact generatedNinth_final_column_arithmetic_packet_13 m
  · exact generatedNinth_final_column_arithmetic_packet_14 m
  · exact generatedNinth_final_column_arithmetic_packet_15 m

/-- Every cached final-column value retains the original odd phase and both source spin rows. -/
theorem generatedNinth_final_column_arithmetic (n : Fin 4096) :
    generatedNinthFinalColumnArithmetic n = generatedNinthFinalColumnInteger n := by
  let k : Fin 16 := ⟨n.val / 256, by omega⟩
  let m : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have hn : (⟨256 * k.val + m.val, by omega⟩ : Fin 4096) = n := by
    apply Fin.ext
    dsimp only [k, m]
    omega
  simpa only [hn] using blocks k m

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
