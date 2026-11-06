/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsIntegerPrimitives
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRational
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot00Packet
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot01Packet
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot02Packet
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot03Packet
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot04Packet
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot05Packet
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot06Packet
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot07Packet
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRoot08Packet

/-! Complete original real short coordinates from the checked finite rational source packets. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- A finite rational preferred-basis packet has these exact real coordinates. -/
theorem generatedAxisGlobal_rational_short_packet_apply
    {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (c : ι → ℚ) (f : ι → κ) (r : κ) :
    ((∑ j, (c j : ℝ) • Pi.single (f j) (1 : ℝ)) r) =
      ((∑ j, c j * (if f j = r then 1 else 0) : ℚ) : ℝ) := by
  simp [Finset.sum_apply, Pi.single_apply, eq_comm, apply_ite]

/-- The complete original rational short coefficient, retaining every actual source phase. -/
def generatedAxisGlobalOddRootShortQ (k : Fin 9) (r : GriessShortIndex) : ℚ :=
  ∑ p : GeneratedAxisGlobalOddShortPacketIndex,
    generatedAxisGlobalOddShortCoefficientQ p *
      (generatedAxisGlobalIntSign (generatedAxisGlobalOddShortRootPhases k
        (generatedAxisGlobalOddShortPacketNumber p)) : ℚ) *
      (if generatedAxisGlobalOddShortRootLabels k
        (generatedAxisGlobalOddShortPacketNumber p) = r then 1 else 0)

private theorem root_short_packet (k : Fin 9) :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord k) generatedOddAxis)).2.1 =
      ∑ p : GeneratedAxisGlobalOddShortPacketIndex,
        (generatedAxisGlobalOddShortPacketCoefficient p *
          qSign (generatedAxisGlobalOddShortRootPhases k
            (generatedAxisGlobalOddShortPacketNumber p))) •
          Pi.single (generatedAxisGlobalOddShortRootLabels k
            (generatedAxisGlobalOddShortPacketNumber p)) (1 : ℝ) := by
  fin_cases k
  · exact generatedAxisGlobalOddShortRoot00_actual
  · exact generatedAxisGlobalOddShortRoot01_actual
  · exact generatedAxisGlobalOddShortRoot02_actual
  · exact generatedAxisGlobalOddShortRoot03_actual
  · exact generatedAxisGlobalOddShortRoot04_actual
  · exact generatedAxisGlobalOddShortRoot05_actual
  · exact generatedAxisGlobalOddShortRoot06_actual
  · exact generatedAxisGlobalOddShortRoot07_actual
  · exact generatedAxisGlobalOddShortRoot08_actual

/-- Every actual original source root short coordinate equals its complete rational packet. -/
theorem generatedAxisGlobalOddRootShortQ_actual (k : Fin 9) (r : GriessShortIndex) :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord k) generatedOddAxis)).2.1 r =
      (generatedAxisGlobalOddRootShortQ k r : ℝ) := by
  rw [root_short_packet]
  unfold generatedAxisGlobalOddRootShortQ
  simp only [Rat.cast_sum, Rat.cast_mul, apply_ite, Rat.cast_one, Rat.cast_zero,
    Rat.cast_intCast, generatedAxisGlobalIntSign_real,
    generatedAxisGlobalOddShortCoefficientQ_actual, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p _
  simp [Pi.single_apply, eq_comm]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
