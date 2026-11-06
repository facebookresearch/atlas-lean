/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneralAxialVector

/-! Exact rational coordinates of every original genuine signed-short axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The whole original integral outer square and signed preferred short unit. -/
def generatedAxisGlobalShortAxisRationalPacket (r : GriessShortIndex) (c : ZMod 2) :
    GeneratedAxisGlobalRationalPacket :=
  ((fun i j => (griessShortIntegral r i : ℚ) * (griessShortIntegral r j : ℚ) / 4),
    ((fun s => if r = s then -8 * (generatedAxisGlobalIntSign c : ℚ) else 0), 0))

/-- Every actual original axis coordinate has this complete rational value. -/
theorem generatedAxisGlobalShortAxisRationalPacket_actual (r : GriessShortIndex) (c : ZMod 2) :
    griessConwayEncode (conwayShortAxis r c) =
      generatedAxisGlobalRationalPacketReal (generatedAxisGlobalShortAxisRationalPacket r c) := by
  rw [conwayShortAxis_encode]
  apply Prod.ext
  · funext i j
    have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
    change (2 : ℝ) * (griessShortVector r i * griessShortVector r j) =
      (((griessShortIntegral r i : ℚ) * (griessShortIntegral r j : ℚ) / 4 : ℚ) : ℝ)
    simp only [griessShortVector, div_mul_div_comm, hs,
      Rat.cast_div, Rat.cast_mul, Rat.cast_intCast, Rat.cast_ofNat]
    ring
  · apply Prod.ext
    · funext s
      by_cases h : r = s <;>
        simp [conwayShortAxisRaw, generatedAxisGlobalRationalPacketReal,
          generatedAxisGlobalShortAxisRationalPacket, h, Ne.symm, generatedAxisGlobalIntSign_real]
    · funext t i
      simp [conwayShortAxisRaw, generatedAxisGlobalRationalPacketReal,
        generatedAxisGlobalShortAxisRationalPacket]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
