/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRawPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortRationalPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTriality

/-! All exact original coordinates of the genuine canonical Fifth axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The entire preferred short-coordinate sum has the original rational coefficients. -/
def generatedAxisGlobalCanonicalFifthShortQ (r : GriessShortIndex) : ℚ :=
  ∑ p : GeneratedAxisGlobalFifthShortPacketIndex,
    if generatedAxisGlobalFifthShortPacketLabel p = r then
      generatedAxisGlobalFifthShortRationalCoefficient p else 0

/-- The original matrix, all preferred short coordinates, and every scaled physical tensor coordinate. -/
def generatedAxisGlobalCanonicalFifthRationalPacket : GeneratedAxisGlobalRationalPacket :=
  (Matrix.diagonal (fun i : Fin 24 => if Nat.testBit 0x0f000f i.val then
      (1 / 2 : ℚ) else 1 / 4),
    (generatedAxisGlobalCanonicalFifthShortQ,
      fun t i => (generatedAxisGlobalFifthTensorInteger (generatedAxisGlobalSpinLabel t) i : ℚ)))

/-- Every short coefficient is the complete actual canonical source coefficient. -/
theorem generatedAxisGlobalCanonicalFifthShortQ_actual (r : GriessShortIndex) :
    (generatedAxisGlobalCanonicalFifthShortQ r : ℝ) =
      (griessConwayEncode generatedFifthAxis).2.1 r := by
  rw [generatedAxisGlobalFifthShortRationalPacket_actual]
  simp only [generatedAxisGlobalCanonicalFifthShortQ, Rat.cast_sum, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : generatedAxisGlobalFifthShortPacketLabel p = r
  · simp [h]
  · simp [h, Ne.symm h]

/-- This complete rational packet equals the genuine original Fifth axis at all coordinates. -/
theorem generatedAxisGlobalCanonicalFifthRationalPacket_actual :
    griessConwayEncode generatedFifthAxis =
      generatedAxisGlobalRationalPacketReal generatedAxisGlobalCanonicalFifthRationalPacket := by
  apply Prod.ext
  · rw [generatedFifth_matrix]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : Nat.testBit 0x0f000f i.val = true <;>
        simp [generatedAxisGlobalRationalPacketReal,
          generatedAxisGlobalCanonicalFifthRationalPacket, hi]
    · simp [generatedAxisGlobalRationalPacketReal,
        generatedAxisGlobalCanonicalFifthRationalPacket, hij]
  · apply Prod.ext
    · funext r
      change (griessConwayEncode generatedFifthAxis).2.1 r =
        (generatedAxisGlobalCanonicalFifthShortQ r : ℝ)
      exact (generatedAxisGlobalCanonicalFifthShortQ_actual r).symm
    · rw [generatedAxisGlobalFifthTensorInteger_eq]
      funext t i
      simp only [generatedAxisGlobalRationalPacketReal,
        generatedAxisGlobalCanonicalFifthRationalPacket, Rat.cast_intCast]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
