/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The original source multiplication determines its binary square polar identity. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoBilinear
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoSquareInvariant

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped commutatorElement
set_option backward.isDefEq.respectTransparency false

/-- Centrality gives the exact original source square-product identity. -/
theorem co1Universal_mul_square
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (x y : Co1UniversalPresentation) :
    (x * y) ^ 2 = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := by
  have hz := co1Universal_commutator_le_center_of_card_le_two hfinite hcard
    (co1UniversalCommutator y x).property
  have hc := Subgroup.mem_center_iff.mp hz x
  change x * ⁅y, x⁆ = ⁅y, x⁆ * x at hc
  have he : y * x = ⁅y, x⁆ * x * y := by
    simp [commutatorElement_def, mul_assoc]
  calc
    (x * y) ^ 2 = x * (y * x) * y := by simp only [pow_two, mul_assoc]
    _ = x * (⁅y, x⁆ * x * y) * y := by rw [he]
    _ = ((x * ⁅y, x⁆) * x) * y * y := by simp only [mul_assoc]
    _ = ((⁅y, x⁆ * x) * x) * y * y := by rw [hc]
    _ = ⁅y, x⁆ * (x ^ 2 * y ^ 2) := by simp only [pow_two, mul_assoc]

/-- The binary square coefficient has the actual source commutator as its polar companion. -/
theorem co1UniversalSquareCoefficient_add
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (v w : Fin 24 → ZMod 2) :
    co1UniversalSquareCoefficient (v + w) =
      co1UniversalSquareCoefficient v + co1UniversalSquareCoefficient w +
        co1UniversalCommutatorPairing w v := by
  have hvw : (co1UniversalIntoBinary
      (co1UniversalBinaryLift v * co1UniversalBinaryLift w)).toAdd = v + w := by
    rw [map_mul, co1UniversalBinaryLift_image, co1UniversalBinaryLift_image]
    rfl
  have hs := co1UniversalBinarySquare_image hfinite hcard
    (co1UniversalBinaryLift v * co1UniversalBinaryLift w)
  rw [hvw] at hs
  have he : co1UniversalBinarySquare (v + w) =
      co1UniversalCommutator (co1UniversalBinaryLift w) (co1UniversalBinaryLift v) *
        co1UniversalBinarySquare v * co1UniversalBinarySquare w := by
    apply Subtype.ext
    change (co1UniversalBinarySquare (v + w)).val =
      ⁅co1UniversalBinaryLift w, co1UniversalBinaryLift v⁆ *
        (co1UniversalBinaryLift v ^ 2) * (co1UniversalBinaryLift w ^ 2)
    rw [hs]
    simpa only [mul_assoc] using co1Universal_mul_square hfinite hcard
      (co1UniversalBinaryLift v) (co1UniversalBinaryLift w)
  change co1UniversalCommutatorCoefficient (co1UniversalBinarySquare (v + w)) = _
  rw [he, co1UniversalCommutatorCoefficient_mul hfinite hcard,
    co1UniversalCommutatorCoefficient_mul hfinite hcard]
  change co1UniversalCommutatorPairing w v + co1UniversalSquareCoefficient v +
      co1UniversalSquareCoefficient w = co1UniversalSquareCoefficient v +
        co1UniversalSquareCoefficient w + co1UniversalCommutatorPairing w v
  ac_rfl

/-- The actual-coordinate source square coefficient vanishes at zero. -/
theorem co1UniversalSquareCoefficient_zero
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2) :
    co1UniversalSquareCoefficient 0 = 0 := by
  simpa only [zero_add, co1UniversalCommutatorPairing_zero_left hfinite hcard,
    add_zero, ZModModule.add_self] using co1UniversalSquareCoefficient_add hfinite hcard 0 0

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
