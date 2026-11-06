/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceFiber
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsIntegerPrimitives
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMonomialInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationLocalTensorFaithfulness

/-! Exact whole tensor packets for the ten phase-preserving odd-family source letters. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem oddInteger_inverse_of_cube {A : Type*} [Group A] (a : A) (ha : a ^ 3 = 1) :
    a⁻¹ = a * a := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using ha

private theorem oddInteger_sign_square (a : Fin 4096)
    (hp : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) :
    generatedFifthSignLocal a 0 ^ 2 = 1 := by
  have hx : sourceGeneratedCode a 0 * sourceGeneratedCode a 0 = 1 := by
    rw [← pow_two, sourceGeneratedCode_square, hp]
    change qIntoGenerated 1 = 1
    exact map_one _
  apply localIntoGenerated_injective
  rw [map_pow, map_one, generatedFifth_sign_local_generated]
  change (extraIntoGenerated⁻¹ * sourceGeneratedCode a 0 * extraIntoGenerated) ^ 2 = 1
  calc
    _ = extraIntoGenerated⁻¹ *
        (sourceGeneratedCode a 0 * sourceGeneratedCode a 0) * extraIntoGenerated := by
          rw [pow_two]
          group
    _ = 1 := by rw [hx]; group

private theorem oddInteger_sign_tensor_inverse (a : Fin 4096)
    (hp : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) :
    (localTensorRepresentation (generatedFifthSignFiber a 0))⁻¹ =
      localTensorRepresentation (generatedFifthSignFiber a 0) := by
  have hi : (generatedFifthSignLocal a 0)⁻¹ = generatedFifthSignLocal a 0 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact oddInteger_sign_square a hp)
  change (monsterLocalTensorRepresentation
      (localFiberIntoH (generatedFifthSignFiber a 0)))⁻¹ =
    monsterLocalTensorRepresentation (localFiberIntoH (generatedFifthSignFiber a 0))
  rw [generatedFifth_sign_fiber_local, ← map_inv, hi]

/-- Exact integer numerators for each signed original source letter. -/
def generatedAxisGlobalOddIntegerLetter (l : Fin 10)
    (N : Fin 4096 → Fin 24 → ℤ) : Fin 4096 → Fin 24 → ℤ :=
  ![generatedAxisGlobalXiIntegerAction N,
    generatedAxisGlobalXiIntegerAction (generatedAxisGlobalXiIntegerAction N),
    generatedAxisGlobalSignIntegerAction N 16 0, generatedAxisGlobalSignIntegerAction N 16 0,
    generatedAxisGlobalSignIntegerAction N 32 0, generatedAxisGlobalSignIntegerAction N 32 0,
    generatedAxisGlobalMonomialIntegerAction [(0, false)] N,
    generatedAxisGlobalMonomialIntegerAction [(0, true)] N,
    generatedAxisGlobalMonomialIntegerAction [(1, false)] N,
    generatedAxisGlobalMonomialIntegerAction [(1, true)] N] l

/-- Actual dyadic denominator factors of the ten complete source tensor actions. -/
def generatedAxisGlobalOddIntegerLetterFactor : Fin 10 → ℕ :=
  ![16, 256, 2, 2, 2, 2, 1, 1, 1, 1]

/-- Every integer packet is the whole genuine tensor action of its signed source fiber. -/
theorem generatedAxisGlobalOddIntegerLetter_packet (l : Fin 10)
    (N : Fin 4096 → Fin 24 → ℤ) (D : ℕ) :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter l)
        (generatedAxisGlobalTensorIntegerPacket N D) =
      generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddIntegerLetter l N)
        (generatedAxisGlobalOddIntegerLetterFactor l * D) := by
  fin_cases l
  · exact generatedAxisGlobalXiInteger_packet N D
  · have hi := oddInteger_inverse_of_cube xiSpinLocalFiber xiSpinLocalFiber_cube
    change localTensorRepresentation xiSpinLocalFiber⁻¹ _ = _
    rw [hi, map_mul, LinearEquiv.mul_apply, generatedAxisGlobalXiInteger_packet,
      generatedAxisGlobalXiInteger_packet]
    congr 1
    change 16 * (16 * D) = 256 * D
    omega
  · exact generatedAxisGlobalSignInteger_packet N D 16 0
  · change localTensorRepresentation (generatedFifthSignFiber 16 0)⁻¹ _ = _
    rw [map_inv, oddInteger_sign_tensor_inverse 16 (by decide +kernel)]
    exact generatedAxisGlobalSignInteger_packet N D 16 0
  · exact generatedAxisGlobalSignInteger_packet N D 32 0
  · change localTensorRepresentation (generatedFifthSignFiber 32 0)⁻¹ _ = _
    rw [map_inv, oddInteger_sign_tensor_inverse 32 (by decide +kernel)]
    exact generatedAxisGlobalSignInteger_packet N D 32 0
  · change localTensorRepresentation (generatedFourthMonomialFiberLetter (0, false))
      (generatedAxisGlobalTensorIntegerPacket N D) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalMonomialIntegerAction [(0, false)] N) (1 * D)
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      one_mul] using generatedAxisGlobalMonomialInteger_packet [(0, false)] N D
  · change localTensorRepresentation (generatedFourthMonomialFiberLetter (0, true))
      (generatedAxisGlobalTensorIntegerPacket N D) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalMonomialIntegerAction [(0, true)] N) (1 * D)
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      one_mul] using generatedAxisGlobalMonomialInteger_packet [(0, true)] N D
  · change localTensorRepresentation (generatedFourthMonomialFiberLetter (1, false))
      (generatedAxisGlobalTensorIntegerPacket N D) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalMonomialIntegerAction [(1, false)] N) (1 * D)
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      one_mul] using generatedAxisGlobalMonomialInteger_packet [(1, false)] N D
  · change localTensorRepresentation (generatedFourthMonomialFiberLetter (1, true))
      (generatedAxisGlobalTensorIntegerPacket N D) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalMonomialIntegerAction [(1, true)] N) (1 * D)
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      one_mul] using generatedAxisGlobalMonomialInteger_packet [(1, true)] N D

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
