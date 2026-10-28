/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTensorRationalPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTensorFactorPairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSparsePairingCoordinates

/-! Exact full pairings from rational physical coordinates and complete sparse source packets. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The complete tensor pairing omits only terms whose original target factor is exactly zero. -/
def generatedAxisGlobalRationalTensorSparsePairing
    (T : SpinIndex → Fin 24 → ℚ) (U : Fin 4096 → ℤ)
    (V : Fin 24 → ℤ) (E : ℕ) : ℚ :=
  ∑ k : Fin 4096, if U k = 0 then 0 else
    ∑ j : Fin 24, if V j = 0 then 0 else
      T (golayLabelCoefficients k) j * (U k : ℚ) * (V j : ℚ) / (2 * (E : ℚ))

/-- The sparse finite rational sum is the entire genuine real tensor pairing. -/
theorem generatedAxisGlobalRationalTensorSparsePairing_actual
    (T : SpinIndex → Fin 24 → ℚ) (U : Fin 4096 → ℤ)
    (V : Fin 24 → ℤ) (E : ℕ) (hE : 0 < E) :
    conwayTensorForm (fun t j => (T t j : ℝ) / Real.sqrt 2)
      (generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddTensorFactor U V) E) =
        (generatedAxisGlobalRationalTensorSparsePairing T U V E : ℝ) := by
  have he : (E : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hE
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  change (∑ t : SpinIndex, ∑ j : Fin 24,
    ((T t j : ℝ) / Real.sqrt 2) *
      generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddTensorFactor U V) E t j) = _
  rw [generatedAxisGlobal_spin_sum_labels]
  simp only [generatedAxisGlobalRationalTensorSparsePairing, Rat.cast_sum, apply_ite,
    Rat.cast_zero, generatedAxisGlobalTensorIntegerPacket_coefficient,
    generatedAxisGlobalOddTensorFactor, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : U k = 0
  · simp [hk]
  · simp only [hk, ite_false]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : V j = 0
    · simp [hj]
    · simp only [hj, ite_false, Rat.cast_div, Rat.cast_mul, Rat.cast_intCast,
        Rat.cast_natCast, Rat.cast_ofNat]
      field_simp
      rw [show Real.sqrt 2 ^ 2 = (2 : ℝ) from Real.sq_sqrt (by norm_num)]

/-- The full rational pairing includes all matrix entries, the complete short packet and all tensor terms. -/
def generatedAxisGlobalRationalSparsePairing {ι : Type*} [Fintype ι]
    (a : GeneratedAxisGlobalRationalPacket) (B : Matrix (Fin 24) (Fin 24) ℚ)
    (c : ι → ℚ) (f : ι → GriessShortIndex)
    (U : Fin 4096 → ℤ) (V : Fin 24 → ℤ) (E : ℕ) : ℚ :=
  (∑ i : Fin 24, ∑ j : Fin 24, a.1 i j * B i j) +
    (∑ p : ι, c p * a.2.1 (f p)) +
    generatedAxisGlobalRationalTensorSparsePairing a.2.2 U V E

/-- Checked complete source coordinates and target packets give the genuine full Griess pairing. -/
theorem generatedAxisGlobalRationalSparsePairing_actual {ι : Type*} [Fintype ι]
    (x y : GriessSpace) (a : GeneratedAxisGlobalRationalPacket)
    (B : Matrix (Fin 24) (Fin 24) ℚ) (c : ι → ℚ) (f : ι → GriessShortIndex)
    (U : Fin 4096 → ℤ) (V : Fin 24 → ℤ) (E : ℕ) (hE : 0 < E)
    (hx : griessConwayEncode x = generatedAxisGlobalRationalPacketReal a)
    (hB : (griessConwayEncode y).1 = B.map (Rat.castHom ℝ))
    (hC : (griessConwayEncode y).2.1 = ∑ p, (c p : ℝ) • Pi.single (f p) (1 : ℝ))
    (hT : (griessConwayEncode y).2.2 =
      generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddTensorFactor U V) E) :
    griessForm x y = (generatedAxisGlobalRationalSparsePairing a B c f U V E : ℝ) := by
  rw [generatedAxisGlobal_griessForm_sparse_coordinates x y _ _ hC, hx, hB, hT]
  simp only [generatedAxisGlobalRationalPacketReal]
  rw [generatedAxisGlobalRationalTensorSparsePairing_actual _ _ _ _ hE]
  simp only [generatedAxisGlobalRationalSparsePairing,
    Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Matrix.map_apply]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
