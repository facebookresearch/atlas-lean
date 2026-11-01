/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTensorFactorPairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance

/-! # Whole pairings of rational coordinate packets

The Griess form of two vectors with complete rational coordinate packets is an exact rational
sum over the matrix, short and tensor blocks (the tensor coordinates are scaled by `√2`, so
their products are halved).  Composed with the rational triality formulas this gives the exact
pairing of a forward or inverse triality image with a second vector.  These are the identities
behind the Cauchy-Schwarz criterion `pairing = 128` of the cheap identification method. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open scoped BigOperators

/-- The exact rational pairing of two complete rational packets. -/
def packetPairQ (a b : GeneratedAxisGlobalRationalPacket) : ℚ :=
  (∑ i : Fin 24, ∑ j : Fin 24, a.1 i j * b.1 i j) + (∑ r, a.2.1 r * b.2.1 r) +
    (∑ k : Fin 4096, ∑ j : Fin 24,
      a.2.2 (golayLabelCoefficients k) j * b.2.2 (golayLabelCoefficients k) j) / 2

/-- The Griess form of two vectors with rational packets is their rational packet pairing. -/
theorem packetPairQ_actual (x y : GriessSpace) (a b : GeneratedAxisGlobalRationalPacket)
    (hx : griessConwayEncode x = generatedAxisGlobalRationalPacketReal a)
    (hy : griessConwayEncode y = generatedAxisGlobalRationalPacketReal b) :
    griessForm x y = (packetPairQ a b : ℝ) := by
  rw [griessForm_eq_conwayRawForm, hx, hy, conwayRawForm, conwayMatrixForm_eq_sum]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ht : conwayTensorForm (generatedAxisGlobalRationalPacketReal a).2.2
      (generatedAxisGlobalRationalPacketReal b).2.2 =
      ((∑ k : Fin 4096, ∑ j : Fin 24,
        a.2.2 (golayLabelCoefficients k) j * b.2.2 (golayLabelCoefficients k) j : ℚ) : ℝ) / 2 := by
    change (∑ t : SpinIndex, ∑ j : Fin 24,
      (generatedAxisGlobalRationalPacketReal a).2.2 t j *
        (generatedAxisGlobalRationalPacketReal b).2.2 t j) = _
    rw [generatedAxisGlobal_spin_sum_labels]
    simp only [generatedAxisGlobalRationalPacketReal, Rat.cast_sum, Rat.cast_mul]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
    rw [hs]
    ring
  rw [ht]
  simp only [generatedAxisGlobalRationalPacketReal, Matrix.map_apply, packetPairQ,
    Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat]
  rfl

/-- The pairing of a forward triality image with a second vector, from rational packets. -/
theorem packetPairQ_triality (x y : GriessSpace) (a b : GeneratedAxisGlobalRationalPacket)
    (hx : griessConwayEncode x = generatedAxisGlobalRationalPacketReal a)
    (hy : griessConwayEncode y = generatedAxisGlobalRationalPacketReal b) :
    griessForm (sExtra x) y = (packetPairQ (generatedAxisGlobalRationalTriality a) b : ℝ) :=
  packetPairQ_actual _ _ _ _ (generatedAxisGlobalRationalTriality_of_actual x a hx) hy

/-- The pairing of an inverse triality image with a second vector, from rational packets. -/
theorem packetPairQ_inverse (x y : GriessSpace) (a b : GeneratedAxisGlobalRationalPacket)
    (hx : griessConwayEncode x = generatedAxisGlobalRationalPacketReal a)
    (hy : griessConwayEncode y = generatedAxisGlobalRationalPacketReal b) :
    griessForm (sExtra.symm x) y = (packetPairQ (generatedAxisGlobalRationalInverse a) b : ℝ) :=
  packetPairQ_actual _ _ _ _ (generatedAxisGlobalRationalInverse_actual x a hx) hy

/-- Equal norms `128` and pairing `128` force equality (positive definiteness). -/
theorem eq_of_pairing_128 (x y : GriessSpace) (hx : griessForm x x = 128)
    (hy : griessForm y y = 128) (hp : griessForm x y = 128) : x = y := by
  apply sub_eq_zero.mp
  apply (griessForm_self_eq_zero_iff _).mp
  have hsymm : griessForm y x = griessForm x y := by
    rw [griessForm_apply, griessForm_apply]
    unfold griessFormFun
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [map_sub, LinearMap.sub_apply]
  rw [hx, hy, hp, hsymm, hp]
  ring

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
