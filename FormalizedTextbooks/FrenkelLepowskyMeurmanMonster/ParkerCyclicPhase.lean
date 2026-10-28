/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SourceCodeAddition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechQuadratic
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadProductPhase
/-! Concrete Parker weight, polarization, and cyclic phase identities.

The theta self-character is the code's quarter-weight parity. This follows
from the actual integral code representative and the Leech half-norm
comparison. The actual integer XOR carry then gives even intersections
and the quarter-weight addition law. Theta polarization and the cyclic
phase identity follow algebraically, for every source code label.
No enumeration of all pairs of code words or compatibility hypothesis is
used. Source: Seysen, arXiv:2002.10921v3, §3.1 and Theorem 6.1. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
-- The source hyperbolic coordinates use the matrix abbreviation.
set_option backward.isDefEq.respectTransparency false

lemma sourceWordTheta_polynomial (d : Fin 4096) :
    sourceWordTheta d = sourceCodeThetaPolynomial (golayLabelCoefficients d) := by
  ext k
  exact sourceCodeThetaPolynomial_mask d k

lemma sourceCodeWord_squareSum (d : Fin 4096) :
    leechSquareSum (leechSourceCodeWordVector d) =
      if golayMaskWeight (golayEncodedMask d.val) % 8 = 0 then
        4 * (golayMaskWeight (golayEncodedMask d.val) : ℤ) else
        4 * (24 - (golayMaskWeight (golayEncodedMask d.val) : ℤ)) := by
  have hs : (∑ i, sourceCodeInteger d i) =
      (golayMaskWeight (golayEncodedMask d.val) : ℤ) := by
    simp only [sourceCodeInteger, golayMaskWeight, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> norm_num
  have ht (i : Fin 24) : leechSourceCodeWordVector d i ^ 2 =
      if golayMaskWeight (golayEncodedMask d.val) % 8 = 0 then
        4 * sourceCodeInteger d i else 4 * (1 - sourceCodeInteger d i) := by
    unfold leechSourceCodeWordVector sourceCodeInteger
    split_ifs <;> norm_num
  unfold leechSquareSum
  simp_rw [ht]
  split_ifs with h
  · simp only [← Finset.mul_sum, hs]
  · simp only [← Finset.mul_sum, Finset.sum_sub_distrib, hs, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    norm_num only [Nat.cast_ofNat]

/-- The actual theta self-character is precisely quarter-weight parity. -/
lemma sourceWordTheta_self_dot (d : Fin 4096) :
    spinDot (sourceWordTheta d) (golayLabelCoefficients d) =
      (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) := by
  have h := leechHyperbolicCoordinates_halfNorm (leechSourceCodeWordLift d)
  rw [leechSourceCodeWordLift_vector, sourceCodeWord_squareSum,
    leechSourceCodeWordLift_hyperbolic] at h
  have hq : squareQuad (Fin.append (golayLabelCoefficients d) (sourceWordTheta d)) =
      spinDot (sourceWordTheta d) (golayLabelCoefficients d) := by
    change (∑ k, golayLabelCoefficients d k * sourceWordTheta d k) =
      ∑ k, sourceWordTheta d k * golayLabelCoefficients d k
    apply Finset.sum_congr rfl
    intro k _
    ring
  change (((if golayMaskWeight (golayEncodedMask d.val) % 8 = 0 then
    4 * (golayMaskWeight (golayEncodedMask d.val) : ℤ) else
    4 * (24 - (golayMaskWeight (golayEncodedMask d.val) : ℤ))) / 16 : ℤ) : ZMod 2) =
      squareQuad (Fin.append (golayLabelCoefficients d) (sourceWordTheta d)) at h
  rw [hq] at h
  rw [← h]
  have hw := golayEncodedMask_weights d
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with hw | hw | hw | hw | hw <;> rw [hw] <;> norm_num

lemma sourceCodeThetaPolynomial_self_dot (d : Fin 4096) :
    spinDot (sourceCodeThetaPolynomial (golayLabelCoefficients d))
      (golayLabelCoefficients d) = (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) := by
  rw [← sourceWordTheta_polynomial]
  exact sourceWordTheta_self_dot d

lemma sourceCodeInteger_cast_encoder (d : Fin 4096) (i : Fin 24) :
    (sourceCodeInteger d i : ZMod 2) = golayEncoder (golayLabelCoefficients d) i := by
  apply ZMod.val_injective
  have h := golayLabelEncoder_match d i
  cases hb : (golayEncodedMask d.val).testBit i.val <;>
    simpa [sourceCodeInteger, hb, show (1 : ZMod 2).val = 1 by decide] using h.symm

lemma sourceCodeIntersection_parity (d e : Fin 4096) :
    integerParity (sourceCodeIntersection d e) =
      fun i => golayEncoder (golayLabelCoefficients d) i *
        golayEncoder (golayLabelCoefficients e) i := by
  ext i
  change ((sourceCodeInteger d i * sourceCodeInteger e i : ℤ) : ZMod 2) = _
  rw [Int.cast_mul, sourceCodeInteger_cast_encoder, sourceCodeInteger_cast_encoder]

lemma sourceCodeIntersection_even (d e f : Fin 4096)
    (hf : golayLabelCoefficients f = golayLabelCoefficients d + golayLabelCoefficients e) :
    (∑ i, (integerParity (sourceCodeIntersection d e)) i) = 0 := by
  change (∑ i, (sourceCodeIntersection d e i : ZMod 2)) = 0
  have h := congrArg (fun n : ℤ => (n : ZMod 2)) (sourceCodeIntersection_sum d e f hf)
  simpa only [Int.cast_sum, Int.cast_mul, Int.cast_ofNat,
    show (2 : ZMod 2) = 0 by decide, zero_mul] using h

lemma sourceCodeIntersection_half_parity (d e f : Fin 4096)
    (hf : golayLabelCoefficients f = golayLabelCoefficients d + golayLabelCoefficients e) :
    (((∑ i, sourceCodeIntersection d e i) / 2 : ℤ) : ZMod 2) =
      (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) +
      (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) -
      (golayMaskWeight (golayEncodedMask f.val) / 4 : ℕ) := by
  rw [sourceCodeIntersection_sum d e f hf,
    Int.mul_ediv_cancel_left _ (by decide)]
  push_cast
  rfl

lemma sourceWordTheta_add_intersection (d e f : Fin 4096)
    (hf : golayLabelCoefficients f = golayLabelCoefficients d + golayLabelCoefficients e) :
    sourceWordTheta f = sourceWordTheta d + sourceWordTheta e +
      golaySyndrome (integerParity (sourceCodeIntersection d e)) := by
  rw [sourceWordTheta_polynomial, hf, sourceCodeThetaPolynomial_add,
    ← sourceWordTheta_polynomial, ← sourceWordTheta_polynomial, sourceCodeIntersection_parity]

private lemma binary_intersection_self (a b : ZMod 2) : a * b * a = a * b := by
  fin_cases a <;> fin_cases b <;> decide

private lemma binary_intersection_sum (a b : ZMod 2) : a * b * (a + b) = 0 := by
  fin_cases a <;> fin_cases b <;> decide

lemma sourceCodeIntersection_dot_sum (d e : Fin 4096) :
    spinDot (golaySyndrome (integerParity (sourceCodeIntersection d e)))
      (golayLabelCoefficients d + golayLabelCoefficients e) = 0 := by
  rw [golaySyndrome_spinDot, sourceCodeIntersection_parity, map_add]
  simp only [Pi.add_apply, binary_intersection_sum, Finset.sum_const_zero]

lemma sourceCodeIntersection_dot_left (d e f : Fin 4096)
    (hf : golayLabelCoefficients f = golayLabelCoefficients d + golayLabelCoefficients e) :
    spinDot (golaySyndrome (integerParity (sourceCodeIntersection d e)))
      (golayLabelCoefficients d) = 0 := by
  rw [golaySyndrome_spinDot, sourceCodeIntersection_parity]
  simp only [binary_intersection_self]
  have h := sourceCodeIntersection_even d e f hf
  rw [sourceCodeIntersection_parity] at h
  exact h

lemma sourceWordTheta_cross_dot (d e f : Fin 4096)
    (hf : golayLabelCoefficients f = golayLabelCoefficients d + golayLabelCoefficients e) :
    spinDot (sourceWordTheta d) (golayLabelCoefficients e) +
      spinDot (sourceWordTheta e) (golayLabelCoefficients d) =
      (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) +
      (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) -
      (golayMaskWeight (golayEncodedMask f.val) / 4 : ℕ) := by
  have h := sourceWordTheta_self_dot f
  rw [hf, sourceWordTheta_add_intersection d e f hf, spinDot_add_left, spinDot_add_left,
    sourceCodeIntersection_dot_sum, add_zero, spinDot_add_right, spinDot_add_right,
    sourceWordTheta_self_dot, sourceWordTheta_self_dot] at h
  linear_combination (norm := skip) h
  ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, sub_zero]

/-- The symmetric theta character equals half the physical intersection parity. -/
lemma sourceWordTheta_cross_intersection (d e f : Fin 4096)
    (hf : golayLabelCoefficients f = golayLabelCoefficients d + golayLabelCoefficients e) :
    spinDot (sourceWordTheta d) (golayLabelCoefficients e) +
      spinDot (sourceWordTheta e) (golayLabelCoefficients d) =
      (((∑ i, sourceCodeIntersection d e i) / 2 : ℤ) : ZMod 2) := by
  rw [sourceWordTheta_cross_dot d e f hf, sourceCodeIntersection_half_parity d e f hf]

lemma sourceWordTheta_sum_dot_left (d e f : Fin 4096)
    (hf : golayLabelCoefficients f = golayLabelCoefficients d + golayLabelCoefficients e) :
    spinDot (sourceWordTheta f) (golayLabelCoefficients d) =
      (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) +
      spinDot (sourceWordTheta e) (golayLabelCoefficients d) := by
  rw [sourceWordTheta_add_intersection d e f hf, spinDot_add_left, spinDot_add_left,
    sourceCodeIntersection_dot_left d e f hf, add_zero, sourceWordTheta_self_dot]

/-- The actual weight and theta phases agree after cycling the code sum. -/
theorem parkerCyclicPhase (d e f : Fin 4096)
    (hf : golayLabelCoefficients f = golayLabelCoefficients d + golayLabelCoefficients e) :
    qSign (golayMaskWeight (golayEncodedMask f.val) / 4 : ℕ) *
      qSign (spinDot (sourceWordTheta d) (golayLabelCoefficients e)) =
    qSign (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) *
      qSign (spinDot (sourceWordTheta f) (golayLabelCoefficients d)) := by
  rw [← qSign_add, ← qSign_add]
  apply congrArg qSign
  have hc := sourceWordTheta_cross_dot d e f hf
  have hs := sourceWordTheta_sum_dot_left d e f hf
  linear_combination (norm := skip) hc - hs
  ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, neg_zero]

theorem parkerThetaPolynomial_cyclicPhase (d e f : Fin 4096)
    (hf : golayLabelCoefficients f = golayLabelCoefficients d + golayLabelCoefficients e) :
    qSign (golayMaskWeight (golayEncodedMask f.val) / 4 : ℕ) *
      qSign (spinDot (sourceCodeThetaPolynomial (golayLabelCoefficients d))
        (golayLabelCoefficients e)) =
    qSign (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) *
      qSign (spinDot (sourceCodeThetaPolynomial (golayLabelCoefficients f))
        (golayLabelCoefficients d)) := by
  rw [← sourceWordTheta_polynomial, ← sourceWordTheta_polynomial]
  exact parkerCyclicPhase d e f hf
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
