/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadDiagonalTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortIntegral
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadPhysicalSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadSupportCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadQBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.CentralizerGeometryShortLines

/-! An explicit Leech lattice isometry carrying the matrix of the octad-diagonal transition vector
to the octad-three projection and its 120-coordinate short support onto the octad-three roots. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix

/-- The frame: the second source permutation after inverse Xi and three Golay signs. -/
def generatedAxisGlobalTwelveOctadDiagonalFrameIsometry : leechIsomSubgroup :=
  golayPermutationIsometry (omegaOrbitGolayPermutation 1) * co1XiIsometry⁻¹ *
    monsterCo1GeometrySignIsometry 9 * monsterCo1GeometrySignIsometry 7 *
      monsterCo1GeometrySignIsometry 5

/-- The explicit rational matrix formula of the frame. -/
def generatedAxisGlobalTwelveOctadDiagonalFrameFormulaQ (i j : Fin 24) : ℚ :=
  (generatedAxisGlobalIntSign (golayGeneratorBit 9 j : ZMod 2) : ℚ) *
    (generatedAxisGlobalIntSign (golayGeneratorBit 7 j : ZMod 2) : ℚ) *
      (generatedAxisGlobalIntSign (golayGeneratorBit 5 j : ZMod 2) : ℚ) *
        (co1XiNumerator j (omegaOrbitPermInverse 1 i) : ℚ) / 2

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
/-- The formula agrees with the displayed frame matrix. -/
theorem generatedAxisGlobalTwelveOctadDiagonalFrameFormula_certificate : ∀ i j : Fin 24,
    generatedAxisGlobalTwelveOctadDiagonalFrameFormulaQ i j = generatedAxisGlobalTwelveOctadDiagonalFrameQ i j := by
  decide +kernel

private theorem sign_code_apply (k : Fin 12) (j : Fin 24) :
    golayEncoder (Pi.single k 1) j = (golayGeneratorBit k j : ZMod 2) := by
  change (∑ l, (Pi.single k (1 : ZMod 2) : Fin 12 → ZMod 2) l *
    (golayGeneratorBit l j : ZMod 2)) = _
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- Every frame matrix entry is the actual lattice isometry action on its coordinate basis. -/
theorem generatedAxisGlobalTwelveOctadDiagonalFrame_actual :
    leechIsomMatrix generatedAxisGlobalTwelveOctadDiagonalFrameIsometry = generatedAxisGlobalTwelveOctadDiagonalFrameQ.map (Rat.castHom ℝ) := by
  ext i j
  rw [Matrix.map_apply, ← generatedAxisGlobalTwelveOctadDiagonalFrameFormula_certificate]
  change golayRealPermute (omegaOrbitPermutation 1)
    ((co1XiMatrix * co1XiMatrix) *ᵥ
      (golayRealSign (golayEncoder (Pi.single 9 1))
        (golayRealSign (golayEncoder (Pi.single 7 1))
          (golayRealSign (golayEncoder (Pi.single 5 1)) (Pi.single j 1))))) i = _
  rw [co1XiMatrix_square_eq_transpose, golayRealPermute_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, golayRealSign_apply,
    sign_code_apply, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, generatedAxisGlobalTwelveOctadDiagonalFrameFormulaQ]
  have hp : (omegaOrbitPermutation 1).symm i = omegaOrbitPermInverse 1 i := rfl
  simp only [co1XiMatrix, co1XiMatrixQ, Matrix.map_apply, hp, Rat.coe_castHom,
    generatedAxisGlobalIntSign, qSign]
  split_ifs <;> push_cast <;> ring

/-- The frame conjugation with exact zero entries skipped. -/
def generatedAxisGlobalTwelveOctadDiagonalFrameMatrixQ (i j : Fin 24) : ℚ :=
  ∑ k : Fin 24, if generatedAxisGlobalTwelveOctadDiagonalFrameQ i k = 0 then 0 else
    ∑ l : Fin 24, if generatedAxisGlobalTwelveOctadDiagonalFrameQ j l = 0 then 0 else
      generatedAxisGlobalTwelveOctadDiagonalFrameQ i k * generatedAxisGlobalTwelveOctadDiagonalXPacket.1 k l * generatedAxisGlobalTwelveOctadDiagonalFrameQ j l

/-- Sparse evaluation retains the complete matrix congruence. -/
theorem generatedAxisGlobalTwelveOctadDiagonalFrameMatrix_conjugation :
    generatedAxisGlobalTwelveOctadDiagonalFrameMatrixQ =
      generatedAxisGlobalTwelveOctadDiagonalFrameQ * generatedAxisGlobalTwelveOctadDiagonalXPacket.1 * generatedAxisGlobalTwelveOctadDiagonalFrameQ.transpose := by
  ext i j
  unfold generatedAxisGlobalTwelveOctadDiagonalFrameMatrixQ
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : generatedAxisGlobalTwelveOctadDiagonalFrameQ i k = 0
  · simp [hk]
  · simp only [hk, ite_false]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : generatedAxisGlobalTwelveOctadDiagonalFrameQ j l = 0
    · simp [hl]
    · simp only [hl, ite_false]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 200000000 in
/-- The transported matrix is exactly the octad-three projection. -/
theorem generatedAxisGlobalTwelveOctadDiagonalFrameMatrix_certificate : ∀ i j : Fin 24,
    generatedAxisGlobalTwelveOctadDiagonalFrameMatrixQ i j = if i = j ∧ (0xff00 : ℕ).testBit i.val then (1 : ℚ) else 0 := by
  decide +kernel

/-- The frame carries the actual transition matrix to the octad-three projection. -/
theorem generatedAxisGlobalTwelveOctadDiagonalFrame_matrix :
    conwayMatrixAction generatedAxisGlobalTwelveOctadDiagonalFrameIsometry (griessConwayEncode generatedAxisGlobalTwelveOctadDiagonalX).1 =
      Matrix.diagonal (fun i : Fin 24 => if (0xff00 : ℕ).testBit i.val then (1 : ℝ) else 0) := by
  rw [conwayMatrixAction_eq_conjugate, generatedAxisGlobalTwelveOctadDiagonalFrame_actual, generatedAxisGlobalTwelveOctadDiagonalXPacket_actual]
  change generatedAxisGlobalTwelveOctadDiagonalFrameQ.map (Rat.castHom ℝ) * generatedAxisGlobalTwelveOctadDiagonalXPacket.1.map (Rat.castHom ℝ) *
    (generatedAxisGlobalTwelveOctadDiagonalFrameQ.map (Rat.castHom ℝ)).transpose = _
  have h := congrArg (Rat.castHom ℝ).mapMatrix generatedAxisGlobalTwelveOctadDiagonalFrameMatrix_conjugation
  simp only [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map] at h
  rw [← h]
  ext i j
  simp only [Matrix.map_apply, generatedAxisGlobalTwelveOctadDiagonalFrameMatrix_certificate, Matrix.diagonal_apply]
  split_ifs <;> simp_all

/-- Integer frame images of the transition support vectors. -/
def generatedAxisGlobalTwelveOctadDiagonalFrameShortQ (k : Fin 120) (i : Fin 24) : ℚ :=
  ∑ j : Fin 24, if generatedAxisGlobalTwelveOctadDiagonalFrameQ i j = 0 then 0 else
    generatedAxisGlobalTwelveOctadDiagonalFrameQ i j * (generatedAxisGlobalShortIntegral (generatedAxisGlobalTwelveOctadDiagonalXLabel k) j : ℚ)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 200000000 in
/-- Every transition support vector reaches its stated octad-three root with its sign. -/
theorem generatedAxisGlobalTwelveOctadDiagonalFrameShort_certificate : ∀ k : Fin 120, ∀ i : Fin 24,
    generatedAxisGlobalTwelveOctadDiagonalFrameShortQ k i = (generatedAxisGlobalTwelveOctadDiagonalXVectorSign k : ℚ) *
      (generatedAxisGlobalShortIntegral (generatedAxisGlobalTwelveOctadDiagonalXTarget k) i : ℚ) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
/-- The signs are units and the transition coefficients have square one. -/
theorem generatedAxisGlobalTwelveOctadDiagonalFrame_units : ∀ k : Fin 120,
    (generatedAxisGlobalTwelveOctadDiagonalXVectorSign k = 1 ∨ generatedAxisGlobalTwelveOctadDiagonalXVectorSign k = -1) ∧ generatedAxisGlobalTwelveOctadDiagonalXCoeff k ^ 2 = 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
/-- Every target root lies in the octad-three coordinates. -/
theorem generatedAxisGlobalTwelveOctadDiagonalXTarget_physical_support : ∀ k : Fin 120, ∀ i : Fin 24,
    (0xff00 : ℕ).testBit i.val = false →
      generatedAxisGlobalShortIntegral (generatedAxisGlobalTwelveOctadDiagonalXTarget k) i = 0 := by
  decide +kernel

/-- Every transition support vector is carried to its target by the actual frame. -/
theorem generatedAxisGlobalTwelveOctadDiagonalShortVector_frame (k : Fin 120) :
    generatedAxisGlobalTwelveOctadDiagonalFrameIsometry.val (griessShortVector (generatedAxisGlobalTwelveOctadDiagonalXLabel k)) =
      (generatedAxisGlobalTwelveOctadDiagonalXVectorSign k : ℝ) • griessShortVector (generatedAxisGlobalTwelveOctadDiagonalXTarget k) := by
  ext i
  rw [← leechIsomMatrix_mulVec, generatedAxisGlobalTwelveOctadDiagonalFrame_actual]
  have hs := generatedAxisGlobalTwelveOctadDiagonalFrameShort_certificate k i
  have hsum : generatedAxisGlobalTwelveOctadDiagonalFrameShortQ k i = ∑ j : Fin 24, generatedAxisGlobalTwelveOctadDiagonalFrameQ i j *
      (generatedAxisGlobalShortIntegral (generatedAxisGlobalTwelveOctadDiagonalXLabel k) j : ℚ) := by
    unfold generatedAxisGlobalTwelveOctadDiagonalFrameShortQ
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj
    · simp only [hj, zero_mul]
    · rfl
  rw [hsum] at hs
  have hr : (∑ j : Fin 24, (generatedAxisGlobalTwelveOctadDiagonalFrameQ i j : ℝ) *
      (generatedAxisGlobalShortIntegral (generatedAxisGlobalTwelveOctadDiagonalXLabel k) j : ℝ)) =
      (generatedAxisGlobalTwelveOctadDiagonalXVectorSign k : ℝ) *
        (generatedAxisGlobalShortIntegral (generatedAxisGlobalTwelveOctadDiagonalXTarget k) i : ℝ) := by
    exact_mod_cast hs
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, griessShortVector,
    ← generatedAxisGlobalShortIntegral_actual, Pi.smul_apply, smul_eq_mul]
  change (∑ j : Fin 24, (generatedAxisGlobalTwelveOctadDiagonalFrameQ i j : ℝ) *
    ((generatedAxisGlobalShortIntegral (generatedAxisGlobalTwelveOctadDiagonalXLabel k) j : ℝ) / Real.sqrt 8)) = _
  simp only [← mul_div_assoc, ← Finset.sum_div]
  rw [hr]

/-- The transition labels are distinct. -/
theorem generatedAxisGlobalTwelveOctadDiagonalXLabel_injective : Function.Injective generatedAxisGlobalTwelveOctadDiagonalXLabel := by
  intro p q hpq
  have hp := generatedAxisGlobalTwelveOctadDiagonalXSource_roundtrip p
  rw [hpq, generatedAxisGlobalTwelveOctadDiagonalXSource_roundtrip q] at hp
  exact Option.some.inj hp.symm

/-- The genuine short permutation of the frame sends each transition label to its target. -/
theorem generatedAxisGlobalTwelveOctadDiagonalShortPermutation_frame (k : Fin 120) :
    griessShortPermutation generatedAxisGlobalTwelveOctadDiagonalFrameIsometry (generatedAxisGlobalTwelveOctadDiagonalXLabel k) = generatedAxisGlobalTwelveOctadDiagonalXTarget k := by
  apply centralizer_shortVector_sign_unique
  have hc := generatedAxisGlobalTwelveOctadDiagonalShortVector_frame k
  have hh : generatedAxisGlobalTwelveOctadDiagonalFrameIsometry.val (griessShortVector (generatedAxisGlobalTwelveOctadDiagonalXLabel k)) =
      griessShortVector (generatedAxisGlobalTwelveOctadDiagonalXTarget k) ∨
    generatedAxisGlobalTwelveOctadDiagonalFrameIsometry.val (griessShortVector (generatedAxisGlobalTwelveOctadDiagonalXLabel k)) =
      -griessShortVector (generatedAxisGlobalTwelveOctadDiagonalXTarget k) := by
    rcases (generatedAxisGlobalTwelveOctadDiagonalFrame_units k).1 with hs | hs
    · left
      simpa only [hs, Int.cast_one, one_smul] using hc
    · right
      simpa only [hs, Int.cast_neg, Int.cast_one, neg_one_smul] using hc
  rcases griessShortPermutation_vector generatedAxisGlobalTwelveOctadDiagonalFrameIsometry (generatedAxisGlobalTwelveOctadDiagonalXLabel k) with hp | hn
  · rcases hh with hh | hh
    · exact Or.inl (hp.symm.trans hh)
    · exact Or.inr (hp.symm.trans hh)
  · rcases hh with hh | hh
    · right
      have he := congrArg Neg.neg (hn.symm.trans hh)
      simpa only [neg_neg] using he
    · left
      have he := congrArg Neg.neg (hn.symm.trans hh)
      simpa only [neg_neg] using he

/-- Every target is a genuine octad-three short line. -/
theorem generatedAxisGlobalTwelveOctadDiagonalXTarget_supported (k : Fin 120) :
    generatedOctadShortSupport generatedOctadBasisOctad (generatedAxisGlobalTwelveOctadDiagonalXTarget k) := by
  apply (generatedOctadShortSupport_iff_physical _ _).mpr
  intro i hi
  rw [generatedOctadBasisOctad_mask] at hi
  have hz := generatedAxisGlobalTwelveOctadDiagonalXTarget_physical_support k i hi
  simp only [griessShortVector, ← generatedAxisGlobalShortIntegral_actual, hz, Int.cast_zero,
    zero_div]

/-- The targets are distinct. -/
theorem generatedAxisGlobalTwelveOctadDiagonalXTarget_injective : Function.Injective generatedAxisGlobalTwelveOctadDiagonalXTarget := by
  intro p q hpq
  apply generatedAxisGlobalTwelveOctadDiagonalXLabel_injective
  apply (griessShortPermutation generatedAxisGlobalTwelveOctadDiagonalFrameIsometry).injective
  rw [generatedAxisGlobalTwelveOctadDiagonalShortPermutation_frame, generatedAxisGlobalTwelveOctadDiagonalShortPermutation_frame, hpq]

/-- Every octad-three short line is a target. -/
theorem generatedAxisGlobalTwelveOctadDiagonalXTarget_coverage (r : GriessShortIndex)
    (hr : generatedOctadShortSupport generatedOctadBasisOctad r) :
    ∃ k : Fin 120, generatedAxisGlobalTwelveOctadDiagonalXTarget k = r := by
  let f : Fin 120 → {r : GriessShortIndex // generatedOctadShortSupport generatedOctadBasisOctad r} :=
    fun k => ⟨generatedAxisGlobalTwelveOctadDiagonalXTarget k, generatedAxisGlobalTwelveOctadDiagonalXTarget_supported k⟩
  have hi : Function.Injective f := by
    intro p q hpq
    exact generatedAxisGlobalTwelveOctadDiagonalXTarget_injective (congrArg Subtype.val hpq)
  have hc : Nat.card {r : GriessShortIndex // generatedOctadShortSupport generatedOctadBasisOctad r} ≤
      Nat.card (Fin 120) := by
    rw [generatedOctad_short_support_card]
    simp
  obtain ⟨k, hk⟩ := hi.bijective_of_nat_card_le hc |>.surjective ⟨r, hr⟩
  exact ⟨k, congrArg Subtype.val hk⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
