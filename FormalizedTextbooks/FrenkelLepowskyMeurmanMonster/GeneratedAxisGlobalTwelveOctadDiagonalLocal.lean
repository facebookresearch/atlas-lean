/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadDiagonalSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceQFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQCoordinateEvaluation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortQFinite
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortCoordinateCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadPhaseExact

/-! The listed Octad representative after the two original source letters, inverse Xi and inverse
second source permutation: complete matrix, short and tensor coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix
open Multiplicative

/-- The two signed original source letters: inverse Xi after the inverse second permutation. -/
def generatedAxisGlobalTwelveOctadDiagonalWord : List (Fin 10) := [1, 9]

/-- Their complete local fiber product. -/
def generatedAxisGlobalTwelveOctadDiagonalFiber : localFiberSubgroup :=
  (generatedAxisGlobalTwelveOctadDiagonalWord.map generatedAxisGlobalOddSourceFiberLetter).prod

/-- The actual local element of the two letters. -/
def generatedAxisGlobalTwelveOctadDiagonalLocal : H := localFiberIntoH generatedAxisGlobalTwelveOctadDiagonalFiber

/-- Binary images of the coordinate generators under the word. -/
def generatedAxisGlobalTwelveOctadDiagonalCacheBinary : Fin 24 → ℕ :=
  ![377504, 1033200, 8434688, 8418304, 2097171, 2097229, 1048611, 1048717, 798771, 205005,
    8389632, 4196352, 3145728, 1048576, 2097160, 2097156, 1114125, 1310723, 2228237, 2621443,
    13, 3, 2060, 1024]

/-- Central phases of the coordinate-generator images under the word. -/
def generatedAxisGlobalTwelveOctadDiagonalCachePhase : Fin 24 → ZMod 2 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Candidate complete images of the coordinate generators. -/
def generatedAxisGlobalTwelveOctadDiagonalCache (i : Fin 24) : Q :=
  ⟨ofAdd (fun j => golayBooleanCast ((generatedAxisGlobalTwelveOctadDiagonalCacheBinary i).testBit j.val)),
    ofAdd (generatedAxisGlobalTwelveOctadDiagonalCachePhase i)⟩

set_option maxHeartbeats 80000000 in
-- Check the 24 complete word images using only verified finite letter formulas.
/-- Every cached generator image is the compact original word image. -/
theorem generatedAxisGlobalTwelveOctadDiagonalCache_certificate (i : Fin 24) :
    generatedAxisGlobalOddSourceFastWord generatedAxisGlobalTwelveOctadDiagonalWord (qCoordinateGenerator i) =
      generatedAxisGlobalTwelveOctadDiagonalCache i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ i j : Fin 24,
        toAdd (generatedAxisGlobalOddSourceFastWord generatedAxisGlobalTwelveOctadDiagonalWord (qCoordinateGenerator i)).base j =
          toAdd (generatedAxisGlobalTwelveOctadDiagonalCache i).base j := by decide +kernel
    exact h i j
  · apply toAdd.injective
    have h : ∀ i : Fin 24,
        toAdd (generatedAxisGlobalOddSourceFastWord generatedAxisGlobalTwelveOctadDiagonalWord (qCoordinateGenerator i)).coeff =
          toAdd (generatedAxisGlobalTwelveOctadDiagonalCache i).coeff := by decide +kernel
    exact h i

/-- The word acts on every extraspecial element by the cached coordinate evaluation. -/
theorem generatedAxisGlobalTwelveOctadDiagonalFiber_Q (q : Q) :
    spinConjugation generatedAxisGlobalTwelveOctadDiagonalFiber.val.1 q = monsterNortonCoordinateEvaluation generatedAxisGlobalTwelveOctadDiagonalCache q := by
  apply monsterNortonCoordinateEvaluation_eq
  intro i
  rw [generatedAxisGlobalTwelveOctadDiagonalFiber, generatedAxisGlobalOddSourceFastWord_actual, generatedAxisGlobalTwelveOctadDiagonalCache_certificate]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 200000000 in
-- Check the 120 preferred source images with their central phases.
/-- Every source support lift has the stated image label and central phase. -/
theorem generatedAxisGlobalTwelveOctadDiagonalQImage_certificate (k : Fin 120) :
    monsterNortonCoordinateEvaluation generatedAxisGlobalTwelveOctadDiagonalCache
        (generatedAxisGlobalShortQFinite (generatedAxisGlobalTwelveOctadDiagonalVLabel k)) =
      qCentral (generatedAxisGlobalTwelveOctadDiagonalUPhase k) * generatedAxisGlobalShortQFinite (generatedAxisGlobalTwelveOctadDiagonalULabel k) := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ k : Fin 120, ∀ j : Fin 24,
        toAdd (monsterNortonCoordinateEvaluation generatedAxisGlobalTwelveOctadDiagonalCache
          (generatedAxisGlobalShortQFinite (generatedAxisGlobalTwelveOctadDiagonalVLabel k))).base j =
        toAdd (qCentral (generatedAxisGlobalTwelveOctadDiagonalUPhase k) *
          generatedAxisGlobalShortQFinite (generatedAxisGlobalTwelveOctadDiagonalULabel k)).base j := by decide +kernel
    exact h k j
  · apply toAdd.injective
    have h : ∀ k : Fin 120,
        toAdd (monsterNortonCoordinateEvaluation generatedAxisGlobalTwelveOctadDiagonalCache
          (generatedAxisGlobalShortQFinite (generatedAxisGlobalTwelveOctadDiagonalVLabel k))).coeff =
        toAdd (qCentral (generatedAxisGlobalTwelveOctadDiagonalUPhase k) *
          generatedAxisGlobalShortQFinite (generatedAxisGlobalTwelveOctadDiagonalULabel k)).coeff := by decide +kernel
    exact h k

/-- Each source unit is carried to its image unit with its phase. -/
theorem generatedAxisGlobalTwelveOctadDiagonalFiber_single (k : Fin 120) :
    localShortOperator generatedAxisGlobalTwelveOctadDiagonalFiber (Pi.single (generatedAxisGlobalTwelveOctadDiagonalVLabel k) 1) =
      qSign (generatedAxisGlobalTwelveOctadDiagonalUPhase k) • Pi.single (generatedAxisGlobalTwelveOctadDiagonalULabel k) (1 : ℝ) := by
  apply monsterNortonShortBasis_of_Q_image
  rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq, generatedAxisGlobalTwelveOctadDiagonalFiber_Q,
    ← generatedAxisGlobalShortQFinite_actual, ← generatedAxisGlobalShortQFinite_actual,
    generatedAxisGlobalTwelveOctadDiagonalQImage_certificate]

/-- The transported short coordinates as a finite sum of preferred units. -/
theorem generatedAxisGlobalTwelveOctadDiagonalUShort_sum :
    (griessConwayEncode (rhoLocal generatedAxisGlobalTwelveOctadDiagonalLocal (generatedOctadLocalAxis 0 0))).2.1 =
      ∑ k : Fin 120, ((generatedAxisGlobalTwelveOctadDiagonalUCoeff k : ℚ) : ℝ) • Pi.single (generatedAxisGlobalTwelveOctadDiagonalULabel k) (1 : ℝ) := by
  rw [generatedAxisGlobalTwelveOctadDiagonalLocal, generatedFourth_local_short, generatedAxisGlobalTwelveOctadDiagonalVShort_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, generatedAxisGlobalTwelveOctadDiagonalFiber_single, smul_smul]
  congr 1
  simp only [generatedAxisGlobalTwelveOctadDiagonalUCoeff, Rat.cast_mul, Rat.cast_intCast, generatedAxisGlobalIntSign_real]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
/-- Every stored transported key is the exact catalogue number of its label. -/
theorem generatedAxisGlobalTwelveOctadDiagonalUTree_valid :
    GeneratedAxisGlobalSparseLookupValid
      (fun k => generatedAxisGlobalShortNumber (generatedAxisGlobalTwelveOctadDiagonalULabel k)) generatedAxisGlobalTwelveOctadDiagonalUTree := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
/-- All transported labels round trip through the lookup. -/
theorem generatedAxisGlobalTwelveOctadDiagonalUSource_roundtrip : ∀ k : Fin 120,
    generatedAxisGlobalTwelveOctadDiagonalUSource (generatedAxisGlobalTwelveOctadDiagonalULabel k) = some k := by
  decide +kernel

/-- Every successful transported lookup returns the label at that coordinate. -/
theorem generatedAxisGlobalTwelveOctadDiagonalUSource_sound (r : GriessShortIndex) (k : Fin 120)
    (h : generatedAxisGlobalTwelveOctadDiagonalUSource r = some k) : generatedAxisGlobalTwelveOctadDiagonalULabel k = r :=
  generatedAxisGlobalShortNumber_injective
    (generatedAxisGlobalSparseLookup_sound _ _ generatedAxisGlobalTwelveOctadDiagonalUTree_valid _ _ h)

/-- The transported short coordinates are the sparse candidate coefficients. -/
theorem generatedAxisGlobalTwelveOctadDiagonalUShort_sparse (r : GriessShortIndex) :
    (griessConwayEncode (rhoLocal generatedAxisGlobalTwelveOctadDiagonalLocal (generatedOctadLocalAxis 0 0))).2.1 r =
      (generatedAxisGlobalTwelveOctadDiagonalUShortQ r : ℝ) := by
  rw [generatedAxisGlobalTwelveOctadDiagonalUShort_sum]
  have h := generatedAxisGlobalSparseLookup_sum generatedAxisGlobalTwelveOctadDiagonalULabel generatedAxisGlobalTwelveOctadDiagonalUSource
    generatedAxisGlobalTwelveOctadDiagonalUSource_roundtrip generatedAxisGlobalTwelveOctadDiagonalUSource_sound generatedAxisGlobalTwelveOctadDiagonalUCoeff r
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  have h' : ((∑ k : Fin 120, generatedAxisGlobalTwelveOctadDiagonalUCoeff k * (if generatedAxisGlobalTwelveOctadDiagonalULabel k = r then 1 else 0) : ℚ) : ℝ) =
      ∑ k : Fin 120, if r = generatedAxisGlobalTwelveOctadDiagonalULabel k then ((generatedAxisGlobalTwelveOctadDiagonalUCoeff k : ℚ) : ℝ) else 0 := by
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : generatedAxisGlobalTwelveOctadDiagonalULabel k = r
    · simp [hk]
    · simp [hk, Ne.symm hk]
  rw [← h', h]
  unfold generatedAxisGlobalTwelveOctadDiagonalUShortQ
  cases generatedAxisGlobalTwelveOctadDiagonalUSource r <;> rfl

/-- Explicit rational intermediate matrix formula. -/
def generatedAxisGlobalTwelveOctadDiagonalUMatrixFormulaQ (i j : Fin 24) : ℚ :=
  (∑ t : Fin 24, if Nat.testBit 0xff00 t.val then
    (co1XiNumerator (omegaOrbitPermInverse 1 t) i : ℚ) *
      (co1XiNumerator (omegaOrbitPermInverse 1 t) j : ℚ) else 0) / 4

set_option maxRecDepth 10000 in
set_option maxHeartbeats 40000000 in
/-- The formula agrees with the displayed intermediate matrix. -/
theorem generatedAxisGlobalTwelveOctadDiagonalUMatrixFormula_certificate : ∀ i j : Fin 24,
    generatedAxisGlobalTwelveOctadDiagonalUMatrixFormulaQ i j = generatedAxisGlobalTwelveOctadDiagonalUMatrixQ i j := by
  decide +kernel

/-- The inverse spatial word sends each coordinate unit to its explicit image. -/
theorem generatedAxisGlobalTwelveOctadDiagonalFiber_inverse_unit (i : Fin 24) :
    generatedAxisGlobalTwelveOctadDiagonalFiber.val.2.val.symm (Pi.single i 1) =
      fun t => (co1XiNumerator (omegaOrbitPermInverse 1 t) i : ℝ) / 2 := by
  have hf : generatedAxisGlobalTwelveOctadDiagonalFiber = xiSpinLocalFiber⁻¹ * (monsterSourcePermutationFiber 1)⁻¹ := by
    simp [generatedAxisGlobalTwelveOctadDiagonalFiber, generatedAxisGlobalTwelveOctadDiagonalWord, generatedAxisGlobalOddSourceFiberLetter,
      generatedAxisGlobalOddSourceBaseFiber]
  have hinv : generatedAxisGlobalTwelveOctadDiagonalFiber⁻¹ = monsterSourcePermutationFiber 1 * xiSpinLocalFiber := by
    rw [hf]
    group
  funext t
  change ((generatedAxisGlobalTwelveOctadDiagonalFiber⁻¹).val.2).val (Pi.single i 1) t = _
  rw [hinv]
  change golayRealPermute (omegaOrbitPermutation 1)
    (xiSpinLocalFiber.val.2.val (Pi.single i 1)) t = _
  rw [golayRealPermute_apply]
  exact generatedFifth_xi_spatial_unit _ i

/-- Every intermediate matrix entry is the explicit rational entry. -/
theorem generatedAxisGlobalTwelveOctadDiagonalUMatrix_entry (i j : Fin 24) :
    (griessConwayEncode (rhoLocal generatedAxisGlobalTwelveOctadDiagonalLocal (generatedOctadLocalAxis 0 0))).1 i j =
      (generatedAxisGlobalTwelveOctadDiagonalUMatrixQ i j : ℝ) := by
  rw [generatedAxisGlobalTwelveOctadDiagonalLocal, generatedFourth_local_matrix]
  have hm := generatedAxis_triality_octad_matrix generatedOctadBasisOctad 0 0
  change (griessConwayEncode (generatedOctadLocalAxis 0 0)).1 = _ at hm
  rw [hm, generatedOctadBasisOctad_mask]
  rw [← Matrix.toBilin'_single (conwayMatrixAction generatedAxisGlobalTwelveOctadDiagonalFiber.val.2
    (Matrix.diagonal (fun t : Fin 24 => if Nat.testBit 0xff00 t.val then 1 else 0))) i j,
    conwayMatrixAction_pairing, generatedAxisGlobalTwelveOctadDiagonalFiber_inverse_unit, generatedAxisGlobalTwelveOctadDiagonalFiber_inverse_unit,
    ← generatedAxisGlobalTwelveOctadDiagonalUMatrixFormula_certificate]
  simp only [Matrix.toBilin'_apply, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, generatedAxisGlobalTwelveOctadDiagonalUMatrixFormulaQ]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hb : Nat.testBit 0xff00 t.val = true
  · simp only [hb, ite_true, mul_one]
    push_cast
    ring
  · simp [hb]

/-- The transported tensor coordinates are zero. -/
theorem generatedAxisGlobalTwelveOctadDiagonalUTensor_zero :
    (griessConwayEncode (rhoLocal generatedAxisGlobalTwelveOctadDiagonalLocal (generatedOctadLocalAxis 0 0))).2.2 = 0 := by
  change (griessConwayEncode (localGriessRepresentation generatedAxisGlobalTwelveOctadDiagonalFiber
    (generatedOctadLocalAxis 0 0))).2.2 = 0
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  change localTensorRepresentation generatedAxisGlobalTwelveOctadDiagonalFiber
    (griessConwayEncode (generatedOctadLocalAxis 0 0)).2.2 = 0
  rw [show (griessConwayEncode (generatedOctadLocalAxis 0 0)).2.2 = 0 from
    generatedAxis_triality_octad_tensor_zero_all generatedOctadBasisOctad 0 0, map_zero]

/-- The complete intermediate rational packet. -/
theorem generatedAxisGlobalTwelveOctadDiagonalUPacket_actual :
    griessConwayEncode (rhoLocal generatedAxisGlobalTwelveOctadDiagonalLocal (generatedOctadLocalAxis 0 0)) =
      generatedAxisGlobalRationalPacketReal generatedAxisGlobalTwelveOctadDiagonalUPacket := by
  apply Prod.ext
  · funext i j
    exact generatedAxisGlobalTwelveOctadDiagonalUMatrix_entry i j
  · apply Prod.ext
    · funext r
      exact generatedAxisGlobalTwelveOctadDiagonalUShort_sparse r
    · rw [generatedAxisGlobalTwelveOctadDiagonalUTensor_zero]
      funext t i
      simp [generatedAxisGlobalRationalPacketReal, generatedAxisGlobalTwelveOctadDiagonalUPacket]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
