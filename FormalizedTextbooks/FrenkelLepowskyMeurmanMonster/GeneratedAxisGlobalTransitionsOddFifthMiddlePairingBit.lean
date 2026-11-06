/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonSparseBitFrames
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialFastTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSparseRationalShortOutputs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalSpatialMatrixWordSparse

/-! The complete original root-three pairing, evaluated with proved sparse and bit formulas. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000000

/-- Every original Fifth frame spin phase, Gaussian input, and physical column is retained. -/
def generatedAxisGlobalOddFifthFastFrameTensor (k : Fin 2)
    (T : GeneratedAxisGlobalRationalTensor) : GeneratedAxisGlobalRationalTensor :=
  generatedAxisGlobalRationalTensorQ (generatedAxisGlobalOddFifthComparisonQ k)
    (generatedAxisGlobalComparisonMonomialFastTensor (Fin.natAdd 6 k)
      (generatedAxisGlobalRationalTensorXiCached
        (generatedAxisGlobalRationalTensorSign (generatedAxisGlobalOddFifthComparisonSign k) 0
          (generatedAxisGlobalComparisonMonomialFastTensor 5 T))))

/-- The fast expression is the entire original signed Fifth frame. -/
theorem generatedAxisGlobalOddFifthFastFrameTensor_eq (k : Fin 2)
    (T : GeneratedAxisGlobalRationalTensor) :
    generatedAxisGlobalOddFifthFastFrameTensor k T = generatedAxisGlobalOddFifthSparseBitFrameTensor k T := by
  simp only [generatedAxisGlobalOddFifthFastFrameTensor, generatedAxisGlobalOddFifthSparseBitFrameTensor,
    generatedAxisGlobalComparisonMonomialFastTensor_eq]

/-- Every original root-three tensor source value in its original physical label. -/
def generatedAxisGlobalOddFifthPhysicalSourceTensor (a : Fin 4096) (i : Fin 24) : ℚ :=
  (generatedAxisGlobalOddRoot03Spin09 a : ℚ) * (generatedAxisGlobalOddRoot03Spatial09 i : ℚ) / 8

/-- Both actual signed outputs keep the full original odd-short and tensor input terms. -/
def generatedAxisGlobalOddFifthPhysicalOutgoingTensor (k : Fin 2)
    (a : Fin 4096) (i : Fin 24) : ℚ :=
  let d := generatedAxisGlobalSpinLabelLow a
  let s : ℚ := generatedAxisGlobalIntSign (golayLabelCoefficients a 11)
  let e : ℚ := generatedAxisGlobalIntSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)
  let z : ℚ := if (golayEncodedMask d.val).testBit i.val then -1 else 1
  let C := generatedAxisGlobalOddOtherSparseShortQ 1 (Sum.inr (Sum.inr (d,i)))
  let lo := generatedAxisGlobalOddFifthPhysicalSourceTensor ⟨d.val, by omega⟩ i
  let hi := generatedAxisGlobalOddFifthPhysicalSourceTensor ⟨d.val+2048, by omega⟩ i
  if k = 0 then s*z*C + e*z*(lo-hi)/2
  else e*C+s*e*z*(lo+hi)/2

/-- Every physical coefficient equals the complete actual original outgoing tensor. -/
theorem generatedAxisGlobalOddFifthPhysicalOutgoingTensor_eq (k : Fin 2) :
    generatedAxisGlobalOddFifthPhysicalOutgoingTensor k = generatedAxisGlobalOddFifthOutgoingTensor k := by
  funext a i
  fin_cases k <;>
    simp [generatedAxisGlobalOddFifthPhysicalOutgoingTensor,
      generatedAxisGlobalOddFifthPhysicalSourceTensor,
      generatedAxisGlobalOddFifthOutgoingTensor, generatedAxisGlobalOddFifthOutgoingPacket,
      generatedAxisGlobalRationalTriality, generatedAxisGlobalRationalInverse,
      generatedAxisGlobalTrialityScaledTensorQ, generatedAxisGlobalInverseTensorQ,
      generatedAxisGlobalOddRoot03RationalPacket, generatedAxisGlobalSpinLabel_coeff]

/-- The entire original signed outgoing Fifth short operator retains all Fourier inputs. -/
def generatedAxisGlobalOddFifthSparseOutgoingShort (k : Fin 2) : GriessShortIndex → ℚ :=
  if k = 0 then generatedAxisGlobalSparseTrialityShortQ generatedAxisGlobalOddRoot03RationalPacket
    else generatedAxisGlobalSparseInverseShortQ generatedAxisGlobalOddRoot03RationalPacket

/-- Every guarded source coefficient equals the full actual original outgoing short coefficient. -/
theorem generatedAxisGlobalOddFifthSparseOutgoingShort_eq (k : Fin 2) (r : GriessShortIndex) :
    generatedAxisGlobalOddFifthSparseOutgoingShort k r = (generatedAxisGlobalOddFifthOutgoingPacket k).2.1 r := by
  fin_cases k <;>
    simp [generatedAxisGlobalOddFifthSparseOutgoingShort, generatedAxisGlobalOddFifthOutgoingPacket,
      generatedAxisGlobalRationalTriality, generatedAxisGlobalRationalInverse,
      generatedAxisGlobalSparseTrialityShortQ_eq, generatedAxisGlobalSparseInverseShortQ_eq]

/-- Every original selected source and central phase, with the true incoming Fourier zero guard. -/
def generatedAxisGlobalOddFifthSparseSelectedShortQ (k : Fin 2) (j : Fin 4136) : ℚ :=
  (generatedAxisGlobalIntSign (generatedAxisGlobalOddFifthSelectedPhase k j) : ℚ) *
    generatedAxisGlobalOddFifthSparseOutgoingShort k (generatedAxisGlobalOddFifthSelectedSource k j)

/-- Every guarded selected coefficient equals its entire original signed coefficient. -/
theorem generatedAxisGlobalOddFifthSparseSelectedShortQ_eq (k : Fin 2) (j : Fin 4136) :
    generatedAxisGlobalOddFifthSparseSelectedShortQ k j = generatedAxisGlobalOddFifthSelectedShortQ k j := by
  unfold generatedAxisGlobalOddFifthSparseSelectedShortQ generatedAxisGlobalOddFifthSelectedShortQ
  rw [generatedAxisGlobalOddFifthSparseOutgoingShort_eq]

/-- Every inverse physical column of the three original Fifth permutation stretches. -/
theorem generatedAxisGlobalOddFifthMonomialInverseColumn (b : Fin 3) (u i : Fin 24) :
    generatedAxisGlobalRationalSpatialInverseMatrix
      (generatedAxisGlobalComparisonMonomialOriginalLetters (Fin.natAdd 5 b)) u i =
        (if u = generatedAxisGlobalComparisonMonomialPhysicalPull (Fin.natAdd 5 b) i
          then (1 : ℚ) else 0) := by
  have h : ∀ (b : Fin 3) (u i : Fin 24),
      generatedAxisGlobalRationalSpatialInverseMatrix
        (generatedAxisGlobalComparisonMonomialOriginalLetters (Fin.natAdd 5 b)) u i =
          (if u = generatedAxisGlobalComparisonMonomialPhysicalPull (Fin.natAdd 5 b) i
            then (1 : ℚ) else 0) := by
    decide +kernel
  exact h b u i

/-- Every source matrix coefficient is transported by the whole original physical permutation. -/
theorem generatedAxisGlobalOddFifthMonomialSpatialMatrix (b : Fin 3)
    (A : Matrix (Fin 24) (Fin 24) ℚ) :
    generatedAxisGlobalRationalSpatialMatrixWordSparse
      (generatedAxisGlobalComparisonMonomialOriginalLetters (Fin.natAdd 5 b)) A =
        fun i j => A (generatedAxisGlobalComparisonMonomialPhysicalPull (Fin.natAdd 5 b) i)
          (generatedAxisGlobalComparisonMonomialPhysicalPull (Fin.natAdd 5 b) j) := by
  rw [generatedAxisGlobalRationalSpatialMatrixWordSparse_eq]
  funext i j
  unfold generatedAxisGlobalRationalSpatialMatrixWord
  simp_rw [generatedAxisGlobalOddFifthMonomialInverseColumn]
  simp [mul_ite, ite_mul]

/-- The entire original pre-permutation matrix is evaluated at its exact actual columns. -/
theorem generatedAxisGlobalOddFifthPreSpatialMatrix (A : Matrix (Fin 24) (Fin 24) ℚ) :
    generatedAxisGlobalRationalSpatialMatrixWordSparse generatedAxisGlobalOddFifthComparisonPreLetters A =
      fun i j => A (generatedAxisGlobalComparisonMonomialPhysicalPull 5 i)
        (generatedAxisGlobalComparisonMonomialPhysicalPull 5 j) :=
  generatedAxisGlobalOddFifthMonomialSpatialMatrix 0 A

/-- Both whole original post-permutation matrices retain every actual physical column. -/
theorem generatedAxisGlobalOddFifthPostSpatialMatrix (k : Fin 2)
    (A : Matrix (Fin 24) (Fin 24) ℚ) :
    generatedAxisGlobalRationalSpatialMatrixWordSparse (generatedAxisGlobalOddFifthComparisonPostLetters k) A =
      fun i j => A (generatedAxisGlobalComparisonMonomialPhysicalPull (Fin.natAdd 6 k) i)
        (generatedAxisGlobalComparisonMonomialPhysicalPull (Fin.natAdd 6 k) j) := by
  fin_cases k
  · exact generatedAxisGlobalOddFifthMonomialSpatialMatrix 1 A
  · exact generatedAxisGlobalOddFifthMonomialSpatialMatrix 2 A

/-- All original single-Xi inverse matrix entries, including every zero column entry. -/
theorem generatedAxisGlobalOddFifthXiInverseColumn (u i : Fin 24) :
    generatedAxisGlobalRationalSpatialInverseMatrix [0] u i = (co1XiNumerator i u : ℚ) / 2 := by
  have h : ∀ (u i : Fin 24),
      generatedAxisGlobalRationalSpatialInverseMatrix [0] u i = (co1XiNumerator i u : ℚ) / 2 := by
    decide +kernel
  exact h u i

/-- The entire original physical matrix action, retaining all true zero guards. -/
def generatedAxisGlobalOddFifthFramedSparseMatrix (k : Fin 2) : Matrix (Fin 24) (Fin 24) ℚ :=
  generatedAxisGlobalRationalSpatialMatrixWordSparse (generatedAxisGlobalOddFifthComparisonPostLetters k)
    (generatedAxisGlobalRationalSpatialMatrixWordSparse [0]
      (generatedAxisGlobalRationalSignMatrix (generatedAxisGlobalOddFifthComparisonSign k)
        (generatedAxisGlobalRationalSpatialMatrixWordSparse
          generatedAxisGlobalOddFifthComparisonPreLetters
          (generatedAxisGlobalOddFifthOutgoingPacket k).1)))

/-- Every guarded coefficient equals the entire original actual framed matrix. -/
theorem generatedAxisGlobalOddFifthFramedSparseMatrix_eq (k : Fin 2) :
    generatedAxisGlobalOddFifthFramedSparseMatrix k = generatedAxisGlobalOddFifthFramedMatrix k := by
  simp only [generatedAxisGlobalOddFifthFramedSparseMatrix,
    generatedAxisGlobalRationalSpatialMatrixWordSparse_eq, generatedAxisGlobalOddFifthFramedMatrix]

/-- The complete original Fifth matrix action with exact columns and its true zero guards. -/
def generatedAxisGlobalOddFifthCachedFramedMatrix (k : Fin 2) : Matrix (Fin 24) (Fin 24) ℚ :=
  fun i j =>
    let p := generatedAxisGlobalComparisonMonomialPhysicalPull (Fin.natAdd 6 k)
    let A := generatedAxisGlobalRationalSignMatrix (generatedAxisGlobalOddFifthComparisonSign k)
      (fun u v => (generatedAxisGlobalOddFifthOutgoingPacket k).1
        (generatedAxisGlobalComparisonMonomialPhysicalPull 5 u)
        (generatedAxisGlobalComparisonMonomialPhysicalPull 5 v))
    ∑ u : Fin 24, if (co1XiNumerator (p i) u : ℚ) / 2 = 0 then 0 else
      ∑ v : Fin 24, if (co1XiNumerator (p j) v : ℚ) / 2 = 0 then 0 else
        A u v * ((co1XiNumerator (p i) u : ℚ) / 2) * ((co1XiNumerator (p j) v : ℚ) / 2)

/-- Every cached coefficient equals the entire original physical Fifth comparison matrix. -/
theorem generatedAxisGlobalOddFifthCachedFramedMatrix_eq (k : Fin 2) :
    generatedAxisGlobalOddFifthCachedFramedMatrix k = generatedAxisGlobalOddFifthFramedSparseMatrix k := by
  funext i j
  unfold generatedAxisGlobalOddFifthFramedSparseMatrix
  rw [generatedAxisGlobalOddFifthPostSpatialMatrix, generatedAxisGlobalOddFifthPreSpatialMatrix]
  simp only [generatedAxisGlobalOddFifthCachedFramedMatrix,
    generatedAxisGlobalRationalSpatialMatrixWordSparse, generatedAxisGlobalOddFifthXiInverseColumn]

/-- Every original inverse matrix coefficient uses the complete preferred pair phases. -/
def generatedAxisGlobalOddFifthMiddleMatrixBitQ (k : Fin 2) (i j : Fin 24) : ℚ :=
  if i = j then generatedAxisGlobalOddFifthFramedSparseMatrix k i i else
    (generatedAxisGlobalOddFifthSelectedShortQ k
      (generatedAxisGlobalOddFifthSelectedPair 0 (generatedAxisGlobalFinitePairIndex i j)) -
    generatedAxisGlobalOddFifthSelectedShortQ k
      (generatedAxisGlobalOddFifthSelectedPair 1 (generatedAxisGlobalFinitePairIndex i j))) / 2

/-- Every original inverse short coefficient retains the entire true frame tensor and phase. -/
def generatedAxisGlobalOddFifthMiddleShortBitQ (k : Fin 2) :
    GeneratedAxisGlobalCanonicalFifthMiddleShortIndex → ℚ
  | Sum.inl j =>
      let d := (generatedFifthOddRootOutputData j).1
      let i := (generatedFifthOddRootOutputData j).2
      (if (golayEncodedMask d.val).testBit i.val then -1 else 1) *
        (generatedAxisGlobalOddFifthSparseBitFrameTensor k (generatedAxisGlobalOddFifthOutgoingTensor k)
          ⟨d.val, by omega⟩ i -
        generatedAxisGlobalOddFifthSparseBitFrameTensor k (generatedAxisGlobalOddFifthOutgoingTensor k)
          ⟨d.val+2048, by omega⟩ i) / 2
  | Sum.inr j => generatedAxisGlobalOddFifthMiddleShortFastQ k (Sum.inr j)

/-- The guarded matrix formula equals every original inverse matrix coefficient. -/
theorem generatedAxisGlobalOddFifthMiddleMatrixBitQ_eq (k : Fin 2) (i j : Fin 24) :
    generatedAxisGlobalOddFifthMiddleMatrixBitQ k i j =
      generatedAxisGlobalOddFifthMiddleMatrixFastQ k i j := by
  by_cases h : i = j
  · simp only [generatedAxisGlobalOddFifthMiddleMatrixBitQ, h, ↓reduceIte,
      generatedAxisGlobalOddFifthFramedSparseMatrix_eq, generatedAxisGlobalOddFifthMiddleMatrixFastQ]
  · simp only [generatedAxisGlobalOddFifthMiddleMatrixBitQ, h, ↓reduceIte,
      generatedAxisGlobalOddFifthMiddleMatrixFastQ]

/-- Both kinds of original finite support terms retain their full actual inverse coefficients. -/
theorem generatedAxisGlobalOddFifthMiddleShortBitQ_eq (k : Fin 2)
    (p : GeneratedAxisGlobalCanonicalFifthMiddleShortIndex) :
    generatedAxisGlobalOddFifthMiddleShortBitQ k p = generatedAxisGlobalOddFifthMiddleShortFastQ k p := by
  rcases p with j | j
  · simp only [generatedAxisGlobalOddFifthMiddleShortBitQ, generatedAxisGlobalOddFifthMiddleShortFastQ,
      generatedAxisGlobalInverseShortQ, generatedFifthOddRootOutputLabel,
      generatedAxisGlobalOddFifthFramedPacket, generatedAxisGlobalOddFifthFramedTensor,
      generatedAxisGlobalSpinLabel_coeff, generatedAxisGlobalOddFifthSparseBitFrameTensor_eq,
      generatedAxisGlobalOddFifthBitFrameTensor_eq]
  · rfl

/-- The complete original finite middle pairing, with guards on genuine zero target entries. -/
def generatedAxisGlobalOddFifthMiddlePairingBitQ (k : Fin 2) : ℚ :=
  (∑ i : Fin 24, ∑ j : Fin 24,
    if generatedAxisGlobalFifthMiddleMatrixQ i j = 0 then 0 else
      generatedAxisGlobalOddFifthMiddleMatrixBitQ k i j * generatedAxisGlobalFifthMiddleMatrixQ i j) +
  (∑ p : GeneratedAxisGlobalCanonicalFifthMiddleShortIndex,
    if generatedAxisGlobalCanonicalFifthMiddleShortCoefficient p = 0 then 0 else
      generatedAxisGlobalCanonicalFifthMiddleShortCoefficient p *
        generatedAxisGlobalOddFifthMiddleShortBitQ k p)

/-- All true original finite terms are retained by the guarded bit expression. -/
theorem generatedAxisGlobalOddFifthMiddlePairingBitQ_eq (k : Fin 2) :
    generatedAxisGlobalOddFifthMiddlePairingBitQ k = generatedAxisGlobalOddFifthMiddlePairingFastQ k := by
  simp only [generatedAxisGlobalOddFifthMiddlePairingBitQ, generatedAxisGlobalOddFifthMiddlePairingFastQ,
    generatedAxisGlobalOddFifthMiddleMatrixBitQ_eq, generatedAxisGlobalOddFifthMiddleShortBitQ_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
