/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddMatrixWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOrbitActions

/-! Actual physical rational coordinate matrices for the five original spatial source letters. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators

/-- Rational physical matrices of the original spatial generators, retaining column orientation. -/
def generatedAxisGlobalOddSpatialBaseQ (k : Fin 5) : Matrix (Fin 24) (Fin 24) ℚ :=
  if h : k.val = 0 then co1XiMatrixQ
  else (omegaOrbitPhysicalMatrices ⟨k.val - 1, by omega⟩).map (Int.castRingHom ℚ)

/-- Each monomial physical integer matrix is also the actual action on arbitrary real vectors. -/
theorem generatedAxisGlobalOddSpatialMonomial_real (k : Fin 4) (x : Fin 24 → ℝ) :
    (omegaOrbitMonomialIsometry k).val x =
      (omegaOrbitPhysicalMatrices k).map (Int.castRingHom ℝ) *ᵥ x := by
  fin_cases k
  all_goals ext i
  all_goals simp [omegaOrbitMonomialIsometry, omegaOrbitPermutationIsometry,
    golaySignIsometry, golayRealSign_apply, golayPermutationIsometry,
    golayRealPermute_apply, omegaOrbitPhysicalMatrices, Matrix.mulVec, dotProduct,
    omegaOrbitGolayPermutation, omegaOrbitPermutation, Matrix.map_apply,
    qSign, ite_mul]

/-- Every source rational matrix is the identical actual real lattice-isometry action. -/
theorem generatedAxisGlobalOddSpatialBaseQ_actual (k : Fin 5) (x : Fin 24 → ℝ) :
    (omegaOrbitIsometry k).val x =
      (generatedAxisGlobalOddSpatialBaseQ k).map (Rat.castHom ℝ) *ᵥ x := by
  by_cases h : k.val = 0
  · have hk : k = 0 := Fin.ext h
    subst k
    rfl
  · simp only [omegaOrbitIsometry, generatedAxisGlobalOddSpatialBaseQ, h, ↓reduceDIte]
    rw [generatedAxisGlobalOddSpatialMonomial_real]
    congr 1

set_option maxHeartbeats 16000000 in
-- Check the five complete rational physical orthogonality identities.
/-- Each original rational matrix has the transpose as its genuine inverse. -/
theorem generatedAxisGlobalOddSpatialBaseQ_orthogonal : ∀ k : Fin 5,
    generatedAxisGlobalOddSpatialBaseQ k *
      (generatedAxisGlobalOddSpatialBaseQ k).transpose = 1 := by
  decide +kernel

/-- The rational transpose is the actual inverse source action on every real vector. -/
theorem generatedAxisGlobalOddSpatialBaseQ_inverse (k : Fin 5) (x : Fin 24 → ℝ) :
    (omegaOrbitIsometry k).val.symm x =
      (generatedAxisGlobalOddSpatialBaseQ k).transpose.map (Rat.castHom ℝ) *ᵥ x := by
  apply (omegaOrbitIsometry k).val.injective
  rw [LinearEquiv.apply_symm_apply, generatedAxisGlobalOddSpatialBaseQ_actual,
    Matrix.mulVec_mulVec]
  have h := congrArg (Rat.castHom ℝ).mapMatrix
    (generatedAxisGlobalOddSpatialBaseQ_orthogonal k)
  rw [map_mul, map_one] at h
  change (generatedAxisGlobalOddSpatialBaseQ k).map (Rat.castHom ℝ) *
    (generatedAxisGlobalOddSpatialBaseQ k).transpose.map (Rat.castHom ℝ) = 1 at h
  rw [h, Matrix.one_mulVec]

/-- Rational physical matrices of all ten original signed source letters. -/
def generatedAxisGlobalOddSpatialLetterQ (l : Fin 10) : Matrix (Fin 24) (Fin 24) ℚ :=
  let k : Fin 5 := ⟨l.val / 2, by omega⟩
  if l.val % 2 = 1 then (generatedAxisGlobalOddSpatialBaseQ k).transpose
  else generatedAxisGlobalOddSpatialBaseQ k

/-- Every signed rational matrix is the identical full real source action. -/
theorem generatedAxisGlobalOddSpatialLetterQ_actual (l : Fin 10) (x : Fin 24 → ℝ) :
    (generatedAxisGlobalOddSourceSpatialLetter l).val x =
      (generatedAxisGlobalOddSpatialLetterQ l).map (Rat.castHom ℝ) *ᵥ x := by
  by_cases h : l.val % 2 = 1
  · simp only [generatedAxisGlobalOddSourceSpatialLetter, generatedAxisGlobalOddSpatialLetterQ,
      h, ↓reduceIte]
    exact generatedAxisGlobalOddSpatialBaseQ_inverse _ x
  · simp only [generatedAxisGlobalOddSourceSpatialLetter, generatedAxisGlobalOddSpatialLetterQ,
      h, ↓reduceIte]
    exact generatedAxisGlobalOddSpatialBaseQ_actual _ x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
