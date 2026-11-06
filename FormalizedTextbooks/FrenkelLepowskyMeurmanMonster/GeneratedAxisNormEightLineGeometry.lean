/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderNormEightOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance

/-! Genuine unoriented norm-eight lines, represented by their physical outer matrices. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The other orientation of an actual norm-eight lattice vector. -/
def generatedNormEightNeg (u : LeechNormEight) : LeechNormEight :=
  ⟨-u.val, by simpa [leechSquareSum] using u.property⟩

/-- The genuine physical vector in the normalized real Leech lattice. -/
def generatedNormEightVector (u : LeechNormEight) : Fin 24 → ℝ :=
  leechCoordinateEmbedding u.val.val

/-- Its physical outer matrix; dividing by eight gives the orthogonal line projector. -/
def generatedNormEightLineMatrix (u : LeechNormEight) : Matrix (Fin 24) (Fin 24) ℝ :=
  Matrix.vecMulVec (generatedNormEightVector u) (generatedNormEightVector u)

/-- Actual unoriented lines represented by physical matrices, rather than source labels. -/
def GeneratedNormEightLines : Set (Matrix (Fin 24) (Fin 24) ℝ) :=
  Set.range generatedNormEightLineMatrix

theorem generatedNormEightVector_pairing (u : LeechNormEight) :
    stdPairingFun (generatedNormEightVector u) (generatedNormEightVector u) = 8 := by
  rw [generatedNormEightVector, leechEmbedding_pairing, u.property]
  norm_num

theorem generatedNormEightVector_ne_zero (u : LeechNormEight) :
    generatedNormEightVector u ≠ 0 := by
  intro h
  have hn := generatedNormEightVector_pairing u
  rw [h] at hn
  simp [stdPairingFun] at hn

theorem generatedNormEightVector_neg (u : LeechNormEight) :
    generatedNormEightVector (generatedNormEightNeg u) = -generatedNormEightVector u :=
  leechCoordinateEmbedding.map_neg u.val.val

theorem generatedNormEightNeg_ne (u : LeechNormEight) : generatedNormEightNeg u ≠ u := by
  intro h
  have hv := congrArg generatedNormEightVector h
  rw [generatedNormEightVector_neg] at hv
  have hz : generatedNormEightVector u = 0 := by
    funext i
    have hi := congrFun hv i
    change -generatedNormEightVector u i = generatedNormEightVector u i at hi
    change generatedNormEightVector u i = 0
    linarith
  exact generatedNormEightVector_ne_zero u hz

/-- A nonzero real outer matrix determines its vector up to the two orientations. -/
theorem generatedNormEight_outer_eq_iff (x y : Fin 24 → ℝ) (hx : x ≠ 0) :
    Matrix.vecMulVec x x = Matrix.vecMulVec y y ↔ y = x ∨ y = -x := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra hn
      apply hx
      funext i
      simpa using (not_exists.mp hn i)
    have hd := congrArg (fun M : Matrix (Fin 24) (Fin 24) ℝ => M i i) h
    change x i * x i = y i * y i at hd
    rcases (mul_self_eq_mul_self_iff.mp hd) with hp | hn
    · left
      funext j
      have he := congrArg (fun M : Matrix (Fin 24) (Fin 24) ℝ => M i j) h
      change x i * x j = y i * y j at he
      rw [← hp] at he
      exact (mul_left_cancel₀ hi he).symm
    · right
      funext j
      have he := congrArg (fun M : Matrix (Fin 24) (Fin 24) ℝ => M i j) h
      change x i * x j = y i * y j at he
      have hy : y i = -x i := by linarith
      rw [hy] at he
      have hc : x i * y j = x i * (-x j) := by linarith
      exact mul_left_cancel₀ hi hc
  · rintro (rfl | rfl)
    · rfl
    · ext i j
      simp [Matrix.vecMulVec]

/-- Equality of the physical matrices is exactly equality up to actual lattice sign. -/
theorem generatedNormEightLineMatrix_eq_iff (u v : LeechNormEight) :
    generatedNormEightLineMatrix u = generatedNormEightLineMatrix v ↔
      v = u ∨ v = generatedNormEightNeg u := by
  rw [generatedNormEightLineMatrix, generatedNormEightLineMatrix,
    generatedNormEight_outer_eq_iff _ _ (generatedNormEightVector_ne_zero u)]
  constructor
  · rintro (h | h)
    · left
      exact Subtype.ext (Subtype.ext (leechCoordinateEmbedding_injective h))
    · right
      rw [← generatedNormEightVector_neg] at h
      exact Subtype.ext (Subtype.ext (leechCoordinateEmbedding_injective h))
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (generatedNormEightVector_neg u)

theorem generatedNormEightLineMatrix_neg (u : LeechNormEight) :
    generatedNormEightLineMatrix (generatedNormEightNeg u) =
      generatedNormEightLineMatrix u :=
  (generatedNormEightLineMatrix_eq_iff u _).mpr (Or.inr rfl) |>.symm

/-- The physical matrices transform by the actual lattice-isometry representation. -/
theorem generatedNormEightLineMatrix_action (g : leechIsomSubgroup) (u : LeechNormEight) :
    generatedNormEightLineMatrix (g • u) =
      conwayMatrixAction g (generatedNormEightLineMatrix u) := by
  unfold generatedNormEightLineMatrix generatedNormEightVector
  rw [conwayMatrixAction_vecMulVec]
  change Matrix.vecMulVec (leechCoordinateEmbedding (leechIntegralAction g u.val).val)
      (leechCoordinateEmbedding (leechIntegralAction g u.val).val) = _
  rw [leechIntegralAction_embedding]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
