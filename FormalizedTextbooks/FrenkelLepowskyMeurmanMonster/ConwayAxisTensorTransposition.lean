/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.AxialSpectrum

/-! The actual tensor block of the denominator-cleared axis transposition formula. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

private theorem involution_projection_transposition {A : Type*} [Ring A]
    (S P : A) (hS : S * S = 1) (hP : P * P = P) (hSP : S * P = P * S) :
    let L := 1 - S + 8 * P + 8 * (S * P)
    14 * S = 14 - 16 * L + L ^ 2 := by
  dsimp only
  have hSS (x : A) : S * (S * x) = x := by rw [← mul_assoc, hS, one_mul]
  have hPP (x : A) : P * (P * x) = P * x := by rw [← mul_assoc, hP]
  have hSP' (x : A) : S * (P * x) = P * (S * x) := by rw [← mul_assoc, hSP, mul_assoc]
  noncomm_ring [hSS, hPP, hSP', hS, hP, hSP]
  norm_num

/-- Conway's actual preferred spin involution is recovered polynomially from
the actual axial multiplication on the tensor constituent. -/
theorem conwayAxisTensorOperator_transposition_polynomial (p : Fin 276) :
    14 * conwayAxisSpin p =
      14 - 16 * conwayAxisTensorOperator p + (conwayAxisTensorOperator p) ^ 2 :=
  involution_projection_transposition (conwayAxisSpin p) (conwayAxisTensorProjection p)
    (conwayAxisSpin_square p) (conwayAxisTensorProjection_square p)
    (conwayAxisSpin_projection_commute p)

/-- The tensor transposition formula holds for every actual short label and
both actual central signs, without a spectral or transposition hypothesis. -/
theorem conwayShortAxisTensorOperator_transposition_polynomial
    (r : GriessShortIndex) (c : ZMod 2) :
    14 * conwayShortAxisSignedSpin r c =
      14 - 16 * conwayShortAxisTensorOperator r c +
        (conwayShortAxisTensorOperator r c) ^ 2 :=
  involution_projection_transposition
    (conwayShortAxisSignedSpin r c) (conwayShortTensorProjection r)
    (conwayShortAxisSignedSpin_square r c) (conwayShortTensorProjection_square r)
    (conwayShortAxisSignedSpin_projection_commute r c)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
