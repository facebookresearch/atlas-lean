/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.RegularGrothendieckSteinberg

noncomputable section

open MathlibExt.LinearAlgebra.HermitianFlags
open MathlibExt.AlgebraicGeometry.RegularGrothendieckSteinberg

private def A : Mat 2 := !![2, 1; 0, 3]

private def eigenvalueThree : SpectralCover :=
  ⟨(⟨A, by norm_num [discriminant, A, Matrix.trace, Fin.sum_univ_two, Matrix.det_fin_two]⟩, 3),
    by norm_num [quadratic, A, Matrix.trace, Fin.sum_univ_two, Matrix.det_fin_two]⟩

/-- This regular matrix is genuinely outside the normal-matrix special case. -/
example : A * A.conjTranspose ≠ A.conjTranspose * A := by
  intro h
  have h00 := congrArg (fun M : Mat 2 => M 0 0) h
  norm_num [map_ofNat, A, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The normalized Hermitian projector follows the non-orthogonal eigenline,
and differs from the raw algebraic spectral idempotent. -/
example : orthogonalProjector eigenvalueThree = !![1 / 2, 1 / 2; 1 / 2, 1 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [map_ofNat, orthogonalProjector, spectralIdempotent, eigenvalueThree, A,
      Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two]
