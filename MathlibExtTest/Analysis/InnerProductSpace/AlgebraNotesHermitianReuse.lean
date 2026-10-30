/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Matrix.Spectrum

set_option autoImplicit false

/-!
# AlgebraNotes canonical API reuse tests

Canonical Hermitian spectrum and nonzero eigenvectors over the real and complex fields.
Hermitian assumptions are not substituted for the distinct normal-matrix theorem.
-/

namespace AlgebraNotesApiProbe

private theorem hermitian_spectrum (A : Matrix (Fin 2) (Fin 2) ℂ) (h : A.IsHermitian) :
    spectrum ℂ A = RCLike.ofReal '' Set.range h.eigenvalues :=
  Matrix.IsHermitian.spectrum_eq_image_range h

private theorem hermitian_eigenvector (A : Matrix (Fin 2) (Fin 2) ℂ) (h : A.IsHermitian)
    (i : Fin 2) :
    Matrix.mulVec A ⇑(h.eigenvectorBasis i) = h.eigenvalues i • ⇑(h.eigenvectorBasis i) :=
  Matrix.IsHermitian.mulVec_eigenvectorBasis h i

private theorem real_spectral_values (A : Matrix (Fin 2) (Fin 2) ℝ) (h : A.IsHermitian) :
    spectrum ℝ A = Set.range h.eigenvalues :=
  Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues h

private theorem eigenvectors_nonzero (A : Matrix (Fin 2) (Fin 2) ℂ) (h : A.IsHermitian)
    (i : Fin 2) : h.eigenvectorBasis i ≠ 0 :=
  h.eigenvectorBasis.orthonormal.ne_zero i

#print axioms hermitian_spectrum
#print axioms hermitian_eigenvector
#print axioms real_spectral_values
#print axioms eigenvectors_nonzero

end AlgebraNotesApiProbe
