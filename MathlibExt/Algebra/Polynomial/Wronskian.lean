/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Leonard Dinh
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Analysis 406

/-!
# Wronskian of a Finite Family of Polynomials

## References

* This is the standard Wronskian determinant for a finite family of functions or polynomials. For
  its use with Hermite polynomials in the present conjecture, see: G. Felder, A. D. Hemery and A.
  P. Veselov, Zeroes of Wronskians of Hermite Polynomials and Young Diagrams, Physica D 241
  (2012), 2131--2137. DOI: 10.1016/j.physd.2012.08.008. https://arxiv.org/abs/1005.2695 (for
  `polynomialWronskian`)
-/

namespace MetaMathlibExt

-- Analysis 406: Wronskian of a Finite Family of Polynomials

/-- Let R be a commutative ring and let P₁,…,Pᵣ∈ R[X].

The Wronskian of this finite family is the polynomial

Wr[P₁,…,Pᵣ]=det(Pᵢ⁽ʲ⁻¹⁾)_{i,j=1}ʳ.

Equivalently, using zero-based indices i,j=0,…,r-1, the (i,j)-entry of the Wronskian matrix is
Pᵢ⁽ʲ⁾.

For the empty family, the Wronskian is the determinant of the empty matrix and hence equals 1.
-/
noncomputable def polynomialWronskian
    {R : Type*}
    [CommRing R]
    {r : ℕ}
    (P : Fin r → Polynomial R) : Polynomial R :=
  Matrix.det
    (fun i j : Fin r =>
      (Polynomial.derivativeFinsupp (P i)) (j : ℕ))

end MetaMathlibExt

end
