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

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Algebra 379

/-!
# Matrix-Valued Polynomial Functional Calculus

## References

* This is the standard matrix amplification of the polynomial functional calculus used in the
  definition of complete spectral sets. See: M. Crouzeix,Numerical Range and Functional Calculus
  in Hilbert Space, Journal of Functional Analysis 244 (2007), 668-690. M. Crouzeix and C.
  Palencia, The Numerical Range Is a $(1+\sqrt2)$-Spectral Set, SIAM Journal on Matrix Analysis
  and Applications 38 (2017), 649-655. (for `matrixPolynomialEval`)

## References

* This is the standard matrix amplification of the polynomial functional calculus used in the
  definition of complete spectral sets. See: M. Crouzeix,Numerical Range and Functional Calculus
  in Hilbert Space, Journal of Functional Analysis 244 (2007), 668-690. M. Crouzeix and C.
  Palencia, The Numerical Range Is a $(1+\sqrt2)$-Spectral Set, SIAM Journal on Matrix Analysis
  and Applications 38 (2017), 649-655. (for `matrixPolynomialEval`)

## References

* This is the standard matrix amplification of the polynomial functional calculus used in the
  definition of complete spectral sets. See: M. Crouzeix,Numerical Range and Functional Calculus
  in Hilbert Space, Journal of Functional Analysis 244 (2007), 668-690. M. Crouzeix and C.
  Palencia, The Numerical Range Is a $(1+\sqrt2)$-Spectral Set, SIAM Journal on Matrix Analysis
  and Applications 38 (2017), 649-655. (for `matrixPolynomialEval`)

## References

* This is the standard matrix amplification of the polynomial functional calculus used in the
  definition of complete spectral sets. See: M. Crouzeix,Numerical Range and Functional Calculus
  in Hilbert Space, Journal of Functional Analysis 244 (2007), 668-690. M. Crouzeix and C.
  Palencia, The Numerical Range Is a $(1+\sqrt2)$-Spectral Set, SIAM Journal on Matrix Analysis
  and Applications 38 (2017), 649-655. (for `matrixPolynomialEval`)

## References

* This is the standard matrix amplification of the polynomial functional calculus used in the
  definition of complete spectral sets. See: M. Crouzeix,Numerical Range and Functional Calculus
  in Hilbert Space, Journal of Functional Analysis 244 (2007), 668-690. M. Crouzeix and C.
  Palencia, The Numerical Range Is a $(1+\sqrt2)$-Spectral Set, SIAM Journal on Matrix Analysis
  and Applications 38 (2017), 649-655. (for `matrixPolynomialEval`)

## References

* This is the standard matrix amplification of the polynomial functional calculus used in the
  definition of complete spectral sets. See: M. Crouzeix,Numerical Range and Functional Calculus
  in Hilbert Space, Journal of Functional Analysis 244 (2007), 668-690. M. Crouzeix and C.
  Palencia, The Numerical Range Is a $(1+\sqrt2)$-Spectral Set, SIAM Journal on Matrix Analysis
  and Applications 38 (2017), 649-655. (for `matrixPolynomialEval`)

## References

* This is the standard matrix amplification of the polynomial functional calculus used in the
  definition of complete spectral sets. See: M. Crouzeix,Numerical Range and Functional Calculus
  in Hilbert Space, Journal of Functional Analysis 244 (2007), 668-690. M. Crouzeix and C.
  Palencia, The Numerical Range Is a $(1+\sqrt2)$-Spectral Set, SIAM Journal on Matrix Analysis
  and Applications 38 (2017), 649-655. (for `matrixPolynomialEval`)
-/

namespace MetaMathlibExt

-- Algebra 379: Matrix-Valued Polynomial Functional Calculus

/-- Let

F(z)=(fᵢⱼ(z))_{i,j=1}ᵐ

be an m× m matrix whose entries are complex polynomials, and let

A∈ Mₙ(ℂ).

Define

F(A)=(fᵢⱼ(A))_{i,j=1}ᵐ,

viewed as an mn× mn block matrix acting on

ℂᵐ⊗ℂⁿ.

For each scalar polynomial

fᵢⱼ(z)=∑ₖ aₖ zᵏ,

the block fᵢⱼ(A) is obtained from the usual polynomial functional
calculus

fᵢⱼ(A)=∑ₖ aₖ Aᵏ.
-/
noncomputable def matrixPolynomialEval
    {m n : ℕ}
    (F : Matrix (Fin m) (Fin m) (Polynomial ℂ))
    (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  fun i j =>
    (Polynomial.eval₂
      (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ))
      A
      (F i.1 j.1))
      i.2 j.2

end MetaMathlibExt

end
