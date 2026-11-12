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

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Analysis 382

/-!
# Numerical Range

## References

* The numerical range is a classical notion in operator theory. See, for example: M. Crouzeix,
  Bounds for Analytical Functions of Matrices,Integral Equations and Operator Theory 48 (2004),
  461-477. M. Crouzeix, Numerical Range and Functional Calculus in Hilbert Space, Journal of
  Functional Analysis 244 (2007), 668-690. (for `numericalRange`)

## References

* The numerical range is a classical notion in operator theory. See, for example: M. Crouzeix,
  Bounds for Analytical Functions of Matrices,Integral Equations and Operator Theory 48 (2004),
  461-477. M. Crouzeix, Numerical Range and Functional Calculus in Hilbert Space, Journal of
  Functional Analysis 244 (2007), 668-690. (for `numericalRange`)

## References

* The numerical range is a classical notion in operator theory. See, for example: M. Crouzeix,
  Bounds for Analytical Functions of Matrices,Integral Equations and Operator Theory 48 (2004),
  461-477. M. Crouzeix, Numerical Range and Functional Calculus in Hilbert Space, Journal of
  Functional Analysis 244 (2007), 668-690. (for `numericalRange`)

## References

* The numerical range is a classical notion in operator theory. See, for example: M. Crouzeix,
  Bounds for Analytical Functions of Matrices,Integral Equations and Operator Theory 48 (2004),
  461-477. M. Crouzeix, Numerical Range and Functional Calculus in Hilbert Space, Journal of
  Functional Analysis 244 (2007), 668-690. (for `numericalRange`)

## References

* The numerical range is a classical notion in operator theory. See, for example: M. Crouzeix,
  Bounds for Analytical Functions of Matrices,Integral Equations and Operator Theory 48 (2004),
  461-477. M. Crouzeix, Numerical Range and Functional Calculus in Hilbert Space, Journal of
  Functional Analysis 244 (2007), 668-690. (for `numericalRange`)

## References

* The numerical range is a classical notion in operator theory. See, for example: M. Crouzeix,
  Bounds for Analytical Functions of Matrices,Integral Equations and Operator Theory 48 (2004),
  461-477. M. Crouzeix, Numerical Range and Functional Calculus in Hilbert Space, Journal of
  Functional Analysis 244 (2007), 668-690. (for `numericalRange`)

## References

* The numerical range is a classical notion in operator theory. See, for example: M. Crouzeix,
  Bounds for Analytical Functions of Matrices,Integral Equations and Operator Theory 48 (2004),
  461-477. M. Crouzeix, Numerical Range and Functional Calculus in Hilbert Space, Journal of
  Functional Analysis 244 (2007), 668-690. (for `numericalRange`)
-/

namespace MetaMathlibExt

-- Analysis 382: Numerical Range

/-- Let

A∈ Mₙ(ℂ).

The numerical range of A is

W(A)={⟨ x,Ax⟩ : x∈ℂⁿ, ‖x‖₂=1}.

Equivalently,

W(A)={x^*Ax:‖x‖₂=1}.
-/
noncomputable def numericalRange
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) : Set ℂ :=
  {z : ℂ |
    ∃ x : EuclideanSpace ℂ (Fin n),
      ‖x‖ = 1 ∧
      z = inner ℂ x (A.toEuclideanLin x)}

end MetaMathlibExt

end
