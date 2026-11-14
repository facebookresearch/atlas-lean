/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Multigraded quotient Hilbert series

The grading takes values in actual finite-support exponent vectors. The
degree pieces are the images of Mathlib's weighted homogeneous submodules
in the quotient ring, and their Hilbert series uses their actual dimensions.

Reference: Miller–Sturmfels, *Combinatorial Commutative Algebra*, Chapter 8,
https://doi.org/10.1007/b138602.
-/

@[expose] public noncomputable section

namespace MathlibExt.RingTheory.MultigradedHilbertSeries

variable {k : Type*} [Field k] {n r : ℕ}

/-- A homogeneous ideal for the vector-valued grading. -/
def IsHomogeneous (w : Fin n → (Fin r →₀ ℕ))
    (I : Ideal (MvPolynomial (Fin n) k)) : Prop :=
  ∀ f ∈ I, ∀ a, MvPolynomial.weightedHomogeneousComponent w a f ∈ I

/-- The actual degree piece of the quotient of a polynomial ring. -/
def quotientPiece (w : Fin n → (Fin r →₀ ℕ))
    (I : Ideal (MvPolynomial (Fin n) k)) (a : Fin r →₀ ℕ) :
    Submodule k (MvPolynomial (Fin n) k ⧸ I) :=
  (MvPolynomial.weightedHomogeneousSubmodule k w a).map
    (Ideal.Quotient.mkₐ k I).toLinearMap

/-- Dimensions recorded as the coefficients of a multivariate formal series. -/
def hilbertSeries (w : Fin n → (Fin r →₀ ℕ))
    (I : Ideal (MvPolynomial (Fin n) k)) : MvPowerSeries (Fin r) ℤ :=
  fun a ↦ (Module.finrank k (quotientPiece w I a) : ℤ)

/-- The denominator specified by the degrees of the polynomial generators. -/
def denominator (w : Fin n → (Fin r →₀ ℕ)) : MvPowerSeries (Fin r) ℤ :=
  ∏ i : Fin n, (1 - MvPowerSeries.monomial (w i) (1 : ℤ))

end MathlibExt.RingTheory.MultigradedHilbertSeries
