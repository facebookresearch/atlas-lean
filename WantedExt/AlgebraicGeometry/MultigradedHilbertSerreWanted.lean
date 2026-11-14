/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.RingTheory.MultigradedHilbertSeries

/-!
# Multigraded Hilbert–Serre requests

Nonzero vectors in `ℕ^r` give a positive grading: each fixed multidegree
contains finitely many monomials. The Hilbert–Serre conclusion is an
identity of actual multivariate formal power series over `ℤ`.

The one-variable weighted polynomial Hilbert-series proofs in TauCeti are
covered source results. This file asks for the vector-valued homogeneous
quotient version with its finite-piece law and polynomial numerator.

References:
* Miller–Sturmfels, *Combinatorial Commutative Algebra*, Chapter 8,
  https://doi.org/10.1007/b138602.
* Covered source: TauCetiProject/TauCeti at
  62bbc0596dc3539d488232e4e924a338548ea0a9,
  `TauCeti/RingTheory/GradedAlgebra/HilbertSeries.lean`.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MultigradedHilbertSerreWanted

open MathlibExt.RingTheory.MultigradedHilbertSeries

variable {k : Type*} [Field k] {n r : ℕ}

/-- Positive vector grading gives finite-dimensional quotient pieces. -/
theorem_wanted finite_quotientPiece (w : Fin n → (Fin r →₀ ℕ))
    (hw : ∀ i, w i ≠ 0) (I : Ideal (MvPolynomial (Fin n) k))
    (a : Fin r →₀ ℕ) : Module.Finite k (quotientPiece w I a)

/-- Hilbert–Serre rationality with the generator-degree denominator. -/
theorem_wanted hilbertSerre (w : Fin n → (Fin r →₀ ℕ))
    (hw : ∀ i, w i ≠ 0) (I : Ideal (MvPolynomial (Fin n) k))
    (hI : IsHomogeneous w I) :
    ∃ p : MvPolynomial (Fin r) ℤ,
      hilbertSeries w I * denominator w = (p : MvPowerSeries (Fin r) ℤ)

end WantedExt.AlgebraicGeometry.MultigradedHilbertSerreWanted
