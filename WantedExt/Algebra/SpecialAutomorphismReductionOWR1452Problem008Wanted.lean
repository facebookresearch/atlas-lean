/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Surjectivity of reduction for special polynomial automorphisms (Oberwolfach Report 1/2007)

S. Vénéreau (with A. van den Essen and S. Maubach), The special automorphism group of `R[t]/(tᵐ)[x₁,
…, xₙ]` and coordinates of a subring of `R[t][x₁, …, xₙ]`, Oberwolfach Report 1/2007, p. 26,
Question 1: is `SAut_{R[t]} R[t][Y] → SAut_{R[t]/(tᵐ)} R[t]/(tᵐ)[Y]` surjective?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span

@[expose] public section

namespace MathlibExt.Algebra.SpecialAutomorphismReductionOWR1452Problem008Wanted

/-!
Source: S. Vénéreau (with A. van den Essen and S. Maubach), The special automorphism group of
R[t]/(t^m)[x_1,...,x_n] and coordinates of a subring of R[t][x_1,...,x_n], in Affine Algebraic
Geometry, Oberwolfach Reports 4 (2007), no. 1, p. 26, Question 1, DOI 10.4171/OWR/2007/01.
UnsolvedMath record UM-30000644 (`OWR-1452-008`), dataset ulamai/UnsolvedMath v1.8.0.

`SAut` is the group of algebra automorphisms with Jacobian determinant `1`; the reduction map
reduces the images of the variables coefficientwise modulo `tᵐ`, so surjectivity says that every
special automorphism over `R[t]/(tᵐ)` is the reduction of a special automorphism over `R[t]`. The
ring `R` is a commutative ring containing `ℚ` (a `ℚ`-algebra), as in Theorem 2 of the abstract,
which is derived from the answer; `m ≥ 1`.
-/

open Polynomial

/-- The Jacobian determinant `det (∂φ(yᵢ)/∂yⱼ)` of an `A`-algebra endomorphism `φ` of the
polynomial ring `A[y₁, …, yₙ]`. -/
noncomputable def jacobianDet {A : Type} [CommRing A] {n : ℕ}
    (φ : MvPolynomial (Fin n) A →ₐ[A] MvPolynomial (Fin n) A) : MvPolynomial (Fin n) A :=
  (Matrix.of fun i j : Fin n => MvPolynomial.pderiv j (φ (MvPolynomial.X i))).det

/-- The truncated polynomial ring `R[t]/(tᵐ)`. -/
abbrev truncatedPolynomialRing (R : Type) [CommRing R] (m : ℕ) : Type :=
  R[X] ⧸ Ideal.span {(X : R[X]) ^ m}

/-- Question 1 of the Oberwolfach Report 1/2007 abstract of Vénéreau (with van den Essen and
Maubach): for every commutative ring `R` containing `ℚ`, every `m ≥ 1` and every `n`, the reduction
map `SAut_{R[t]} R[t][y₁, …, yₙ] → SAut_{R[t]/(tᵐ)} (R[t]/(tᵐ))[y₁, …, yₙ]` is surjective: every
automorphism of `(R[t]/(tᵐ))[y₁, …, yₙ]` with Jacobian determinant `1` is the reduction modulo `tᵐ`
of an automorphism of `R[t][y₁, …, yₙ]` with Jacobian determinant `1`. -/
def specialAutomorphismReductionSurjective : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℚ R] (m n : ℕ), 1 ≤ m →
    ∀ ψ : MvPolynomial (Fin n) (truncatedPolynomialRing R m) ≃ₐ[truncatedPolynomialRing R m]
        MvPolynomial (Fin n) (truncatedPolynomialRing R m),
      jacobianDet ψ.toAlgHom = 1 →
      ∃ φ : MvPolynomial (Fin n) R[X] ≃ₐ[R[X]] MvPolynomial (Fin n) R[X],
        jacobianDet φ.toAlgHom = 1 ∧
        ∀ i, MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {(X : R[X]) ^ m}))
          (φ (MvPolynomial.X i)) = ψ (MvPolynomial.X i)

/--
Resolved true: the abstract records "Answer 1 (van den Essen, Maubach). YES" with a proof sketch
(locally nilpotent derivations and exponentials, using `ℚ ⊆ R`), and derives from it Theorem 2 for
every ring `R` containing `ℚ` and every `m ≥ 1`; the result is published by van den Essen, Maubach
and Vénéreau. Source: S. Vénéreau (with A. van den Essen and S. Maubach), The special automorphism
group of R[t]/(t^m)[x_1,...,x_n] and coordinates of a subring of R[t][x_1,...,x_n], in Affine
Algebraic Geometry, Oberwolfach Reports 4 (2007), no. 1, p. 26, Question 1, DOI 10.4171/OWR/2007/01;
resolution: A. van den Essen, S. Maubach and S. Vénéreau, The special automorphism group of
R[t]/(t^m)[x_1,...,x_n] and coordinates of a subring of R[t][x_1,...,x_n], J. Pure Appl. Algebra 210
(2007), 141-146, Zbl 1112.14068, surjectivity of SAut_{R[t]} R[t][Y] -> SAut_{R[t]/(t^m)}
R[t]/(t^m)[Y] for rings R containing Q, recorded as Answer 1 with proof sketch in Oberwolfach Report
1/2007, p. 26, and used for Theorem 2 (p. 27), https://doi.org/10.1016/j.jpaa.2006.09.013.
-/
public theorem_wanted specialAutomorphismReductionSurjective_holds :
    specialAutomorphismReductionSurjective

end MathlibExt.Algebra.SpecialAutomorphismReductionOWR1452Problem008Wanted
