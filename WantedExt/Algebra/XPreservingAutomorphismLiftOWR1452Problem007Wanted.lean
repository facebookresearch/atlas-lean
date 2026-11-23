/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lifting x-preserving automorphisms from dual numbers (Oberwolfach Report 1/2007)

S. Vénéreau (with A. van den Essen and S. Maubach), Oberwolfach Report 1/2007, p. 25: for `d ≥ 3`
and `R` a reduced ring containing `ℚ`, with `Y = (y₁, …, y_{d-1})`, is there an automorphism `γ̄ ∈
Aut_x R[t]/(t²)[x, Y] ∩ Aut R[t][x, Y]` with `γ̄ ∉ Aut_x R[t][x, Y]`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span

@[expose] public section

namespace MathlibExt.Algebra.XPreservingAutomorphismLiftOWR1452Problem007Wanted

/-!
Source: S. Vénéreau (with A. van den Essen and S. Maubach), The special automorphism group of
R[t]/(t^m)[x_1,...,x_n] and coordinates of a subring of R[t][x_1,...,x_n], in Affine Algebraic
Geometry, Oberwolfach Reports 4 (2007), no. 1, p. 25, DOI 10.4171/OWR/2007/01. UnsolvedMath record
UM-30000643 (`OWR-1452-007`), dataset ulamai/UnsolvedMath v1.8.0.

The abstract writes `γ̄` for the reduction modulo `t²` of an automorphism `γ` of `R[t][x, Y]` (as
for its characteristic-2 example `γ̄ ∈ Aut_x F₂[t]/(t²)[x, y] ∩ Aut F₂[t][x, y]` on p. 25): `γ̄ ∈
Aut_x R[t]/(t²)[x, Y] ∩ Aut R[t][x, Y]` means that `γ̄` fixes `x` and lifts to an
`R[t]`-automorphism `γ`, and `γ̄ ∉ Aut_x R[t][x, Y]` means that it is not the reduction of any
`x`-fixing `R[t]`-automorphism. The question asks whether such `γ̄` exists for some `d ≥ 3` and some
reduced `R ⊇ ℚ`; with `x = X 0` and `k = d - 1 ≥ 2` further variables the claim is stated
existentially and refuted.
-/

open Polynomial

/-- The reduction modulo `t²` of a polynomial over `R[t]`, coefficientwise. -/
noncomputable abbrev reduceModTSq {R : Type} [CommRing R] {σ : Type} :
    MvPolynomial σ R[X] →+* MvPolynomial σ (R[X] ⧸ Ideal.span {(X : R[X]) ^ 2}) :=
  MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {(X : R[X]) ^ 2}))

/-- Vénéreau's question (Oberwolfach Report 1/2007, p. 25): for some `d ≥ 3` and some reduced
ring `R` containing `ℚ`, with variables `x = X 0` and `Y = (X 1, …, X (d - 1))`, there is an
`R[t]`-automorphism `γ` of `R[t][x, Y]` whose reduction `γ̄` modulo `t²` fixes `x` (so
`γ̄ ∈ Aut_x (R[t]/(t²))[x, Y] ∩ Aut R[t][x, Y]`) but which is not the reduction modulo `t²` of any
`x`-fixing `R[t]`-automorphism of `R[t][x, Y]` (`γ̄ ∉ Aut_x R[t][x, Y]`). -/
def nonliftableXPreservingReductionExists : Prop :=
  ∃ (k : ℕ) (R : Type) (_ : CommRing R) (_ : Algebra ℚ R), 2 ≤ k ∧ IsReduced R ∧
    ∃ γ : MvPolynomial (Fin (k + 1)) R[X] ≃ₐ[R[X]] MvPolynomial (Fin (k + 1)) R[X],
      reduceModTSq (γ (MvPolynomial.X 0)) = MvPolynomial.X 0 ∧
      ¬ ∃ δ : MvPolynomial (Fin (k + 1)) R[X] ≃ₐ[R[X]] MvPolynomial (Fin (k + 1)) R[X],
        δ (MvPolynomial.X 0) = MvPolynomial.X 0 ∧
        ∀ i, reduceModTSq (δ (MvPolynomial.X i)) = reduceModTSq (γ (MvPolynomial.X i))

/--
Resolved false: the abstract answers "Unfortunately(?) the answer is no" (p. 24) and explains (p.
26): if `γ̄` lifts to an automorphism of `R[t][x, Y]` its Jacobian lies in `R[t][x, Y]* = R*` for
reduced `R`, so one may assume Jacobian `1`, and the question reduces to Question 1, `SAut_{R[t]}
R[t][Y] → SAut_{R[t]/(tᵐ)} R[t]/(tᵐ)[Y]` surjective, with `x` absorbed into the coefficient ring,
answered YES by van den Essen and Maubach; consequently "there is no possible generalization of the
construction of bad lines and bad residual variables" (p. 27). Source: S. Vénéreau (with A. van den
Essen and S. Maubach), The special automorphism group of R[t]/(t^m)[x_1,...,x_n] and coordinates of
a subring of R[t][x_1,...,x_n], in Affine Algebraic Geometry, Oberwolfach Reports 4 (2007), no. 1,
p. 25, DOI 10.4171/OWR/2007/01; resolution: S. Vénéreau (with A. van den Essen and S. Maubach),
Oberwolfach Report 1/2007, pp. 24-27; A. van den Essen, S. Maubach and S. Vénéreau, J. Pure Appl.
Algebra 210 (2007), 141-146, p. 24: 'Unfortunately(?) the answer is no'; p. 26: reduction to
Question 1 via j(γ) in R[t][x,Y]* = R* and Answer 1 (van den Essen, Maubach): YES, 'There is no more
x since it can be considered as an element of R now'; p. 27: 'Consequently there is no possible
generalization', https://doi.org/10.4171/owr/2007/01.
-/
public theorem_wanted nonliftableXPreservingReductionExists_refuted :
    ¬ nonliftableXPreservingReductionExists

end MathlibExt.Algebra.XPreservingAutomorphismLiftOWR1452Problem007Wanted
