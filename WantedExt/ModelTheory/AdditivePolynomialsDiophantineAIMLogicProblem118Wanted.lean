/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The additive polynomials are Diophantine in `𝔽_p[Z]` (AIM Hilbert's tenth extensions, Question 5)

AIM workshop Extensions of Hilbert's tenth problem, problem list, Question 5 (Pheidas): an additive
polynomial in `𝔽_p[Z]` is a polynomial of the form `F(Z) = α₀Z + α₁Z^p + α₂Z^{p²} + ⋯ + αₙZ^{pⁿ}`
(`αᵢ ∈ 𝔽_p`); these are the polynomials that satisfy `f(A + B) = f(A) + f(B)` for all
`A, B ∈ 𝔽_p[Z]`. Can we Diophantinely define the additive polynomials? (The notes add Demeyer's
remark that Pheidas's proposed predicate does not work.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import MathlibExt.Logic.Diophantine

@[expose] public section

namespace MathlibExt.ModelTheory.AdditivePolynomialsDiophantineAIMLogicProblem118Wanted

/-!
Source: AIM workshop Extensions of Hilbert's tenth problem, problem list moderated by B. Poonen and
T. Scanlon, notes by J. Demeyer, Question 5 (T. Pheidas),
https://aimath.org/WWN/hilberts10th/hilberts10th.pdf. UnsolvedMath record UM-20002342
(`AIM-LOGIC-0118`), dataset ulamai/UnsolvedMath v1.8.0.

The additive polynomials are the list's `α₀Z + α₁Z^p + ⋯ + αₙZ^{pⁿ}` with `αᵢ ∈ 𝔽_p`, that is the
polynomials in `𝔽_p[Z]` all of whose monomials have an exponent that is a power of `p` (the zero
polynomial included). "Diophantinely define" is `MetaMathlibExt.IsDiophantineSet` over `𝔽_p[Z]` with
coefficients in `𝔽_p[Z]`, so the constant `Z` is available (Demeyer's Diophantine interpretation,
§1, uses only `+, ·, 0, 1, Z`; without `Z` the set is not definable: `Z ↦ Z + 1` is a ring
automorphism of `𝔽_p[Z]` that moves `Z` off the set). The target is the positive answer for every
prime `p`.
-/

open Polynomial MetaMathlibExt

/-- The additive polynomials of `𝔽_p[Z]`: `α₀Z + α₁Z^p + ⋯ + αₙZ^{pⁿ}` with `αᵢ ∈ 𝔽_p`, i.e. the
polynomials whose monomials all have exponents that are powers of `p` (the zero polynomial
included). -/
def additivePolynomials (p : ℕ) : Set (ZMod p)[X] :=
  {F | ∀ k ∈ F.support, ∃ i : ℕ, k = p ^ i}

/-- AIM Extensions of Hilbert's tenth problem, Question 5 (Pheidas), positive answer: for every
prime `p` the additive polynomials are Diophantine over `𝔽_p[Z]` (existentially definable by
polynomial equations with coefficients in `𝔽_p[Z]`, so with the constant `Z`). -/
def additivePolynomialsDiophantine : Prop :=
  ∀ p : ℕ, p.Prime → IsDiophantineSet (RingHom.id (ZMod p)[X]) (additivePolynomials p)

/--
Resolved true: Demeyer proves that every recursively enumerable subset of `𝔽_q[Z]^k` is Diophantine
over `𝔽_q[Z]`. The instance `q = p`, `k = 1` applies to the additive polynomials because they form a
decidable, hence recursively enumerable, subset of `𝔽_p[Z]`: a polynomial is additive exactly when
every exponent of a monomial with nonzero coefficient is a power of `p`, a finite check on its
coefficient list. Source: AIM workshop Extensions of Hilbert's tenth problem, problem list moderated
by B. Poonen and T. Scanlon, notes by J. Demeyer, Question 5 (T. Pheidas),
https://aimath.org/WWN/hilberts10th/hilberts10th.pdf; resolution: J. Demeyer, Recursively enumerable
sets of polynomials over a finite field are Diophantine, Invent. Math. 170 (2007), 655-670, abstract
and Section 5: every recursively enumerable subset of F_q[Z]^k (any prime power q, any k ≥ 1) is
Diophantine over F_q[Z]; §1: the Diophantine interpretation of F_q[W, Z] over F_q[Z] uses the
language {+, ·, 0, 1, Z}, https://doi.org/10.1007/s00222-007-0078-6.
-/
public theorem_wanted additivePolynomialsDiophantine_holds : additivePolynomialsDiophantine

end MathlibExt.ModelTheory.AdditivePolynomialsDiophantineAIMLogicProblem118Wanted
