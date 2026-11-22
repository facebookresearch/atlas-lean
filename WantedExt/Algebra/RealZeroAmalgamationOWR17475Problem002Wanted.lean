/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The real zero amalgamation conjecture (Oberwolfach Reports 12/2020)

Oberwolfach workshop Real Algebraic Geometry with a View Toward Hyperbolic Programming and Free
Probability (2020), M. Schweighofer: real zero polynomials `p ∈ ℝ[x, y]` and `q ∈ ℝ[x, z]` of degree
at most `d` with `p(x, 0) = q(x, 0)` have a real zero amalgam `r ∈ ℝ[x, y, z]` of degree at most
`d`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Basic.Complex.Basic

@[expose] public section

namespace MathlibExt.Algebra.RealZeroAmalgamationOWR17475Problem002Wanted

/-!
Source: M. Schweighofer, Spectrahedral relaxations of hyperbolicity cones, in Real Algebraic
Geometry with a View Toward Hyperbolic Programming and Free Probability, Oberwolfach Reports 17
(2020), no. 12, pp. 652-654, real zero amalgamation conjecture (RZAC), p. 653, DOI
10.4171/OWR/2020/12. UnsolvedMath record UM-30004437 (`OWR-17475-002`), dataset ulamai/UnsolvedMath
v1.8.0.

The blocks `x, y, z` of `ℓ, m, n` variables are indexed by `Fin ℓ ⊕ Fin m`, `Fin ℓ ⊕ Fin n` and `Fin
ℓ ⊕ (Fin m ⊕ Fin n)`. A polynomial `p` is real zero, as in the source, when `p(λa) = 0` for `a` real
and `λ` complex forces `λ ∈ ℝ` (the evaluation uses the complexification of `p`); taking `a = 0`
gives `p(0) ≠ 0`. Degree means total degree, and `p(x, 0)`, `r(x, y, 0)`, `r(x, 0, z)` are the
substitutions of `0` for a block of variables.
-/

open MvPolynomial

/-- A real polynomial `p` in the variables `σ` is a *real zero polynomial* if for every real point
`a : σ → ℝ` and every complex number `t`, `p (t • a) = 0` forces `t` to be real. (Taking `a = 0`
shows `p 0 ≠ 0`.) -/
def IsRealZero {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  ∀ (a : σ → ℝ) (t : ℂ), eval (fun i => t * (a i : ℂ)) (map Complex.ofRealHom p) = 0 → t.im = 0

/-- The substitution `p ↦ p (x, 0)` from `ℝ[x, y]` to `ℝ[x]` (the `y`-block set to zero). -/
noncomputable def restrictShared (ℓ m : ℕ) :
    MvPolynomial (Fin ℓ ⊕ Fin m) ℝ →ₐ[ℝ] MvPolynomial (Fin ℓ) ℝ :=
  aeval (Sum.elim X fun _ => 0)

/-- The substitution `r ↦ r (x, y, 0)` from `ℝ[x, y, z]` to `ℝ[x, y]` (`z`-block set to zero). -/
noncomputable def zeroThirdBlock (ℓ m n : ℕ) :
    MvPolynomial (Fin ℓ ⊕ (Fin m ⊕ Fin n)) ℝ →ₐ[ℝ] MvPolynomial (Fin ℓ ⊕ Fin m) ℝ :=
  aeval (Sum.elim (fun i => X (Sum.inl i)) (Sum.elim (fun j => X (Sum.inr j)) fun _ => 0))

/-- The substitution `r ↦ r (x, 0, z)` from `ℝ[x, y, z]` to `ℝ[x, z]` (`y`-block set to zero). -/
noncomputable def zeroSecondBlock (ℓ m n : ℕ) :
    MvPolynomial (Fin ℓ ⊕ (Fin m ⊕ Fin n)) ℝ →ₐ[ℝ] MvPolynomial (Fin ℓ ⊕ Fin n) ℝ :=
  aeval (Sum.elim (fun i => X (Sum.inl i)) (Sum.elim (fun _ => 0) fun k => X (Sum.inr k)))

/-- The real zero amalgamation conjecture (M. Schweighofer, Oberwolfach Report 12/2020, p. 653):
for blocks `x, y, z` of `ℓ, m, n` variables and every `d`, if `p ∈ ℝ[x, y]` and `q ∈ ℝ[x, z]` are
real zero polynomials of degree at most `d` with `p (x, 0) = q (x, 0)`, then some real zero
polynomial `r ∈ ℝ[x, y, z]` of degree at most `d` satisfies `r (x, y, 0) = p` and
`r (x, 0, z) = q`. -/
def realZeroAmalgamationConjecture : Prop :=
  ∀ (ℓ m n d : ℕ) (p : MvPolynomial (Fin ℓ ⊕ Fin m) ℝ) (q : MvPolynomial (Fin ℓ ⊕ Fin n) ℝ),
    IsRealZero p → IsRealZero q → p.totalDegree ≤ d → q.totalDegree ≤ d →
      restrictShared ℓ m p = restrictShared ℓ n q →
        ∃ r : MvPolynomial (Fin ℓ ⊕ (Fin m ⊕ Fin n)) ℝ, IsRealZero r ∧ r.totalDegree ≤ d ∧
          zeroThirdBlock ℓ m n r = p ∧ zeroSecondBlock ℓ m n r = q

/--
Resolved false: Sawall and Schweighofer (Example 6.1) give cubic real zero polynomials `p ∈ ℝ[x, y]`
and `q ∈ ℝ[x, z]`, with `ℓ = 6` shared variables and one variable each in `y` and `z`, such that
`p(x, 0) = q(x, 0)` but no real zero polynomial `r ∈ ℝ[x, y, z]` of any degree has `r(x, y, 0) = p`
and `r(x, 0, z) = q`; in particular none of degree at most `3`. Source: M. Schweighofer,
Spectrahedral relaxations of hyperbolicity cones, in Real Algebraic Geometry with a View Toward
Hyperbolic Programming and Free Probability, Oberwolfach Reports 17 (2020), no. 12, pp. 652-654,
real zero amalgamation conjecture (RZAC), p. 653, DOI 10.4171/OWR/2020/12; resolution: D. Sawall and
M. Schweighofer, Amalgamation of real zero polynomials, Indag. Math. (N.S.) 35 (2024), no. 1, 37-59,
DOI 10.1016/j.indag.2023.08.002, arXiv:2305.07403, Section 6, Example 6.1: for the cubic polynomials
p = p_{M1} and q = p_{M2} built from the Poljak-Turzik matroids (ℓ = 6 shared variables, m = n = 1),
p(x + 1, y) and q(x + 1, z) are real zero with p(x + 1, 0) = q(x + 1, 0) but have no real zero
amalgam r of any degree; Section 1: 'In the same preprint of the second author, it was conjectured
that two (compatible) real zero polynomials can always be amalgamated (by a real zero polynomial).
The first author recently disproved this', https://arxiv.org/abs/2305.07403.
-/
public theorem_wanted realZeroAmalgamationConjecture_refuted : ¬ realZeroAmalgamationConjecture

end MathlibExt.Algebra.RealZeroAmalgamationOWR17475Problem002Wanted
