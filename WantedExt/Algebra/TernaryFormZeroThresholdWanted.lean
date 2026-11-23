/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Algebra.TernaryFormZeroThresholdWanted

/-!
# Zero thresholds for positive semidefinite ternary forms

Source report: Real Algebraic Geometry With A View Toward Systems Control and
Free Positivity (2014), Oberwolfach Reports, DOI 10.4171/owr/2014/17,
pp. 977--1045; curated item [OWR-12975-007].

Clause inventory from the source question, each encoded in the proposition below:
(a) quantifier domain k : ℕ with side condition 3 ≤ k;
(b) real base field ℝ for coefficients and points;
(c) ternary: polynomials in Fin 3 variables;
(d) degree: homogeneous of degree 2 * k;
(e) positive semidefinite: nonnegative at every real point;
(f) projective zeros: nonzero real vectors annihilating p, identified up to
nonzero real scaling;
(g) count: more than k ^ 2 such projective zeros, witnessed by one shared
family over Fin (k ^ 2 + 1) of pairwise non-proportional zeros;
(h) factorisation shape p = h ^ 2 * q with h q ternary real polynomials;
(i) h indefinite: strictly positive at some real point and strictly negative
at some real point;
(j) threshold inequality with endpoint k ^ 2 + 1, in unfolded form: for every
k ≥ 3 there is a form as above with more than k ^ 2 projective zeros that does
not factor as above. The least-threshold object is represented by this
unfolded failure-at-k^2 formulation, the closest Mathlib-grounded reading.
-/

/-- Zero-threshold question for positive semidefinite ternary forms
([OWR-12975-007]; Real Algebraic Geometry With A View Toward Systems Control
and Free Positivity (2014), Oberwolfach Reports, DOI 10.4171/owr/2014/17,
pp. 977--1045). Unfolded reading of Is the threshold at least k ^ 2 + 1 for
every k ≥ 3: for each k ≥ 3 there exists a positive semidefinite real ternary
form of degree 2 * k with more than k ^ 2 projective zeros that is not
h ^ 2 * q for indefinite h. Posed as an open question in the source; resolved
affirmatively (see `conjecture_holds` below). -/
def conjecture : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∃ p : MvPolynomial (Fin 3) ℝ,
      p.IsHomogeneous (2 * k) ∧
      (∀ x : Fin 3 → ℝ, 0 ≤ p.eval x) ∧
      (∃ v : Fin (k ^ 2 + 1) → (Fin 3 → ℝ),
        (∀ i : Fin (k ^ 2 + 1), ∃ t : Fin 3, v i t ≠ 0) ∧
        (∀ i : Fin (k ^ 2 + 1), p.eval (v i) = 0) ∧
        (∀ i : Fin (k ^ 2 + 1), ∀ j : Fin (k ^ 2 + 1), i ≠ j →
          ¬ ∃ c : ℝ, c ≠ 0 ∧ ∀ t : Fin 3, v i t = c * v j t)) ∧
      ¬ ∃ h : MvPolynomial (Fin 3) ℝ, ∃ q : MvPolynomial (Fin 3) ℝ,
        p = h ^ 2 * q ∧
        (∃ a : Fin 3 → ℝ, 0 < h.eval a) ∧
        (∃ b : Fin 3 → ℝ, h.eval b < 0)

/--
Resolved true: Resolved affirmatively: Brugallé, Degtyarev, Itenberg and Mangolte (Real
algebraic curves with large finite number of real points, Eur. J. Math. 5 (2019) 686-711,
arXiv:1807.03992, Theorem 4.8 with g = 0) construct, for every k >= 3, a real plane curve of
degree 2k with exactly k^2 + 1 real points and no others. Its equation has constant sign, so up
to sign it is a psd ternary form with k^2 + 1 zeros, and finitely many zeros rule out a
factorization h^2 q with h indefinite. Source: E. Brugallé, A. Degtyarev, I. Itenberg, F.
Mangolte, Real algebraic curves with large finite number of real points, Eur. J. Math. 5 (2019)
686-711, arXiv:1807.03992, https://doi.org/10.1007/s40879-019-00324-9. Moved from
`OpenConjectures/Algebra/TernaryFormZeroThreshold`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Algebra.TernaryFormZeroThresholdWanted
