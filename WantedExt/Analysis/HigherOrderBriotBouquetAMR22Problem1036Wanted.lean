/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Solutions of F(y⁽ⁿ⁾, y) = 0 outside the class W (Hayman–Lingham Problem 1.36)

W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Problem 1.36 (A. Eremenko):
let `F` be a polynomial in two variables and `y` a meromorphic solution of `F(y⁽ⁿ⁾, y) = 0`; must
`y` be an elliptic function, a rational function of exponentials, or a rational function?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

namespace MathlibExt.Analysis.HigherOrderBriotBouquetAMR22Problem1036Wanted

/-!
Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary
Edition (2019), arXiv:1809.07200, Problem 1.36 (A. Eremenko). UnsolvedMath record UM-02301036
(`AMR-022-1036`), dataset ulamai/UnsolvedMath v1.8.0.

'A rational function of exponentials' is read as Eremenko–Liao–Ng's class `W` (doubly periodic
functions, rational functions, and `R(e^{az})` with `R` rational), the reading of the list's Update
1.36 ('neither rational, nor a rational function of an exponential'). The target restricts the claim
to entire solutions, which are meromorphic, so its refutation also refutes the claim for meromorphic
solutions. `n ≥ 1` and `F ≠ 0` (for `n = 0` or `F = 0` every function is a solution). For an entire
`y` the identities defining `W` are required away from the zeros of the denominator; `a ≠ 0` keeps
those zeros discrete (`a = 0` gives constants, already rational). Eremenko–Liao–Ng's positive result
(every meromorphic solution with at least one pole lies in `W`) is not formalized.
-/

/-- The class `W` of Eremenko–Liao–Ng, for an entire function `y`: `y` is doubly periodic
(two `ℝ`-linearly independent periods), or a rational function `P/Q`, or `R(e^{az})` for a
rational `R = P/Q` and `a ≠ 0`; the identities are required away from the (finitely many, resp.
discrete) zeros of the denominator. -/
def IsInClassW (y : ℂ → ℂ) : Prop :=
  (∃ ω₁ ω₂ : ℂ, LinearIndependent ℝ ![ω₁, ω₂] ∧ ∀ z, y (z + ω₁) = y z ∧ y (z + ω₂) = y z) ∨
    (∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ ∀ z, Q.eval z ≠ 0 → y z = P.eval z / Q.eval z) ∨
    ∃ a : ℂ, a ≠ 0 ∧ ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ ∀ z, Q.eval (Complex.exp (a * z)) ≠ 0 →
      y z = P.eval (Complex.exp (a * z)) / Q.eval (Complex.exp (a * z))

/-- Eremenko's question (Hayman–Lingham Problem 1.36), for entire solutions: for every `n ≥ 1` and
every nonzero polynomial `F` in two variables, every entire solution `y` of `F(y⁽ⁿ⁾, y) = 0` is an
elliptic function, a rational function of an exponential, or a rational function (class `W`). -/
def entireSolutionsInClassW : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ F : MvPolynomial (Fin 2) ℂ, F ≠ 0 → ∀ y : ℂ → ℂ, Differentiable ℂ y →
    (∀ z, MvPolynomial.eval ![iteratedDeriv n y z, y z] F = 0) → IsInClassW y

/--
Resolved false: Eremenko, Liao and Ng note that `y‴ = y` (`n = 3`, `F = X₀ - X₁`) has solutions
outside `W`, for instance `y(z) = e^z + e^{ωz}` with `ω = e^{2πi/3}`, an entire solution that is not
rational, not doubly periodic, and not `R(e^{az})`; the list's Update 1.36 records the problem as
solved by this example. Source: W. K. Hayman and E. F. Lingham, Research Problems in Function
Theory, Fiftieth Anniversary Edition (2019), arXiv:1809.07200, Problem 1.36 (A. Eremenko);
resolution: A. Eremenko, L. Liao and T. W. Ng, Meromorphic solutions of higher order Briot–Bouquet
differential equations, Math. Proc. Cambridge Philos. Soc. 146 (2009), no. 1, 197-206,
arXiv:0707.2898; recorded in Hayman–Lingham, Update 1.36, §1: W is the class of doubly periodic
functions, rational functions and R(e^{az}) with R rational; Theorem 1: every meromorphic solution
with at least one pole belongs to W; 'It is not true that all meromorphic solutions of higher order
Briot–Bouquet equations belong to W, a simple counterexample is y‴ = y'; Update 1.36: they 'give an
example of an entire solution which is neither rational, nor a rational function of an exponential',
https://arxiv.org/abs/0707.2898.
-/
public theorem_wanted entireSolutionsInClassW_refuted : ¬ entireSolutionsInClassW

end MathlibExt.Analysis.HigherOrderBriotBouquetAMR22Problem1036Wanted
