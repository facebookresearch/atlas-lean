/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Analytic derivatives of multivariate polynomials

The formal partial derivatives give the Fréchet derivative of evaluation.
Along a curve with polynomial velocity, the chain rule identifies the analytic
derivative with evaluation of Mathlib's existing `mkDerivation`. Over the reals,
this is the polynomial Lie derivative; no new derivation structure is needed.
Within-set derivatives retain their domain and allow singleton time sets.

The polynomial Lie derivative convention is equation (4) in Ghorbal, Sogokon
and Platzer, *A Hierarchy of Proof Rules for Checking Positive Invariance of
Algebraic and Semi-Algebraic Sets*, §2:
https://logic.kastel.kit.edu/pub/alginv-bench-long.pdf.
-/

@[expose] public section

namespace MvPolynomial

/-- In finitely many variables over a commutative semiring, the derivation
sending `X i` to `F i` is the sum of the formal partial derivatives multiplied
by those polynomial values. -/
theorem mkDerivation_eq_sum_pderiv {σ R : Type*} [Fintype σ] [CommSemiring R]
    (F : σ → MvPolynomial σ R) (p : MvPolynomial σ R) :
    mkDerivation R F p = ∑ i, pderiv i p * F i := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp [Derivation.leibniz, mkDerivation_X, hp, Pi.single_apply,
      mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm, mul_comm]

variable {σ 𝕜 : Type*} [Fintype σ] [NontriviallyNormedField 𝕜]

/-- Evaluation of a polynomial in finitely many variables over a nontrivially
normed field has Fréchet derivative equal to the finite sum of coordinate
projections scaled by the evaluated formal partial derivatives. -/
theorem hasFDerivAt_eval (p : MvPolynomial σ 𝕜) (x : σ → 𝕜) :
    HasFDerivAt (𝕜 := 𝕜) (fun y => eval y p)
      (∑ i, eval x (pderiv i p) • ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ => 𝕜) i) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
    convert! hasFDerivAt_const (𝕜 := 𝕜) c x using 1
    · ext y; simp
    · ext v; simp
  | add p q hp hq =>
    convert! hp.add hq using 1
    · ext y; simp
    · ext v; simp [add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    convert! hp.mul (hasFDerivAt_apply (𝕜 := 𝕜) j x) using 1
    · ext y; simp
    · ext v
      simp [Pi.single_apply, apply_ite, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum, mul_left_comm, mul_comm]

/-- The formal gradient of a polynomial in finitely many variables gives its
analytic derivative along a curve with a supplied within-set velocity. The
parameter set is arbitrary; no unique-differentiability assumption is needed. -/
theorem hasDerivWithinAt_eval (p : MvPolynomial σ 𝕜) {u : 𝕜 → σ → 𝕜}
    {v : σ → 𝕜} {s : Set 𝕜} {t : 𝕜} (hu : HasDerivWithinAt u v s t) :
    HasDerivWithinAt (fun r => eval (u r) p)
      (∑ i, eval (u t) (pderiv i p) * v i) s t := by
  convert! (hasFDerivAt_eval p (u t)).comp_hasDerivWithinAt t hu using 1
  simp

omit [Fintype σ] in
/-- Along a curve whose supplied within-set velocity is the evaluation of a
polynomial field `F`, the analytic derivative of evaluating `p` is evaluation
of `mkDerivation 𝕜 F p`. Variables are finite, the coefficient/parameter field
is nontrivially normed, and the time set is arbitrary, including singletons. -/
theorem hasDerivWithinAt_eval_mkDerivation [Finite σ] (p : MvPolynomial σ 𝕜)
    (F : σ → MvPolynomial σ 𝕜) {u : 𝕜 → σ → 𝕜} {s : Set 𝕜} {t : 𝕜}
    (hu : HasDerivWithinAt u (fun i => eval (u t) (F i)) s t) :
    HasDerivWithinAt (fun r => eval (u r) p)
      (eval (u t) (mkDerivation 𝕜 F p)) s t := by
  let := Fintype.ofFinite σ
  simpa only [mkDerivation_eq_sum_pderiv, map_sum, map_mul] using
    hasDerivWithinAt_eval p hu

end MvPolynomial
