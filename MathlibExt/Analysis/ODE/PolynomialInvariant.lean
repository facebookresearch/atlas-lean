/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.Analysis.ODE.RegularSublevel
public import MathlibExt.Analysis.Calculus.MvPolynomial
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Polynomial regular-sublevel invariance

The gradient test makes zero a regular value; nonpositive evaluation of the
polynomial Lie derivative gives the inward boundary condition. Polynomial
vector fields are locally Lipschitz, so Nagumo applies to every supplied
solution on a closed interval. This does not assert global existence.

Source: Ghorbal–Sogokon–Platzer, *A Hierarchy of Proof Rules for Checking
Positive Invariance of Algebraic and Semi-Algebraic Sets*, §5.3, p.14,
https://logic.kastel.kit.edu/pub/alginv-bench-long.pdf.
-/

@[expose] public section

open Set
namespace MvPolynomial

/-- For a real polynomial `p` in finitely many variables and a polynomial
vector field `F`, suppose the evaluated gradient is nonzero and the evaluated
Lie derivative `mkDerivation ℝ F p` is nonpositive at every zero of `p`.
A supplied solution whose within-interval velocity on `Icc a b` is
`fun i => eval (u t) (F i)`, initially satisfying `eval (u a) p ≤ 0`,
stays in `{x | eval x p ≤ 0}` throughout that closed interval.
Each constraint requires these hypotheses on its entire zero set. -/
theorem mapsTo_sublevel_of_mkDerivation_nonpos {σ : Type*} [Finite σ]
    (F : σ → MvPolynomial σ ℝ) (p : MvPolynomial σ ℝ)
    (hreg : ∀ x, eval x p = 0 → ∃ i, eval x (pderiv i p) ≠ 0)
    (hin : ∀ x, eval x p = 0 → eval x (mkDerivation ℝ F p) ≤ 0)
    {a b : ℝ} {u : ℝ → σ → ℝ}
    (hu : ∀ t ∈ Icc a b,
      HasDerivWithinAt u (fun i => eval (u t) (F i)) (Icc a b) t)
    (hu₀ : eval (u a) p ≤ 0) : MapsTo u (Icc a b) {x | eval x p ≤ 0} := by
  classical
  let := Fintype.ofFinite σ
  have hF : ContDiff ℝ 1 (fun x i => eval x (F i)) :=
    contDiff_pi.mpr (fun i => (AnalyticOnNhd.eval_mvPolynomial (F i)).contDiff)
  apply Nagumo.mapsTo_sublevel_of_fderiv_nonpos hF.locallyLipschitz
    (fun x => (hasFDerivAt_eval p x).differentiableAt) _ _ hu hu₀
  · intro x hx hzero
    obtain ⟨i, hi⟩ := hreg x hx
    have he := congrArg (fun L : (σ → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) hzero
    rw [(hasFDerivAt_eval p x).fderiv] at he
    apply hi
    simpa [Pi.single_apply] using he
  · intro x hx
    rw [(hasFDerivAt_eval p x).fderiv]
    simpa [mkDerivation_eq_sum_pderiv] using hin x hx

end MvPolynomial
