/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.Analysis.ODE.PolynomialInvariant
public import MathlibExt.Analysis.ODE.CompactSublevel
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Forward global polynomial ODE solutions in compact regular sublevels

Polynomial vector fields are locally Lipschitz. A regular zero level with
nonpositive Lie derivative gives finite-interval invariance; compactness of
the sublevel then gives an actual forward global solution.

Sources: Teschl, *Ordinary Differential Equations and Dynamical Systems*, §2.6,
Corollaries 2.15–2.16, https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf;
Ghorbal–Sogokon–Platzer, *A Hierarchy of Proof Rules for Checking Positive
Invariance of Algebraic and Semi-Algebraic Sets*, §5.3,
https://logic.kastel.kit.edu/pub/alginv-bench-long.pdf.
-/

@[expose] public section

open Set
namespace MvPolynomial

/-- For real polynomials in finitely many variables, suppose the evaluated
sublevel of `p` is compact, its gradient is nonzero on the entire zero set,
and `mkDerivation ℝ F p` evaluates nonpositively there. Through every initial
point satisfying `eval x₀ p ≤ 0` at any initial time `a`, there is a forward
global solution with evaluated polynomial velocity `F`, remaining in this
sublevel for all `t ≥ a`. Its ordinary derivative is supplied at `a` as well. -/
theorem exists_forward_solution_of_compact_sublevel {σ : Type*} [Finite σ]
    (F : σ → MvPolynomial σ ℝ) (p : MvPolynomial σ ℝ)
    (hK : IsCompact {x | eval x p ≤ 0})
    (hreg : ∀ x, eval x p = 0 → ∃ i, eval x (pderiv i p) ≠ 0)
    (hin : ∀ x, eval x p = 0 → eval x (mkDerivation ℝ F p) ≤ 0)
    (a : ℝ) {x₀ : σ → ℝ} (h₀ : eval x₀ p ≤ 0) :
    ∃ x : ℝ → σ → ℝ, x a = x₀ ∧ (∀ t ∈ Ici a, eval (x t) p ≤ 0) ∧
      ∀ t ∈ Ici a, HasDerivAt x (fun i => eval (x t) (F i)) t := by
  classical
  let := Fintype.ofFinite σ
  have hF : ContDiff ℝ 1 (fun x i => eval x (F i)) :=
    contDiff_pi.mpr (fun i => (AnalyticOnNhd.eval_mvPolynomial (F i)).contDiff)
  apply MathlibExt.Analysis.ODE.exists_forward_solution_of_compact_invariant
    hF.locallyLipschitz hK a x₀
  intro b _ x hx hd
  exact mapsTo_sublevel_of_mkDerivation_nonpos F p hreg hin hd (by rwa [hx])

end MvPolynomial
