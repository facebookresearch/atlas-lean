/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.Analysis.ODE.RegularSublevel
public import MathlibExt.Analysis.ODE.CompactSublevel

/-!
# Forward global solutions in compact regular sublevels

Regular weakly inward boundaries give finite-interval invariance. Compactness
then rules out finite forward escape using the existing continuation theorem.
No global solution or global Lipschitz estimate is assumed.

Sources: Teschl, *Ordinary Differential Equations and Dynamical Systems*, §2.6,
Corollaries 2.15–2.16, https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf;
Ghorbal–Sogokon–Platzer, *A Hierarchy of Proof Rules for Checking Positive
Invariance of Algebraic and Semi-Algebraic Sets*, §5.3,
https://logic.kastel.kit.edu/pub/alginv-bench-long.pdf.
-/

@[expose] public section

open Set

/-- In a finite-dimensional real normed space, suppose `h : E → ℝ` is
everywhere differentiable, `{x | h x ≤ 0}` is compact, and the vector field
`f` is locally Lipschitz. If `fderiv ℝ h x` is nonzero and its value on `f x`
is nonpositive at every zero of `h`, then through each `x₀` with `h x₀ ≤ 0`
at any initial time `a` there is a forward global solution in this sublevel.
The solution has ordinary derivative `f (x t)` at every time in `Ici a`,
including `a`; confinement is asserted only for these times. -/
theorem Nagumo.exists_forward_solution_of_compact_regular_sublevel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → E} (hf : LocallyLipschitz f) {h : E → ℝ} (hh : Differentiable ℝ h)
    (hK : IsCompact {x | h x ≤ 0})
    (hreg : ∀ x, h x = 0 → fderiv ℝ h x ≠ 0)
    (hin : ∀ x, h x = 0 → fderiv ℝ h x (f x) ≤ 0)
    (a : ℝ) {x₀ : E} (h₀ : h x₀ ≤ 0) :
    ∃ x : ℝ → E, x a = x₀ ∧ (∀ t ∈ Ici a, h (x t) ≤ 0) ∧
      ∀ t ∈ Ici a, HasDerivAt x (f (x t)) t := by
  apply MathlibExt.Analysis.ODE.exists_forward_solution_of_compact_invariant hf hK a x₀
  intro b _ x hx hd
  exact Nagumo.mapsTo_sublevel_of_fderiv_nonpos hf hh hreg hin hd (by rwa [hx])
