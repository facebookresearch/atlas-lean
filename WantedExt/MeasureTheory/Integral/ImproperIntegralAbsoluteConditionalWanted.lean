/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

open MeasureTheory Filter Set

namespace MathlibExt.MeasureTheory.Integral.ImproperIntegralAbsoluteConditionalWanted

/-!
Conditional convergence of an improper integral on `[a, ∞)`: every finite
truncation is interval-integrable and the proper integrals over `[a, b]`
converge as `b → ∞`, but `f` is not Lebesgue integrable on `(a, ∞)`.

Sources:
- Mathlib `docs/undergrad.yaml`, section "Single Variable Real Analysis / Integration",
  entry "absolute vs conditional convergence of improper integrals"
  (currently missing: external URL, no Mathlib declaration).
- T. Apostol, *Mathematical Analysis*, 2nd ed., §10.23 (absolute and conditional
  convergence of improper integrals).
- https://en.wikipedia.org/wiki/Conditional_convergence
-/

/-- **Conditional convergence of the Dirichlet integral on $[1, \infty)$.** The function
$x \mapsto \sin x / x$ is interval integrable on $[1, b]$ for every real $b \ge 1$, the integrals
$\int_1^b \frac{\sin x}{x}\,dx$ converge to a real limit as $b \to \infty$, and $\sin x / x$ is
not Lebesgue integrable on $(1, \infty)$.

Sources:
- Mathlib `docs/undergrad.yaml`, section "Single Variable Real Analysis / Integration",
  entry "absolute vs conditional convergence of improper integrals"
  (currently missing).
- W. Rudin, *Principles of Mathematical Analysis*, 3rd ed., Ch. 11, Exercise 15
  (conditional convergence of the sine integral).
-/
public theorem_wanted dirichlet_integral_conditionally_convergent :
    (∀ b : ℝ, 1 ≤ b → IntervalIntegrable (fun x ↦ Real.sin x / x) volume 1 b) ∧
      (∃ L : ℝ, Tendsto (fun b ↦ ∫ x in (1 : ℝ)..b, Real.sin x / x) atTop (nhds L)) ∧
      ¬ Integrable (fun x ↦ Real.sin x / x) (volume.restrict (Ioi 1))

end MathlibExt.MeasureTheory.Integral.ImproperIntegralAbsoluteConditionalWanted
