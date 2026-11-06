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

namespace MathlibExt.MeasureTheory.Integral.ImproperIntegralComparisonWanted

/-- **Comparison test for improper integrals.** Let $a \in \mathbb{R}$ and let
$f, g : \mathbb{R} \to \mathbb{R}$ be interval integrable on $[a, b]$ for every $b \ge a$, with
$0 \le f(x) \le g(x)$ for all $x \ge a$. If $\int_a^b g(x)\,dx$ converges to a real limit as
$b \to \infty$, then $\int_a^b f(x)\,dx$ also converges to a real limit as $b \to \infty$.

Sources:
- Mathlib `docs/undergrad.yaml`, section "Single Variable Real Analysis / Integration",
  entry "comparison test for improper integrals" (currently missing).
- https://mathbooks.unl.edu/Calculus/sec-5-11-comparison.html
-/
public theorem_wanted improper_integral_comparison_test {f g : ℝ → ℝ} {a : ℝ}
    (hfg : ∀ x : ℝ, a ≤ x → 0 ≤ f x ∧ f x ≤ g x)
    (hfi : ∀ b : ℝ, a ≤ b → IntervalIntegrable f volume a b)
    (hgi : ∀ b : ℝ, a ≤ b → IntervalIntegrable g volume a b)
    (hg : ∃ L : ℝ, Tendsto (fun b ↦ ∫ x in a..b, g x) atTop (nhds L)) :
    ∃ L : ℝ, Tendsto (fun b ↦ ∫ x in a..b, f x) atTop (nhds L)

/-- **Limit comparison test for improper integrals.** Let $a, L \in \mathbb{R}$
with $L \ne 0$, and let $f, g : \mathbb{R} \to \mathbb{R}$ be interval integrable on $[a, b]$ for
every $b \ge a$, with $f(x) > 0$ and $g(x) > 0$ for all $x \ge a$. If $f(x) / g(x) \to L$ as
$x \to \infty$, then $\int_a^b f(x)\,dx$ converges to a real limit as $b \to \infty$ if and
only if $\int_a^b g(x)\,dx$ converges to a real limit as $b \to \infty$.

Sources:
- Mathlib `docs/undergrad.yaml`, section "Single Variable Real Analysis / Integration",
  entry "comparison test for improper integrals" (currently missing).
- T. Apostol, *Mathematical Analysis*, 2nd ed., §10.23 (limit comparison test).
-/
public theorem_wanted improper_integral_limit_comparison_test
    {f g : ℝ → ℝ} {a : ℝ} {L : ℝ}
    (hf : ∀ x : ℝ, a ≤ x → 0 < f x)
    (hg : ∀ x : ℝ, a ≤ x → 0 < g x)
    (hfi : ∀ b : ℝ, a ≤ b → IntervalIntegrable f volume a b)
    (hgi : ∀ b : ℝ, a ≤ b → IntervalIntegrable g volume a b)
    (hL : L ≠ 0)
    (hlim : Tendsto (fun x ↦ f x / g x) atTop (nhds L)) :
    (∃ L' : ℝ, Tendsto (fun b ↦ ∫ x in a..b, f x) atTop (nhds L')) ↔
      ∃ L' : ℝ, Tendsto (fun b ↦ ∫ x in a..b, g x) atTop (nhds L')

end MathlibExt.MeasureTheory.Integral.ImproperIntegralComparisonWanted
