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

/-- Comparison test for improper integrals: a nonnegative function dominated on
`[a, ∞)` by an improper-integrable function is itself improper-integrable.

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

/-- Limit comparison test for improper integrals: two eventually strictly positive
functions whose ratio tends to a nonzero limit are improper-integrable together.

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
