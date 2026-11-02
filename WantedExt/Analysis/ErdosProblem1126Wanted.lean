/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 1126
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Real.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Order.Filter.Basic

@[expose] public section

open Filter

namespace MathlibExt.Analysis.ErdosProblem1126Wanted

/-! Source record `FC-ErdosProblem1126`, ported from FormalConjectures
`ErdosProblems/1126.lean` (`theorem erdos_1126`) and checked against
erdosproblems.com/1126. The `answer(True)` wrapper is dropped. Status:
resolved true (de Bruijn; Jurkat). -/

/-- **Erdős Problem 1126 on almost additive functions.** This is the statement that for every
function $f : \mathbb{R} \to \mathbb{R}$ with $f(x + y) = f(x) + f(y)$ for almost every
$(x, y) \in \mathbb{R}^2$ with respect to Lebesgue measure on $\mathbb{R}^2$, there is a function
$h : \mathbb{R} \to \mathbb{R}$ with $h(x + y) = h(x) + h(y)$ for all $x, y \in \mathbb{R}$ and
$f(x) = h(x)$ for almost every $x \in \mathbb{R}$.

Source: erdosproblems.com/1126 (record FC-ErdosProblem1126). -/
def conjecture : Prop :=
  ∀ (f : ℝ → ℝ),
    (∀ᵐ (p : ℝ × ℝ) ∂(MeasureTheory.volume.prod MeasureTheory.volume),
      f (p.1 + p.2) = f p.1 + f p.2) →
    ∃ h : ℝ → ℝ,
      (∀ x y, h (x + y) = h x + h y) ∧ (∀ᵐ x ∂MeasureTheory.volume, f x = h x)

/--
**Almost additive functions agree almost everywhere with additive functions.** Let
$f : \mathbb{R} \to \mathbb{R}$ satisfy $f(x + y) = f(x) + f(y)$ for almost every
$(x, y) \in \mathbb{R}^2$ with respect to Lebesgue measure on $\mathbb{R}^2$. Then there is a
function $h : \mathbb{R} \to \mathbb{R}$ with $h(x + y) = h(x) + h(y)$ for all
$x, y \in \mathbb{R}$ and $f(x) = h(x)$ for almost every $x \in \mathbb{R}$.

Source: de Bruijn [dB66] and Jurkat [Ju65], independently, per
erdosproblems.com/1126, https://www.erdosproblems.com/1126. Moved from
`OpenConjectures/Analysis/ErdosProblem1126`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.ErdosProblem1126Wanted
