/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Semicontinuity.Basic

@[expose] public section

namespace MathlibExt.Analysis.ScottishBook184Wanted

/-- A function `φ` on the plane is subharmonic if it is upper
semicontinuous and satisfies the sub-mean-value property on every
circle. -/
def IsSubharmonic (φ : ℝ × ℝ → ℝ) : Prop :=
  UpperSemicontinuous φ ∧ ∀ (p : ℝ × ℝ) (r : ℝ), 0 < r →
    φ p ≤ (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      φ (p.1 + r * Real.cos θ, p.2 + r * Real.sin θ)

/-- The partial derivatives `φ x`, `φ xx`, `φ y`, `φ yy` exist at every
point of the plane. -/
def HasSecondPartialDerivatives (φ : ℝ × ℝ → ℝ) : Prop :=
  ∀ p : ℝ × ℝ,
    DifferentiableAt ℝ (fun s => φ (s, p.2)) p.1 ∧
    DifferentiableAt ℝ (fun t => deriv (fun s => φ (s, p.2)) t) p.1 ∧
    DifferentiableAt ℝ (fun s => φ (p.1, s)) p.2 ∧
    DifferentiableAt ℝ (fun t => deriv (fun s => φ (p.1, s)) t) p.2

/--
Saks's Problem 184 from the Scottish Book, affirmative: if a subharmonic
function `φ` has the partial derivatives `φ xx` and `φ yy` everywhere,
then its Laplacian `Δ φ = φ xx + φ yy` is nonnegative everywhere. The
point is that this is not immediate outside the (dense) set where the
second derivatives are continuous. Source: S. Saks, Problem 184 of the
Scottish Book; solved by A. Eremenko, "A problem of Stanislaw Saks",
Mat. Stud. 52 (2019), 173-175 (arXiv:1911.09530). See the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted saks184_subharmonic_laplacian_nonneg :
    ∀ φ : ℝ × ℝ → ℝ, IsSubharmonic φ → HasSecondPartialDerivatives φ →
      ∀ p : ℝ × ℝ, 0 ≤ deriv (fun t => deriv (fun s => φ (s, p.2)) t) p.1 +
        deriv (fun t => deriv (fun s => φ (p.1, s)) t) p.2

end MathlibExt.Analysis.ScottishBook184Wanted
