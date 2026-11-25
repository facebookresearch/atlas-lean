/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Envelope kernel for value functions

If `f ≤ g` on a neighborhood of `x₀`, the two functions agree at `x₀`, and both are Fréchet
differentiable at `x₀`, then their derivatives at `x₀` agree: `g - f` has a local minimum at `x₀`,
so its derivative vanishes there (Fermat). This is the envelope argument for value functions, with
the roles of `f` and `g` depending on the direction of optimization:

* for a supremum value function (Hotelling's lemma, profit), `f` is the objective evaluated at an
  optimizer fixed at `x₀` and `g` is the value function;
* for an infimum value function (Shephard's lemma, expenditure), `f` is the value function and `g`
  is the objective evaluated at an optimizer fixed at `x₀`.

## Main results

* `Economics.hasFDerivAt_eq_of_eventually_le_of_eq`: derivatives agree under one-sided touching.
-/

@[expose] public section

open Filter Topology

namespace Economics

/-- **Envelope kernel.** If `f ≤ g` near `x₀`, with equality at `x₀`, and both
are differentiable at `x₀`, then their derivatives agree. -/
theorem hasFDerivAt_eq_of_eventually_le_of_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : E → ℝ} {x₀ : E} {f' g' : E →L[ℝ] ℝ}
    (hle : ∀ᶠ x in 𝓝 x₀, f x ≤ g x) (heq : f x₀ = g x₀)
    (hf : HasFDerivAt f f' x₀) (hg : HasFDerivAt g g' x₀) : f' = g' := by
  have hmin : IsLocalMin (g - f) x₀ := by
    show ∀ᶠ x in 𝓝 x₀, (g - f) x₀ ≤ (g - f) x
    filter_upwards [hle] with x hx
    simp only [Pi.sub_apply]
    rw [heq, sub_self]
    exact sub_nonneg.mpr hx
  have hzero := hmin.hasFDerivAt_eq_zero (hg.sub hf)
  exact (sub_eq_zero.mp hzero).symm

end Economics
