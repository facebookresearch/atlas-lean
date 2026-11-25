/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Periodic
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Meromorphic.Basic

/-!
# Meromorphic functions at modular cusps
-/

@[expose] public section

open scoped UpperHalfPlane MatrixGroups

namespace ModularFunction

/-- **Meromorphy at infinity.** A function $f \colon \mathbb{H} \to \mathbb{C}$ on the upper
half-plane is meromorphic at infinity when there are a positive integer $N$ and a function
$g \colon \mathbb{C} \to \mathbb{C}$ meromorphic at $0$ such that
$f(\tau) = g(e^{2 \pi i \tau / N})$ for every $\tau \in \mathbb{H}$ with sufficiently large
imaginary part. -/
def IsMeromorphicAtInfty (f : ℍ → ℂ) : Prop :=
  ∃ (N : ℕ) (_ : 0 < N) (g : ℂ → ℂ), MeromorphicAt g 0 ∧
    ∀ᶠ τ in UpperHalfPlane.atImInfty,
      f τ = g (Function.Periodic.qParam (N : ℝ) (τ : ℂ))

/-- **Meromorphy at the cusps.** A function $f \colon \mathbb{H} \to \mathbb{C}$ on the upper
half-plane is meromorphic at the cusps when, for every $\gamma \in \mathrm{SL}(2, \mathbb{Z})$,
the function $\tau \mapsto f(\gamma \cdot \tau)$ is meromorphic at infinity, where $\gamma$ acts
on $\mathbb{H}$ by Möbius transformations. -/
def IsMeromorphicAtCusps (f : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), IsMeromorphicAtInfty (fun τ ↦ f (γ • τ))

theorem IsMeromorphicAtCusps.at_infty {f : ℍ → ℂ} (hf : IsMeromorphicAtCusps f) :
    IsMeromorphicAtInfty f := by
  simpa using hf 1

end ModularFunction
