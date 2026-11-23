/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

namespace MathlibExt.Analysis.Distribution.Dirichlet1DWanted

/--
**Existence for the one-dimensional Dirichlet problem.** Let $f : \mathbb{R} \to \mathbb{R}$ be
continuous on $[0, 1]$. Then there is a twice continuously differentiable function
$u : \mathbb{R} \to \mathbb{R}$ with $u(0) = u(1) = 0$ and $u''(x) = f(x)$ for every
$x \in (0, 1)$.

Sources: Mathlib `docs/undergrad.yaml`, section "Topology" / "Hilbert spaces" /
entry "H^1_0([0,1]) and its application to the one-dimensional Dirichlet problem";
L. Evans, *Partial Differential Equations*, Ch. 6.
-/
public theorem_wanted dirichlet_1d_exists {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) :
    ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ u 0 = 0 ∧ u 1 = 0 ∧
      ∀ x ∈ Set.Ioo 0 1, deriv (deriv u) x = f x

/--
**Uniqueness for the one-dimensional Dirichlet problem.** Let $f : \mathbb{R} \to \mathbb{R}$ be
any function, and let $u_1, u_2 : \mathbb{R} \to \mathbb{R}$ be twice continuously
differentiable functions such that, for $i = 1, 2$, $u_i(0) = u_i(1) = 0$ and
$u_i''(x) = f(x)$ for every $x \in (0, 1)$. Then $u_1(x) = u_2(x)$ for every $x \in [0, 1]$.

Sources: Mathlib `docs/undergrad.yaml`, section "Topology" / "Hilbert spaces" /
entry "H^1_0([0,1]) and its application to the one-dimensional Dirichlet problem";
L. Evans, *Partial Differential Equations*, Ch. 6.
-/
public theorem_wanted dirichlet_1d_unique {f : ℝ → ℝ} {u₁ u₂ : ℝ → ℝ}
    (h₁ : ContDiff ℝ 2 u₁ ∧ u₁ 0 = 0 ∧ u₁ 1 = 0 ∧
      ∀ x ∈ Set.Ioo 0 1, deriv (deriv u₁) x = f x)
    (h₂ : ContDiff ℝ 2 u₂ ∧ u₂ 0 = 0 ∧ u₂ 1 = 0 ∧
      ∀ x ∈ Set.Ioo 0 1, deriv (deriv u₂) x = f x) :
    ∀ x ∈ Set.Icc 0 1, u₁ x = u₂ x

end MathlibExt.Analysis.Distribution.Dirichlet1DWanted
