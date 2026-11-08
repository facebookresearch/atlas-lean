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
One-dimensional Dirichlet problem, existence: every continuous `f` on `[0, 1]` is the second
derivative of a `C²` function vanishing at both endpoints.

Sources: Mathlib `docs/undergrad.yaml`, section "Topology" / "Hilbert spaces" /
entry "H^1_0([0,1]) and its application to the one-dimensional Dirichlet problem";
L. Evans, *Partial Differential Equations*, Ch. 6.
-/
public theorem_wanted dirichlet_1d_exists {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1)) :
    ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ u 0 = 0 ∧ u 1 = 0 ∧
      ∀ x ∈ Set.Ioo 0 1, deriv (deriv u) x = f x

/--
One-dimensional Dirichlet problem, uniqueness: the zero-boundary `C²` solution is unique
on `[0, 1]`.

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
