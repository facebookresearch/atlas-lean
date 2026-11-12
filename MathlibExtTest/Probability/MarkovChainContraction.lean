/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovChainContraction

/-- Boundary check: starting both chains at the same state keeps
the distance at `0` (both sides are the same law). -/
example {α : Type*} [Fintype α] (K : α → PMF α) (x : α) (t : ℕ) :
    tvDist (chainDist K x (t + 1)) (chainDist K x (t + 1)) ≤
      tvDist (chainDist K x t) (chainDist K x t) :=
  tvDist_chainDist_mono K x x t

/-- The zero-step chain is the point mass at the start. -/
example {α : Type*} (K : α → PMF α) (x : α) : chainDist K x 0 = PMF.pure x := rfl
