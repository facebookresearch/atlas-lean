/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.FiniteChainDirichlet

@[expose] public section

-- Consumer with the original binders.
example {ι : Type*} [Finite ι] (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) (r : ι → ℕ → ℤ) :
    ∃ (ν : ι → ℤ) (c : ι → ℕ → ℤ),
      (∀ i, n i = 1 → ν i = 0) ∧ (∀ i, c i 0 = 0) ∧ (∀ i d, n i ≤ d → c i d = 0) ∧
      ∀ i d, 1 ≤ d → d + 1 ≤ n i →
        c i (d - 1) - 2 * c i d + c i (d + 1) = -(if d = 1 then r i d - ν i else r i d) :=
  ModularCurve.ChainDirichlet.exists_depthOne_correction_dirichlet n hn r

-- The length hypothesis matters: a chain of length zero has no interior
-- vertex at which the stated equation could hold.
example : ¬ (1 ≤ (0 : ℕ)) := by omega
