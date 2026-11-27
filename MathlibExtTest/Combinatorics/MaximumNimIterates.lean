/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Filter.AtTopBot.Basic
import MathlibExt.Combinatorics.MaximumNimIterates

/-! # Tests for divergence of Maximum Nim iterates -/

open MetaMathlibExt

-- Even at the smallest allowed k and with seed zero, the orbit eventually exceeds any bound.
example (m : ℕ) : ∀ᶠ p in Filter.atTop, m ≤ Nat.iterate (maximumNimH 2) p 0 :=
  Filter.tendsto_atTop.mp (maximumNimH_iterate_tendsto_atTop 2 0 le_rfl) m

-- The orbit from a nonzero seed eventually meets a fixed threshold and stays above it.
example : ∃ N : ℕ, ∀ p ≥ N, 100 ≤ Nat.iterate (maximumNimH 3) p 2 :=
  Filter.eventually_atTop.mp
    (Filter.tendsto_atTop.mp (maximumNimH_iterate_tendsto_atTop 3 2 (by decide)) 100)
