/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.BesselTypeOdeInfinitelyManyZeros
import Mathlib.Data.Set.Finite.Basic

open Set MathlibExt.Analysis.Calculus.BesselTypeOdeInfinitelyManyZerosWanted

-- In particular, a solution as in the theorem has two distinct zeros beyond one.
example (u : ℝ → ℝ) (hd : ContDiffOn ℝ 2 u (Ioi 0))
    (he : ∀ x > 0, x * iteratedDeriv 2 u x + 2 * deriv u x + u x = 0)
    (hn : ∃ x > 0, u x ≠ 0) : ∃ x y : ℝ, x ≠ y ∧ 1 < x ∧ 1 < y ∧ u x = 0 ∧ u y = 0 := by
  have hz := setInfinite_zero_of_mul_iteratedDeriv_two_add_two_deriv_add_eq_zero u hd he hn
  obtain ⟨x, hx⟩ := hz.nonempty
  obtain ⟨y, hy, hne⟩ := hz.exists_notMem_finite (finite_singleton x)
  refine ⟨x, y, ?_, hx.1, hy.1, hx.2, hy.2⟩
  exact Ne.symm (by simpa using hne)
