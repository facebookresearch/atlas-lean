/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.PNat.Basic
import MathlibExt.Combinatorics.Additive.MonochromaticProgressionLargeDifference

open MathlibExt.Combinatorics.MonochromaticProgressionLargeDifferenceErdosProblem645Wanted

-- A colouring defined only on positive integers can be extended arbitrarily at zero.
example (c : ℕ+ → Bool) (atZero : Bool) :
    ∃ x d : ℕ+, x < d ∧ c x = c (x + d) ∧ c (x + d) = c (x + 2 * d) := by
  let C (n : ℕ) := if h : 0 < n then c ⟨n, h⟩ else atZero
  obtain ⟨x, d, hx, hd, h₁, h₂⟩ := monochromaticProgressionLargeDifference_holds C
  have hC (n : ℕ+) : C n = c n := dite_eq_left n.pos
  let X : ℕ+ := ⟨x, hx⟩
  let D : ℕ+ := ⟨d, by omega⟩
  refine ⟨X, D, hd, ?_, ?_⟩
  · exact (hC X).symm.trans (h₁.trans (hC (X + D)))
  · exact (hC (X + D)).symm.trans (h₂.trans (hC (X + 2 * D)))
