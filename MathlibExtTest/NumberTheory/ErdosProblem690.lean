/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.ErdosProblem690

open MathlibExt.NumberTheory.ErdosProblem690Wanted

-- In 2² · 3 · 5 · 13, the repeated factor 2 occupies only one rank.
example : IsKthSmallestPrimeFactor 4 780 13 ∧ ¬ IsKthSmallestPrimeFactor 5 780 13 := by
  unfold IsKthSmallestPrimeFactor
  decide +kernel

-- Truncated subtraction makes rank zero agree with rank one.
example (n p : ℕ) : IsKthSmallestPrimeFactor 0 n p ↔ IsKthSmallestPrimeFactor 1 n p := Iff.rfl

example (k p : ℕ) : ¬ IsKthSmallestPrimeFactor k 0 p := by
  simp [IsKthSmallestPrimeFactor]

example : ¬ conjecture := conjecture_refuted
