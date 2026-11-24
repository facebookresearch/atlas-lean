/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ArndtCompositions

open MetaMathlibExt

-- The empty composition is the only Arndt composition of 0. A single part must be positive.
example : arndtCompositionCount (fun _ => True) 0 0 = 1 ∧
    arndtCompositionCount (fun _ => True) 0 1 = 0 ∧
      arndtCompositionCount (fun _ => True) 5 1 = 1 := by
  decide

-- The pair (1, 1) is not descending, while (2, 1) is.
example : arndtCompositionCount (fun _ => True) 2 2 = 0 ∧
    arndtCompositionCount (fun _ => True) 3 2 = 1 := by
  decide

-- With odd parts only, (3, 1) is the only Arndt composition of 4 with two parts.
example : arndtCompositionCount (fun i => i % 2 = 1) 4 2 = 1 := by
  decide

-- With two parts the leading term is n / 2: one descending pair halves C(n - 1, 1).
example : Asymptotics.IsEquivalent Filter.atTop
    (fun n : ℕ => (arndtCompositionCount (fun _ => True) n 2 : ℝ))
    (fun n : ℕ => (n : ℝ) / 2) := by
  simpa using arndtCompositionCount_isEquivalent 2 (by decide)

-- With three parts there is still one pair, so the leading term is n² / (2 · 2!).
example : Asymptotics.IsEquivalent Filter.atTop
    (fun n : ℕ => (arndtCompositionCount (fun _ => True) n 3 : ℝ))
    (fun n : ℕ => (n : ℝ) ^ 2 / 4) := by
  have h := arndtCompositionCount_isEquivalent 3 (by decide)
  norm_num [Nat.factorial] at h
  exact h
