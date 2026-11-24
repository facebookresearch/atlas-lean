/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ShadowMarkoffTree

/-! # Tests for shadow Markoff mutations and the tree rooted at the all-ones triple -/

open MetaMathlibExt

-- The path 0, 1, 0 reaches the classical triple (13, 5, 1).
example :
    let r := shadowMarkoffRoot (fun _ => 1)
    let s := shadowMarkoffMutate 0 (shadowMarkoffMutate 1 (shadowMarkoffMutate 0 r))
    s.2 0 = 13 := by
  intro r s
  have hs : s ∈ shadowMarkoffTree (fun _ => 1) :=
    Or.inr ⟨0, .mutate 0 .start (by decide)⟩
  rw [shadowMarkoffTree_one_shadow_eq s hs]
  norm_num [s, r, shadowMarkoffMutate, shadowMarkoffRoot, Function.update,
    Finset.sum_erase_eq_sub, Fin.sum_univ_three]

-- Both parts of the mutated coordinate vanish when the classical denominator is zero.
example :
    let s := shadowMarkoffMutate 0 (![0, 1, 2], ![3, 4, 5])
    (s.1 0, s.2 0) = (0, 0) := by
  simp [shadowMarkoffMutate]
