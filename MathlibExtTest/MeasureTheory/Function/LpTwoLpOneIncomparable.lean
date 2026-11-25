/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.LpTwoLpOneIncomparable
import Mathlib.Tactic.NormNum

open MeasureTheory
open MathlibExt.MeasureTheory.LpTwoLpOneIncomparableWanted

-- In dimension 1 there are no remaining coordinates after the split.
example : ¬ ∀ f : (Fin 1 → ℝ) → ℝ, MemLp f 2 → MemLp f 1 :=
  (not_memLp_two_subset_one_and_not_memLp_one_subset_two 1 (by norm_num)).1

-- Check the other non-inclusion in a dimension with a nontrivial transverse cube.
example : ¬ ∀ f : (Fin 3 → ℝ) → ℝ, MemLp f 1 → MemLp f 2 :=
  (not_memLp_two_subset_one_and_not_memLp_one_subset_two 3 (by norm_num)).2
