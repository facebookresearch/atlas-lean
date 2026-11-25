/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.HypersequenceRecurrence

open MetaMathlibExt

-- From index zero and generation zero, the newly included term is the first nonzero value.
example : hypersequence (fun k : ℕ => (k : ℂ)) 1 1 = 1 := by
  rw [hypersequence_succ_succ _ 0 0]
  norm_num [hypersequence, Finset.sum_range_succ]

-- At generation two the new summand is itself a first-generation partial sum.
example : hypersequence (fun k : ℕ => (k : ℂ)) 2 2 = 4 := by
  rw [hypersequence_succ_succ _ 1 1]
  norm_num [hypersequence, Finset.sum_range_succ]
