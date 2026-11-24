/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.GeneralizedHyperFibonacci
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- The recurrence allows negative p and arbitrary initial terms.
example : generalizedHyperFibonacci (-2) 1 3 2 2 = -5 := by
  rw [generalizedHyperFibonacci_succ_succ (-2) 1 3 1 1]
  norm_num [generalizedHyperFibonacci, generalizedPFibonacci, Finset.sum_range_succ]
