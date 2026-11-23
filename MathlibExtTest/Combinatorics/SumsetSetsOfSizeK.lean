/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SumsetSetsOfSizeK
import Mathlib.Algebra.Order.Group.Int

/-! # Tests for iterated sumsets with a missing penultimate term -/

open scoped Pointwise
open MetaMathlibExt

-- One summand already gives the claimed size, including for a nonunit step.
example {k : ℕ} (hk : 3 ≤ k) :
    (insert (k • (2 : ℤ)) ((Finset.range (k - 1)).image fun i => i • (2 : ℤ))).card = k := by
  simpa only [one_nsmul, one_mul] using
    card_nsmul_arithProg_skip_penultimate (2 : ℤ) (by decide) k 1 hk le_rfl

-- At the smallest k, doubling fills the original gap at 2 and leaves a gap at 5.
example : (2 : ℕ) • ({0, 1, 3} : Finset ℤ) = {0, 1, 2, 3, 4, 6} := by decide

-- In the same double sumset, 3 is the only sum absent from the list of trivial elements.
example : sumsetTrivialElements 2 3 (fun n => if n = 2 then (3 : ℤ) else n) =
    {0, 1, 2, 4, 6} := by decide
