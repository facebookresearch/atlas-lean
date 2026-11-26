/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.AlternatingHyperharmonicTypeII
import Mathlib.Tactic.NormNum

/-! # Tests for the finite-sum formula for type II alternating hyperharmonic numbers -/

open MetaMathlibExt Finset

-- Order one has a single coefficient, a(1, 0, 0) = 1.
example {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p) :
    signedIteratedPartialSum false (alternatingGeneralizedHarmonic p) 1 n =
      alternatingGeneralizedHarmonic p n := by
  simpa [liCoeffA_one_zero_zero] using
    alternatingHyperharmonic_typeII_eq_sum (r := 1) (n := n) (p := p) le_rfl hn hp

-- Order three with p = 1 exercises the negative shifted exponent p - 2.
example : signedIteratedPartialSum false (alternatingGeneralizedHarmonic 1) 3 2 = 5 / 2 := by
  have h := alternatingHyperharmonic_typeII_eq_sum (r := 3) (n := 2) (p := 1)
    (by decide) (by decide) (by decide)
  simp only [Nat.cast_one] at h
  rw [h]
  norm_num [liCoeffA, Finset.sum_range_succ, Finset.sum_Icc_succ_top, alternatingGeneralizedHarmonic,
    Real.rpow_neg_one]
