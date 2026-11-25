/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.AlternatingHyperharmonic
import Mathlib.Tactic.NormNum

/-! # Tests for type II alternating hyperharmonic numbers -/

open MetaMathlibExt Asymptotics Filter
open scoped Topology

-- At the smallest exponent and order, the asymptotic gives the alternating harmonic limit.
example : Tendsto (alternatingGeneralizedHarmonic 1) atTop (𝓝 (Real.log 2)) := by
  have h := alternatingHyperharmonic_typeII_isEquivalent (r := 1) (p := 1) le_rfl le_rfl
  apply IsEquivalent.tendsto_const (c := Real.log 2)
  simpa [signedIteratedPartialSum_one, Function.const_def] using h

-- Only the inner sum alternates in type II, so the two contributions are 1 and 1/2.
example : signedIteratedPartialSum false (alternatingGeneralizedHarmonic 1) 2 2 = 3 / 2 := by
  norm_num [signedIteratedPartialSum, alternatingGeneralizedHarmonic, Finset.sum_Icc_succ_top]

-- Order three introduces the factorial denominator.
example : (fun n => signedIteratedPartialSum false (alternatingGeneralizedHarmonic 2) 3 n)
    ~[atTop] fun n : ℕ => (n : ℝ) ^ 2 * alternatingZeta 2 / 2 := by
  simpa [Nat.factorial] using
    alternatingHyperharmonic_typeII_isEquivalent (r := 3) (p := 2) (by decide) (by decide)
