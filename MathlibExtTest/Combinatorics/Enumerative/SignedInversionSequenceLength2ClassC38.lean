/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2ClassC38

/-! # Tests for signed inversion sequences in class C38 -/

namespace MetaMathlibExt.signedInvSeq_wilf_and_gf_b1b0_b0b1_0b1_01.Tests

open PowerSeries

private abbrev patterns (b : Bool) : Finset SignedPattern2 :=
  {⟨.gt, true, b⟩, ⟨.lt, true, true⟩, ⟨.lt, false, true⟩, ⟨.lt, false, false⟩}

-- Five of the eight length-two words avoid each set. Extract the first
-- nontrivial coefficient and transport it across the Wilf-equivalence.
example : signedInvAvoidCount (patterns true) 2 = 5 ∧
    signedInvAvoidCount (patterns false) 2 = 5 := by
  obtain ⟨hc, hgf⟩ := signedInvSeq_wilf_and_gf_b1b0_b0b1_0b1_01
  change signedInvAvoidCount (patterns true) = signedInvAvoidCount (patterns false) at hc
  let F := signedInvAvoidGF (patterns true)
  have h : F - (X * F + X * F + X * F) + X * (X * F) = 1 - X := by
    calc
      _ = (1 - 3 * X + X ^ 2) * F := by ring
      _ = _ := hgf
  have h₂ := congrArg (coeff (R := ℚ) 2) h
  norm_num [coeff_succ_X_mul, F, coeff_signedInvAvoidGF, signedInvAvoidCount_zero,
    signedInvAvoidCount_one, coeff_one, coeff_X] at h₂
  rw [← hc, and_self]
  exact_mod_cast (show (signedInvAvoidCount (patterns true) 2 : ℚ) = 5 by linarith)

end MetaMathlibExt.signedInvSeq_wilf_and_gf_b1b0_b0b1_0b1_01.Tests
