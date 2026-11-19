/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.BinomialNoArbitrage
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Probability.Finance.BinomialNoArbitrage`

* A no-arbitrage instance (`S₀ = 100`, `u = 1.1`, `d = 0.9`, `R = 1.05`).
* Explicit arbitrages below (`R = 0.8`) and above (`R = 1.2`) the no-arbitrage interval.
* The risk-neutral probability value `rnProb = 3/4` at the no-arbitrage instance.
-/

@[expose] public section

open MathlibExt.Probability.Finance.BinomialNoArbitrage

namespace MathlibExtTest.Probability.Finance.BinomialNoArbitrage

example : NoOneStepArbitrage 100 (11/10) (9/10) (21/20) :=
  (noOneStepArbitrage_iff (S₀ := (100 : ℝ)) (u := (11/10 : ℝ)) (d := (9/10 : ℝ))
    (R := (21/20 : ℝ)) (by norm_num) (by norm_num) (by norm_num)).mpr
    ⟨by norm_num, by norm_num⟩

example : IsOneStepArbitrage 100 (11/10) (9/10) (4/5) 1 (-100) :=
  ⟨by norm_num, by norm_num, by norm_num, Or.inl (by norm_num)⟩

example : IsOneStepArbitrage 100 (11/10) (9/10) (6/5) (-1) 100 :=
  ⟨by norm_num, by norm_num, by norm_num, Or.inl (by norm_num)⟩

example : MathlibExt.Probability.Finance.BinomialReplication.rnProb (11/10) (9/10) (21/20)
    = 3/4 := by
  unfold MathlibExt.Probability.Finance.BinomialReplication.rnProb
  norm_num

example : NoOneStepArbitrage 100 (11/10) (9/10) (21/20) ↔
    0 < (3/4 : ℝ) ∧ (3/4 : ℝ) < 1 := by
  have h := noOneStepArbitrage_iff_rnProb (S₀ := (100 : ℝ)) (u := (11/10 : ℝ))
    (d := (9/10 : ℝ)) (R := (21/20 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hrn : MathlibExt.Probability.Finance.BinomialReplication.rnProb (11/10) (9/10) (21/20)
      = 3/4 := by
    unfold MathlibExt.Probability.Finance.BinomialReplication.rnProb
    norm_num
  rw [hrn] at h
  exact h

end MathlibExtTest.Probability.Finance.BinomialNoArbitrage
