/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.BernoulliPointwiseDifferential

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.BernoulliPointwiseDifferential`

* `hasDerivAt_crossing_bernoulli` (Russo's formula, unconditional) for the increasing event
  "edge `0` is open" on `Fin 1` at `x = 1/2`;
* `expect_indicator_nonneg` and `expect_indicator_le_one` for the Bernoulli weight at `1/2`;
* `osss_fk_sharpness_final`, the conditional exponential decay, stated as a term.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.BernoulliPointwiseDifferential

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.CovLowerBound

-- Russo's formula for the event "edge `0` is open" on a single edge at `x = 1/2`.
example :
    HasDerivAt
      (fun x => expect (bernoulliWeight (E := Fin 1) x)
        ({ω | ω 0 = true}.indicator (fun _ => (1 : ℝ))))
      ((1 / ((1 / 2) * (1 - 1 / 2)))
        * ∑ e, cov (bernoulliWeight (E := Fin 1) (1 / 2)) (coordI e)
            ({ω | ω 0 = true}.indicator (fun _ => (1 : ℝ)))) (1 / 2) :=
  hasDerivAt_crossing_bernoulli _ (fun a b hab ha => by
      have h := hab 0
      rw [show a 0 = true from ha] at h
      exact Bool.eq_true_of_true_le h)
    (by norm_num) (by norm_num)

-- Probabilities of events under the Bernoulli weight at `1/2` lie in `[0, 1]`.
example (A : Set (ConfigSpace (Fin 2))) :
    0 ≤ expect (bernoulliWeight (E := Fin 2) (1 / 2)) (A.indicator (fun _ => (1 : ℝ))) ∧
      expect (bernoulliWeight (E := Fin 2) (1 / 2)) (A.indicator (fun _ => (1 : ℝ))) ≤ 1 :=
  ⟨expect_indicator_nonneg (bernoulliWeight_isProbWeight (by norm_num) (by norm_num)) A,
    expect_indicator_le_one (bernoulliWeight_isProbWeight (by norm_num) (by norm_num)) A⟩

-- The conditional final sharpness statement elaborates with its full hypothesis list.
example := @osss_fk_sharpness_final

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.BernoulliPointwiseDifferential
