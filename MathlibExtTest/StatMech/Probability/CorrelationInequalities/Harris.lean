/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.Harris

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.Harris`

`harris_inequality` is applied under the product Bernoulli(`p`) measure on `ConfigSpace (Fin 2)`
for `p = 1/2` and `p = 0`, to the increasing events `open0 = {ω | ω 0}` and
`open1 = {ω | ω 1}` (both `IsIncreasing` hypotheses proved), and to the self-pair `open0, open0`,
where the conclusion reads `P(open0)^2 ≤ P(open0)`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.Harris

open _root_.StatMech

/-- The event "coordinate `0` is open" on two coordinates. -/
def open0 : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = true}

/-- The event "coordinate `1` is open" on two coordinates. -/
def open1 : Set (ConfigSpace (Fin 2)) := {ω | ω 1 = true}

-- `open0` is increasing.
theorem isIncreasing_open0 : IsIncreasing open0 := by
  intro x y hxy hx
  have h := hxy 0
  simp only [open0, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

-- `open1` is increasing.
theorem isIncreasing_open1 : IsIncreasing open1 := by
  intro x y hxy hx
  have h := hxy 1
  simp only [open1, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

-- `harris_inequality` at `p = 1/2` for two different increasing events.
example : (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real open0
      * (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real open1
    ≤ (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real (open0 ∩ open1) :=
  harris_inequality _ isIncreasing_open0 isIncreasing_open1

-- `harris_inequality` at the endpoint `p = 0`.
example : (bernoulliProductMeasure (E := Fin 2) 0 zero_le_one).real open0
      * (bernoulliProductMeasure (E := Fin 2) 0 zero_le_one).real open1
    ≤ (bernoulliProductMeasure (E := Fin 2) 0 zero_le_one).real (open0 ∩ open1) :=
  harris_inequality _ isIncreasing_open0 isIncreasing_open1

-- For the self-pair, Harris gives `P(open0)^2 ≤ P(open0)`.
example : (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real open0 ^ 2
    ≤ (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real open0 := by
  have h := harris_inequality (E := Fin 2) (p := 1 / 2) (by norm_num)
    isIncreasing_open0 isIncreasing_open0
  rwa [Set.inter_self, ← sq] at h

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.Harris
