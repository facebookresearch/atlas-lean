/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FinitePrefix

/-!
# Prefix-dependent finite-horizon law tests

A genuinely history-dependent rational kernel on `Bool`: `[false]` and
`[true, false]` end in the same token but induce different next-token
laws, so the kernel uses more than the last token.
-/

open scoped ENNReal

@[expose] public section

namespace MathlibExtTest.Probability.FinitePrefix

open MathlibExt.Probability.FinitePrefix

theorem ennreal_half_mul_three_quarter : (1 / 2 : ℝ≥0∞) * (3 / 4) = 3 / 8 := by
  apply (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp
  · simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_ofNat]
    norm_num
  · finiteness
  · finiteness

theorem ennreal_one_sub_quarter : (1 - 1 / 4 : ℝ≥0∞) = 3 / 4 := by
  refine ENNReal.sub_eq_of_eq_add (by finiteness) ?_
  apply (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp
  · have ha : (3 / 4 : ℝ≥0∞) ≠ ∞ := by finiteness
    have hb : (1 / 4 : ℝ≥0∞) ≠ ∞ := by finiteness
    rw [ENNReal.toReal_add ha hb]
    simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
    norm_num
  · finiteness
  · finiteness

section BoolExamples

/-- DEF (test only): the biased Bool law with `P(true) = p`, for `p ≤ 1`. -/
noncomputable def boolPMF (p : ℝ≥0∞) (hp : p ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => cond b p (1 - p)) (by
    rw [Fintype.sum_bool]
    simp only [Bool.cond_true, Bool.cond_false]
    exact add_tsub_cancel_of_le hp)

/-- DEF (test only): a genuinely history-dependent rational kernel on Bool.

The empty prefix is fair; a nonempty odd-length prefix gives `true`
probability `1/4`; a nonempty even-length prefix gives `3/4`.  Hence
`[false]` and `[true, false]`, which end in the same token, induce
different next-token laws: the kernel uses more than the last token. -/
noncomputable def histKernel (w : List Bool) : PMF Bool :=
  if w = [] then boolPMF (1 / 2) (by norm_num)
  else if w.length % 2 = 1 then boolPMF (1 / 4) (by norm_num)
  else boolPMF (3 / 4)
    ((ENNReal.div_le_iff (by norm_num) (by norm_num)).2 (by norm_num))

/-- DEF (test only): a kernel that never emits `true`. -/
noncomputable def zeroKernel (_ : List Bool) : PMF Bool :=
  boolPMF 0 (by norm_num)

theorem histKernel_singleton_true_false :
    histKernel [true] false = 1 - 1 / 4 := by
  simp only [histKernel]
  rw [ite_eq_right (show ([true] : List Bool) ≠ [] from by simp),
    ite_eq_left (show ([true].length % 2 = 1) from rfl)]
  simp only [boolPMF, PMF.ofFintype_apply, Bool.cond_false]

/-- TEST: horizon zero puts mass one on the empty word. -/
theorem law_zero_histKernel_mass_nil :
    (law 0 histKernel) ([] : List Bool) = 1 := by
  simp [law_zero]

/-- TEST: horizon zero puts mass zero on every nonempty word. -/
theorem law_zero_histKernel_mass_cons :
    (law 0 histKernel) ([false] : List Bool) = 0 := by
  simp [law_zero]

/-- TEST: a zero-probability token has zero mass in a one-token word. -/
theorem law_one_zeroKernel_mass_true :
    (law 1 zeroKernel) ([true] : List Bool) = 0 := by
  have h := mass_cons 0 zeroKernel true []
  simpa [zeroKernel, boolPMF, PMF.ofFintype_apply, Bool.cond_true] using h

/-- TEST: the complementary token carries all mass for `zeroKernel`. -/
theorem law_one_zeroKernel_mass_false :
    (law 1 zeroKernel) ([false] : List Bool) = 1 := by
  have h := mass_cons 0 zeroKernel false []
  simpa [zeroKernel, boolPMF, PMF.ofFintype_apply, Bool.cond_false, law_zero] using h

/-- TEST: first-step value of the history-dependent kernel. -/
theorem histKernel_nil_true :
    histKernel [] true = (1 / 2 : ℝ≥0∞) := by
  simp [histKernel, boolPMF, PMF.ofFintype_apply]

/-- TEST: odd-length nonempty prefix value. -/
theorem histKernel_singleton_false_true :
    histKernel [false] true = (1 / 4 : ℝ≥0∞) := by
  simp only [histKernel]
  rw [ite_eq_right (show ([false] : List Bool) ≠ [] from by simp),
    ite_eq_left (show ([false].length % 2 = 1) from rfl)]
  simp only [boolPMF, PMF.ofFintype_apply, Bool.cond_true]

/-- TEST: even-length nonempty prefix value, same last token as above. -/
theorem histKernel_pair_true_false_true :
    histKernel [true, false] true = (3 / 4 : ℝ≥0∞) := by
  have hmod : [true, false].length % 2 = 0 := rfl
  simp only [histKernel]
  rw [ite_eq_right (show ([true, false] : List Bool) ≠ [] from by simp),
    ite_eq_right (show ([true, false].length % 2 ≠ 1) from by rw [hmod]; simp)]
  simp only [boolPMF, PMF.ofFintype_apply, Bool.cond_true]

/-- TEST: the kernel is genuinely history-dependent, not last-token-only. -/
theorem histKernel_history_dependent :
    histKernel [false] ≠ histKernel [true, false] := by
  intro h
  have h1 := congrArg (fun p : PMF Bool => p true) h
  rw [histKernel_singleton_false_true, histKernel_pair_true_false_true] at h1
  have hne : (1 / 4 : ℝ≥0∞) ≠ 3 / 4 := by
    intro hc
    have hc' := congrArg ENNReal.toReal hc
    simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at hc'
    norm_num at hc'
  exact hne h1

/-- TEST: concrete rational word mass under the history-dependent kernel.
First token `true` has mass `1/2` at `[]`; then `false` has mass
`1 - 1/4 = 3/4` at `[true]`; product `3/8`. -/
theorem law_two_histKernel_mass :
    (law 2 histKernel) ([true, false] : List Bool) = (3 / 8 : ℝ≥0∞) := by
  have hw : ([true, false] : List Bool).length = 2 := rfl
  rw [mass_prefix_match 2 histKernel hw]
  simp only [prefixProd]
  rw [histKernel_nil_true, histKernel_singleton_true_false, ennreal_one_sub_quarter,
    mul_one, ennreal_half_mul_three_quarter]

/-- TEST: the same mass computed through the prefix product. -/
theorem prefixProd_histKernel_example :
    prefixProd histKernel ([true, false] : List Bool) = (3 / 8 : ℝ≥0∞) := by
  simp only [prefixProd]
  rw [histKernel_nil_true, histKernel_singleton_true_false, ennreal_one_sub_quarter,
    mul_one, ennreal_half_mul_three_quarter]

end BoolExamples

end MathlibExtTest.Probability.FinitePrefix
