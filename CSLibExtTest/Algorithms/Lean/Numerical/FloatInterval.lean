/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Numerical.FloatInterval
public meta import CSLibExt.Algorithms.Lean.Numerical.FloatInterval

/-!
# Tests for directed rounding and floating-point intervals

Exhaustive kernel-checked tests on the frozen test format `p = 3`,
`qmin = -2`, `qmax = 0` (31 values, 496 ordered endpoint intervals), plus the
boundary examples: subnormal rounding, stepwise versus final-only rounding,
intermediate overflow, and unsupported division.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.FloatInterval

open Cslib.Algorithms.Lean.FloatingPoint
open MathlibExt.Analysis.Numerical.Certified

/-- The 31 values of the test format `p = 3`, `qmin = -2`, `qmax = 0`. -/
def testVals : List ℚ :=
  [(-7 : ℚ), (-6 : ℚ), (-5 : ℚ), (-4 : ℚ), (-7/2 : ℚ), (-3 : ℚ), (-5/2 : ℚ),
    (-2 : ℚ), (-7/4 : ℚ), (-3/2 : ℚ), (-5/4 : ℚ), (-1 : ℚ), (-3/4 : ℚ),
    (-1/2 : ℚ), (-1/4 : ℚ), 0, 1/4, 1/2, 3/4, 1, 5/4, 3/2, 7/4, 2, 5/2, 3,
    7/2, 4, 5, 6, 7]

/-- The 496 ordered endpoint intervals over the test values. -/
def testIntervals : List RatInterval :=
  (testVals.product testVals).filterMap
    (fun (l, u) => if l ≤ u then some ⟨l, u⟩ else none)

/-- In the test format, `maxFloat 3 0` equals `7`. -/
lemma hmaxFloat_test : maxFloat 3 0 = 7 := by simp only [maxFloat, zpow_zero]; norm_num

/-- The test format has precision `3`, satisfying `1 ≤ 3`. -/
lemma hp_testFormat : 1 ≤ (3 : ℕ) := by norm_num

/-- The test format exponent floor `-2` satisfies `-2 ≤ 0`. -/
lemma hq_testFormat : (-2 : ℤ) ≤ 0 := by norm_num

/-- Every interval in `testIntervals` is ordered: `lower ≤ upper`. -/
lemma mem_testIntervals_order {I : RatInterval} (h : I ∈ testIntervals) :
    I.lower ≤ I.upper := by
  simp only [testIntervals, List.mem_filterMap] at h
  obtain ⟨p, -, hsome⟩ := h
  obtain ⟨l, u⟩ := p
  dsimp only at hsome
  by_cases hle : l ≤ u
  · rw [ite_eq_left hle] at hsome
    obtain rfl := Option.some_inj.mp hsome
    exact hle
  · rw [ite_eq_right hle] at hsome
    simp at hsome

/-- `testVals` contains exactly `31` values. -/
theorem testVals_length : testVals.length = 31 := by
  decide

#print axioms testVals_length

/-- `testIntervals` contains exactly `496` intervals. -/
theorem testIntervals_length : testIntervals.length = 496 := by
  decide +kernel

#print axioms testIntervals_length

/-- In the test format, `IsFloatIn` holds exactly for members of `testVals`. -/
theorem isFloatIn_testFormat_iff {x : ℚ} :
    IsFloatIn 3 (-2) 0 x ↔ x ∈ testVals := by
  constructor
  · intro h
    obtain ⟨m, e, hm, he1, he2, rfl⟩ := h
    norm_num at hm
    rw [abs_lt] at hm
    obtain ⟨hmlo, hmhi⟩ := hm
    have hlo : -7 ≤ m := by omega
    have hhi : m ≤ 7 := by omega
    interval_cases m <;> interval_cases e <;> norm_num [testVals]
  · intro h
    simp only [testVals, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨-7, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨-6, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨-5, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨-4, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨-7, -1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨-3, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨-5, -1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨-2, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨-7, -2, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨-3, -1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨-5, -2, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨-1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨-3, -2, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨-1, -1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨-1, -2, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨0, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨1, -2, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨1, -1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, -2, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, -2, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, -1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, -2, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨2, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, -1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, -1, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨4, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨6, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩

#print axioms isFloatIn_testFormat_iff

/-- Round-down fixes every value already in `testVals`. -/
lemma rd_of_mem_testVals {x : ℚ} (hx : x ∈ testVals) : rd 3 (-2) x = x :=
  rd_of_isFloatIn hp_testFormat hq_testFormat (isFloatIn_testFormat_iff.mpr hx)

/-- Round-up fixes every value already in `testVals`. -/
lemma ru_of_mem_testVals {x : ℚ} (hx : x ∈ testVals) : ru 3 (-2) x = x :=
  ru_of_isFloatIn hp_testFormat hq_testFormat (isFloatIn_testFormat_iff.mpr hx)

/-- Checked round-down fails once `|x|` exceeds the test bound `7`. -/
lemma rdChecked_none_of {x : ℚ} (h : 7 < |x|) : rdChecked 3 (-2) 0 x = none := by
  simp only [rdChecked, hmaxFloat_test, ite_eq_right (not_le.mpr h)]

/-- Checked round-up fails once `|x|` exceeds the test bound `7`. -/
lemma ruChecked_none_of {x : ℚ} (h : 7 < |x|) : ruChecked 3 (-2) 0 x = none := by
  simp only [ruChecked, hmaxFloat_test, ite_eq_right (not_le.mpr h)]

/-- In-range checked round-down agrees with plain `rd`. -/
lemma rdChecked_some_of_le {x : ℚ} (h : |x| ≤ 7) :
    rdChecked 3 (-2) 0 x = some (rd 3 (-2) x) := by
  rw [rdChecked_eq_some_iff, hmaxFloat_test]
  exact ⟨h, rfl⟩

/-- In-range checked round-up agrees with plain `ru`. -/
lemma ruChecked_some_of_le {x : ℚ} (h : |x| ≤ 7) :
    ruChecked 3 (-2) 0 x = some (ru 3 (-2) x) := by
  rw [ruChecked_eq_some_iff, hmaxFloat_test]
  exact ⟨h, rfl⟩

/-- Both roundings fix every value in `testVals`. -/
theorem rd_ru_fixed_on_testVals :
    ∀ x ∈ testVals, rd 3 (-2) x = x ∧ ru 3 (-2) x = x := by
  intro x hx
  exact ⟨rd_of_mem_testVals hx, ru_of_mem_testVals hx⟩

#print axioms rd_ru_fixed_on_testVals

/-- Rounded scalar sums enclose the exact sum, or both checked roundings fail. -/
theorem scalar_add_enclosure :
    ∀ x ∈ testVals, ∀ y ∈ testVals,
      (|x + y| ≤ 7 → rd 3 (-2) (x + y) ≤ x + y ∧ x + y ≤ ru 3 (-2) (x + y)
        ∧ rd 3 (-2) (x + y) ∈ testVals ∧ ru 3 (-2) (x + y) ∈ testVals)
      ∧ (7 < |x + y| → rdChecked 3 (-2) 0 (x + y) = none
        ∧ ruChecked 3 (-2) 0 (x + y) = none) := by
  intro x _ y _
  constructor
  · intro hle
    have hleM : |x + y| ≤ maxFloat 3 0 := by
      rw [hmaxFloat_test]
      exact hle
    refine ⟨rd_le 3 (-2) (x + y), le_ru 3 (-2) (x + y), ?_, ?_⟩
    · exact isFloatIn_testFormat_iff.mp (rd_isFloatIn hp_testFormat hq_testFormat hleM)
    · exact isFloatIn_testFormat_iff.mp (ru_isFloatIn hp_testFormat hq_testFormat hleM)
  · intro hlt
    exact ⟨rdChecked_none_of hlt, ruChecked_none_of hlt⟩

#print axioms scalar_add_enclosure

/-- Rounded scalar differences enclose the exact difference, or both checked roundings fail. -/
theorem scalar_sub_enclosure :
    ∀ x ∈ testVals, ∀ y ∈ testVals,
      (|x - y| ≤ 7 → rd 3 (-2) (x - y) ≤ x - y ∧ x - y ≤ ru 3 (-2) (x - y)
        ∧ rd 3 (-2) (x - y) ∈ testVals ∧ ru 3 (-2) (x - y) ∈ testVals)
      ∧ (7 < |x - y| → rdChecked 3 (-2) 0 (x - y) = none
        ∧ ruChecked 3 (-2) 0 (x - y) = none) := by
  intro x _ y _
  constructor
  · intro hle
    have hleM : |x - y| ≤ maxFloat 3 0 := by
      rw [hmaxFloat_test]
      exact hle
    refine ⟨rd_le 3 (-2) (x - y), le_ru 3 (-2) (x - y), ?_, ?_⟩
    · exact isFloatIn_testFormat_iff.mp (rd_isFloatIn hp_testFormat hq_testFormat hleM)
    · exact isFloatIn_testFormat_iff.mp (ru_isFloatIn hp_testFormat hq_testFormat hleM)
  · intro hlt
    exact ⟨rdChecked_none_of hlt, ruChecked_none_of hlt⟩

#print axioms scalar_sub_enclosure

/-- Rounded scalar products enclose the exact product, or both checked roundings fail. -/
theorem scalar_mul_enclosure :
    ∀ x ∈ testVals, ∀ y ∈ testVals,
      (|x * y| ≤ 7 → rd 3 (-2) (x * y) ≤ x * y ∧ x * y ≤ ru 3 (-2) (x * y)
        ∧ rd 3 (-2) (x * y) ∈ testVals ∧ ru 3 (-2) (x * y) ∈ testVals)
      ∧ (7 < |x * y| → rdChecked 3 (-2) 0 (x * y) = none
        ∧ ruChecked 3 (-2) 0 (x * y) = none) := by
  intro x _ y _
  constructor
  · intro hle
    have hleM : |x * y| ≤ maxFloat 3 0 := by
      rw [hmaxFloat_test]
      exact hle
    refine ⟨rd_le 3 (-2) (x * y), le_ru 3 (-2) (x * y), ?_, ?_⟩
    · exact isFloatIn_testFormat_iff.mp (rd_isFloatIn hp_testFormat hq_testFormat hleM)
    · exact isFloatIn_testFormat_iff.mp (ru_isFloatIn hp_testFormat hq_testFormat hleM)
  · intro hlt
    exact ⟨rdChecked_none_of hlt, ruChecked_none_of hlt⟩

#print axioms scalar_mul_enclosure

/-- For `I, J ∈ testIntervals`, a successful `addF` result has ordered `testVals`
endpoints and encloses the exact sum. -/
theorem interval_add_sound :
    ∀ I ∈ testIntervals, ∀ J ∈ testIntervals, ∀ K : RatInterval,
      addF 3 (-2) 0 I J = some K →
        K.lower ≤ (I.add J).lower ∧ (I.add J).upper ≤ K.upper
          ∧ K.lower ∈ testVals ∧ K.upper ∈ testVals ∧ K.lower ≤ K.upper := by
  intro I hI J hJ K h
  obtain ⟨hwlo, hwhi⟩ := addF_widen h
  simp only [addF, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def] at h
  obtain ⟨l, hl, u, hu, hK⟩ := h
  obtain rfl := Option.some_inj.mp hK
  rw [rdChecked_eq_some_iff] at hl
  rw [ruChecked_eq_some_iff] at hu
  obtain ⟨hle1, rfl⟩ := hl
  obtain ⟨hle2, rfl⟩ := hu
  have hlord : I.lower ≤ I.upper := mem_testIntervals_order hI
  have hjord : J.lower ≤ J.upper := mem_testIntervals_order hJ
  refine ⟨hwlo, hwhi, ?_, ?_, ?_⟩
  · exact isFloatIn_testFormat_iff.mp (rd_isFloatIn hp_testFormat hq_testFormat hle1)
  · exact isFloatIn_testFormat_iff.mp (ru_isFloatIn hp_testFormat hq_testFormat hle2)
  · exact le_trans (le_trans (rd_le 3 (-2) _) (add_le_add hlord hjord))
      (le_ru 3 (-2) _)

#print axioms interval_add_sound

/-- For `I, J ∈ testIntervals`, `addF` fails exactly when either
`|I.lower + J.lower|` or `|I.upper + J.upper|` exceeds `7`. -/
theorem interval_add_overflow :
    ∀ I ∈ testIntervals, ∀ J ∈ testIntervals,
      (addF 3 (-2) 0 I J = none) ↔
        (7 < |I.lower + J.lower| ∨ 7 < |I.upper + J.upper|) := by
  intro I _ J _
  constructor
  · intro h
    by_contra hc
    simp only [not_or, not_lt] at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hs1 : rdChecked 3 (-2) 0 (I.lower + J.lower) =
        some (rd 3 (-2) (I.lower + J.lower)) :=
      rdChecked_some_of_le hc1
    have hs2 : ruChecked 3 (-2) 0 (I.upper + J.upper) =
        some (ru 3 (-2) (I.upper + J.upper)) :=
      ruChecked_some_of_le hc2
    have hsome : addF 3 (-2) 0 I J =
        some ⟨rd 3 (-2) (I.lower + J.lower), ru 3 (-2) (I.upper + J.upper)⟩ := by
      simp only [addF, Option.bind_eq_bind, hs1, hs2, Option.bind_some,
        Option.pure_def]
    rw [h] at hsome
    simp at hsome
  · rintro (h | h)
    · have hn : rdChecked 3 (-2) 0 (I.lower + J.lower) = none :=
        rdChecked_none_of h
      simp only [addF, Option.bind_eq_bind, hn, Option.bind_none]
    · have hn : ruChecked 3 (-2) 0 (I.upper + J.upper) = none :=
        ruChecked_none_of h
      simp only [addF, Option.bind_eq_bind, hn, Option.bind_none,
        Option.bind_fun_none]

#print axioms interval_add_overflow

/-- For `I, J ∈ testIntervals`, a successful `subF` result has ordered `testVals`
endpoints and encloses the exact difference. -/
theorem interval_sub_sound :
    ∀ I ∈ testIntervals, ∀ J ∈ testIntervals, ∀ K : RatInterval,
      subF 3 (-2) 0 I J = some K →
        K.lower ≤ (I.sub J).lower ∧ (I.sub J).upper ≤ K.upper
          ∧ K.lower ∈ testVals ∧ K.upper ∈ testVals ∧ K.lower ≤ K.upper := by
  intro I hI J hJ K h
  obtain ⟨hwlo, hwhi⟩ := subF_widen h
  simp only [subF, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def] at h
  obtain ⟨l, hl, u, hu, hK⟩ := h
  obtain rfl := Option.some_inj.mp hK
  rw [rdChecked_eq_some_iff] at hl
  rw [ruChecked_eq_some_iff] at hu
  obtain ⟨hle1, rfl⟩ := hl
  obtain ⟨hle2, rfl⟩ := hu
  have hlord : I.lower ≤ I.upper := mem_testIntervals_order hI
  have hjord : J.lower ≤ J.upper := mem_testIntervals_order hJ
  refine ⟨hwlo, hwhi, ?_, ?_, ?_⟩
  · exact isFloatIn_testFormat_iff.mp (rd_isFloatIn hp_testFormat hq_testFormat hle1)
  · exact isFloatIn_testFormat_iff.mp (ru_isFloatIn hp_testFormat hq_testFormat hle2)
  · exact le_trans (le_trans (rd_le 3 (-2) _) (sub_le_sub hlord hjord))
      (le_ru 3 (-2) _)

#print axioms interval_sub_sound

/-- For `I, J ∈ testIntervals`, `subF` fails exactly when either
`|I.lower - J.upper|` or `|I.upper - J.lower|` exceeds `7`. -/
theorem interval_sub_overflow :
    ∀ I ∈ testIntervals, ∀ J ∈ testIntervals,
      (subF 3 (-2) 0 I J = none) ↔
        (7 < |I.lower - J.upper| ∨ 7 < |I.upper - J.lower|) := by
  intro I _ J _
  constructor
  · intro h
    by_contra hc
    simp only [not_or, not_lt] at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hs1 : rdChecked 3 (-2) 0 (I.lower - J.upper) =
        some (rd 3 (-2) (I.lower - J.upper)) :=
      rdChecked_some_of_le hc1
    have hs2 : ruChecked 3 (-2) 0 (I.upper - J.lower) =
        some (ru 3 (-2) (I.upper - J.lower)) :=
      ruChecked_some_of_le hc2
    have hsome : subF 3 (-2) 0 I J =
        some ⟨rd 3 (-2) (I.lower - J.upper), ru 3 (-2) (I.upper - J.lower)⟩ := by
      simp only [subF, Option.bind_eq_bind, hs1, hs2, Option.bind_some,
        Option.pure_def]
    rw [h] at hsome
    simp at hsome
  · rintro (h | h)
    · have hn : rdChecked 3 (-2) 0 (I.lower - J.upper) = none :=
        rdChecked_none_of h
      simp only [subF, Option.bind_eq_bind, hn, Option.bind_none]
    · have hn : ruChecked 3 (-2) 0 (I.upper - J.lower) = none :=
        ruChecked_none_of h
      simp only [subF, Option.bind_eq_bind, hn, Option.bind_none,
        Option.bind_fun_none]

#print axioms interval_sub_overflow

/-- A successful `mulF` result has ordered `testVals` endpoints and encloses the exact product. -/
theorem interval_mul_sound :
    ∀ I ∈ testIntervals, ∀ J ∈ testIntervals, ∀ K : RatInterval,
      mulF 3 (-2) 0 I J = some K →
        K.lower ≤ (I.mul J).lower ∧ (I.mul J).upper ≤ K.upper
          ∧ K.lower ∈ testVals ∧ K.upper ∈ testVals ∧ K.lower ≤ K.upper := by
  intro I _ J _ K h
  obtain ⟨hwlo, hwhi⟩ := mulF_widen h
  simp only [mulF, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def] at h
  obtain ⟨l, hl, u, hu, hK⟩ := h
  obtain rfl := Option.some_inj.mp hK
  rw [rdChecked_eq_some_iff] at hl
  rw [ruChecked_eq_some_iff] at hu
  obtain ⟨hle1, rfl⟩ := hl
  obtain ⟨hle2, rfl⟩ := hu
  refine ⟨hwlo, hwhi, ?_, ?_, ?_⟩
  · exact isFloatIn_testFormat_iff.mp (rd_isFloatIn hp_testFormat hq_testFormat hle1)
  · exact isFloatIn_testFormat_iff.mp (ru_isFloatIn hp_testFormat hq_testFormat hle2)
  · refine le_trans (le_trans (rd_le 3 (-2) _) ?_) (le_ru 3 (-2) _)
    exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _))
      (le_trans (le_max_left _ _) (le_max_left _ _))

#print axioms interval_mul_sound

/-- `mulF` fails exactly when an exact endpoint product exceeds `7` in magnitude. -/
theorem interval_mul_overflow : ∀ I ∈ testIntervals, ∀ J ∈ testIntervals,
    (mulF 3 (-2) 0 I J = none) ↔
    (7 < |(I.mul J).lower| ∨ 7 < |(I.mul J).upper|) := by
  intro I _ J _
  simp only [RatInterval.mul_lower, RatInterval.mul_upper]
  constructor
  · intro h
    by_contra hc
    simp only [not_or, not_lt] at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hs1 := rdChecked_some_of_le hc1
    have hs2 := ruChecked_some_of_le hc2
    simp only [mulF, Option.bind_eq_bind, hs1, hs2, Option.bind_some,
      Option.pure_def] at h
    simp at h
  · rintro (h | h)
    · have hn := rdChecked_none_of h
      simp only [mulF, Option.bind_eq_bind, hn, Option.bind_none]
    · have hn := ruChecked_none_of h
      simp only [mulF, Option.bind_eq_bind, hn, Option.bind_none,
        Option.bind_fun_none]

#print axioms interval_mul_overflow

/-- In the test format, `1/8` rounds down to `0` and up to `1/4`. -/
theorem subnormal_rounding :
    rd 3 (-2) (1 / 8 : ℚ) = 0 ∧ ru 3 (-2) (1 / 8 : ℚ) = 1 / 4 := by
  decide +kernel

#print axioms subnormal_rounding

/-- `evalF` rounds stepwise: `(-7 * -3/4) + -7` evaluates to `⟨-2, -1⟩`. -/
theorem stepwise_not_final_only :
    evalF 3 (-2) 0 (fun _ : Unit => ⟨0, 0⟩)
        (RatInterval.Expr.add
          (RatInterval.Expr.mul (RatInterval.Expr.const (-7))
            (RatInterval.Expr.const (-3 / 4)))
          (RatInterval.Expr.const (-7)))
      = some ⟨-2, -1⟩ := by
  have h1 : (evalF 3 (-2) 0 (fun _ : Unit => ⟨0, 0⟩)
      (RatInterval.Expr.add
        (RatInterval.Expr.mul (RatInterval.Expr.const (-7))
          (RatInterval.Expr.const (-3 / 4)))
        (RatInterval.Expr.const (-7)))).map RatInterval.lower
      = some (-2 : ℚ) := by decide +kernel
  have h2 : (evalF 3 (-2) 0 (fun _ : Unit => ⟨0, 0⟩)
      (RatInterval.Expr.add
        (RatInterval.Expr.mul (RatInterval.Expr.const (-7))
          (RatInterval.Expr.const (-3 / 4)))
        (RatInterval.Expr.const (-7)))).map RatInterval.upper
      = some (-1 : ℚ) := by decide +kernel
  cases hE : evalF 3 (-2) 0 (fun _ : Unit => ⟨0, 0⟩)
      (RatInterval.Expr.add
        (RatInterval.Expr.mul (RatInterval.Expr.const (-7))
          (RatInterval.Expr.const (-3 / 4)))
        (RatInterval.Expr.const (-7))) with
  | none => simp [hE] at h1
  | some K =>
    simp [hE] at h1 h2
    obtain ⟨lo, hi⟩ := K
    change lo = -2 at h1
    change hi = -1 at h2
    rw [h1, h2]

#print axioms stepwise_not_final_only

/-- `evalF` fails when an intermediate result overflows, even if the final value fits. -/
theorem intermediate_overflow_fails :
    evalF 3 (-2) 0 (fun _ : Unit => ⟨0, 0⟩)
        (RatInterval.Expr.sub
          (RatInterval.Expr.add (RatInterval.Expr.const 7) (RatInterval.Expr.const 7))
          (RatInterval.Expr.const 7))
      = none := by
  decide +kernel

#print axioms intermediate_overflow_fails

/-- `evalF` rejects division expressions. -/
theorem division_unsupported :
    evalF 3 (-2) 0 (fun _ : Unit => ⟨0, 0⟩)
        (RatInterval.Expr.div (RatInterval.Expr.const 1)
          (RatInterval.Expr.const 1))
      = none := by
  decide +kernel

#print axioms division_unsupported

/-- `evalF` rejects a variable interval with a non-float lower bound. -/
theorem evalF_var_rejects_nonfloat :
    evalF 3 (-2) 0 (fun _ : Unit => ⟨1/8, 1/4⟩) (RatInterval.Expr.var ()) = none := by
  decide +kernel

#print axioms evalF_var_rejects_nonfloat

/-- `evalF` rejects a variable interval with `upper < lower`. -/
theorem evalF_var_rejects_reversed :
    evalF 3 (-2) 0 (fun _ : Unit => ⟨1, 0⟩) (RatInterval.Expr.var ()) = none := by
  decide +kernel

#print axioms evalF_var_rejects_reversed

/-- `evalF` rejects a variable interval outside the test range. -/
theorem evalF_var_rejects_overflow :
    evalF 3 (-2) 0 (fun _ : Unit => ⟨8, 8⟩) (RatInterval.Expr.var ()) = none := by
  decide +kernel

#print axioms evalF_var_rejects_overflow

/-- `evalF` rejects a variable interval with a non-float upper bound. -/
theorem evalF_var_rejects_upper_nonfloat :
    evalF 3 (-2) 0 (fun _ : Unit => ⟨0, 1/8⟩) (RatInterval.Expr.var ()) = none := by
  decide +kernel

#print axioms evalF_var_rejects_upper_nonfloat

/-- `evalF` accepts the full-range variable interval `⟨-7, 7⟩` unchanged. -/
theorem evalF_var_accepts :
    evalF 3 (-2) 0 (fun _ : Unit => ⟨-7, 7⟩) (RatInterval.Expr.var ())
      = some ⟨-7, 7⟩ := by
  have h1 : (evalF 3 (-2) 0 (fun _ : Unit => ⟨-7, 7⟩)
      (RatInterval.Expr.var ())).map RatInterval.lower
      = some (-7 : ℚ) := by decide +kernel
  have h2 : (evalF 3 (-2) 0 (fun _ : Unit => ⟨-7, 7⟩)
      (RatInterval.Expr.var ())).map RatInterval.upper
      = some (7 : ℚ) := by decide +kernel
  cases hE : evalF 3 (-2) 0 (fun _ : Unit => ⟨-7, 7⟩)
      (RatInterval.Expr.var ()) with
  | none => simp [hE] at h1
  | some K =>
    simp [hE] at h1 h2
    obtain ⟨lo, hi⟩ := K
    change lo = -7 at h1
    change hi = 7 at h2
    rw [h1, h2]

#print axioms evalF_var_accepts

/-- `evalF` evaluates negation by negating and swapping the variable bounds. -/
theorem evalF_neg_var :
    evalF 3 (-2) 0 (fun _ : Unit => ⟨-7/4, 5/2⟩)
        (RatInterval.Expr.neg (RatInterval.Expr.var ())) = some ⟨-5/2, 7/4⟩ := by
  have h1 : (evalF 3 (-2) 0 (fun _ : Unit => ⟨-7/4, 5/2⟩)
      (RatInterval.Expr.neg (RatInterval.Expr.var ()))).map RatInterval.lower
      = some (-5 / 2 : ℚ) := by decide +kernel
  have h2 : (evalF 3 (-2) 0 (fun _ : Unit => ⟨-7/4, 5/2⟩)
      (RatInterval.Expr.neg (RatInterval.Expr.var ()))).map RatInterval.upper
      = some (7 / 4 : ℚ) := by decide +kernel
  cases hE : evalF 3 (-2) 0 (fun _ : Unit => ⟨-7/4, 5/2⟩)
      (RatInterval.Expr.neg (RatInterval.Expr.var ())) with
  | none => simp [hE] at h1
  | some K =>
    simp [hE] at h1 h2
    obtain ⟨lo, hi⟩ := K
    change lo = -5 / 2 at h1
    change hi = 7 / 4 at h2
    rw [h1, h2]

#print axioms evalF_neg_var

/-- For `|x + y| ≤ 7`, rounded sums are the extremal `testVals` below and above the exact sum. -/
theorem scalar_extremal : ∀ x ∈ testVals, ∀ y ∈ testVals, |x + y| ≤ 7 →
    some (rd 3 (-2) (x + y)) = (testVals.filter (· ≤ x + y)).max? ∧
    some (ru 3 (-2) (x + y)) = (testVals.filter (x + y ≤ ·)).min? := by
  intro x _ y _ hle
  have hleM : |x + y| ≤ maxFloat 3 0 := by
    rw [hmaxFloat_test]
    exact hle
  have hrdmem : rd 3 (-2) (x + y) ∈ testVals :=
    isFloatIn_testFormat_iff.mp (rd_isFloatIn hp_testFormat hq_testFormat hleM)
  have hrumem : ru 3 (-2) (x + y) ∈ testVals :=
    isFloatIn_testFormat_iff.mp (ru_isFloatIn hp_testFormat hq_testFormat hleM)
  constructor
  · symm
    rw [List.max?_eq_some_iff]
    refine ⟨?_, ?_⟩
    · simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨hrdmem, rd_le 3 (-2) (x + y)⟩
    · intro b hb
      simp only [List.mem_filter, decide_eq_true_eq] at hb
      obtain ⟨hbmem, hble⟩ := hb
      exact le_rd_of_isFloatIn hp_testFormat hq_testFormat hleM
        (isFloatIn_testFormat_iff.mpr hbmem) hble
  · symm
    rw [List.min?_eq_some_iff]
    refine ⟨?_, ?_⟩
    · simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨hrumem, le_ru 3 (-2) (x + y)⟩
    · intro b hb
      simp only [List.mem_filter, decide_eq_true_eq] at hb
      obtain ⟨hbmem, hbge⟩ := hb
      exact ru_le_of_isFloatIn hp_testFormat hq_testFormat hleM
        (isFloatIn_testFormat_iff.mpr hbmem) hbge

#print axioms scalar_extremal

#print axioms rd_isFloatIn

#print axioms ru_isFloatIn

#print axioms le_rd_of_isFloatIn

#print axioms ru_le_of_isFloatIn

#print axioms floatOk_eq_true_iff

#print axioms addF_widen

#print axioms subF_widen

#print axioms mulF_widen

#print axioms evalF_widen

#print axioms evalF_encloses

end Cslib.Algorithms.Lean.FloatInterval
