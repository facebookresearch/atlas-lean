/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Set.Function
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# ABSOLUTE copy-ratio and allelic-fraction algebra

A tumor DNA sample is a mixture of a fraction `α` (the purity) of cancer cells and `1 - α` of
diploid normal cells. A locus with integer copy number `q` in the cancer cells has average
absolute copy number `α q + 2 (1 - α)` in the mixture (`mixCopy α q`), and the sample's average
ploidy is `D = α τ + 2 (1 - α) = mixCopy α τ`, where `τ` is the cancer-cell ploidy (the genome
average of `q`). Copy numbers are in units of haploid genomes. Carter et al. (2012) read off:

* the relative copy ratio `R = (α q + 2 (1 - α)) / D = (α / D) q + 2 (1 - α) / D` (Eq. 1);
* the allelic fraction `α s / (α q + 2 (1 - α))` of a somatic mutation present in `s` copies
  per cancer cell (Eq. 2; Eq. 10 is the case `s = 1`);
* the allelic fraction `((1 - α) + α g) / (α q + 2 (1 - α))` of a heterozygous germline variant
  present in `g` copies per cancer cell (Eq. 11).

All definitions are total functions of real arguments. The biological domain is
`0 ≤ α ≤ 1`, `0 ≤ q`, `0 < τ`, `0 ≤ s ≤ q`, and the identities below state their hypotheses.

## Main results

* `copyRatio_eq_slope_mul_add_intercept`: `R` is affine in `q` with slope `α / D` and
  intercept `2 (1 - α) / D` (Eq. 1); this holds for all real arguments.
* `sum_mul_copyRatio_eq_one`: with segment weights summing to one and `τ` the weighted mean of
  `q`, the weighted mean copy ratio is `1`.
* `somaticAF_eq_slope_mul_div_copyRatio`: allelic fractions are determined by the copy-ratio
  slope, `α s / D_s = (α / D) s / R`.
* `bijOn_slope_intercept`: `(α, τ) ↦ (α / D, 2 (1 - α) / D)` is a bijection from
  `{0 < α ≤ 1, 0 < τ}` onto `{0 < b, 0 ≤ δ < 1}`, with inverse
  `α = 2 b / (2 b + δ)`, `τ = (1 - δ) / b` (`purity_eq`, `ploidy_eq`). Carter et al. search
  over the equivalent pair `(2 (1 - α), α / D)`; the bijection is stated here for the two
  coefficients of Eq. 1.
* `somaticAF_mono_purity`, `somaticAF_anti_copy`, `somaticAF_mono_mult`: the somatic allelic
  fraction increases with purity and multiplicity and decreases with copy number.
* `copyRatio_scale`, `somaticAF_scale`, `germlineAF_scale`: ploidy-scaling
  non-identifiability. Multiplying every copy number, multiplicity and the ploidy by `m > 0`
  and replacing the purity by `α / (m - (m - 1) α)` leaves every copy ratio and allelic fraction
  unchanged; `scaledPurity_ne` shows the purity really changes when `0 < α < 1` and `m ≠ 1`.
  The genome-doubling case is `m = 2`, purity `α / (2 - α)` (`copyRatio_doubling`).

The explicit rescaled purity `α / (m - (m - 1) α)` is derived here from Eqs. 1, 2 and 11; Carter
et al. describe the ambiguity (a profile without alterations fits ploidy 1, 2, 3, …, and
genome-doubled solutions) but do not state this formula.

## References

* S. L. Carter et al., *Absolute quantification of somatic DNA alterations in human cancer*,
  Nat. Biotechnol. 30 (2012), 413–421 (Eqs. 1, 2, 10, 11).
-/

@[expose] public section

namespace MathlibExt.Biology.CancerGenomics.Absolute

/-- Average absolute copy number `α q + 2 (1 - α)` of a locus with copy number `q` in the cancer
cells, in a sample of purity `α` whose normal cells are diploid (Carter et al. 2012). With
`q = τ` this is the sample ploidy `D` of Eq. 1; with the local copy number it is `D_s` of
Eq. 2. -/
def mixCopy (α q : ℝ) : ℝ := α * q + 2 * (1 - α)

/-- Relative copy ratio `R = (α q + 2 (1 - α)) / (α τ + 2 (1 - α))` of a locus with copy number
`q`, purity `α` and cancer-cell ploidy `τ` (Carter et al. 2012, Eq. 1). -/
noncomputable def copyRatio (α τ q : ℝ) : ℝ := mixCopy α q / mixCopy α τ

/-- The copy-ratio slope `α / D` of Eq. 1 (Carter et al. 2012), the copy ratio of one extra
copy per cancer cell. -/
noncomputable def slope (α τ : ℝ) : ℝ := α / mixCopy α τ

/-- The copy-ratio intercept `2 (1 - α) / D` of Eq. 1 (Carter et al. 2012), the copy ratio of a
homozygously deleted locus. -/
noncomputable def intercept (α τ : ℝ) : ℝ := 2 * (1 - α) / mixCopy α τ

/-- Expected allelic fraction `α s / (α q + 2 (1 - α))` of a clonal somatic point mutation with
multiplicity `s` (copies per cancer cell) at a locus of copy number `q` (Carter et al. 2012,
Eq. 2; Eq. 10 is `s = 1`). -/
noncomputable def somaticAF (α q s : ℝ) : ℝ := α * s / mixCopy α q

/-- Expected allelic fraction `((1 - α) + α g) / (α q + 2 (1 - α))` of a heterozygous germline
variant present in `g` copies per cancer cell at a locus of copy number `q` (Carter et al.
2012, Eq. 11). -/
noncomputable def germlineAF (α q g : ℝ) : ℝ := ((1 - α) + α * g) / mixCopy α q

/-- The purity `α / (m - (m - 1) α)` that, together with all copy numbers multiplied by `m`,
reproduces the copy ratios and allelic fractions of purity `α` (derived from Carter et al.
2012, Eqs. 1, 2, 11). -/
noncomputable def scaledPurity (m α : ℝ) : ℝ := α / (m - (m - 1) * α)

/-- The mixture copy number is positive in the biological domain `0 ≤ α ≤ 1`, `0 < q`. -/
theorem mixCopy_pos {α q : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hq : 0 < q) :
    0 < mixCopy α q := by
  unfold mixCopy
  rcases hα0.lt_or_eq with h | h
  · nlinarith
  · subst h; norm_num

/-- **Eq. 1 is affine in `q`**: `R = (α / D) q + 2 (1 - α) / D`, for all real arguments. -/
theorem copyRatio_eq_slope_mul_add_intercept (α τ q : ℝ) :
    copyRatio α τ q = slope α τ * q + intercept α τ := by
  unfold copyRatio slope intercept mixCopy
  rw [div_mul_eq_mul_div, ← add_div]

/-- **Calibrated copy ratios have mean `1`**: if the segment weights `w` sum to one and the
ploidy is the weighted mean copy number `τ = ∑ w q`, the weighted mean copy ratio is `1`
(Carter et al. 2012, Methods: "correctly calibrated copy-ratio data always has mean = 1"). -/
theorem sum_mul_copyRatio_eq_one {ι : Type*} (s : Finset ι) (w q : ι → ℝ) {α : ℝ}
    (hw : ∑ i ∈ s, w i = 1) (hD : mixCopy α (∑ i ∈ s, w i * q i) ≠ 0) :
    ∑ i ∈ s, w i * copyRatio α (∑ j ∈ s, w j * q j) (q i) = 1 := by
  unfold copyRatio
  simp_rw [mul_div_assoc', ← Finset.sum_div]
  rw [div_eq_one_iff_eq hD]
  unfold mixCopy
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul]
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => by ring

/-- **Allelic fractions are determined by the copy-ratio slope** (Carter et al. 2012, Eq. 2):
`α s / D_s = (α / D) s / R`, whenever `D ≠ 0`. -/
theorem somaticAF_eq_slope_mul_div_copyRatio {α τ q : ℝ} (s : ℝ) (hD : mixCopy α τ ≠ 0) :
    somaticAF α q s = slope α τ * s / copyRatio α τ q := by
  unfold somaticAF slope copyRatio
  rw [div_mul_eq_mul_div, div_div_div_cancel_right₀ hD]

/-- Inverse of Eq. 1, purity: `α = 2 b / (2 b + δ)` for the slope `b` and intercept `δ`, when
`0 < α ≤ 1` and `0 < τ`. -/
theorem purity_eq {α τ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hτ : 0 < τ) :
    α = 2 * slope α τ / (2 * slope α τ + intercept α τ) := by
  have hD := mixCopy_pos hα0.le hα1 hτ
  unfold slope intercept
  field_simp
  ring

/-- Inverse of Eq. 1, ploidy: `τ = (1 - δ) / b` for the slope `b` and intercept `δ`, when
`0 < α ≤ 1` and `0 < τ`. -/
theorem ploidy_eq {α τ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hτ : 0 < τ) :
    τ = (1 - intercept α τ) / slope α τ := by
  have hD := mixCopy_pos hα0.le hα1 hτ
  unfold slope intercept
  field_simp
  unfold mixCopy
  ring

/-- **Purity and ploidy are identifiable from the slope and intercept of Eq. 1**: the map
`(α, τ) ↦ (α / D, 2 (1 - α) / D)` is a bijection from `{0 < α ≤ 1, 0 < τ}` onto
`{0 < b, 0 ≤ δ < 1}`. -/
theorem bijOn_slope_intercept :
    Set.BijOn (fun p : ℝ × ℝ => (slope p.1 p.2, intercept p.1 p.2))
      {p | 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2} {x | 0 < x.1 ∧ 0 ≤ x.2 ∧ x.2 < 1} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨α, τ⟩ ⟨hα0, hα1, hτ⟩
    have hD := mixCopy_pos hα0.le hα1 hτ
    refine ⟨div_pos hα0 hD, div_nonneg (by linarith) hD.le, ?_⟩
    change 2 * (1 - α) / mixCopy α τ < 1
    rw [div_lt_one hD]
    unfold mixCopy
    nlinarith
  · rintro ⟨α, τ⟩ ⟨hα0, hα1, hτ⟩ ⟨α', τ'⟩ ⟨hα0', hα1', hτ'⟩ h
    simp only [Prod.mk.injEq] at h hα0 hα1 hτ hα0' hα1' hτ' ⊢
    have e1 := purity_eq hα0 hα1 hτ
    have e2 := purity_eq hα0' hα1' hτ'
    have f1 := ploidy_eq hα0 hα1 hτ
    have f2 := ploidy_eq hα0' hα1' hτ'
    constructor
    · rw [e1, e2, h.1, h.2]
    · rw [f1, f2, h.1, h.2]
  · rintro ⟨b, δ⟩ ⟨hb, hδ0, hδ1⟩
    refine ⟨(2 * b / (2 * b + δ), (1 - δ) / b), ⟨?_, ?_, ?_⟩, ?_⟩
    · positivity
    · change 2 * b / (2 * b + δ) ≤ 1
      rw [div_le_one (by positivity)]
      linarith
    · change 0 < (1 - δ) / b
      exact div_pos (by linarith) hb
    · have h2 : (0 : ℝ) < 2 * b + δ := by positivity
      have hD : mixCopy (2 * b / (2 * b + δ)) ((1 - δ) / b) = 2 / (2 * b + δ) := by
        unfold mixCopy
        field_simp
        ring
      simp only [Prod.mk.injEq, slope, intercept, hD]
      constructor
      · field_simp
      · field_simp
        ring

/-- The denominator `m - (m - 1) α = m (1 - α) + α` of the rescaled purity is positive for
`m > 0` and `0 ≤ α ≤ 1`. -/
theorem scaledPurity_denom_pos {m α : ℝ} (hm : 0 < m) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    0 < m - (m - 1) * α := by
  rcases hα0.lt_or_eq with h | h
  · nlinarith [mul_nonneg hm.le (sub_nonneg.2 hα1)]
  · subst h; simpa using hm

/-- The rescaled purity is again a purity: `0 ≤ α / (m - (m - 1) α) ≤ 1` for `m > 0` and
`0 ≤ α ≤ 1`. -/
theorem scaledPurity_mem {m α : ℝ} (hm : 0 < m) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    0 ≤ scaledPurity m α ∧ scaledPurity m α ≤ 1 := by
  have h := scaledPurity_denom_pos hm hα0 hα1
  unfold scaledPurity
  refine ⟨div_nonneg hα0 h.le, ?_⟩
  rw [div_le_one h]
  nlinarith [mul_nonneg hm.le (sub_nonneg.2 hα1)]

private theorem mixCopy_scale {m α : ℝ} (hm : 0 < m) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (q : ℝ) :
    mixCopy (scaledPurity m α) (m * q) = m * mixCopy α q / (m - (m - 1) * α) := by
  have he := (scaledPurity_denom_pos hm hα0 hα1).ne'
  unfold mixCopy scaledPurity
  set e := m - (m - 1) * α with hdef
  rw [eq_div_iff he]
  field_simp
  rw [hdef]
  ring

/-- **Ploidy-scaling non-identifiability, copy ratios**: scaling every copy number and the
ploidy by `m > 0` and the purity to `α / (m - (m - 1) α)` leaves every copy ratio of Eq. 1
unchanged. -/
theorem copyRatio_scale {m α : ℝ} (hm : 0 < m) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (τ q : ℝ) :
    copyRatio (scaledPurity m α) (m * τ) (m * q) = copyRatio α τ q := by
  have he := (scaledPurity_denom_pos hm hα0 hα1).ne'
  unfold copyRatio
  rw [mixCopy_scale hm hα0 hα1, mixCopy_scale hm hα0 hα1]
  rcases eq_or_ne (mixCopy α τ) 0 with hτ | hτ
  · simp [hτ]
  · rw [div_div_div_cancel_right₀ he, mul_div_mul_left _ _ hm.ne']

/-- **Ploidy-scaling non-identifiability, somatic allelic fractions** (Eq. 2): with copy
number and multiplicity both scaled by `m > 0` and the purity rescaled, the allelic fraction is
unchanged. -/
theorem somaticAF_scale {m α : ℝ} (hm : 0 < m) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (q s : ℝ) :
    somaticAF (scaledPurity m α) (m * q) (m * s) = somaticAF α q s := by
  have he := (scaledPurity_denom_pos hm hα0 hα1).ne'
  unfold somaticAF
  rw [mixCopy_scale hm hα0 hα1]
  unfold scaledPurity
  rcases eq_or_ne (mixCopy α q) 0 with hq | hq
  · simp [hq]
  · rw [div_eq_div_iff (div_ne_zero (mul_ne_zero hm.ne' hq) he) hq]
    field_simp

/-- **Ploidy-scaling non-identifiability, germline allelic fractions** (Eq. 11): with copy
number and germline multiplicity both scaled by `m > 0` and the purity rescaled, the allelic
fraction is unchanged. -/
theorem germlineAF_scale {m α : ℝ} (hm : 0 < m) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (q g : ℝ) :
    germlineAF (scaledPurity m α) (m * q) (m * g) = germlineAF α q g := by
  have he := (scaledPurity_denom_pos hm hα0 hα1).ne'
  unfold germlineAF
  rw [mixCopy_scale hm hα0 hα1]
  unfold scaledPurity
  rcases eq_or_ne (mixCopy α q) 0 with hq | hq
  · simp [hq]
  · set e := m - (m - 1) * α with hdef
    rw [div_eq_div_iff (div_ne_zero (mul_ne_zero hm.ne' hq) he) hq]
    field_simp
    rw [hdef]
    ring

/-- The rescaled solution is a genuinely different purity: for `0 < α < 1` and `m ≠ 1`,
`α / (m - (m - 1) α) ≠ α`. -/
theorem scaledPurity_ne {m α : ℝ} (hm : 0 < m) (hm1 : m ≠ 1) (hα0 : 0 < α) (hα1 : α < 1) :
    scaledPurity m α ≠ α := by
  have h := scaledPurity_denom_pos hm hα0.le hα1.le
  unfold scaledPurity
  rw [Ne, div_eq_iff h.ne']
  intro hc
  have : (m - 1) * (1 - α) * α = 0 := by linear_combination -hc
  rcases mul_eq_zero.1 this with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact hm1 (by linarith)
    · linarith
  · linarith

/-- **Genome doubling**: doubling every copy number and the ploidy and replacing the purity by
`α / (2 - α)` reproduces every copy ratio (the `m = 2` case of `copyRatio_scale`). -/
theorem copyRatio_doubling {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (τ q : ℝ) :
    copyRatio (α / (2 - α)) (2 * τ) (2 * q) = copyRatio α τ q := by
  have := copyRatio_scale (m := 2) two_pos hα0 hα1 τ q
  unfold scaledPurity at this
  norm_num at this
  exact this

/-- Somatic allelic fractions are nonnegative in the biological domain. -/
theorem somaticAF_nonneg {α q s : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hq : 0 < q) (hs : 0 ≤ s) :
    0 ≤ somaticAF α q s :=
  div_nonneg (mul_nonneg hα0 hs) (mixCopy_pos hα0 hα1 hq).le

/-- A somatic allelic fraction is at most one when the multiplicity does not exceed the copy
number (`s ≤ q`). -/
theorem somaticAF_le_one {α q s : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hq : 0 < q) (hsq : s ≤ q) :
    somaticAF α q s ≤ 1 := by
  have hD := mixCopy_pos hα0 hα1 hq
  unfold somaticAF
  rw [div_le_one hD]
  unfold mixCopy
  nlinarith [mul_le_mul_of_nonneg_left hsq hα0]

/-- The somatic allelic fraction increases with the purity (`0 ≤ s`, `0 < q`). -/
theorem somaticAF_mono_purity {α α' q s : ℝ} (hα0 : 0 ≤ α) (hαα' : α ≤ α') (hα1 : α' ≤ 1)
    (hq : 0 < q) (hs : 0 ≤ s) : somaticAF α q s ≤ somaticAF α' q s := by
  have hD := mixCopy_pos hα0 (hαα'.trans hα1) hq
  have hD' := mixCopy_pos (hα0.trans hαα') hα1 hq
  unfold somaticAF
  rw [div_le_div_iff₀ hD hD']
  unfold mixCopy
  nlinarith [mul_le_mul_of_nonneg_right hαα' hs]

/-- The somatic allelic fraction decreases with the local copy number (`0 ≤ α ≤ 1`,
`0 ≤ s`, `0 < q ≤ q'`). -/
theorem somaticAF_anti_copy {α q q' s : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hq : 0 < q)
    (hqq' : q ≤ q') (hs : 0 ≤ s) : somaticAF α q' s ≤ somaticAF α q s := by
  have hD := mixCopy_pos hα0 hα1 hq
  unfold somaticAF
  refine div_le_div_of_nonneg_left (mul_nonneg hα0 hs) hD ?_
  unfold mixCopy
  nlinarith [mul_le_mul_of_nonneg_left hqq' hα0]

/-- The somatic allelic fraction increases with the multiplicity (`0 ≤ α ≤ 1`, `0 < q`). -/
theorem somaticAF_mono_mult {α q s s' : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hq : 0 < q)
    (hss' : s ≤ s') : somaticAF α q s ≤ somaticAF α q s' := by
  unfold somaticAF
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hss' hα0)
    (mixCopy_pos hα0 hα1 hq).le

end MathlibExt.Biology.CancerGenomics.Absolute
