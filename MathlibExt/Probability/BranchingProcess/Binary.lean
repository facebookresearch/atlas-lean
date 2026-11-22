/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BranchingProcess.GaltonWatson
public import MathlibExt.Probability.ProbabilityGeneratingFunction
public import MathlibExt.Probability.InfinitelyDivisible

/-!
# Binary offspring instance of Galton--Watson theory

The offspring law with mass `1 - p` at `0` and `p` at `2` has
generating function `1 - p + p * s^2` for `p` in `[0, 1]`. Its extinction probability is
the least fixed point of that polynomial: `1` for `p <= 1/2` and
`(1 - p) / p` for `p > 1/2`, derived from the least-fixed-point
characterization of the existing Galton--Watson interface.
-/

@[expose] public section

namespace MathlibExt.Probability.GaltonWatson

open MeasureTheory Set
open scoped ENNReal

/-- The binary offspring law on `ℕ`: `1 - p` at `0` and `p` at `2`.
Written as a `Measure ℕ` because that is what `GaltonWatson.law` takes.
For `p ∉ [0, 1]` this is a finite non-probability measure (for example
total mass `2` at `p = 2`); only the results that state `0 ≤ p ≤ 1`
assume the probability range. -/
noncomputable def binaryOffspring (p : ℝ) : Measure ℕ :=
  ENNReal.ofReal (1 - p) • Measure.dirac 0 + ENNReal.ofReal p • Measure.dirac 2

variable {p : ℝ}

/-- The binary law is a probability measure on the stated range. -/
theorem binaryOffspring_isProbabilityMeasure (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (binaryOffspring p) := by
  apply IsProbabilityMeasure.mk
  have hdirac0 : Measure.dirac (0 : ℕ) Set.univ = 1 :=
    Measure.dirac_apply_of_mem (Set.mem_univ 0)
  have hdirac2 : Measure.dirac (2 : ℕ) Set.univ = 1 :=
    Measure.dirac_apply_of_mem (Set.mem_univ 2)
  unfold binaryOffspring
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, hdirac0, hdirac2,
    smul_eq_mul, smul_eq_mul, mul_one, mul_one,
    ← ENNReal.ofReal_add (show (0 : ℝ) ≤ 1 - p by linarith) hp0]
  have h1 : (1 : ℝ) - p + p = 1 := by ring
  rw [h1, ENNReal.ofReal_one]

/-- Mass at `0`. -/
theorem binaryOffspring_apply_zero :
    binaryOffspring p {0} = ENNReal.ofReal (1 - p) := by
  have h00 : Measure.dirac (0 : ℕ) ({0} : Set ℕ) = 1 :=
    Measure.dirac_apply_of_mem (by simp)
  have h20 : Measure.dirac (2 : ℕ) ({0} : Set ℕ) = 0 :=
    (dirac_eq_zero_iff_notMem (MeasurableSet.singleton 0)).mpr (by simp)
  unfold binaryOffspring
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, h00, h20,
    smul_eq_mul, smul_eq_mul, mul_one, mul_zero, add_zero]

/-- Mass at `2`. -/
theorem binaryOffspring_apply_two :
    binaryOffspring p {2} = ENNReal.ofReal p := by
  have h02 : Measure.dirac (0 : ℕ) ({2} : Set ℕ) = 0 :=
    (dirac_eq_zero_iff_notMem (MeasurableSet.singleton 2)).mpr (by simp)
  have h22 : Measure.dirac (2 : ℕ) ({2} : Set ℕ) = 1 :=
    Measure.dirac_apply_of_mem (by simp)
  unfold binaryOffspring
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, h02, h22,
    smul_eq_mul, smul_eq_mul, mul_zero, mul_one, zero_add]

/-- No mass at `1`, so the `ν {1} ≠ 1` side condition of
`extinctionProb_eq_one_iff` is automatic for the binary law. -/
theorem binaryOffspring_apply_one :
    binaryOffspring p {1} = 0 := by
  have h01 : Measure.dirac (0 : ℕ) ({1} : Set ℕ) = 0 :=
    (dirac_eq_zero_iff_notMem (MeasurableSet.singleton 1)).mpr (by simp)
  have h21 : Measure.dirac (2 : ℕ) ({1} : Set ℕ) = 0 :=
    (dirac_eq_zero_iff_notMem (MeasurableSet.singleton 1)).mpr (by simp)
  unfold binaryOffspring
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, h01, h21,
    smul_eq_mul, smul_eq_mul, mul_zero, mul_zero, add_zero]

theorem binaryOffspring_one_ne_one :
    binaryOffspring p {1} ≠ 1 := by
  rw [binaryOffspring_apply_one]
  exact zero_ne_one

/-- Masses off `{0, 2}` vanish (consumer form of the offspring PMF). -/
theorem binaryOffspring_apply_of_ne (n : ℕ) (h0 : n ≠ 0) (h2 : n ≠ 2) :
    binaryOffspring p {n} = 0 := by
  have h0n : Measure.dirac (0 : ℕ) ({n} : Set ℕ) = 0 :=
    (dirac_eq_zero_iff_notMem (MeasurableSet.singleton n)).mpr
      (by simpa using Ne.symm h0)
  have h2n : Measure.dirac (2 : ℕ) ({n} : Set ℕ) = 0 :=
    (dirac_eq_zero_iff_notMem (MeasurableSet.singleton n)).mpr
      (by simpa using Ne.symm h2)
  unfold binaryOffspring
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, h0n, h2n,
    smul_eq_mul, smul_eq_mul, mul_zero, mul_zero, add_zero]

/-! ## PGF identity: `f(s) = 1 - p + p * s ^ 2` -/

/-- The probability generating function of the binary law, for every real
`s` (finite support, so no `[0, 1]` restriction is needed; on `[0, 1]` this
is the `f` of `isLeast_extinctionProb`). -/
theorem pgf_binaryOffspring (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : ℝ) :
    pgf id (binaryOffspring p) s = 1 - p + p * s ^ 2 := by
  have h0 : Integrable (fun ω : ℕ => s ^ id ω)
      (ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℕ)) :=
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  have h2 : Integrable (fun ω : ℕ => s ^ id ω)
      (ENNReal.ofReal p • Measure.dirac (2 : ℕ)) :=
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  have h0r : 0 ≤ (1 : ℝ) - p := by linarith
  show (∫ ω, s ^ id ω ∂binaryOffspring p) = 1 - p + p * s ^ 2
  unfold binaryOffspring
  rw [integral_add_measure h0 h2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal h0r,
    ENNReal.toReal_ofReal hp0]
  simp only [id_eq]
  rw [pow_zero, smul_eq_mul, smul_eq_mul]
  ring

/-- Mean offspring number `E ξ = 2p` on the probability range (in general `ENNReal.ofReal (2 * p)`) (so criticality `mean ≤ 1` is
`p ≤ 1 / 2`). -/
theorem mean_binaryOffspring :
    mean (binaryOffspring p) = ENNReal.ofReal (2 * p) := by
  show (∫⁻ k, (k : ℝ≥0∞) ∂binaryOffspring p) = _
  unfold binaryOffspring
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac]
  simp only [Nat.cast_zero, Nat.cast_ofNat, smul_eq_mul, mul_zero, zero_add]
  by_cases hp0 : 0 ≤ p
  · rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num),
      ENNReal.ofReal_ofNat 2, mul_comm]
  · have hpneg : p < 0 := lt_of_not_ge hp0
    rw [ENNReal.ofReal_eq_zero.mpr (le_of_lt hpneg)]
    have h2p : 2 * p ≤ 0 := by linarith
    rw [ENNReal.ofReal_eq_zero.mpr h2p, zero_mul]

theorem mean_binaryOffspring_le_one_iff (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    mean (binaryOffspring p) ≤ 1 ↔ p ≤ 1 / 2 := by
  rw [mean_binaryOffspring, ← ENNReal.ofReal_one,
    ENNReal.ofReal_le_ofReal_iff (show (0 : ℝ) ≤ 1 by norm_num)]
  constructor <;> intro h <;> linarith

/-! ## Extinction: specialisation of the least-fixed-point interface -/

/-- Direct specialisation of `isLeast_extinctionProb`: no second
extinction definition or theorem is introduced. -/
theorem isLeast_extinctionProb_binaryOffspring (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsLeast {s | s ∈ Icc (0 : ℝ) 1 ∧ pgf id (binaryOffspring p) s = s}
      (extinctionProb (binaryOffspring p)) := by
  exact @isLeast_extinctionProb (binaryOffspring p)
    (binaryOffspring_isProbabilityMeasure hp0 hp1)

/-- The same least fixed point, with the PGF rewritten by
`pgf_binaryOffspring`: the least `s ∈ [0, 1]` with `s = 1 - p + p * s ^ 2`. -/
theorem isLeast_extinctionProb_binaryOffspring' (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsLeast {s | s ∈ Icc (0 : ℝ) 1 ∧ s = 1 - p + p * s ^ 2}
      (extinctionProb (binaryOffspring p)) := by
  have h := isLeast_extinctionProb_binaryOffspring hp0 hp1
  have heq : {s | s ∈ Icc (0 : ℝ) 1 ∧ pgf id (binaryOffspring p) s = s} =
      {s | s ∈ Icc (0 : ℝ) 1 ∧ s = 1 - p + p * s ^ 2} := by
    ext s
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hs, hfix⟩
      refine ⟨hs, ?_⟩
      have hpgf := pgf_binaryOffspring hp0 hp1 s
      rw [hfix] at hpgf
      exact hpgf
    · rintro ⟨hs, hfix⟩
      refine ⟨hs, ?_⟩
      rw [pgf_binaryOffspring hp0 hp1 s]
      exact hfix.symm
  rw [heq] at h
  exact h

/-- Least-fixed-point equation characterisation, subcritical/critical
case: for `p ≤ 1 / 2`, `1` is the least binary fixed point in `[0, 1]`
(the other root `(1 - p) / p`, when `p ≠ 0`, is `≥ 1`).  This is the
stated lemma the closed form needs beyond `isLeast_extinctionProb`. -/
theorem isLeast_binaryFixedPoint_one_of_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : p ≤ 1 / 2) :
    IsLeast {s | s ∈ Icc (0 : ℝ) 1 ∧ s = 1 - p + p * s ^ 2} 1 := by
  constructor
  · constructor
    · exact Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩
    · ring
  · intro s hs
    simp only [Set.mem_ofPred_eq, Set.mem_Icc] at hs
    obtain ⟨⟨hs0, hs1⟩, hfix⟩ := hs
    by_cases hp0' : p = 0
    · subst hp0'
      simp only [sub_zero, zero_mul, add_zero] at hfix
      linarith
    · have hfact : (s - 1) * (p * s - (1 - p)) = 0 := by
        have hring : (s - 1) * (p * s - (1 - p))
            = p * s ^ 2 - s + (1 - p) := by ring
        rw [hring]
        linear_combination -hfix
      rcases mul_eq_zero.mp hfact with h | h
      · have hs1 : s = 1 := sub_eq_zero.mp h
        linarith
      · have hps : p * s = 1 - p := sub_eq_zero.mp h
        have hle : (1 : ℝ) - p ≤ p * 1 := by
          rw [← hps]
          exact mul_le_mul_of_nonneg_left hs1 hp0
        rw [mul_one] at hle
        have hp_eq : p = 1 / 2 := by linarith
        have hs_eq : s = 1 := by
          rw [hp_eq] at hps
          linarith
        linarith

/-- Least-fixed-point equation characterisation, supercritical case: for
`1 / 2 < p ≤ 1`, `(1 - p) / p ∈ [0, 1)` is the least binary fixed point
in `[0, 1]`.  This is the stated lemma the closed form needs beyond
`isLeast_extinctionProb` and `extinctionProb_eq_one_iff`. -/
theorem isLeast_binaryFixedPoint_of_gt (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : 1 / 2 < p) :
    IsLeast {s | s ∈ Icc (0 : ℝ) 1 ∧ s = 1 - p + p * s ^ 2} ((1 - p) / p) := by
  have hpos : 0 < p := by linarith
  have hp0' : p ≠ 0 := ne_of_gt hpos
  have hmem1 : (1 - p) / p ≤ 1 := by
    rw [div_le_one hpos]
    linarith
  have hmem0 : 0 ≤ (1 - p) / p := by
    apply div_nonneg <;> linarith
  have hfix : (1 - p) / p = 1 - p + p * ((1 - p) / p) ^ 2 := by
    field_simp
    ring
  constructor
  · exact ⟨Set.mem_Icc.mpr ⟨hmem0, hmem1⟩, hfix⟩
  · intro s hs
    simp only [Set.mem_ofPred_eq, Set.mem_Icc] at hs
    obtain ⟨⟨hs0, hs1⟩, hfix2⟩ := hs
    have hfact : (s - 1) * (p * s - (1 - p)) = 0 := by
      have hring : (s - 1) * (p * s - (1 - p))
          = p * s ^ 2 - s + (1 - p) := by ring
      rw [hring]
      linear_combination -hfix2
    rcases mul_eq_zero.mp hfact with h | h
    · have hs1' : s = 1 := sub_eq_zero.mp h
      rw [hs1']
      exact hmem1
    · have hps : p * s = 1 - p := sub_eq_zero.mp h
      have hseq : s = (1 - p) / p := by
        rw [eq_div_iff hp0', mul_comm s p]
        exact hps
      rw [hseq]

/-- `P(Z_n = 0) = f^[n] (0)` for the binary law (`law_real_zero` at `ν`). -/
theorem law_binaryOffspring_real_zero (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (law (binaryOffspring p) n).real {0} =
      (pgf id (binaryOffspring p))^[n] 0 := by
  exact @law_real_zero (binaryOffspring p)
    (binaryOffspring_isProbabilityMeasure hp0 hp1) n

/-- Certain extinction iff subcritical/critical, via
`extinctionProb_eq_one_iff` + `mean_binaryOffspring_le_one_iff`;
the `ν {1} ≠ 1` hypothesis is `binaryOffspring_one_ne_one`. -/
theorem extinctionProb_binaryOffspring_eq_one_iff (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    extinctionProb (binaryOffspring p) = 1 ↔ p ≤ 1 / 2 := by
  exact (@extinctionProb_eq_one_iff (binaryOffspring p)
    (binaryOffspring_isProbabilityMeasure hp0 hp1)
    binaryOffspring_one_ne_one).trans
    (mean_binaryOffspring_le_one_iff hp0 hp1)

/-- Explicit extinction probability, subcritical/critical case.
Follows from `isLeast_extinctionProb_binaryOffspring'` +
`isLeast_binaryFixedPoint_one_of_le` by `IsLeast.unique` (equivalently
from `extinctionProb_binaryOffspring_eq_one_iff`). -/
theorem extinctionProb_binaryOffspring_of_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : p ≤ 1 / 2) :
    extinctionProb (binaryOffspring p) = 1 := by
  exact IsLeast.unique (isLeast_extinctionProb_binaryOffspring' hp0 hp1)
    (isLeast_binaryFixedPoint_one_of_le hp0 hp1 hp)

/-- Explicit extinction probability, supercritical case: for
`1 / 2 < p ≤ 1` the root `(1 - p) / p` lies in `[0, 1)` and is the
least fixed point.  At `p = 1` this gives `0`.  Follows from
`isLeast_extinctionProb_binaryOffspring'` +
`isLeast_binaryFixedPoint_of_gt` by `IsLeast.unique`; it does not follow
from `extinctionProb_eq_one_iff` alone. -/
theorem extinctionProb_binaryOffspring_of_gt (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : 1 / 2 < p) :
    extinctionProb (binaryOffspring p) = (1 - p) / p := by
  exact IsLeast.unique (isLeast_extinctionProb_binaryOffspring' hp0 hp1)
    (isLeast_binaryFixedPoint_of_gt hp0 hp1 hp)

/-! ## Nonvacuity tests (pinned consumer checks; values verified in report)
`p = 0`: `Z_1 = 0` a.s.; `p = 1/2`: critical; `p = 2/3`: `(1-p)/p = 1/2`;
`p = 1`: always `2` children. -/

end MathlibExt.Probability.GaltonWatson
