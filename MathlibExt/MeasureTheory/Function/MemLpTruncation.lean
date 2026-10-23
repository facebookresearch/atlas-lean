/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.MeasureTheory.Function.MemLpTruncation

/-!
# `L^p` membership via truncated integrals on `ℝ`

For a measurable set `S ⊆ ℝ` and `1 ≤ p < ∞`, a measurable function `f : ℝ → F`
belongs to `L^p (S)` if and only if the integrals of `‖f‖ ^ p` over the truncations
`[-n, n] ∩ S` stay bounded, i.e. their supremum is finite. Since those truncated
integrals increase with `n`, the supremum is the limit of the truncated integrals,
which is the statement in the book.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/LpSpaces.lean`,
`LpSpaces.lintegral_eq_iSup_lintegral_Icc_inter` and
`LpSpaces.memLp_iff_iSup_lintegral_Icc_inter_lt_top`
(Proposition, Characterization of `L^p` membership, April 6, 2021 section).
-/

/-- For a measurable set `S ⊆ ℝ` and a measurable function `g : ℝ → ℝ≥0∞`, the
integral of `g` over `S` equals the supremum over `n : ℕ` of the integrals over
the truncations `[-n, n] ∩ S`. This is monotone convergence applied to the
indicators of the truncations. -/
theorem lintegral_eq_iSup_lintegral_Icc_inter
    (S : Set ℝ) (hS : MeasurableSet S) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in S, g x ∂volume =
      ⨆ n : ℕ, ∫⁻ x in (Set.Icc (-(n : ℝ)) n) ∩ S, g x ∂volume := by
  rw [← lintegral_indicator hS]
  have h_eq : ∀ n : ℕ, ∫⁻ x in (Set.Icc (-(n : ℝ)) n) ∩ S, g x ∂volume =
      ∫⁻ x, (Set.Icc (-(n : ℝ)) n ∩ S).indicator g x ∂volume :=
    fun n => (lintegral_indicator (measurableSet_Icc.inter hS) g).symm
  simp_rw [h_eq]
  set F : ℕ → ℝ → ℝ≥0∞ := fun n => (Set.Icc (-(n : ℝ)) n ∩ S).indicator g with hF_def
  have h_mono : Monotone F := by
    intro m n hmn x
    apply Set.indicator_le_indicator_of_subset
    · exact Set.inter_subset_inter_left S
        (Set.Icc_subset_Icc (neg_le_neg_iff.mpr (Nat.cast_le.mpr hmn))
          (Nat.cast_le.mpr hmn))
    · intro x; exact zero_le
  have h_sup : (fun x => ⨆ n : ℕ, F n x) = S.indicator g := by
    ext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      apply le_antisymm
      · exact iSup_le (fun n => Set.indicator_le_self _ _ x)
      · obtain ⟨N, hN⟩ := exists_nat_ge |x|
        apply le_iSup_of_le N
        simp only [hF_def]
        rw [Set.indicator_of_mem (show x ∈ Set.Icc (-(N : ℝ)) N ∩ S from
          ⟨⟨neg_le_of_abs_le hN, le_of_abs_le hN⟩, hx⟩)]
    · rw [Set.indicator_of_notMem hx]
      apply le_antisymm
      · apply iSup_le; intro n
        simp only [hF_def]
        rw [Set.indicator_of_notMem (fun h => hx h.2)]
      · exact zero_le
  have h_meas : ∀ n : ℕ, Measurable (F n) :=
    fun n => hg.indicator (measurableSet_Icc.inter hS)
  rw [← h_sup, lintegral_iSup h_meas h_mono]

/-- **Characterization of `L^p` membership via truncated integrals.** For `E ⊆ ℝ`
measurable and `1 ≤ p < ∞` (here `p ≠ 0` and `p ≠ ⊤`), a measurable function
`f : ℝ → F` belongs to `L^p (E)` if and only if
`⨆ n : ℕ, ∫⁻ x in [-n, n] ∩ E, ‖f x‖ₑ ^ p.toReal < ⊤`. -/
theorem memLp_iff_iSup_lintegral_Icc_inter_lt_top
    {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F]
    {p : ℝ≥0∞} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ⊤)
    (S : Set ℝ) (hS : MeasurableSet S) {f : ℝ → F} (hf : Measurable f) :
    MemLp f p (volume.restrict S) ↔
      ⨆ n : ℕ, ∫⁻ x in (Set.Icc (-(n : ℝ)) n) ∩ S, (‖f x‖ₑ) ^ p.toReal ∂volume < ⊤ := by
  constructor
  · intro hfp
    rw [← lintegral_eq_iSup_lintegral_Icc_inter S hS _ (by measurability)]
    exact (MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      hp_ne_zero hp_ne_top hf.aestronglyMeasurable.restrict).mp hfp.eLpNorm_lt_top
  · intro h
    rw [memLp_iff,
      MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_ne_zero hp_ne_top
        hf.aestronglyMeasurable.restrict]
    rwa [lintegral_eq_iSup_lintegral_Icc_inter S hS _ (by measurability)]

#print axioms lintegral_eq_iSup_lintegral_Icc_inter
#print axioms memLp_iff_iSup_lintegral_Icc_inter_lt_top

end MathlibExt.MeasureTheory.Function.MemLpTruncation
