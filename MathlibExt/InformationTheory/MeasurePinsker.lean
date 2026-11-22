/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import MathlibExt.Probability.TotalVariationDistance
import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
import MathlibExt.InformationTheory.FiniteEntropy
import MathlibExt.InformationTheory.Pinsker

/-!
# Total variation, optimal tests and Pinsker's inequality for probability measures

For probability measures `μ` and `ν` on an arbitrary measurable space, write
`TV(μ, ν) = sup_B |μ(B) - ν(B)|` (`totalVariationDist`, values in `[0, 1]`). This file proves:

* `totalVariationDist_eq_of_isHahnDecomposition` and `tvDist_eq_two_mul_totalVariationDist`:
  the supremum is attained at a Hahn set, and equals half of Mathlib's `tvDist`, which is the
  total variation norm `‖μ - ν‖` (values in `[0, 2]`).
* `one_sub_totalVariationDist_le_add_compl` and `exists_add_compl_eq_one_sub_totalVariationDist`:
  the minimal total error `μ(A) + ν(Aᶜ)` of a test `A` between `μ` and `ν` is `1 - TV(μ, ν)`.
* `exists_le_le_measure_univ_eq`: `μ` and `ν` dominate a common measure of mass `1 - TV(μ, ν)`.
* `ofReal_two_mul_totalVariationDist_sq_le_klDiv` (**Pinsker's inequality**):
  `2 TV(μ, ν)² ≤ D(μ ‖ ν)` with natural logarithms, with no positivity, finiteness or absolute
  continuity hypothesis (the divergence is `∞` when `μ` is not absolutely continuous with
  respect to `ν`). `ofReal_tvDist_sq_div_two_le_klDiv` is the same statement for `tvDist`, and
  `totalVariationDist_le_sqrt_klDiv` is the form `TV ≤ √(D / 2)`.

The Pinsker proof follows Polyanskiy and Wu: the data-processing inequality for `klDiv`
(Mathlib's `klDiv_map_le`) applied to the indicator of a Hahn set reduces the inequality to
two Bernoulli laws, where `binary_pinsker_of_mem_Icc` applies.

## References

* Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University
  Press, 2025, Theorem 7.7 (variational representations of total variation, and the minimal
  total error `1 - TV` of a test, eq. (7.19)) and Theorem 7.10 (Pinsker's inequality).
-/

@[expose] public section

open MeasureTheory ENNReal
open MathlibExt.Probability.TotalVariationDistance

namespace MathlibExt.InformationTheory.MeasurePinsker

variable {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}

section Hahn

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν] {s : Set Ω}

omit [IsFiniteMeasure μ] in
private lemma real_inter_le (h : IsHahnDecomposition μ ν s) (t : Set Ω) :
    μ.real (s ∩ t) ≤ ν.real (s ∩ t) := by
  have h1 := Measure.le_iff'.mp h.le_on t
  rw [Measure.restrict_apply' h.measurableSet, Measure.restrict_apply' h.measurableSet,
    Set.inter_comm] at h1
  exact ENNReal.toReal_mono (measure_ne_top _ _) h1

omit [IsFiniteMeasure ν] in
private lemma real_inter_compl_le (h : IsHahnDecomposition μ ν s) (t : Set Ω) :
    ν.real (sᶜ ∩ t) ≤ μ.real (sᶜ ∩ t) := by
  have h1 := Measure.le_iff'.mp h.ge_on_compl t
  rw [Measure.restrict_apply' h.measurableSet.compl,
    Measure.restrict_apply' h.measurableSet.compl, Set.inter_comm] at h1
  exact ENNReal.toReal_mono (measure_ne_top _ _) h1

private lemma real_split (ρ : Measure Ω) [IsFiniteMeasure ρ] (hs : MeasurableSet s) (B : Set Ω) :
    ρ.real (s ∩ B) + ρ.real (sᶜ ∩ B) = ρ.real B := by
  have h := measureReal_inter_add_sdiff (μ := ρ) (s := B) hs
  rw [Set.inter_comm, Set.sdiff_eq, Set.inter_comm B sᶜ] at h
  exact h

private lemma real_split' (ρ : Measure Ω) [IsFiniteMeasure ρ] {B : Set Ω} (hB : MeasurableSet B)
    (t : Set Ω) : ρ.real (t ∩ B) + ρ.real (t ∩ Bᶜ) = ρ.real t := by
  have h := measureReal_inter_add_sdiff (μ := ρ) (s := t) hB
  rw [Set.sdiff_eq] at h
  exact h

end Hahn

/-- For probability measures and a measurable set `B`, `|μ(B) - ν(B)| ≤ TV(μ, ν)`.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 7.7(a) (`TV` is a supremum over events). -/
theorem abs_sub_le_totalVariationDist [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : Set Ω} (hB : MeasurableSet B) :
    |μ.real B - ν.real B| ≤ totalVariationDist μ ν := by
  have hb : BddAbove (Set.range fun B : {B : Set Ω // MeasurableSet B} =>
      |(μ B.1).toReal - (ν B.1).toReal|) := by
    refine ⟨2, ?_⟩
    rintro _ ⟨B, rfl⟩
    have : |μ.real B.1 - ν.real B.1| ≤ 2 := by
      have := measureReal_le_one (μ := μ) (s := B.1)
      have := measureReal_le_one (μ := ν) (s := B.1)
      have := measureReal_nonneg (μ := μ) (s := B.1)
      have := measureReal_nonneg (μ := ν) (s := B.1)
      rw [abs_le]; constructor <;> linarith
    exact this
  exact le_ciSup hb ⟨B, hB⟩

/-- For probability measures, the supremum `sup_B |μ(B) - ν(B)|` defining `totalVariationDist`
is attained at a Hahn set `s` (one where `μ ≤ ν` on subsets of `s` and `ν ≤ μ` on subsets of
`sᶜ`), and equals `ν(s) - μ(s)`.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 7.7(a); the maximising event is `{dν/dμ' > dμ/dμ'}` there. -/
theorem totalVariationDist_eq_of_isHahnDecomposition [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {s : Set Ω} (h : IsHahnDecomposition μ ν s) :
    totalVariationDist μ ν = ν.real s - μ.real s := by
  have hs := h.measurableSet
  have hμc : μ.real sᶜ = 1 - μ.real s := by rw [probReal_compl_eq_one_sub hs]
  have hνc : ν.real sᶜ = 1 - ν.real s := by rw [probReal_compl_eq_one_sub hs]
  apply le_antisymm
  · apply ciSup_le
    rintro ⟨B, hB⟩
    change |μ.real B - ν.real B| ≤ ν.real s - μ.real s
    have a1 := real_inter_le h B
    have a2 := real_inter_le h Bᶜ
    have b1 := real_inter_compl_le h B
    have b2 := real_inter_compl_le h Bᶜ
    have sμ := real_split μ hs B
    have sν := real_split ν hs B
    have tμ := real_split' μ hB s
    have tν := real_split' ν hB s
    have uμ := real_split' μ hB sᶜ
    have uν := real_split' ν hB sᶜ
    rw [abs_sub_le_iff]
    constructor <;> linarith
  · have hle := abs_sub_le_totalVariationDist (μ := μ) (ν := ν) hs
    calc ν.real s - μ.real s ≤ |μ.real s - ν.real s| := by
          rw [abs_sub_comm]; exact le_abs_self _
      _ ≤ _ := hle

/-- For probability measures, Mathlib's total variation distance `tvDist μ ν = ‖μ - ν‖`
(values in `[0, 2]`) is twice the supremum `sup_B |μ(B) - ν(B)|` over measurable sets.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 7.7(a), the identity `TV(P, Q) = sup_E (P(E) - Q(E))`
for `TV(P, Q) = ½ ∫ |dP - dQ|`. -/
theorem tvDist_eq_two_mul_totalVariationDist (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    tvDist μ ν = 2 * totalVariationDist μ ν := by
  obtain ⟨s, h⟩ := exists_isHahnDecomposition μ ν
  rw [h.tvDist_eq, totalVariationDist_eq_of_isHahnDecomposition h,
    probReal_compl_eq_one_sub h.measurableSet, probReal_compl_eq_one_sub h.measurableSet]
  ring

/-- **Two-point testing bound.** For probability measures `μ`, `ν` and any measurable event
`A` (a test rejecting `μ` on `A`), the total error is at least `1 - TV(μ, ν)`:
`1 - TV(μ, ν) ≤ μ(A) + ν(Aᶜ)`.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 7.7(a), eq. (7.19). -/
theorem one_sub_totalVariationDist_le_add_compl [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : Set Ω} (hA : MeasurableSet A) :
    1 - totalVariationDist μ ν ≤ μ.real A + ν.real Aᶜ := by
  obtain ⟨s, h⟩ := exists_isHahnDecomposition μ ν
  rw [totalVariationDist_eq_of_isHahnDecomposition h, probReal_compl_eq_one_sub hA]
  have hs := h.measurableSet
  have a1 := real_inter_le h A
  have b1 := real_inter_compl_le h A
  have sμ := real_split μ hs A
  have sν := real_split ν hs A
  have hμc : μ.real sᶜ = 1 - μ.real s := probReal_compl_eq_one_sub hs
  have hνc : ν.real sᶜ = 1 - ν.real s := probReal_compl_eq_one_sub hs
  have tμ := real_split' μ hA s
  have tν := real_split' ν hA s
  have a2 := real_inter_le h Aᶜ
  linarith

/-- The two-point testing bound is attained: some measurable event `A` (a Hahn set) has total
error `μ(A) + ν(Aᶜ) = 1 - TV(μ, ν)`. With `one_sub_totalVariationDist_le_add_compl`, the minimal
total error of a test between two probability measures is exactly `1 - TV(μ, ν)`.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 7.7(a), eq. (7.19). -/
theorem exists_add_compl_eq_one_sub_totalVariationDist [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    ∃ A : Set Ω, MeasurableSet A ∧ μ.real A + ν.real Aᶜ = 1 - totalVariationDist μ ν := by
  obtain ⟨s, h⟩ := exists_isHahnDecomposition μ ν
  refine ⟨s, h.measurableSet, ?_⟩
  rw [totalVariationDist_eq_of_isHahnDecomposition h, probReal_compl_eq_one_sub h.measurableSet]
  ring

/-- **Pinsker's inequality** for probability measures on an arbitrary measurable space:
`2 TV(μ, ν)² ≤ D(μ ‖ ν)`, where `TV(μ, ν) = sup_B |μ(B) - ν(B)|` and `D = klDiv` uses the
natural logarithm. No positivity or absolute-continuity hypothesis is needed: `klDiv μ ν = ∞`
when `μ` is not absolutely continuous with respect to `ν`.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 7.10 (stated there as `D ≥ 2 log e · TV²`); M. S. Pinsker,
Information and Information Stability of Random Variables and Processes (1964). -/
theorem ofReal_two_mul_totalVariationDist_sq_le_klDiv (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    ENNReal.ofReal (2 * totalVariationDist μ ν ^ 2) ≤ InformationTheory.klDiv μ ν := by
  classical
  obtain ⟨s, h⟩ := exists_isHahnDecomposition μ ν
  have hs := h.measurableSet
  rw [totalVariationDist_eq_of_isHahnDecomposition h]
  set g : Ω → Bool := fun ω => decide (ω ∈ s) with hg_def
  have hpre : g ⁻¹' {true} = s := by ext ω; simp [hg_def]
  have hpre' : g ⁻¹' {false} = sᶜ := by ext ω; simp [hg_def]
  have hg : Measurable g := measurable_to_countable' fun b => by
    cases b
    · rw [hpre']; exact hs.compl
    · rw [hpre]; exact hs
  have hDPI := InformationTheory.klDiv_map_le (μ := μ) (ν := ν) hg
  refine le_trans ?_ hDPI
  by_cases hac : μ.map g ≪ ν.map g
  swap
  · rw [InformationTheory.klDiv_of_not_ac hac]; exact le_top
  have hfin : InformationTheory.klDiv (μ.map g) (ν.map g) ≠ ⊤ :=
    InformationTheory.klDiv_ne_top hac Integrable.of_finite
  have hsum := InformationTheory.toReal_klDiv_eq_sum hac (by rw [measure_univ, measure_univ])
  rw [Fintype.sum_bool] at hsum
  have eμt : (μ.map g).real {true} = μ.real s := by
    rw [map_measureReal_apply hg (measurableSet_singleton _), hpre]
  have eμf : (μ.map g).real {false} = 1 - μ.real s := by
    rw [map_measureReal_apply hg (measurableSet_singleton _), hpre', probReal_compl_eq_one_sub hs]
  have eνt : (ν.map g).real {true} = ν.real s := by
    rw [map_measureReal_apply hg (measurableSet_singleton _), hpre]
  have eνf : (ν.map g).real {false} = 1 - ν.real s := by
    rw [map_measureReal_apply hg (measurableSet_singleton _), hpre', probReal_compl_eq_one_sub hs]
  rw [eμt, eμf, eνt, eνf] at hsum
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  rw [hsum]
  set u := μ.real s
  set v := ν.real s
  have hu0 : 0 ≤ u := measureReal_nonneg
  have hu1 : u ≤ 1 := measureReal_le_one
  have hv0 : 0 ≤ v := measureReal_nonneg
  have hv1 : v ≤ 1 := measureReal_le_one
  rcases hv0.lt_or_eq with hv0' | hv0'
  · rcases hv1.lt_or_eq with hv1' | hv1'
    · have := MathlibExt.InformationTheory.Pinsker.binary_pinsker_of_mem_Icc hu0 hu1 hv0' hv1'
      nlinarith [this]
    · -- `ν(s) = 1`: absolute continuity forces `μ(s) = 1`, so both sides vanish
      have hz : (ν.map g) {false} = 0 := by
        rw [Measure.map_apply hg (measurableSet_singleton _), hpre', prob_compl_eq_zero_iff hs]
        rw [← ENNReal.toReal_eq_one_iff]; exact hv1'
      have hz' := hac hz
      rw [Measure.map_apply hg (measurableSet_singleton _), hpre', prob_compl_eq_zero_iff hs] at hz'
      have hu : u = 1 := by simp [u, measureReal_def, hz']
      rw [hu, ← hv1']; simp
  · -- `ν(s) = 0`: absolute continuity forces `μ(s) = 0`, so both sides vanish
    have hz : (ν.map g) {true} = 0 := by
      rw [Measure.map_apply hg (measurableSet_singleton _), hpre]
      exact ((ENNReal.toReal_eq_zero_iff _).mp hv0'.symm).resolve_right (measure_ne_top _ _)
    have hz' := hac hz
    rw [Measure.map_apply hg (measurableSet_singleton _), hpre] at hz'
    have hu : u = 0 := by simp [u, measureReal_def, hz']
    rw [hu, ← hv0']; simp

/-- **Pinsker's inequality** in Mathlib's `tvDist` convention (`tvDist = ‖μ - ν‖ ∈ [0, 2]`):
`tvDist(μ, ν)² / 2 ≤ D(μ ‖ ν)` for probability measures, natural logarithm.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 7.10, with `tvDist = 2 TV` (Theorem 7.7(a)). -/
theorem ofReal_tvDist_sq_div_two_le_klDiv (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    ENNReal.ofReal (tvDist μ ν ^ 2 / 2) ≤ InformationTheory.klDiv μ ν := by
  have h := ofReal_two_mul_totalVariationDist_sq_le_klDiv μ ν
  rw [tvDist_eq_two_mul_totalVariationDist]
  convert h using 2
  ring

/-- **Pinsker's inequality**, square-root form: if `D(μ ‖ ν) < ∞` then
`TV(μ, ν) ≤ √(D(μ ‖ ν) / 2)`, natural logarithm.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 7.10 (the form `√(½ D(P‖Q)) ≥ TV(P, Q)` in its proof). -/
theorem totalVariationDist_le_sqrt_klDiv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfin : InformationTheory.klDiv μ ν ≠ ⊤) :
    totalVariationDist μ ν ≤ Real.sqrt ((InformationTheory.klDiv μ ν).toReal / 2) := by
  have h := ofReal_two_mul_totalVariationDist_sq_le_klDiv μ ν
  rw [← ENNReal.ofReal_toReal hfin, ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg] at h
  apply Real.le_sqrt_of_sq_le
  linarith

/-- Two probability measures `μ` and `ν` dominate a common measure `m ≤ μ`, `m ≤ ν` of total mass
`1 - TV(μ, ν)`, namely `μ` restricted to a Hahn set plus `ν` restricted to its complement (this is
the overlap `μ ∧ ν`, whose density is `min (dμ/dρ) (dν/dρ)`).
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), proof of Theorem 31.1 (the identity `∫ min(p₀, p₁) = 1 - TV`). -/
theorem exists_le_le_measure_univ_eq (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    ∃ m : Measure Ω, m ≤ μ ∧ m ≤ ν ∧ m Set.univ = ENNReal.ofReal (1 - totalVariationDist μ ν) := by
  obtain ⟨s, h⟩ := exists_isHahnDecomposition μ ν
  have hs := h.measurableSet
  refine ⟨μ.restrict s + ν.restrict sᶜ, ?_, ?_, ?_⟩
  · calc μ.restrict s + ν.restrict sᶜ ≤ μ.restrict s + μ.restrict sᶜ :=
          add_le_add le_rfl h.ge_on_compl
      _ = μ := Measure.restrict_add_restrict_compl hs
  · calc μ.restrict s + ν.restrict sᶜ ≤ ν.restrict s + ν.restrict sᶜ :=
          add_le_add h.le_on le_rfl
      _ = ν := Measure.restrict_add_restrict_compl hs
  · rw [Measure.add_apply, Measure.restrict_apply_univ, Measure.restrict_apply_univ,
      totalVariationDist_eq_of_isHahnDecomposition h, ← ENNReal.ofReal_toReal (measure_ne_top μ s),
      ← ENNReal.ofReal_toReal (measure_ne_top ν sᶜ), ← ENNReal.ofReal_add ENNReal.toReal_nonneg
        ENNReal.toReal_nonneg]
    congr 1
    change μ.real s + ν.real sᶜ = 1 - (ν.real s - μ.real s)
    rw [probReal_compl_eq_one_sub hs]
    ring

end MathlibExt.InformationTheory.MeasurePinsker
