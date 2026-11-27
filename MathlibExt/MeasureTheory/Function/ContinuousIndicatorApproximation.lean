/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Continuous unit-interval approximation of measurable indicators

On a normal topological Borel space, let `μ` be finite and weakly regular and `s` measurable.
Its indicator has continuous real approximants taking values in `[0,1]`, with arbitrarily small
L² error.

A sequence of these approximants can converge both in L² and pointwise almost everywhere to
`1_s`. Compactness, Hausdorffness and a nonempty source are not assumed.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace MathlibExt.MeasureTheory.Function
universe uX
variable {X : Type uX} [TopologicalSpace X] [NormalSpace X]
  [MeasurableSpace X] [BorelSpace X]

private theorem clip_norm_sub_zero (t : ℝ) :
    ‖max 0 (min 1 t) - 0‖ ≤ ‖t - 0‖ := by
  simp only [sub_zero, Real.norm_eq_abs]
  rw [abs_of_nonneg (le_max_left 0 (min 1 t))]
  exact max_le (abs_nonneg t) ((min_le_right 1 t).trans (le_abs_self t))

private theorem clip_norm_sub_one (t : ℝ) :
    ‖max 0 (min 1 t) - 1‖ ≤ ‖t - 1‖ := by
  by_cases ht : t ≤ 1
  · rw [min_eq_right ht]
    have htop : max 0 t ≤ 1 := max_le zero_le_one ht
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonpos (sub_nonpos.mpr htop), abs_of_nonpos (sub_nonpos.mpr ht)]
    exact neg_le_neg (sub_le_sub_right (le_max_right 0 t) 1)
  · have h1 : 1 ≤ t := (lt_of_not_ge ht).le
    rw [min_eq_left h1, max_eq_right zero_le_one, sub_self, norm_zero]
    exact norm_nonneg _

/-- **Continuous indicator approximation at any nonzero extended tolerance.** Let `X` be a
normal topological space with its Borel structure, `μ` a finite weakly regular measure,
and `s⊆X` measurable. for `ε∈[0,∞]` with `ε≠0`, there exists `f∈C(X,ℝ)` with `0≤f≤1` and
`eLpNorm(f-1_s,2,μ)≤ε`. The tolerance may be infinite. -/
theorem exists_continuous_indicator_eLpNorm_le
    (μ : Measure X) [μ.WeaklyRegular] [IsFiniteMeasure μ]
    (s : Set X) (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ f : C(X, ℝ), (∀ x : X, 0 ≤ f x ∧ f x ≤ 1) ∧
      eLpNorm (fun x => f x - s.indicator (fun _ => (1 : ℝ)) x) 2 μ ≤ ε := by
  have hI : MemLp (s.indicator (fun _ => (1 : ℝ))) 2 μ :=
    MemLp.indicator hs.nullMeasurableSet (memLp_const (1 : ℝ))
  obtain ⟨g, hg, _hgMemLp⟩ := hI.exists_boundedContinuous_eLpNorm_sub_le
    (by simp : (2 : ℝ≥0∞) ≠ ∞) hε
  let f : C(X, ℝ) :=
    ⟨fun x => max 0 (min 1 (g x)), continuous_const.max (continuous_const.min g.continuous)⟩
  have hf : ∀ x : X, 0 ≤ f x ∧ f x ≤ 1 := by
    intro x
    exact ⟨le_max_left 0 (min 1 (g x)), max_le zero_le_one (min_le_left 1 (g x))⟩
  have hpoint : ∀ x : X,
      ‖f x - s.indicator (fun _ => (1 : ℝ)) x‖ ≤
        ‖(s.indicator (fun _ => (1 : ℝ)) - (g : X → ℝ)) x‖ := by
    intro x
    by_cases hx : x ∈ s
    · simp only [Pi.sub_apply, indicator_of_mem hx]
      change ‖max 0 (min 1 (g x)) - 1‖ ≤ ‖1 - g x‖
      rw [norm_sub_rev (1 : ℝ) (g x)]
      exact clip_norm_sub_one (g x)
    · simp only [Pi.sub_apply, indicator_of_notMem hx]
      change ‖max 0 (min 1 (g x)) - 0‖ ≤ ‖0 - g x‖
      rw [norm_sub_rev (0 : ℝ) (g x)]
      exact clip_norm_sub_zero (g x)
  have hmeas : AEStronglyMeasurable
      (fun x => f x - s.indicator (fun _ => (1 : ℝ)) x) μ :=
    f.continuous.aestronglyMeasurable.sub hI.aestronglyMeasurable
  exact ⟨f, hf, (eLpNorm_mono hmeas hpoint).trans hg⟩

/-- **Sequence of bounded continuous L² indicator approximants.** Let `X` be a normal
topological space with its Borel structure, `μ` a finite weakly regular measure, and `s⊆X`
measurable. there are `f_n∈C(X,ℝ)` with `0≤f_n≤1` everywhere and `eLpNorm(f_n-1_s,2,μ)→0`. -/
theorem exists_continuous_indicator_l2
    (μ : Measure X) [μ.WeaklyRegular] [IsFiniteMeasure μ]
    (s : Set X) (hs : MeasurableSet s) :
    ∃ f : ℕ → C(X, ℝ), (∀ n x, 0 ≤ f n x ∧ f n x ≤ 1) ∧
      Tendsto (fun n => eLpNorm (fun x => f n x - s.indicator (fun _ => (1 : ℝ)) x) 2 μ)
        atTop (𝓝 0) := by
  classical
  have happ : ∀ n : ℕ,
      ∃ f : C(X, ℝ), (∀ x : X, 0 ≤ f x ∧ f x ≤ 1) ∧
        eLpNorm (fun x => f x - s.indicator (fun _ => (1 : ℝ)) x) 2 μ ≤
          ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    intro n
    exact exists_continuous_indicator_eLpNorm_le μ s hs
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top (n + 1)))
  let f : ℕ → C(X, ℝ) := fun n => Classical.choose (happ n)
  have hf : ∀ n x, 0 ≤ f n x ∧ f n x ≤ 1 := fun n => (Classical.choose_spec (happ n)).1
  have herror : ∀ n : ℕ,
      eLpNorm (fun x => f n x - s.indicator (fun _ => (1 : ℝ)) x) 2 μ ≤
        ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := fun n => (Classical.choose_spec (happ n)).2
  have hε : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  refine ⟨f, hf, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hε
    (fun _ => bot_le) herror

/-- **Continuous indicator approximants converging in L² and almost everywhere.** Let `X` be a
normal topological space with its Borel structure, `μ` a finite weakly regular measure,
and `s⊆X` measurable. there are `f_n∈C(X,ℝ)` with `0≤f_n≤1`, `eLpNorm(f_n-1_s,2,μ)→0`, and
`f_n(x)→1_s(x)` for `μ`-almost every `x`. -/
theorem exists_continuous_indicator_l2_ae
    (μ : Measure X) [μ.WeaklyRegular] [IsFiniteMeasure μ]
    (s : Set X) (hs : MeasurableSet s) :
    ∃ f : ℕ → C(X, ℝ), (∀ n x, 0 ≤ f n x ∧ f n x ≤ 1) ∧
      Tendsto (fun n => eLpNorm (fun x => f n x - s.indicator (fun _ => (1 : ℝ)) x) 2 μ)
        atTop (𝓝 0) ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (s.indicator (fun _ => (1 : ℝ)) x)) := by
  obtain ⟨f, hf, hL2⟩ := exists_continuous_indicator_l2 μ s hs
  have hmeasure : TendstoInMeasure μ (fun n x => f n x) atTop
      (s.indicator (fun _ => (1 : ℝ))) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by simp : (2 : ℝ≥0∞) ≠ 0) hL2
  obtain ⟨ns, hns, hae⟩ := hmeasure.exists_seq_tendsto_ae
  refine ⟨fun n => f (ns n), fun n x => hf (ns n) x, ?_, hae⟩
  exact hL2.comp hns.tendsto_atTop

end MathlibExt.MeasureTheory.Function
