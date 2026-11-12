/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.CDF
import Mathlib.Tactic.Ring

/-!
# Quantiles of real probability measures

This file provides a public generalized inverse for a real cumulative
distribution function. Values outside `(0, 1)` are set to zero; they are
irrelevant for the pushforward of Lebesgue measure restricted to `[0, 1]`.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Set
open scoped Topology

/-- **Quantile function of a real measure.** Let $\mu$ be a measure on $\mathbb{R}$ with cumulative
distribution function $F_\mu$ (for a probability measure, $F_\mu(x) = \mu((-\infty, x])$). The
quantile function of $\mu$, the generalized inverse of $F_\mu$, is the function
$Q_\mu : \mathbb{R} \to \mathbb{R}$ given by
$Q_\mu(u) = \inf \lbrace x \in \mathbb{R} : u \le F_\mu(x) \rbrace$ for $u \in (0, 1)$ and
$Q_\mu(u) = 0$ for $u \notin (0, 1)$. -/
noncomputable def cdfQuantile (μ : Measure ℝ) (u : ℝ) : ℝ :=
  if u ∈ Ioo (0 : ℝ) 1 then sInf {x : ℝ | u ≤ cdf μ x} else 0

private theorem cdfQuantile_set_nonempty (μ : Measure ℝ) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) : {x : ℝ | u ≤ cdf μ x}.Nonempty := by
  have hev : ∀ᶠ x in Filter.atTop, u < cdf μ x :=
    Filter.Tendsto.eventually_const_lt hu.2 (tendsto_cdf_atTop μ)
  obtain ⟨x, hx⟩ := hev.exists
  exact ⟨x, hx.le⟩

private theorem cdfQuantile_set_bddBelow (μ : Measure ℝ) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) : BddBelow {x : ℝ | u ≤ cdf μ x} := by
  have hev : ∀ᶠ x in Filter.atBot, cdf μ x < u :=
    Filter.Tendsto.eventually_lt_const hu.1 (tendsto_cdf_atBot μ)
  rw [Filter.eventually_atBot] at hev
  obtain ⟨x₀, hx₀⟩ := hev
  refine ⟨x₀, fun x hx ↦ ?_⟩
  by_contra h
  have hlt : x < x₀ := lt_of_not_ge h
  exact (not_lt_of_ge hx) (hx₀ x hlt.le)

/-- **The cdf at the quantile is at least the level.** Let $\mu$ be a measure on $\mathbb{R}$ with
cumulative distribution function $F_\mu$ and quantile function $Q_\mu$. For every $u \in (0, 1)$,
$u \le F_\mu(Q_\mu(u))$. -/
theorem cdfQuantile_mem (μ : Measure ℝ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    u ≤ cdf μ (cdfQuantile μ u) := by
  have hne := cdfQuantile_set_nonempty μ hu
  have habove : ∀ x : ℝ, sInf {t : ℝ | u ≤ cdf μ t} < x → u ≤ cdf μ x := by
    intro x hx
    obtain ⟨t, ht, htx⟩ := exists_lt_of_csInf_lt hne hx
    exact ht.trans (monotone_cdf μ htx.le)
  have hright : Filter.Tendsto (cdf μ)
      (nhdsWithin (sInf {t : ℝ | u ≤ cdf μ t})
        (Ioi (sInf {t : ℝ | u ≤ cdf μ t})))
      (𝓝 (cdf μ (sInf {t : ℝ | u ≤ cdf μ t}))) := by
    exact (cdf μ).right_continuous _ |>.mono_left
      (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hev : ∀ᶠ x in nhdsWithin (sInf {t : ℝ | u ≤ cdf μ t})
      (Ioi (sInf {t : ℝ | u ≤ cdf μ t})), u ≤ cdf μ x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact habove x hx
  simpa only [cdfQuantile, hu, ite_true] using ge_of_tendsto hright hev

/-- **The quantile function as a generalized inverse of the cdf.** Let $\mu$ be a measure on
$\mathbb{R}$ with cumulative distribution function $F_\mu$ and quantile function $Q_\mu$. For
every $u \in (0, 1)$ and every real $x$, $Q_\mu(u) \le x$ if and only if $u \le F_\mu(x)$. -/
theorem cdfQuantile_le_iff (μ : Measure ℝ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    {x : ℝ} : cdfQuantile μ u ≤ x ↔ u ≤ cdf μ x := by
  have hmem := cdfQuantile_mem μ hu
  have hbdd := cdfQuantile_set_bddBelow μ hu
  simp only [cdfQuantile, hu, ite_true] at hmem ⊢
  constructor
  · exact fun h ↦ hmem.trans (monotone_cdf μ h)
  · exact fun h ↦ csInf_le hbdd h

/-- **Monotonicity of the quantile function.** For every measure $\mu$ on $\mathbb{R}$, the quantile
function $Q_\mu$ is monotone on $(0, 1)$: if $0 < u \le v < 1$, then $Q_\mu(u) \le Q_\mu(v)$. -/
theorem cdfQuantile_monoOn (μ : Measure ℝ) : MonotoneOn (cdfQuantile μ) (Ioo 0 1) := by
  intro u hu v hv huv
  have h1 : v ≤ cdf μ (cdfQuantile μ v) :=
    (cdfQuantile_le_iff μ hv).mp le_rfl
  exact (cdfQuantile_le_iff μ hu).mpr (huv.trans h1)

/-- **Measurability of the quantile function.** For every measure $\mu$ on $\mathbb{R}$, the
quantile function $Q_\mu : \mathbb{R} \to \mathbb{R}$ is measurable. -/
theorem measurable_cdfQuantile (μ : Measure ℝ) : Measurable (cdfQuantile μ) := by
  apply measurable_of_Iic
  intro x
  have hset : cdfQuantile μ ⁻¹' Iic x =
      (Ioo (0 : ℝ) 1 ∩ Iic (cdf μ x)) ∪
        (if (0 : ℝ) ≤ x then (Ioo (0 : ℝ) 1)ᶜ else ∅) := by
    ext u
    by_cases hu : u ∈ Ioo (0 : ℝ) 1
    · by_cases hx : (0 : ℝ) ≤ x
      · simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, hx, ite_true]
        rw [cdfQuantile_le_iff μ hu]
        simp [hu]
      · simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, hx, ite_false,
          mem_empty_iff_false, or_false]
        rw [cdfQuantile_le_iff μ hu]
        exact ⟨fun h ↦ ⟨hu, h⟩, fun h ↦ h.2⟩
    · have hq : cdfQuantile μ u = 0 := by simp only [cdfQuantile, hu, ite_false]
      by_cases hx : (0 : ℝ) ≤ x
      · simp only [mem_preimage, mem_Iic, hq, mem_union, mem_inter_iff]
        simp [hu, hx]
      · simp only [mem_preimage, mem_Iic, hq, mem_union, mem_inter_iff, hx, ite_false,
          mem_empty_iff_false, or_false]
        exact (iff_false_intro (fun h ↦ hu h.1)).symm
  rw [hset]
  exact (measurableSet_Ioo.inter measurableSet_Iic).union
    (by split_ifs <;> simp)

/-- **Inverse transform sampling.** Let $\mu$ be a probability measure on $\mathbb{R}$ with quantile
function $Q_\mu$. The pushforward under $Q_\mu$ of Lebesgue measure restricted to $[0, 1]$ is
$\mu$. -/
theorem map_cdfQuantile_restrict_Icc (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measure.map (cdfQuantile μ) (volume.restrict (Icc (0 : ℝ) 1)) = μ := by
  have hIoo : volume.restrict (Ioo (0 : ℝ) 1) = volume.restrict (Icc (0 : ℝ) 1) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc
  apply Eq.symm
  rw [← hIoo]
  apply Measure.ext_of_Iic _ _
  intro x
  rw [Measure.map_apply (measurable_cdfQuantile μ) measurableSet_Iic,
    Measure.restrict_apply ((measurable_cdfQuantile μ) measurableSet_Iic)]
  have hpre : cdfQuantile μ ⁻¹' Iic x ∩ Ioo (0 : ℝ) 1 =
      Ioo (0 : ℝ) 1 ∩ Iic (cdf μ x) := by
    ext u
    by_cases hu : u ∈ Ioo (0 : ℝ) 1
    · simp only [mem_inter_iff, mem_preimage, mem_Iic, hu, and_true, true_and]
      exact cdfQuantile_le_iff μ hu
    · simp [hu]
  rw [hpre, Set.inter_comm]
  set c := cdf μ x with hc
  have hc0 : 0 ≤ c := cdf_nonneg μ x
  have hc1 : c ≤ 1 := cdf_le_one μ x
  rw [← ofReal_cdf μ x]
  by_cases hclt : c < 1
  · have hset : Iic c ∩ Ioo (0 : ℝ) 1 = Ioc 0 c := by
      ext u
      simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
      constructor
      · intro h
        exact ⟨h.2.1, h.1⟩
      · intro h
        exact ⟨h.2, h.1, lt_of_le_of_lt h.2 hclt⟩
    rw [hset, Real.volume_Ioc]
    congr 1
    ring
  · have hceq : c = 1 := le_antisymm hc1 (le_of_not_gt hclt)
    have hset : Iic c ∩ Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 := by
      rw [hceq]
      ext u
      simp only [mem_inter_iff, mem_Iic, mem_Ioo]
      constructor
      · intro h
        exact h.2
      · intro h
        exact ⟨h.2.le, h⟩
    rw [hset, Real.volume_Ioo, ← hc, hceq]
    norm_num

end ProbabilityTheory
