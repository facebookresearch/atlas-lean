/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.ContinuousMap.Basic
public import MathlibExt.Probability.Statistics.Nonparametric.EmpiricalCDFPointwise
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import MathlibExt.Probability.Statistics.GlivenkoCantelli
public import MathlibExt.Probability.Quantile

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory

/-- Finite-sample empirical CDFs are right-continuous step functions. -/
theorem empCDF_rightContinuous {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (X : Fin n → Ω → ℝ) (ω : Ω) (x : ℝ) :
    ContinuousWithinAt (fun t => empCDF (fun i => X i ω) t) (Set.Ici x) x := by
  have hev : ∀ i, ∀ᶠ t in 𝓝[Set.Ici x] x, (X i ω ≤ t ↔ X i ω ≤ x) := by
    intro i
    by_cases hi : X i ω ≤ x
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_Ici] at ht
      exact ⟨fun _ => hi, fun _ => le_trans hi ht⟩
    · have hi' : x < X i ω := not_le.mp hi
      have hmem : Set.Iio (X i ω) ∈ 𝓝[Set.Ici x] x :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hi')
      filter_upwards [hmem] with t ht
      simp only [Set.mem_Iio] at ht
      exact ⟨fun h => absurd h (not_le.mpr ht), fun h => absurd h hi⟩
  have hall : ∀ᶠ t in 𝓝[Set.Ici x] x, ∀ i, (X i ω ≤ t ↔ X i ω ≤ x) :=
    eventually_all.mpr hev
  refine ContinuousWithinAt.congr_of_eventuallyEq
    (f := fun _ => empCDF (fun i => X i ω) x) continuousWithinAt_const ?_ rfl
  filter_upwards [hall] with t ht
  have hset : Finset.univ.filter (fun i => X i ω ≤ t)
      = Finset.univ.filter (fun i => X i ω ≤ x) := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ht i
  simp only [empCDF, hset]

/-- Supremum of a pointwise deviation of two right-continuous functions equals
its supremum over the rationals. -/
theorem iSup_abs_sub_eq_iSup_rat (f g : ℝ → ℝ)
    (hf : ∀ x, ContinuousWithinAt f (Set.Ici x) x)
    (hg : ∀ x, ContinuousWithinAt g (Set.Ici x) x)
    (hbdd : ∃ C, ∀ x, |f x - g x| ≤ C) :
    ⨆ x : ℝ, |f x - g x| = ⨆ q : ℚ, |f (q : ℝ) - g (q : ℝ)| := by
  obtain ⟨C, hC⟩ := hbdd
  have hRng : BddAbove (Set.range fun x : ℝ => |f x - g x|) := by
    refine ⟨C, fun y hy => ?_⟩
    obtain ⟨x, rfl⟩ := hy
    exact hC x
  have hQng : BddAbove (Set.range fun q : ℚ => |f (q : ℝ) - g (q : ℝ)|) := by
    refine ⟨C, fun y hy => ?_⟩
    obtain ⟨q, rfl⟩ := hy
    exact hC _
  have hcont : ∀ x, ContinuousWithinAt (fun x => |f x - g x|) (Set.Ici x) x :=
    fun x => ((hf x).sub (hg x)).abs
  have hle : ∀ x : ℝ, |f x - g x| ≤ ⨆ q : ℚ, |f (q : ℝ) - g (q : ℝ)| := by
    intro x
    apply le_of_forall_pos_le_add
    intro ε hε
    have hcx := hcont x
    rw [Metric.continuousWithinAt_iff] at hcx
    obtain ⟨δ, hδ, hball⟩ := hcx ε hε
    obtain ⟨q, hxq, hqx⟩ := exists_rat_btwn (show x < x + δ from by linarith)
    have hq_le : |f (q : ℝ) - g (q : ℝ)| ≤ ⨆ q : ℚ, |f (q : ℝ) - g (q : ℝ)| :=
      le_ciSup hQng q
    have hdist_q : dist (q : ℝ) x < δ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hxq)]
      linarith
    have hclose := hball (le_of_lt hxq) hdist_q
    rw [Real.dist_eq] at hclose
    have hle' : |f x - g x| - |f (q : ℝ) - g (q : ℝ)|
        ≤ |(|f (q : ℝ) - g (q : ℝ)|) - (|f x - g x|)| := by
      rw [abs_sub_comm (|f (q : ℝ) - g (q : ℝ)|) (|f x - g x|)]
      exact le_abs_self _
    linarith [hclose, hle', hq_le]
  apply le_antisymm
  · exact ciSup_le hle
  · exact ciSup_le (fun q => le_ciSup hRng (q : ℝ))

/-- The empirical/theoretical uniform deviation equals its rational
restriction. -/
theorem uniform_deviation_eq_iSup_rat {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (X : Fin n → Ω → ℝ) (ω : Ω) (F : ℝ → ℝ)
    (hF : ∀ x, ContinuousWithinAt F (Set.Ici x) x)
    (hbdd : ∃ C, ∀ x, |empCDF (fun i => X i ω) x - F x| ≤ C) :
    ⨆ x : ℝ, |empCDF (fun i => X i ω) x - F x|
      = ⨆ q : ℚ, |empCDF (fun i => X i ω) (q : ℝ) - F (q : ℝ)| := by
  exact iSup_abs_sub_eq_iSup_rat (fun t => empCDF (fun i => X i ω) t) F
    (empCDF_rightContinuous X ω) hF hbdd

/-- The rationally-witnessed uniform-deviation event is measurable,
at every sample size including `n = 0` (where the empirical CDF is
identically zero and division is by the constant zero). -/
theorem measurableSet_uniform_deviation {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (X : Fin n → Ω → ℝ)
    (F : ℝ → ℝ) (eps : ℝ)
    (hX : ∀ i, Measurable (X i)) :
    MeasurableSet {ω | ∃ q : ℚ, |empCDF (fun i => X i ω) (q : ℝ) - F (q : ℝ)| > eps} := by
  have hset : {ω | ∃ q : ℚ, |empCDF (fun i => X i ω) (q : ℝ) - F (q : ℝ)| > eps}
      = ⋃ q : ℚ, {ω | |empCDF (fun i => X i ω) (q : ℝ) - F (q : ℝ)| > eps} := by
    ext ω
    simp
  rw [hset]
  apply MeasurableSet.iUnion
  intro q
  have hind : ∀ i, Measurable (fun ω => if X i ω ≤ (q : ℝ) then (1 : ℝ) else 0) :=
    fun i => Measurable.ite (measurableSet_le (hX i) measurable_const)
      measurable_const measurable_const
  have hsum : Measurable
      (fun ω => ∑ i ∈ Finset.univ, (if X i ω ≤ (q : ℝ) then (1 : ℝ) else 0)) :=
    Finset.measurable_sum Finset.univ (fun i _ => hind i)
  have hemp : Measurable (fun ω => empCDF (fun i => X i ω) (q : ℝ)) := by
    have heq : (fun ω => empCDF (fun i => X i ω) (q : ℝ))
        = fun ω => (∑ i ∈ Finset.univ, (if X i ω ≤ (q : ℝ) then (1 : ℝ) else 0)) / (n : ℝ) := by
      funext ω
      exact empCDF_eq_sum_div _ _
    rw [heq]
    exact hsum.div_const _
  have hsub : Measurable (fun ω => empCDF (fun i => X i ω) (q : ℝ) - F (q : ℝ)) :=
    hemp.sub_const _
  have habs : Measurable (fun ω => |empCDF (fun i => X i ω) (q : ℝ) - F (q : ℝ)|) :=
    measurable_abs.comp hsub
  have hIoi : MeasurableSet
      ((fun ω => |empCDF (fun i => X i ω) (q : ℝ) - F (q : ℝ)|) ⁻¹' Set.Ioi eps) :=
    habs measurableSet_Ioi
  exact hIoi

section KSReduction

open MathlibExt.Probability.Statistics.GlivenkoCantelliWanted

private theorem count_eq_coupled
    {μ : Measure ℝ}
    {u : ℕ → ℝ} {n : ℕ}
    (hu : ∀ i ∈ Finset.range (n + 1), u i ∈ Set.Ioo (0 : ℝ) 1)
    (hle : ∀ {v : ℝ}, v ∈ Set.Ioo (0 : ℝ) 1 → ∀ {x : ℝ},
      cdfQuantile μ v ≤ x ↔ v ≤ cdf μ x)
    (x : ℝ) :
    empiricalCount (fun i _ => cdfQuantile μ (u i)) n () x =
      empiricalCount (fun i _ => u i) n () (cdf μ x) := by
  unfold empiricalCount
  congr 1
  apply Finset.filter_congr
  intro i hi
  exact hle (hu i hi)

private theorem unif_dev_le_one
    {u : ℕ → ℝ} {n : ℕ} {v : ℝ}
    (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    |((empiricalCount (fun i _ => u i) n () v : ℝ) / ((n + 1 : ℕ) : ℝ)) - v| ≤ 1 := by
  have hcard : empiricalCount (fun i _ => u i) n () v ≤ n + 1 := by
    unfold empiricalCount
    refine (Finset.card_filter_le _ _).trans ?_
    simp [Finset.card_range]
  have hnpos : (0 : ℕ) < n + 1 := by omega
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hnpos
  have hG1 : ((empiricalCount (fun i _ => u i) n () v : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 1 :=
    (div_le_one hpos).mpr (Nat.cast_le.mpr hcard)
  have hG0 : (0 : ℝ) ≤ ((empiricalCount (fun i _ => u i) n () v : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hpos.le
  obtain ⟨hv0, hv1⟩ := Set.mem_Icc.mp hv
  rw [abs_le]
  constructor <;> linarith

/-- **Quantile-coupling distribution-free reduction.** On the good event
(`hu`: every uniform draw lies in `(0,1)`), the empirical CDF of the coupled sample
equals the uniform empirical CDF composed with the population CDF, pointwise in `x`
(by `cdfQuantile_le_iff`, applied simultaneously at every `x`). Hence the KS distance is
bounded by the uniform deviation over `[0,1]`. No continuity of the population law. -/
theorem ks_reduction_quantile_coupling
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {u : ℕ → ℝ} {n : ℕ}
    (hu : ∀ i ∈ Finset.range (n + 1), u i ∈ Set.Ioo (0 : ℝ) 1) :
    (⨆ x, |((empiricalCount (fun i _ => cdfQuantile μ (u i)) n () x : ℝ) /
      ((n + 1 : ℕ) : ℝ)) - cdf μ x|) ≤
    (⨆ v ∈ Set.Icc (0 : ℝ) 1, |((empiricalCount (fun i _ => u i) n () v : ℝ) /
      ((n + 1 : ℕ) : ℝ)) - v|) := by
  have hle : ∀ {v : ℝ}, v ∈ Set.Ioo (0 : ℝ) 1 → ∀ {x : ℝ},
      cdfQuantile μ v ≤ x ↔ v ≤ cdf μ x := fun hv => cdfQuantile_le_iff μ hv
  have hmem : ∀ x : ℝ, cdf μ x ∈ Set.Icc (0 : ℝ) 1 := fun x =>
    Set.mem_Icc.mpr ⟨cdf_nonneg μ x, cdf_le_one μ x⟩
  have hbdd : BddAbove (Set.range fun v =>
      ⨆ _ : v ∈ Set.Icc (0 : ℝ) 1,
        |((empiricalCount (fun i _ => u i) n () v : ℝ) / ((n + 1 : ℕ) : ℝ)) - v|) := by
    refine ⟨1, fun y hy => ?_⟩
    obtain ⟨v, rfl⟩ := hy
    by_cases hv : v ∈ Set.Icc (0 : ℝ) 1
    · have : Nonempty (v ∈ Set.Icc (0 : ℝ) 1) := ⟨hv⟩
      exact ciSup_le (fun _ => unif_dev_le_one hv)
    · have : IsEmpty (v ∈ Set.Icc (0 : ℝ) 1) := ⟨hv⟩
      simp only [Real.iSup_of_isEmpty]
      exact zero_le_one
  apply ciSup_le
  intro x
  have hcount := count_eq_coupled hu hle x
  have hbdd_inner : BddAbove (Set.range fun _ : cdf μ x ∈ Set.Icc (0 : ℝ) 1 =>
      |((empiricalCount (fun i _ => u i) n () (cdf μ x) : ℝ) / ((n + 1 : ℕ) : ℝ)) - cdf μ x|) := by
    refine ⟨|((empiricalCount (fun i _ => u i) n () (cdf μ x) : ℝ) / ((n + 1 : ℕ) : ℝ)) - cdf μ x|,
      fun y hy => ?_⟩
    obtain ⟨_, rfl⟩ := hy
    exact le_rfl
  calc |((empiricalCount (fun i _ => cdfQuantile μ (u i)) n () x : ℝ) / ((n + 1 : ℕ) : ℝ))
          - cdf μ x|
        = |((empiricalCount (fun i _ => u i) n () (cdf μ x) : ℝ) / ((n + 1 : ℕ) : ℝ))
          - cdf μ x| := by
          rw [hcount]
      _ ≤ ⨆ _ : cdf μ x ∈ Set.Icc (0 : ℝ) 1,
          |((empiricalCount (fun i _ => u i) n () (cdf μ x) : ℝ) / ((n + 1 : ℕ) : ℝ)) - cdf μ x| :=
          le_ciSup hbdd_inner (hmem x)
      _ ≤ (⨆ v ∈ Set.Icc (0 : ℝ) 1,
          |((empiricalCount (fun i _ => u i) n () v : ℝ) / ((n + 1 : ℕ) : ℝ)) - v|) :=
          le_ciSup hbdd (cdf μ x)

end KSReduction

end ProbabilityTheory
