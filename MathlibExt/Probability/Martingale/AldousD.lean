/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Martingale.MartingaleTightness

import Mathlib.Topology.Instances.ENat

/-!
# Aldous's tightness criterion for step processes in `D([0,1])`

`MartingaleTightness.lean` proves Aldous's criterion in its continuous-limit form: the
polygonal interpolations `arrayPolygon n ξ` of a triangular array are tight in `C([0,1])`.
This file proves the criterion for the **step processes** `arrayStepProcess n ξ` themselves,
as random elements of the Skorokhod space `D([0,1])` with the J1 topology.

## Main results

* `isTightMeasureSet_arrayStepProcess_of_isTightMeasureSet_arrayPolygon`: tightness of the
  polygons in `C([0,1])` implies tightness of the step processes in `D([0,1])` (J1). No jump
  hypothesis is needed for this transfer.
* `isTightMeasureSet_arrayStepProcess_of_aldousCondition` (**Aldous's criterion in `D`**):
  Aldous's condition plus asymptotically negligible jumps implies tightness of the laws of the
  step processes in `D([0,1])` with the J1 topology (Jacod–Shiryaev VI.4.5 for this class of
  step processes, with VI.3.26).
* `isTightMeasureSet_arrayStepProcess_of_martingaleDifference`: square-integrable martingale
  difference arrays whose predictable quadratic variation converges to `t`, under Lindeberg,
  have tight step processes in `D([0,1])` (Jacod–Shiryaev VI.4.13 with VI.4.5). Unlike
  `tendstoInDistribution_arrayStepProcess`, this needs no finite-dimensional input (T81).

## Proof idea

The step process of row `n` is the grid sampling `t ↦ P(⌊n t⌋ / n)` of its own polygon `P`,
because the polygon passes through the partial sums at the grid times. Index the grid
samplings by `n ∈ ℕ∞`, with `n = ⊤` the path itself (`gridPath`, normalized to start at `0`).
The map `(n, f) ↦ gridPath n f` from `ℕ∞ × C([0,1])` to `D([0,1])` is continuous: in `n` at
`⊤` by uniform continuity of `f`, because grid sampling at mesh `1/n` moves a continuous path
by at most its modulus of continuity at `1/n` in the uniform metric, which dominates J1. Since
`ℕ∞` is compact, the image of `ℕ∞ × K` is compact in `D([0,1])` for every compact `K` of
polygons, and it contains every step process whose polygon lies in `K`.

## What is weakened or deferred

* **Negligible jumps are assumed** in the Aldous criterion (`hjump`), exactly as in the `C`
  version: the conclusion is tightness in `D`, but its proof goes through `C`-tightness of the
  polygons. The general `D`-valued criterion (Jacod–Shiryaev VI.4.5 for processes with
  non-vanishing jumps, giving tightness with possibly discontinuous limit points) needs
  Billingsley's characterization of compact sets of `D` by the modulus `w'` (Billingsley 1999,
  Theorem 12.3), which is not formalized here; T43's J1 structure is only an extended
  pseudo-metric, without completeness or separability.
* **Equally spaced grid** `k / n` with `n` increments in row `n`, as in `MartingaleTightness`.
* The martingale corollary inherits `aldousCondition_of_martingaleDifference`'s hypotheses
  (unconditional Lindeberg, quadratic-variation limit equal to the identity `t`).

Sources: J. Jacod, A. N. Shiryaev, *Limit Theorems for Stochastic Processes*, 2nd ed., Springer
(2003), Theorem VI.4.5 (Aldous's criterion), Proposition VI.3.26 (`C`-tightness), Theorem VI.4.13
(Rebolledo). D. Aldous, *Stopping times and tightness*, Ann. Probab. 6 (1978) 335–340.
P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley (1999), §§12–13.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal

namespace MathlibExt.Probability.Martingale

noncomputable section

variable {Ω : Type*}

/-! ### Grid samplings of a continuous path -/

/-- The grid point `k / n`, projected into `[0,1]`. -/
private def gridPoint (n k : ℕ) : Set.Icc (0 : ℝ) 1 :=
  Set.projIcc 0 1 zero_le_one ((k : ℝ) / n)

/-- The increments of a continuous path along the grid of mesh `1 / n`, as a deterministic
triangular array on a one-point sample space. -/
private def pathGridIncrements (f : C(Set.Icc (0 : ℝ) 1, ℝ)) : ℕ → ℕ → Unit → ℝ :=
  fun n i _ => f (gridPoint n (i + 1)) - f (gridPoint n i)

/-- Grid sampling of a continuous path, normalized to start at `0`: for `n : ℕ` the step path
`t ↦ f (⌊n t⌋ / n) - f 0`, and for `n = ⊤` the path `t ↦ f t - f 0` itself. -/
private def gridPath : ℕ∞ → C(Set.Icc (0 : ℝ) 1, ℝ) → SkorokhodSpace 1
  | ⊤, f => SkorokhodSpace.ofContinuous (f - ContinuousMap.const _ (f 0))
  | (n : ℕ), f => arrayStepProcess n (pathGridIncrements f) ()

private lemma gridPoint_zero (n : ℕ) : gridPoint n 0 = 0 := by
  simp [gridPoint, Set.projIcc_left]

private lemma gridPoint_floor_val {n : ℕ} (hn : 0 < n) (t : Set.Icc (0 : ℝ) 1) :
    (gridPoint n ⌊(n : ℝ) * t.1⌋₊ : ℝ) = ⌊(n : ℝ) * t.1⌋₊ / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht0 : 0 ≤ (n : ℝ) * t.1 := mul_nonneg hnR.le t.2.1
  have h0 : (0 : ℝ) ≤ ⌊(n : ℝ) * t.1⌋₊ / n := by positivity
  have h1 : (⌊(n : ℝ) * t.1⌋₊ : ℝ) / n ≤ 1 := by
    rw [div_le_one hnR]
    exact (Nat.floor_le ht0).trans (by simpa using mul_le_mul_of_nonneg_left t.2.2 hnR.le)
  simp [gridPoint, Set.projIcc_of_mem _ ⟨h0, h1⟩]

private lemma dist_gridPoint_floor_le {n : ℕ} (hn : 0 < n) (t : Set.Icc (0 : ℝ) 1) :
    dist (gridPoint n ⌊(n : ℝ) * t.1⌋₊) t ≤ 1 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht0 : 0 ≤ (n : ℝ) * t.1 := mul_nonneg hnR.le t.2.1
  rw [Subtype.dist_eq, gridPoint_floor_val hn, Real.dist_eq, abs_le]
  have hfl := Nat.floor_le ht0
  have hlt := Nat.lt_floor_add_one ((n : ℝ) * t.1)
  constructor
  · rw [neg_le_sub_iff_le_add, ← add_div, le_div_iff₀ hnR]
    linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hnR, add_mul, one_div, inv_mul_cancel₀ hnR.ne',
      mul_comm t.1]
    linarith

private lemma gridPath_top_apply (f : C(Set.Icc (0 : ℝ) 1, ℝ)) (t : Set.Icc (0 : ℝ) 1) :
    gridPath ⊤ f t = f t - f 0 := rfl

private lemma gridPath_coe_apply (n : ℕ) (f : C(Set.Icc (0 : ℝ) 1, ℝ))
    (t : Set.Icc (0 : ℝ) 1) :
    gridPath n f t = f (gridPoint n ⌊(n : ℝ) * t.1⌋₊) - f 0 := by
  change arrayStepProcess n (pathGridIncrements f) () t = _
  rw [arrayStepProcess_apply]
  simp only [pathGridIncrements]
  rw [Finset.sum_range_sub (fun k => f (gridPoint n k)), gridPoint_zero]

/-! ### The step process is the grid sampling of its polygon -/

/-- The polygon passes through the partial sums at the grid times. -/
private lemma arrayPolygon_gridPoint_floor (n : ℕ) (ξ : ℕ → ℕ → Ω → ℝ) (ω : Ω)
    (t : Set.Icc (0 : ℝ) 1) :
    arrayPolygon n ξ ω (gridPoint n ⌊(n : ℝ) * t.1⌋₊) =
      ∑ i ∈ Finset.range ⌊(n : ℝ) * t.1⌋₊, ξ n i ω := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [arrayPolygon_apply]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfl : ⌊(n : ℝ) * (gridPoint n ⌊(n : ℝ) * t.1⌋₊ : ℝ)⌋₊ = ⌊(n : ℝ) * t.1⌋₊ := by
    rw [gridPoint_floor_val hn, mul_div_cancel₀ _ hnR.ne', Nat.floor_natCast]
  rw [arrayPolygon_apply, hfl, gridPoint_floor_val hn, mul_div_cancel₀ _ hnR.ne', sub_self]
  simp

/-- The step process of row `n` is the grid sampling of its polygon. -/
private lemma arrayStepProcess_eq_gridPath (n : ℕ) (ξ : ℕ → ℕ → Ω → ℝ) (ω : Ω) :
    arrayStepProcess n ξ ω = gridPath n (arrayPolygon n ξ ω) := by
  ext t
  rw [gridPath_coe_apply, arrayPolygon_gridPoint_floor, arrayStepProcess_apply,
    show (0 : Set.Icc (0 : ℝ) 1) = ⟨0, le_rfl, zero_le_one⟩ from rfl, arrayPolygon_zero, sub_zero]

/-! ### Continuity of grid sampling on `ℕ∞ × C([0,1])` -/

private lemma edist_le_ofReal_of_abs_le {x y : SkorokhodSpace 1} {c : ℝ}
    (h : ∀ t, |x t - y t| ≤ c) : edist x y ≤ ENNReal.ofReal c :=
  (SkorokhodSpace.edist_le_iSup_edist _ _).trans (iSup_le fun t => by
    rw [edist_dist, Real.dist_eq]
    exact ENNReal.ofReal_le_ofReal (h t))

private lemma abs_sub_apply_le (f g : C(Set.Icc (0 : ℝ) 1, ℝ)) (t : Set.Icc (0 : ℝ) 1) :
    |g t - f t| ≤ dist g f := by
  rw [← Real.dist_eq]
  exact ContinuousMap.dist_apply_le_dist t

/-- Grid sampling is jointly continuous in the mesh index `n ∈ ℕ∞` and the path, from the
uniform metric to the J1 topology. -/
private lemma continuous_gridPath :
    Continuous fun p : ℕ∞ × C(Set.Icc (0 : ℝ) 1, ℝ) => gridPath p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun ⟨a, f⟩ => ?_
  rw [ContinuousAt, EMetric.tendsto_nhds]
  intro ε hε
  obtain ⟨r, -, hr0, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hr : 0 < r := ENNReal.ofReal_pos.1 hr0
  suffices h : ∀ᶠ x in 𝓝 (a, f), edist (gridPath x.1 x.2) (gridPath a f) ≤ ENNReal.ofReal r from
    h.mono fun x hx => hx.trans_lt hrε
  induction a using ENat.recTopCoe with
  | top =>
    obtain ⟨δ, hδ, hf⟩ := Metric.uniformContinuous_iff.1
      (CompactSpace.uniformContinuous_of_continuous f.continuous) (r / 2) (by positivity)
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
    have h1 : Set.Ioi (N : ℕ∞) ∈ 𝓝 (⊤ : ℕ∞) := Ioi_mem_nhds (ENat.natCast_lt_top N)
    have h2 : Metric.ball f (r / 4) ∈ 𝓝 f := Metric.ball_mem_nhds f (by positivity)
    filter_upwards [prod_mem_nhds h1 h2] with ⟨m, g⟩ ⟨hm, hg⟩
    simp only [Set.mem_Ioi, Metric.mem_ball] at hm hg
    have h0 := abs_sub_apply_le f g 0
    induction m using ENat.recTopCoe with
    | top =>
      refine edist_le_ofReal_of_abs_le fun t => ?_
      rw [gridPath_top_apply, gridPath_top_apply]
      have ht := abs_sub_apply_le f g t
      rw [abs_le] at ht h0 ⊢
      constructor <;> linarith
    | coe k =>
      have hk : N < k := by exact_mod_cast hm
      have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
      have hkpos : 0 < k := by
        have : (0 : ℝ) < k := hNpos.trans (by exact_mod_cast hk)
        exact_mod_cast this
      refine edist_le_ofReal_of_abs_le fun t => ?_
      rw [gridPath_coe_apply, gridPath_top_apply]
      set p := gridPoint k ⌊(k : ℝ) * t.1⌋₊
      have hp : dist p t < δ := by
        refine (dist_gridPoint_floor_le hkpos t).trans_lt ?_
        rw [one_div] at hN ⊢
        refine lt_of_le_of_lt (inv_anti₀ hNpos (by exact_mod_cast hk.le)) ?_
        exact (inv_lt_comm₀ hδ hNpos).1 hN
      have hfp := hf hp
      rw [Real.dist_eq] at hfp
      have hgp := abs_sub_apply_le f g p
      rw [abs_lt] at hfp
      rw [abs_le] at hgp h0 ⊢
      constructor <;> linarith
  | coe n =>
    have h1 : ({(n : ℕ∞)} : Set ℕ∞) ∈ 𝓝 (n : ℕ∞) := (ENat.mem_nhds_natCast_iff n).2 rfl
    have h2 : Metric.ball f (r / 2) ∈ 𝓝 f := Metric.ball_mem_nhds f (by positivity)
    filter_upwards [prod_mem_nhds h1 h2] with ⟨m, g⟩ ⟨hm, hg⟩
    simp only [Set.mem_singleton_iff, Metric.mem_ball] at hm hg
    subst hm
    refine edist_le_ofReal_of_abs_le fun t => ?_
    simp only
    rw [gridPath_coe_apply, gridPath_coe_apply]
    have hgp := abs_sub_apply_le f g (gridPoint n ⌊(n : ℝ) * t.1⌋₊)
    have h0 := abs_sub_apply_le f g 0
    rw [abs_le] at hgp h0 ⊢
    constructor <;> linarith

/-- The grid samplings of a compact set of continuous paths, at all meshes `n ∈ ℕ∞`, form a
compact subset of `D([0,1])`. -/
private lemma isCompact_gridPath_image {K : Set C(Set.Icc (0 : ℝ) 1, ℝ)} (hK : IsCompact K) :
    IsCompact ((fun p : ℕ∞ × C(Set.Icc (0 : ℝ) 1, ℝ) => gridPath p.1 p.2) '' (univ ×ˢ K)) :=
  (isCompact_univ.prod hK).image continuous_gridPath

/-! ### Tightness of the step processes in `D([0,1])` -/

/-- **From `C`-tightness of the polygons to `D`-tightness of the step processes.** If the laws
of the polygons `arrayPolygon n ξ` are tight in `C([0,1])`, then the laws of the step processes
`arrayStepProcess n ξ` are tight in the Skorokhod space `D([0,1])` with the J1 topology.

The compact set witnessing tightness in `D` is the closure of the grid samplings, at all
meshes `n ∈ ℕ∞`, of the compact set witnessing tightness in `C`. -/
theorem isTightMeasureSet_arrayStepProcess_of_isTightMeasureSet_arrayPolygon
    {m : MeasurableSpace Ω} {μ : Measure Ω} {ξ : ℕ → ℕ → Ω → ℝ}
    (hξ : ∀ n i, Measurable (ξ n i))
    (hpoly : IsTightMeasureSet (Set.range fun n => μ.map (arrayPolygon n ξ))) :
    IsTightMeasureSet (Set.range fun n => μ.map (arrayStepProcess n ξ)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hpoly ⊢
  intro ε hε
  obtain ⟨K, hK, hKμ⟩ := hpoly ε hε
  refine ⟨closure ((fun p : ℕ∞ × C(Set.Icc (0 : ℝ) 1, ℝ) => gridPath p.1 p.2) '' (univ ×ˢ K)),
    (isCompact_gridPath_image hK).closure, ?_⟩
  rintro _ ⟨n, rfl⟩
  rw [Measure.map_apply (measurable_arrayStepProcess n ξ (hξ n))
    isClosed_closure.measurableSet.compl]
  refine le_trans ?_ ((Measure.le_map_apply
    (measurable_arrayPolygon n ξ (hξ n)).aemeasurable Kᶜ).trans (hKμ _ ⟨n, rfl⟩))
  refine measure_mono fun ω hω => ?_
  simp only [Set.mem_preimage, Set.mem_compl_iff] at hω ⊢
  intro hPK
  refine hω (subset_closure ⟨((n : ℕ∞), arrayPolygon n ξ ω), ⟨Set.mem_univ _, hPK⟩, ?_⟩)
  exact (arrayStepProcess_eq_gridPath n ξ ω).symm

/-- **Aldous's tightness criterion in `D([0,1])`** (for the step processes of triangular
arrays).

Let row `n` of the array `ξ` be adapted to the filtration `𝓕 n` (`ξ n i` is
`𝓕 n (i + 1)`-measurable). If the largest increment of row `n` tends to `0` in probability and
the partial sums satisfy Aldous's condition (`AldousCondition`, the two-stopping-time form of
Jacod–Shiryaev VI.4.5 (ii)), then the laws of the step processes
`arrayStepProcess n ξ : Ω → D([0,1])`, `t ↦ ∑_{i < ⌊n t⌋} ξ n i`, are tight for the Skorokhod
J1 topology.

Source: Jacod–Shiryaev (2003), Theorem VI.4.5 (Aldous's criterion for tightness in `D`), for
step processes with asymptotically negligible jumps (Proposition VI.3.26); Aldous (1978). The
paths start at `0`, so the compact-containment condition (i) of VI.4.5 is not needed.
Proof: `C`-tightness of the polygons (`isTightMeasureSet_arrayPolygon_of_aldousCondition`),
transferred to `D` by
`isTightMeasureSet_arrayStepProcess_of_isTightMeasureSet_arrayPolygon`. -/
theorem isTightMeasureSet_arrayStepProcess_of_aldousCondition {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓕 : ℕ → Filtration ℕ m} {ξ : ℕ → ℕ → Ω → ℝ}
    (hξ : ∀ n i, Measurable[𝓕 n (i + 1)] (ξ n i))
    (hjump : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ω | ∃ i < n, ε < |ξ n i ω|}) atTop (𝓝 0))
    (hA : AldousCondition 𝓕 ξ μ) :
    IsTightMeasureSet (Set.range fun n => μ.map (arrayStepProcess n ξ)) :=
  isTightMeasureSet_arrayStepProcess_of_isTightMeasureSet_arrayPolygon
    (fun n i => (hξ n i).mono ((𝓕 n).le _) le_rfl)
    (isTightMeasureSet_arrayPolygon_of_aldousCondition hξ hjump hA)

/-- **Tightness in `D([0,1])` of martingale difference arrays.** Let row `n` of `ξ` be a
square-integrable martingale difference sequence for `𝓕 n` whose predictable quadratic
variation converges in probability to the identity at every `t ∈ [0,1]`, and let `ξ` satisfy
the Lindeberg condition. Then the laws of the step processes `arrayStepProcess n ξ` are tight
in `D([0,1])` with the J1 topology.

Source: Jacod–Shiryaev (2003), Theorem VI.4.13 (Rebolledo: the quadratic-variation condition
gives Aldous's condition) with Theorem VI.4.5. Proof: `aldousCondition_of_martingaleDifference`
and `tendsto_measure_exists_abs_gt_of_lindeberg` discharge the hypotheses of
`isTightMeasureSet_arrayStepProcess_of_aldousCondition`. -/
theorem isTightMeasureSet_arrayStepProcess_of_martingaleDifference {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓕 : ℕ → Filtration ℕ m} {ξ : ℕ → ℕ → Ω → ℝ}
    (hξ : ∀ n i, StronglyMeasurable[𝓕 n (i + 1)] (ξ n i))
    (hmds : ∀ n i, μ[ξ n i | 𝓕 n i] =ᵐ[μ] 0) (hL2 : ∀ n i, MemLp (ξ n i) 2 μ)
    (hQV : ∀ t ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)
      atTop (fun _ => t))
    (hLind : LindebergConditionTriangular ξ μ) :
    IsTightMeasureSet (Set.range fun n => μ.map (arrayStepProcess n ξ)) := by
  have hξm : ∀ n i, Measurable (ξ n i) := fun n i =>
    ((hξ n i).mono ((𝓕 n).le _)).measurable
  exact isTightMeasureSet_arrayStepProcess_of_aldousCondition (fun n i => (hξ n i).measurable)
    (tendsto_measure_exists_abs_gt_of_lindeberg hξm hL2 hLind)
    (aldousCondition_of_martingaleDifference hξ hmds hL2 hQV)

end

end MathlibExt.Probability.Martingale
