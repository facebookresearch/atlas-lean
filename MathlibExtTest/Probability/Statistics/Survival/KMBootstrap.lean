/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.KMBootstrap

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Topology
open scoped ENNReal NNReal RealInnerProductSpace
open MathlibExt.Probability.Statistics.KaplanMeier ProbabilityTheory.Bootstrap
open MathlibExt.Probability.Statistics.KMBootstrap

namespace MathlibExtTest.Probability.Statistics.KMBootstrap

/-! ### A concrete bootstrap law at one grid point

Grid `1 < 2`; the sample of size `2` is a death at `1` and a censoring at `2`. The Kaplan–Meier
estimate at `1` is `1 - 1/2 = 1/2`. A bootstrap resample of size `2` contains the death twice
with probability `1/4`, and then `Ŝ*(1) = 0`. Everything below is computed from the definitions
of `kmGrid`, `world` and `empirical`, not through the limit theorems. -/

/-- The grid `1 < 2`. -/
noncomputable def t₂ : Fin 2 → ℝ := ![1, 2]

theorem t₂_strictMono : StrictMono t₂ := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i
  norm_num [t₂]

/-- The death at `1`. -/
noncomputable def a₂ : ℝ × ℝ := (1, 1)

/-- The censoring at `2`. -/
noncomputable def b₂ : ℝ × ℝ := (2, 0)

/-- The sample: `x 0 = (1, 1)`, `x 1 = (2, 0)` (later points are not used at `n = 2`). -/
noncomputable def x₂ : ℕ → ℝ × ℝ := fun i => if i = 0 then a₂ else b₂

theorem a₂_ne_b₂ : a₂ ≠ b₂ := by simp [a₂, b₂, Prod.ext_iff]

theorem x₂_mem_grid (i : ℕ) : (x₂ i).1 ∈ Set.range t₂ := by
  by_cases hi : i = 0
  · exact ⟨0, by simp [x₂, hi, a₂, t₂]⟩
  · exact ⟨1, by simp [x₂, hi, b₂, t₂]⟩

/-- For a sample of size `2` drawn from `{a₂, b₂}`, `Ŝ(1) = 1 - (number of deaths at 1) / 2`. -/
theorem kmGrid_two (y : ℕ → ℝ × ℝ) (hy : ∀ i < 2, y i ∈ ({a₂, b₂} : Set (ℝ × ℝ))) :
    kmGrid t₂_strictMono y 2 0 =
      1 - ((if y 0 = a₂ then 1 else 0) + (if y 1 = a₂ then 1 else 0)) / 2 := by
  have hy' : ∀ i < 2, y i = a₂ ∨ y i = b₂ := fun i hi => hy i hi
  have hgrid : ∀ i < 2, (y i).1 ∈ Set.range t₂ := fun i hi => by
    rcases hy' i hi with h | h
    · exact ⟨0, by simp [h, a₂, t₂]⟩
    · exact ⟨1, by simp [h, b₂, t₂]⟩
  have hr : ∀ i < 2, t₂ 0 ≤ (y i).1 := fun i hi => by
    rcases hy' i hi with h | h <;> norm_num [h, a₂, b₂, t₂]
  rw [kmGrid_eq_kmMap t₂_strictMono y 2 hgrid]
  simp only [kmMap, sampleMeanVec_apply, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, obsVec_inl, obsVec_inr]
  have hfilter : ({l | l ≤ (0 : Fin 2)} : Finset (Fin 2)) = {0} := by decide
  rw [hfilter, Finset.prod_singleton]
  simp only [hr 0 (by norm_num), hr 1 (by norm_num), ↓reduceIte]
  simp only [a₂, t₂, Matrix.cons_val_zero]
  by_cases h0 : y 0 = (1, 1) <;> by_cases h1 : y 1 = (1, 1) <;> simp [h0, h1] <;> norm_num

/-- The Kaplan–Meier estimate of the sample at `1` is `1/2`. -/
theorem kmGrid_x₂ : kmGrid t₂_strictMono x₂ 2 0 = 1 / 2 := by
  rw [kmGrid_two x₂ fun i hi => by
    interval_cases i <;> simp [x₂]]
  simp [x₂, a₂_ne_b₂.symm]
  norm_num

/-- `Ŝ*(1) = 0` exactly when both draws are the death. -/
theorem kmGrid_two_eq_zero_iff (y : ℕ → ℝ × ℝ)
    (hy : ∀ i < 2, y i ∈ ({a₂, b₂} : Set (ℝ × ℝ))) :
    kmGrid t₂_strictMono y 2 0 = 0 ↔ y 0 = a₂ ∧ y 1 = a₂ := by
  rw [kmGrid_two y hy]
  by_cases h0 : y 0 = a₂ <;> by_cases h1 : y 1 = a₂ <;> simp [h0, h1] <;> norm_num

/-- Each bootstrap draw from the sample of size `2` equals the death with probability `1/2`. -/
theorem empirical_x₂_a₂ : empirical x₂ 2 {a₂} = 2⁻¹ := by
  rw [empirical_of_ne_zero (by norm_num)]
  simp [Finset.sum_range_succ, x₂, Measure.dirac_apply' _ (measurableSet_singleton _),
    a₂_ne_b₂.symm]

/-- **The bootstrap law of `Ŝ*(1)` puts mass `1/4` at `0`**, computed from the bootstrap world
`world x₂`: both draws of the size-`2` resample must be the death. -/
theorem world_kmGrid_eq_zero :
    (world x₂).real {ω | kmGrid t₂_strictMono (ω 2) 2 0 = 0} = 1 / 4 := by
  have hS : MeasurableSet ({a₂, b₂} : Set (ℝ × ℝ)) :=
    (Set.toFinite _).measurableSet
  have hae := ae_resample_mem x₂ hS (n := 2) fun i hi => by
    interval_cases i <;> simp [x₂]
  have hcongr : {ω : ℕ → ℕ → ℝ × ℝ | kmGrid t₂_strictMono (ω 2) 2 0 = 0} =ᵐ[world x₂]
      (fun ω : ℕ → ℕ → ℝ × ℝ => ω 2) ⁻¹'
        Set.pi (({0, 1} : Finset ℕ) : Set ℕ) (fun _ => {a₂}) := by
    filter_upwards [hae] with ω hω
    apply propext
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_insert,
      Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
      forall_eq]
    exact kmGrid_two_eq_zero_iff (ω 2) hω
  rw [measureReal_def, measure_congr hcongr]
  change ((Measure.infinitePi fun n => Measure.infinitePi fun _ : ℕ => empirical x₂ n)
    (Function.eval 2 ⁻¹' _)).toReal = _
  rw [(measurePreserving_eval_infinitePi
      (fun n => Measure.infinitePi fun _ : ℕ => empirical x₂ n) 2).measure_preimage
      (MeasurableSet.pi (Finset.countable_toSet _) fun _ _ =>
        measurableSet_singleton _).nullMeasurableSet,
    Measure.infinitePi_pi (μ := fun _ : ℕ => empirical x₂ 2) (s := {0, 1})
      (t := fun _ => {a₂}) fun _ _ => measurableSet_singleton _]
  simp [empirical_x₂_a₂]
  norm_num

/-! ### A grid point with no events

Grid `1 < 2 < 3` and data with deaths at `1` and `3` and a censoring at `2`. No observation is
a death at `2`, so the Kaplan–Meier factor at `2` is `1` and `Ŝ(2) = Ŝ(1)`; almost surely the
same holds for every bootstrap resample, since resamples only contain data points. -/

/-- The grid `1 < 2 < 3`. -/
noncomputable def t₃ : Fin 3 → ℝ := ![1, 2, 3]

theorem t₃_strictMono : StrictMono t₃ := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i <;> norm_num [t₃]

/-- If none of the first `n` observations is a death at the middle grid point, the grid
Kaplan–Meier estimate does not move there. -/
theorem kmGrid_one_eq_kmGrid_zero (y : ℕ → ℝ × ℝ) (n : ℕ) (hy : ∀ i < n, y i ≠ (t₃ 1, 1)) :
    kmGrid t₃_strictMono y n 1 = kmGrid t₃_strictMono y n 0 := by
  classical
  have hd : (gridData t₃_strictMono y n).deaths 1 = 0 := by
    simp only [gridData]
    exact Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun i hi =>
      hy i (Finset.mem_range.1 hi))
  have hf : (gridData t₃_strictMono y n).kmFactor 1 = 1 := by
    simp [CensoredData.kmFactor, hd]
  simp only [kmGrid, CensoredData.kmSurvival, Finset.prod_filter, Fin.prod_univ_three]
  simp only [gridData, t₃, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hf ⊢
  norm_num [hf]

/-- The data: deaths at `1` and `3`, a censoring at `2`, repeated. -/
noncomputable def x₃ : ℕ → ℝ × ℝ :=
  fun i => if i % 3 = 0 then (1, 1) else if i % 3 = 1 then (2, 0) else (3, 1)

theorem x₃_ne (i : ℕ) : x₃ i ≠ (t₃ 1, 1) := by
  simp only [x₃, t₃, Matrix.cons_val_one]
  split_ifs <;> simp [Prod.ext_iff]

/-- The Kaplan–Meier estimate of the data is flat at the event-free grid point. -/
theorem kmGrid_x₃ (n : ℕ) : kmGrid t₃_strictMono x₃ n 1 = kmGrid t₃_strictMono x₃ n 0 :=
  kmGrid_one_eq_kmGrid_zero x₃ n fun i _ => x₃_ne i

/-- **Every bootstrap resample is flat at the event-free grid point**, almost surely under the
bootstrap world. -/
theorem ae_world_kmGrid_x₃ (n : ℕ) :
    ∀ᵐ ω ∂world x₃, kmGrid t₃_strictMono (ω n) n 1 = kmGrid t₃_strictMono (ω n) n 0 := by
  have hS : MeasurableSet ({(t₃ 1, 1)}ᶜ : Set (ℝ × ℝ)) := (measurableSet_singleton _).compl
  filter_upwards [ae_resample_mem x₃ hS (n := n) fun i _ => x₃_ne i] with ω hω
  exact kmGrid_one_eq_kmGrid_zero (ω n) n hω

/-! ### Boundary mass: where validity is not claimed

Population: half the subjects die at `1`, half are censored at `1`, so nobody is at risk at the
last grid point `2`. The mean indicator vector `θb` has at-risk coordinate `θb (inr 1) = 0`, so
the positivity hypothesis `hpos` of the bootstrap theorems fails. It must: `kmMap` is not even
continuous at `θb`. With `ε` subjects at risk at `2`, all dying there, the estimate at `2` is
`0`; with nobody at risk it is `1/2`. Resamples of such data hit both regimes, and no bootstrap
validity is claimed. -/

/-- The boundary mean vector: deaths `1/2, 0`, at risk `1, 0`. -/
noncomputable def θb : Coord 2 := WithLp.toLp 2 (Sum.elim ![1 / 2, 0] ![1, 0])

/-- The perturbation direction: one more death and one more subject at risk at `2`. -/
noncomputable def eb : Coord 2 := WithLp.toLp 2 (Sum.elim ![0, 1] ![0, 1])

/-- `θb` is the indicator mean of the sample `(1, 1), (1, 0)` on the grid `1 < 2`. -/
theorem sampleMeanVec_boundary :
    sampleMeanVec (fun i => obsVec t₂ (if i = 0 then ((1 : ℝ), (1 : ℝ)) else (1, 0))) 2 = θb := by
  ext i
  rcases i with j | j <;> fin_cases j <;>
    simp only [sampleMeanVec_apply, Finset.sum_range_succ, Finset.sum_range_zero, obsVec_inl,
      obsVec_inr] <;>
    norm_num [θb, t₂, Prod.ext_iff]

theorem θb_atRisk_one : θb (Sum.inr 1) = 0 := by simp [θb]

theorem kmMap_θb : kmMap θb 1 = 1 / 2 := by
  simp [kmMap, Finset.prod_filter, Fin.prod_univ_two, θb]
  norm_num

theorem kmMap_θb_add (ε : ℝ) (hε : ε ≠ 0) : kmMap (θb + ε • eb) 1 = 0 := by
  simp [kmMap, Finset.prod_filter, Fin.prod_univ_two, θb, eb, hε]

/-- **The Kaplan–Meier map is discontinuous at the boundary mean.** -/
theorem not_continuousAt_kmMap_θb : ¬ ContinuousAt (fun m : Coord 2 => kmMap m 1) θb := by
  intro h
  have hseq : Tendsto (fun n : ℕ => θb + (1 / ((n : ℝ) + 1)) • eb) atTop (𝓝 θb) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h0 := h1.smul_const eb
    simpa using (tendsto_const_nhds (x := θb)).add h0
  have h2 := h.tendsto.comp hseq
  have hval : (fun m : Coord 2 => kmMap m 1) ∘ (fun n : ℕ => θb + (1 / ((n : ℝ) + 1)) • eb) =
      fun _ => 0 := by
    funext n
    exact kmMap_θb_add _ (by positivity)
  rw [hval, kmMap_θb] at h2
  have := tendsto_nhds_unique tendsto_const_nhds h2
  norm_num at this

/-- Hence no strict derivative exists at the boundary mean: the delta-method input of the
bootstrap theorems is unavailable there. -/
theorem not_hasStrictFDerivAt_kmMap_θb (L : Coord 2 →L[ℝ] (Fin 2 → ℝ)) :
    ¬ HasStrictFDerivAt kmMap L θb := fun h =>
  not_continuousAt_kmMap_θb ((continuous_apply 1).continuousAt.comp h.continuousAt)

/-! ### Satisfiability of the iid theorems

Population: the death at `1` (`a₂`) and the censoring at `2` (`b₂`), each with probability
`1/2`; the observations are the coordinates of the infinite product. The at-risk means are `1`
and `1/2`. The law is not degenerate: the death indicator at `1` is Bernoulli `1/2`. -/

/-- The population law `(δ_{a₂} + δ_{b₂}) / 2`. -/
noncomputable def popKM : Measure (ℝ × ℝ) := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac a₂ + Measure.dirac b₂)

instance : IsProbabilityMeasure popKM :=
  ⟨by simp [popKM, ENNReal.inv_two_add_inv_two]⟩

/-- The iid sequence space. -/
noncomputable def seqKM : Measure (ℕ → ℝ × ℝ) := Measure.infinitePi fun _ => popKM

/-- The `i`-th observation. -/
def XKM (i : ℕ) (ω : ℕ → ℝ × ℝ) : ℝ × ℝ := ω i

instance : IsProbabilityMeasure seqKM := by unfold seqKM; infer_instance

theorem measurePreserving_XKM (i : ℕ) : MeasurePreserving (XKM i) seqKM popKM :=
  measurePreserving_eval_infinitePi (fun _ => popKM) i

theorem integral_obsVec_popKM :
    ∫ ω, obsVec t₂ (XKM 0 ω) ∂seqKM = (2⁻¹ : ℝ) • (obsVec t₂ a₂ + obsVec t₂ b₂) := by
  rw [← integral_map (measurePreserving_XKM 0).measurable.aemeasurable
    (measurable_obsVec t₂).aestronglyMeasurable, (measurePreserving_XKM 0).map_eq]
  rw [popKM, integral_smul_measure, integral_add_measure (integrable_dirac enorm_lt_top)
    (integrable_dirac enorm_lt_top), integral_dirac, integral_dirac]
  simp

theorem XKM_hyps :
    iIndepFun XKM seqKM ∧ (∀ i, IdentDistrib (XKM i) (XKM 0) seqKM seqKM) ∧
    (∀ i, ∀ᵐ ω ∂seqKM, (XKM i ω).1 ∈ Set.range t₂) ∧
    (∀ j, 0 < (∫ ω, obsVec t₂ (XKM 0 ω) ∂seqKM) (Sum.inr j)) := by
  refine ⟨?_, fun i => ?_, fun i => ?_, fun j => ?_⟩
  · rw [iIndepFun_iff_map_fun_eq_infinitePi_map fun i => (measurePreserving_XKM i).measurable]
    change seqKM.map id = _
    rw [Measure.map_id]
    unfold seqKM
    congr
    funext i
    exact ((measurePreserving_XKM i).map_eq).symm
  · exact ⟨(measurePreserving_XKM i).measurable.aemeasurable,
      (measurePreserving_XKM 0).measurable.aemeasurable,
      by rw [(measurePreserving_XKM i).map_eq, (measurePreserving_XKM 0).map_eq]⟩
  · have hpop : ∀ᵐ o ∂popKM, o.1 ∈ Set.range t₂ := by
      rw [ae_iff, popKM]
      have hS : MeasurableSet {o : ℝ × ℝ | ¬ o.1 ∈ Set.range t₂} :=
        (measurable_fst (Set.finite_range t₂).measurableSet).compl
      simp only [Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hS]
      simp [Set.indicator, a₂, b₂, t₂]
    exact (measurePreserving_XKM i).quasiMeasurePreserving.ae hpop
  · rw [integral_obsVec_popKM]
    fin_cases j <;> simp [a₂, b₂, t₂]

theorem memLp_obsVec_XKM : MemLp (fun ω => obsVec t₂ (XKM 0 ω)) 2 seqKM :=
  MemLp.of_bound ((measurable_obsVec t₂).comp
    (measurePreserving_XKM 0).measurable).aestronglyMeasurable _
    (ae_of_all _ fun _ => norm_obsVec_le t₂ _)

/-- **The iid theorem applies:** with a Gaussian limit built on `stdGaussian`, the sampling law
and, almost surely, the bootstrap law of grid Kaplan–Meier share the limit. -/
example : ∃ A : Coord 2 →L[ℝ] Coord 2,
    TendstoInDistribution
        (fun (n : ℕ) ω => √(n : ℝ) •
          (kmGrid t₂_strictMono (fun i => XKM i ω) n -
            kmMap (∫ ω, obsVec t₂ (XKM 0 ω) ∂seqKM)))
        atTop (fun z => fderiv ℝ kmMap (∫ ω, obsVec t₂ (XKM 0 ω) ∂seqKM) (A z))
        (fun _ => seqKM) (stdGaussian (Coord 2)) ∧
      ∀ᵐ ω ∂seqKM, TendstoInDistribution
        (fun (n : ℕ) ω' => √(n : ℝ) •
          (kmGrid t₂_strictMono (ω' n) n - kmGrid t₂_strictMono (fun i => XKM i ω) n))
        atTop (fun z => fderiv ℝ kmMap (∫ ω, obsVec t₂ (XKM 0 ω) ∂seqKM) (A z))
        (fun _ => world (fun i => XKM i ω)) (stdGaussian (Coord 2)) := by
  obtain ⟨hind, hid, hgr, hpos⟩ := XKM_hyps
  obtain ⟨A, hA⟩ := exists_hasLaw_inner_gaussianReal memLp_obsVec_XKM
  exact ⟨A, kmGrid_bootstrap_consistent t₂_strictMono XKM hind hid hgr hpos
    A.continuous.aemeasurable hA⟩

/-- **The limit-as-hypothesis theorem applies**, with the sampling limit as `hKM`. -/
example : ∃ A : Coord 2 →L[ℝ] Coord 2,
    ∀ᵐ ω ∂seqKM, TendstoInDistribution
      (fun (n : ℕ) ω' => √(n : ℝ) •
        (kmGrid t₂_strictMono (ω' n) n - kmGrid t₂_strictMono (fun i => XKM i ω) n))
      atTop (fun z => fderiv ℝ kmMap (∫ ω, obsVec t₂ (XKM 0 ω) ∂seqKM) (A z))
      (fun _ => world (fun i => XKM i ω)) (stdGaussian (Coord 2)) := by
  obtain ⟨hind, hid, hgr, hpos⟩ := XKM_hyps
  obtain ⟨A, hA⟩ := exists_hasLaw_inner_gaussianReal memLp_obsVec_XKM
  exact ⟨A, ae_tendstoInDistribution_bootstrap_kmGrid_of_limit t₂_strictMono XKM hind
    hid hgr hpos A.continuous.aemeasurable hA
    (kmGrid_bootstrap_consistent t₂_strictMono XKM hind hid hgr hpos
      A.continuous.aemeasurable hA).1⟩

/-! ### Satisfiability of the fixed-data theorem

A constant instance: one grid point `1`, every observation the death `a₂`, limit `Z = 0`. -/

/-- The one-point grid `1`. -/
noncomputable def t₁ : Fin 1 → ℝ := ![1]

theorem t₁_strictMono : StrictMono t₁ := fun i j h => by
  fin_cases i; fin_cases j; exact absurd h (lt_irrefl _)

theorem sampleMean_const (c : ℝ) {n : ℕ} (hn : n ≠ 0) :
    MathlibExt.Probability.Causality.sampleMean (fun _ : ℕ => c) (range n) = c := by
  rw [sampleMean_range]
  simp [hn]

example : TendstoInDistribution
    (fun (n : ℕ) ω => √(n : ℝ) •
      (kmGrid t₁_strictMono (ω n) n - kmGrid t₁_strictMono (fun _ => a₂) n))
    atTop (fun _ => fderiv ℝ kmMap (obsVec t₁ a₂) 0) (fun _ => world fun _ => a₂)
    (Measure.dirac ()) := by
  have hdev : ∀ (s : Coord 1) (n : ℕ), ∀ i ∈ range n, ⟪obsVec t₁ a₂, s⟫ -
      MathlibExt.Probability.Causality.sampleMean (fun _ => ⟪obsVec t₁ a₂, s⟫) (range n) = 0 :=
    fun s n i hi => by
      rw [sampleMean_const _ (Finset.nonempty_range_iff.1 ⟨i, hi⟩), sub_self]
  refine tendstoInDistribution_bootstrap_kmGrid t₁_strictMono (fun _ => a₂)
    (fun _ => ⟨0, by simp [a₂, t₁]⟩)
    (Z := fun _ : Unit => (0 : Coord 1)) aemeasurable_const 0 (fun s => ?_) (fun s => ?_)
    (fun s ε hε => ?_) (θ := obsVec t₁ a₂) ?_ (fun j => ?_)
  · exact ⟨aemeasurable_const, by simp [gaussianReal_zero_var]⟩
  · refine tendsto_const_nhds.congr fun n => ?_
    simp only [empiricalVar]
    rw [Finset.sum_eq_zero fun i hi => by rw [hdev s n i hi]; ring]
    simp
  · refine tendsto_const_nhds.congr fun n => ?_
    rw [Finset.sum_eq_zero fun i hi => by rw [hdev s n i hi]; simp]
    simp
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp only [sampleMeanVec, Finset.sum_const, Finset.card_range]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn), one_smul]
  · fin_cases j; simp [a₂, t₁]

/-! ### A grid containing time `0`

The fixed-data theorem has no sign condition on the grid. On the one-point grid `0` the
encoding does not send the origin of `ℝ × ℝ` to `0` (the origin is at risk at time `0`), and the
theorem still applies to constant data, a death at time `0`. -/

/-- The one-point grid `0`. -/
noncomputable def t₀ : Fin 1 → ℝ := ![0]

theorem t₀_strictMono : StrictMono t₀ := fun i j h => by
  fin_cases i; fin_cases j; exact absurd h (lt_irrefl _)

/-- The death at time `0`. -/
noncomputable def a₀ : ℝ × ℝ := (0, 1)

/-- The origin is at risk at time `0`, so its encoding on the grid `0` is not `0`. -/
theorem obsVec_t₀_zero_ne : obsVec t₀ 0 ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : Coord 1 => v (Sum.inr 0)) h
  simp [t₀] at h1

example : TendstoInDistribution
    (fun (n : ℕ) ω => √(n : ℝ) •
      (kmGrid t₀_strictMono (ω n) n - kmGrid t₀_strictMono (fun _ => a₀) n))
    atTop (fun _ => fderiv ℝ kmMap (obsVec t₀ a₀) 0) (fun _ => world fun _ => a₀)
    (Measure.dirac ()) := by
  have hdev : ∀ (s : Coord 1) (n : ℕ), ∀ i ∈ range n, ⟪obsVec t₀ a₀, s⟫ -
      MathlibExt.Probability.Causality.sampleMean (fun _ => ⟪obsVec t₀ a₀, s⟫) (range n) = 0 :=
    fun s n i hi => by
      rw [sampleMean_const _ (Finset.nonempty_range_iff.1 ⟨i, hi⟩), sub_self]
  refine tendstoInDistribution_bootstrap_kmGrid t₀_strictMono (fun _ => a₀)
    (fun _ => ⟨0, by simp [a₀, t₀]⟩)
    (Z := fun _ : Unit => (0 : Coord 1)) aemeasurable_const 0 (fun s => ?_) (fun s => ?_)
    (fun s ε hε => ?_) (θ := obsVec t₀ a₀) ?_ (fun j => ?_)
  · exact ⟨aemeasurable_const, by simp [gaussianReal_zero_var]⟩
  · refine tendsto_const_nhds.congr fun n => ?_
    simp only [empiricalVar]
    rw [Finset.sum_eq_zero fun i hi => by rw [hdev s n i hi]; ring]
    simp
  · refine tendsto_const_nhds.congr fun n => ?_
    rw [Finset.sum_eq_zero fun i hi => by rw [hdev s n i hi]; simp]
    simp
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp only [sampleMeanVec, Finset.sum_const, Finset.card_range]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn), one_smul]
  · fin_cases j; simp [a₀, t₀]

end MathlibExtTest.Probability.Statistics.KMBootstrap
