/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.RandomizedEstimandHolm

/-!
# An explicit PRDS p-value family for zero-ATE endpoints, and its power

`MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.RandomizedEstimand` and
`...RandomizedEstimandHolm` prove that Bonferroni, Holm, BH (under independence or PRDS) and
Benjamini–Yekutieli control error over the zero-ATE endpoints `ateNulls μ Y₀ Y₁`, taking as
hypotheses that the p-values are calibrated for the observed-data IPW null
(`IsIPWNullCalibrated`) and, for BH under dependence, PRDS on the causal nulls (`IsPRDSOn`).
Neither file constructs such p-values or says anything about power. This file gives an explicit
family that satisfies both hypotheses and computes its power.

**The family.** `k` clusters carry null noises `U b`, uniform on `[0, 1]` and mutually
independent; endpoint `j` belongs to cluster `c j`, and endpoints of one cluster share their
noise. Endpoint `j` reports the Lehmann p-value
`p j = max (U (c j)) 0 ^ θ j` with `θ j = exp (κ j * ipwContrast μ T X (Y j))`
(`ateLehmannPValue`). The scale `κ j > 0` plays the role of `√n / σ j`. When the observed IPW
contrast vanishes, `θ j = 1` and `p j` is the uniform noise; when it is positive, `θ j > 1` and
`p j` has the Beta(`1 / θ j`, 1) law, Lehmann's alternative `P(p j ≤ t) = t ^ (1 / θ j)`. The
exponent depends only on the observed-data law, so the family is calibrated for the
observed-data null without causal assumptions, and identification
(`ipwContrast_observed_eq_integral`) rewrites `θ j` in terms of the ATE `E[Y₁ j - Y₀ j]`.

This is a model of a p-value family (signal through the observed-data law, randomness through
the cluster noises), not a test computed from a sample: the noises are not tied to `(T, X, Y)`.

## Main definitions

* `lehmannPValue U c θ`: the clustered Lehmann p-values `max (U (c j)) 0 ^ θ j`.
* `ateLehmannExponent μ T X Y κ`: the exponents `exp (κ j * ipwContrast μ T X (Y j))`.
* `ateLehmannPValue μ T X Y κ U c`: the clustered Lehmann p-values with the ATE exponents.

## Main results

* `isPRDSOn_of_eq_comp_indepFun`: a PRDS criterion: for each `i ∈ H0` the p-value vector is
  `F (p i) W` with `W` independent of `p i` and `F` nondecreasing in its first argument. For
  probability measures it contains the merged `isPRDSOn_of_monotone_comp` and
  `isPRDSOn_of_iIndepFun`.
* `bonferroniRejections_subset_holmRejections`, `bonferroniRejections_subset_bhRejections`:
  Holm and BH reject every hypothesis Bonferroni rejects.
* Construction: `isIPWNullCalibrated_ateLehmannPValue` (calibration for the observed-data IPW
  null) and `isPRDSOn_ateLehmannPValue` / `isPRDSOn_lehmannPValue` (PRDS on every set of
  endpoints, so on the causal nulls; dependent within a cluster).
* Error control with every p-value hypothesis discharged:
  `integral_falseDiscoveryProportion_bhRejections_ateNulls_ateLehmannPValue_le` (BH FDR over the
  causal nulls at most `q |ateNulls| / m`) and
  `measure_holm_ateNulls_familywiseError_ateLehmannPValue_le` (Holm FWER at most `α`).
* Power of one test: `measure_lehmannPValue_le` (`P(p j ≤ t) = t ^ (1 / θ j)`),
  `measure_ateLehmannPValue_le`, `measure_ateLehmannPValue_observed_le` (power
  `t ^ exp (-(κ j * E[Y₁ j - Y₀ j]))` under strong ignorability),
  `ofReal_le_measure_lehmannPValue_le` / `ofReal_lt_measure_lehmannPValue_le` (unbiased; strictly
  for a positive effect) and `tendsto_measure_lehmannPValue_le` (consistency).
* Power of the procedures: `measure_mem_bonferroniRejections_lehmannPValue` (exactly
  `(α / m) ^ (1 / θ j)`), `ofReal_le_measure_mem_holmRejections_lehmannPValue`,
  `ofReal_le_measure_mem_bhRejections_lehmannPValue` and
  `ofReal_le_measure_mem_bhRejections_ateLehmannPValue_observed` (at least the Bonferroni
  power), `tendsto_measure_mem_holmRejections_lehmannPValue`,
  `tendsto_measure_mem_bhRejections_lehmannPValue` and
  `tendsto_measure_mem_bhRejections_ateLehmannPValue` (power tends to `1` as the scale grows,
  for a positive observed contrast).

## Not covered

No estimator is constructed: a Wald test of an IPW estimator with an estimated propensity, and
its asymptotic calibration by a central limit theorem, are not formalized. The dependence
allowed is block-comonotone (correlation `0` across clusters, `1` within a cluster); PRDS of
one-sided Gaussian p-values with arbitrary nonnegative correlations (Benjamini–Yekutieli 2001,
§3.1) is not proved. The power bounds for Holm and BH are the Bonferroni power; their exact power
depends on the other endpoints and is not computed. No sample-size formula is given.

## References

* E. L. Lehmann, *The power of rank tests*, Ann. Math. Statist. 24 (1953), 23–43 (the
  alternatives `G = F ^ k`).
* S. Pounds and S. W. Morris, *Estimating the occurrence of false positives and false negatives
  in microarray studies by approximating and partitioning the empirical distribution of
  p-values*, Bioinformatics 19 (2003), 1236–1242 (the Beta(`a`, 1) p-value alternative).
* Y. Benjamini and D. Yekutieli, *The control of the false discovery rate in multiple testing
  under dependency*, Ann. Statist. 29 (2001), 1165–1188 (PRDS, Theorem 1.2).
* S. Holm, *A simple sequentially rejective multiple test procedure*, Scand. J. Statist. 6
  (1979), 65–70.
* Y. Benjamini and Y. Hochberg, *Controlling the false discovery rate: a practical and powerful
  approach to multiple testing*, J. Roy. Statist. Soc. Ser. B 57 (1995), 289–300.
* P. R. Rosenbaum and D. B. Rubin, *The central role of the propensity score in observational
  studies for causal effects*, Biometrika 70 (1983), 41–55.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Causality Filter Topology

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] {m k : ℕ}

/-! ### PRDS from a monotone representation with independent remainder -/

/-- **PRDS from a monotone representation with an independent remainder.** Suppose that for
every `i ∈ H0` the whole p-value vector is `F (p i) W`, where `W` is a random element independent
of `p i` and `F` is jointly measurable and nondecreasing in its first argument. Then `p` is PRDS
on `H0`: given `p i = x`, the vector is `F x W` with `W` keeping its law, so
`P(P ∈ D | p i = x) = P(F x W ∈ D)`, nondecreasing in `x` for increasing `D`.

For probability measures both merged criteria are special cases: `isPRDSOn_of_monotone_comp`
(constant `W`; that theorem itself only needs a finite measure) and `isPRDSOn_of_iIndepFun` (`W` the
other coordinates, `F` inserting `x` at coordinate `i`).
The proof is the one of `isPRDSOn_of_iIndepFun`.

Source: the PRDS definition of Benjamini & Yekutieli (2001); the criterion has no named source
theorem and is proved directly from `isPRDSOn_iff_setLIntegral`. -/
theorem isPRDSOn_of_eq_comp_indepFun {β : Type*} [MeasurableSpace β] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    (H0 : Finset (Fin m))
    (h : ∀ i ∈ H0, ∃ (W : Ω → β) (F : ℝ → β → Fin m → ℝ), Measurable W ∧
      Measurable (Function.uncurry F) ∧ IndepFun (p i) W μ ∧
      (∀ w, Monotone fun x => F x w) ∧ ∀ ω, (fun j => p j ω) = F (p i ω) (W ω)) :
    IsPRDSOn μ p H0 := by
  classical
  rw [isPRDSOn_iff_setLIntegral μ p hp H0]
  intro i hi D hD hup
  obtain ⟨W, F, hW, hF, hind, hmono, hPF⟩ := h i hi
  have hSet : MeasurableSet (Function.uncurry F ⁻¹' D) := hF hD
  let ρ := μ.map W
  refine ⟨fun x => ρ (Prod.mk x ⁻¹' (Function.uncurry F ⁻¹' D)), ?_, fun B hB => ?_⟩
  · intro x y hxy
    exact measure_mono fun w hw => hup (hmono w hxy) hw
  · have hpre : {ω | (fun j => p j ω) ∈ D} ∩ p i ⁻¹' B =
        (fun ω => (p i ω, W ω)) ⁻¹' ((B ×ˢ Set.univ) ∩ Function.uncurry F ⁻¹' D) := by
      ext ω
      simp [hPF ω, and_comm]
    have hslice (x : ℝ) : ρ (Prod.mk x ⁻¹' ((B ×ˢ Set.univ) ∩ Function.uncurry F ⁻¹' D)) =
        B.indicator (fun x => ρ (Prod.mk x ⁻¹' (Function.uncurry F ⁻¹' D))) x := by
      by_cases hx : x ∈ B
      · rw [Set.indicator_of_mem hx]
        congr 1
        ext w
        simp [hx]
      · rw [Set.indicator_of_notMem hx]
        convert measure_empty (μ := ρ)
        ext w
        simp [hx]
    rw [hpre, ← Measure.map_apply ((hp i).prodMk hW) ((hB.prod MeasurableSet.univ).inter hSet),
      (indepFun_iff_map_prod_eq_prod_map_map (hp i).aemeasurable hW.aemeasurable).mp hind,
      Measure.prod_apply ((hB.prod MeasurableSet.univ).inter hSet)]
    rw [← lintegral_indicator hB]
    exact lintegral_congr fun x => hslice x

/-! ### Every Bonferroni rejection is a Holm and a BH rejection -/

/-- **Holm rejects everything Bonferroni rejects.** If `p j ≤ α / m` then Holm's step-down
procedure at level `α ≥ 0` rejects `j`: its first step succeeds, and every later threshold
`α / (m - r + 1)` is at least `α / m`.

Source: Holm (1979) (the sequentially rejective test rejects whenever Bonferroni does). -/
theorem bonferroniRejections_subset_holmRejections {α : ℝ} (hα : 0 ≤ α) (p : Fin m → ℝ) :
    bonferroniRejections α p ⊆ holmRejections α p := by
  classical
  intro j hj
  simp only [bonferroniRejections, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  have hm : 1 ≤ m := j.pos
  have hcount : 1 ≤ numBelow p (α / ((m : ℝ) - (1 : ℕ) + 1)) := by
    rw [show (m : ℝ) - (1 : ℕ) + 1 = m by push_cast; ring]
    exact Finset.card_pos.2 ⟨j, by simp [hj]⟩
  have h1 : 1 ≤ holmIndex α p := le_holmIndex hm fun l hl => by
    obtain rfl : l = 1 := le_antisymm (Finset.mem_Icc.1 hl).2 (Finset.mem_Icc.1 hl).1
    exact hcount
  have hr : (holmIndex α p : ℝ) ≤ m := by exact_mod_cast holmIndex_le α p
  have hr1 : (1 : ℝ) ≤ holmIndex α p := by exact_mod_cast h1
  simp only [holmRejections, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hj.trans (div_le_div_of_nonneg_left hα (by linarith) (by linarith))

/-- **BH rejects everything Bonferroni rejects.** If `p j ≤ q / m` then the Benjamini–Hochberg
procedure at level `q ≥ 0` rejects `j`: the step-up index is at least `1`, and the threshold
`q k / m` at `k ≥ 1` is at least `q / m`.

Source: Benjamini & Hochberg (1995) (the step-up procedure's first threshold is `q / m`). -/
theorem bonferroniRejections_subset_bhRejections {q : ℝ} (hq : 0 ≤ q) (p : Fin m → ℝ) :
    bonferroniRejections q p ⊆ bhRejections q p := by
  classical
  intro j hj
  simp only [bonferroniRejections, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  have hm : 1 ≤ m := j.pos
  have h1 : 1 ≤ bhIndex q p := le_bhIndex hm (by
    rw [Nat.cast_one, mul_one]
    exact Finset.card_pos.2 ⟨j, by simp [hj]⟩)
  have hk1 : (1 : ℝ) ≤ bhIndex q p := by exact_mod_cast h1
  simp only [bhRejections, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hj.trans (div_le_div_of_nonneg_right (le_mul_of_one_le_right hq hk1) (Nat.cast_nonneg m))

/-! ### The clustered Lehmann p-value family -/

/-- The **clustered Lehmann p-values** with null noise `U`, cluster map `c` and exponents `θ`:
endpoint `j` reports `max (U (c j)) 0 ^ θ j`. The `k` noise variables `U` are the null
p-values of `k` clusters; endpoints in one cluster share their noise. With `U (c j)` uniform on
`[0, 1]` and `θ j > 0`, the p-value of `j` has the Beta(`1 / θ j`, 1) law, the Lehmann
alternative `P(p ≤ t) = t ^ (1 / θ j)`; `θ j = 1` is the null. Truncation at `0` makes `p j` a
monotone function of the noise; under the uniform law it only matters on a null set. -/
noncomputable def lehmannPValue (U : Fin k → Ω → ℝ) (c : Fin m → Fin k) (θ : Fin m → ℝ) :
    Fin m → Ω → ℝ :=
  fun j ω => max (U (c j) ω) 0 ^ θ j

/-- The Lehmann p-values are measurable when the noises are. -/
theorem measurable_lehmannPValue {U : Fin k → Ω → ℝ} (hU : ∀ c, Measurable (U c))
    (c : Fin m → Fin k) (θ : Fin m → ℝ) (j : Fin m) : Measurable (lehmannPValue U c θ j) :=
  ((hU (c j)).max measurable_const).pow_const _

omit [MeasurableSpace Ω] in
/-- The Lehmann p-values are nonnegative. -/
theorem lehmannPValue_nonneg (U : Fin k → Ω → ℝ) (c : Fin m → Fin k) (θ : Fin m → ℝ)
    (j : Fin m) (ω : Ω) : 0 ≤ lehmannPValue U c θ j ω :=
  Real.rpow_nonneg (le_max_right _ _) _

omit [MeasurableSpace Ω] in
/-- With exponent `1` the Lehmann p-value is the (truncated) null noise. -/
theorem lehmannPValue_of_eq_one {U : Fin k → Ω → ℝ} {c : Fin m → Fin k} {θ : Fin m → ℝ}
    {j : Fin m} (hj : θ j = 1) : lehmannPValue U c θ j = fun ω => max (U (c j) ω) 0 := by
  funext ω
  simp [lehmannPValue, hj]

/-- A uniform null noise gives a valid p-value at exponent `1`. -/
theorem isValidPValue_lehmannPValue_of_eq_one {μ : Measure Ω} {U : Fin k → Ω → ℝ}
    {c : Fin m → Fin k} {θ : Fin m → ℝ} {j : Fin m}
    (hU : HasLaw (U (c j)) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ) (hj : θ j = 1) :
    IsValidPValue μ (lehmannPValue U c θ j) := by
  rw [lehmannPValue_of_eq_one hj]
  exact (isValidPValue_of_hasLaw_uniform hU).mono_ae (ae_of_all _ fun ω => le_max_left _ _)

private theorem indepFun_cluster_rest {μ' : Measure Ω} [IsProbabilityMeasure μ']
    {U : Fin k → Ω → ℝ} (hU : ∀ c, Measurable (U c)) (hind : iIndepFun U μ') (a : Fin k) :
    IndepFun (U a) (fun ω (b : Fin k) => if b = a then 0 else U b ω) μ' := by
  classical
  have h := hind.indepFun_finset {a} (Finset.univ.erase a)
    (Finset.disjoint_singleton_left.2 (Finset.notMem_erase a _)) hU
  let f₁ : (↥({a} : Finset (Fin k)) → ℝ) → ℝ := fun v => v ⟨a, Finset.mem_singleton_self a⟩
  let f₂ : (↥(Finset.univ.erase a) → ℝ) → Fin k → ℝ :=
    fun v b => if hb : b = a then 0 else v ⟨b, Finset.mem_erase.2 ⟨hb, Finset.mem_univ b⟩⟩
  have hf₁ : Measurable f₁ := measurable_pi_apply _
  have hf₂ : Measurable f₂ := by
    refine Measurable.of_eval fun b => ?_
    by_cases hb : b = a
    · simp only [f₂, hb, dite_true]
      exact measurable_const
    · simp only [f₂, hb, dite_false]
      exact measurable_pi_apply _
  have e₁ : U a = f₁ ∘ fun ω (i : ↥({a} : Finset (Fin k))) => U i ω := rfl
  have e₂ : (fun ω (b : Fin k) => if b = a then 0 else U b ω) =
      f₂ ∘ fun ω (i : ↥(Finset.univ.erase a)) => U i ω := by
    funext ω b
    by_cases hb : b = a <;> simp [f₂, hb]
  rw [e₁, e₂]
  exact h.comp hf₁ hf₂

/-- **The clustered Lehmann p-values are PRDS on every set of endpoints.** If the cluster noises
are measurable and mutually independent and all exponents are positive, the Lehmann p-values
are PRDS on every `H0`, true nulls or not. Given `p i = x`, an endpoint `j` in the cluster of `i`
reports `x ^ (θ j / θ i)`, nondecreasing in `x`, and endpoints of the other clusters keep their
law by independence (`isPRDSOn_of_eq_comp_indepFun`).

Independent p-values (`c` injective) and comonotone p-values (one cluster) are the extreme
cases. -/
theorem isPRDSOn_lehmannPValue {μ : Measure Ω} [IsProbabilityMeasure μ] {U : Fin k → Ω → ℝ}
    (hU : ∀ c, Measurable (U c)) (hind : iIndepFun U μ) (c : Fin m → Fin k) {θ : Fin m → ℝ}
    (hθ : ∀ j, 0 < θ j) (H0 : Finset (Fin m)) : IsPRDSOn μ (lehmannPValue U c θ) H0 := by
  classical
  refine isPRDSOn_of_eq_comp_indepFun (β := Fin k → ℝ) μ _ (measurable_lehmannPValue hU c θ) H0
    fun i _ => ?_
  let W : Ω → Fin k → ℝ := fun ω b => if b = c i then 0 else U b ω
  let F : ℝ → (Fin k → ℝ) → Fin m → ℝ := fun x w j =>
    if c j = c i then max x 0 ^ (θ j / θ i) else max (w (c j)) 0 ^ θ j
  refine ⟨W, F, ?_, ?_, ?_, ?_, ?_⟩
  · refine Measurable.of_eval fun b => ?_
    by_cases hb : b = c i
    · simp only [W, hb, ↓reduceIte]; exact measurable_const
    · simp only [W, hb, ↓reduceIte]; exact hU b
  · refine Measurable.of_eval fun j => ?_
    change Measurable fun z : ℝ × (Fin k → ℝ) => F z.1 z.2 j
    by_cases hj : c j = c i
    · simp only [F, hj, ↓reduceIte]
      exact (measurable_fst.max measurable_const).pow_const _
    · simp only [F, hj, ↓reduceIte]
      exact (((measurable_pi_apply (c j)).comp measurable_snd).max measurable_const).pow_const _
  · have hg : Measurable fun u : ℝ => max u 0 ^ θ i :=
      (measurable_id.max measurable_const).pow_const _
    exact (indepFun_cluster_rest hU hind (c i)).comp hg measurable_id
  · intro w x y hxy j
    by_cases hj : c j = c i
    · simp only [F, hj, ↓reduceIte]
      exact Real.rpow_le_rpow (le_max_right _ _) (max_le_max_right 0 hxy)
        (div_pos (hθ j) (hθ i)).le
    · simp only [F, hj, ↓reduceIte, le_refl]
  · intro ω
    funext j
    by_cases hj : c j = c i
    · simp only [F, hj, ↓reduceIte, lehmannPValue]
      rw [max_eq_left (Real.rpow_nonneg (le_max_right _ _) _), ← Real.rpow_mul (le_max_right _ _),
        mul_div_cancel₀ _ (hθ i).ne']
    · simp only [F, W, hj, ↓reduceIte, lehmannPValue]

/-! ### Power of a single Lehmann p-value -/

private theorem measure_le_eq_of_hasLaw_uniform {μ : Measure Ω} {V : Ω → ℝ}
    (hV : HasLaw V (volume.restrict (Set.Icc (0 : ℝ) 1)) μ) {s : ℝ} (hs₁ : s ≤ 1) :
    μ {ω | V ω ≤ s} = ENNReal.ofReal s := by
  have h : μ {ω | V ω ≤ s} = volume.restrict (Set.Icc (0 : ℝ) 1) (Set.Iic s) := by
    rw [← hV.map_eq, Measure.map_apply_of_aemeasurable hV.aemeasurable measurableSet_Iic]
    rfl
  have hI : Set.Iic s ∩ Set.Icc 0 1 = Set.Icc 0 s := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨hxs, hx0, -⟩
      exact ⟨hx0, hxs⟩
    · rintro ⟨hx0, hxs⟩
      exact ⟨hxs, hx0, hxs.trans hs₁⟩
  rw [h, Measure.restrict_apply measurableSet_Iic, hI, Real.volume_Icc, sub_zero]

/-- **Power of a Lehmann p-value (Lehmann alternative).** If the noise of the cluster of `j` is
uniform on `[0, 1]` and `θ j > 0`, then `P(p j ≤ t) = t ^ (1 / θ j)` for `t ∈ [0, 1]`: the
p-value has the Beta(`1 / θ j`, 1) law.

Source: Lehmann (1953), the alternatives `G = F ^ k`; for p-values, the Beta(`a`, 1)
alternative of the beta-uniform mixture of Pounds & Morris (2003). -/
theorem measure_lehmannPValue_le {μ : Measure Ω} {U : Fin k → Ω → ℝ} {c : Fin m → Fin k}
    {θ : Fin m → ℝ} {j : Fin m} (hU : HasLaw (U (c j)) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ)
    (hθ : 0 < θ j) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    μ {ω | lehmannPValue U c θ j ω ≤ t} = ENNReal.ofReal (t ^ (θ j)⁻¹) := by
  have hset : {ω | lehmannPValue U c θ j ω ≤ t} = {ω | U (c j) ω ≤ t ^ (θ j)⁻¹} := by
    ext ω
    simp only [lehmannPValue, Set.mem_ofPred_eq]
    rw [← Real.le_rpow_inv_iff_of_pos (le_max_right _ _) ht₀ hθ, max_le_iff]
    simp [Real.rpow_nonneg ht₀]
  rw [hset, measure_le_eq_of_hasLaw_uniform hU (Real.rpow_le_one ht₀ ht₁ (inv_nonneg.2 hθ.le))]

/-- **Unbiasedness.** With exponent `θ j ≥ 1` (a nonnegative effect), the test rejecting when
`p j ≤ t` has power at least its level `t`, for `t ∈ [0, 1]`. -/
theorem ofReal_le_measure_lehmannPValue_le {μ : Measure Ω} {U : Fin k → Ω → ℝ}
    {c : Fin m → Fin k} {θ : Fin m → ℝ} {j : Fin m}
    (hU : HasLaw (U (c j)) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ) (hθ : 1 ≤ θ j) {t : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    ENNReal.ofReal t ≤ μ {ω | lehmannPValue U c θ j ω ≤ t} := by
  rw [measure_lehmannPValue_le hU (by linarith) ht₀ ht₁]
  exact ENNReal.ofReal_le_ofReal (Real.self_le_rpow_of_le_one ht₀ ht₁ (inv_le_one_of_one_le₀ hθ))

/-- **Strict unbiasedness.** With exponent `θ j > 1` (a positive effect), the power at a level
`t ∈ (0, 1)` is strictly larger than `t`. In particular a non-null Lehmann p-value is not a
valid p-value. -/
theorem ofReal_lt_measure_lehmannPValue_le {μ : Measure Ω} {U : Fin k → Ω → ℝ}
    {c : Fin m → Fin k} {θ : Fin m → ℝ} {j : Fin m}
    (hU : HasLaw (U (c j)) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ) (hθ : 1 < θ j) {t : ℝ}
    (ht₀ : 0 < t) (ht₁ : t < 1) :
    ENNReal.ofReal t < μ {ω | lehmannPValue U c θ j ω ≤ t} := by
  rw [measure_lehmannPValue_le hU (by linarith) ht₀.le ht₁.le,
    ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos ht₀ _)]
  calc t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
    _ < t ^ (θ j)⁻¹ := Real.rpow_lt_rpow_of_exponent_gt ht₀ ht₁ (inv_lt_one_of_one_lt₀ hθ)

/-- `t ^ (1 / θ) → 1` as `θ → ∞`, for `t ∈ (0, 1]`. -/
private theorem tendsto_ofReal_rpow_inv {ι : Type*} {l : Filter ι} {θ : ι → ℝ}
    (hθ : Tendsto θ l atTop) {t : ℝ} (ht₀ : 0 < t) :
    Tendsto (fun n => ENNReal.ofReal (t ^ (θ n)⁻¹)) l (𝓝 1) := by
  have h0 : Tendsto (fun n => (θ n)⁻¹) l (𝓝 0) := tendsto_inv_atTop_zero.comp hθ
  have h1 : Tendsto (fun n => t ^ (θ n)⁻¹) l (𝓝 1) := by
    have := ((Real.continuousAt_const_rpow ht₀.ne').tendsto).comp h0
    simpa [Function.comp_def, Real.rpow_zero] using this
  simpa using ENNReal.tendsto_ofReal h1

/-- **Consistency.** Along any family of exponents `θ n j → ∞` (growing effect or sample size),
the power of the test rejecting when `p j ≤ t` tends to `1`, for every level `t ∈ (0, 1]`. -/
theorem tendsto_measure_lehmannPValue_le {ι : Type*} {l : Filter ι} {μ : Measure Ω}
    {U : Fin k → Ω → ℝ} {c : Fin m → Fin k} {θ : ι → Fin m → ℝ} {j : Fin m}
    (hU : HasLaw (U (c j)) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ)
    (hθ : Tendsto (fun n => θ n j) l atTop) {t : ℝ} (ht₀ : 0 < t) (ht₁ : t ≤ 1) :
    Tendsto (fun n => μ {ω | lehmannPValue U c (θ n) j ω ≤ t}) l (𝓝 1) := by
  refine (tendsto_ofReal_rpow_inv hθ ht₀).congr' ?_
  filter_upwards [hθ.eventually_gt_atTop 0] with n hn
  exact (measure_lehmannPValue_le hU hn ht₀.le ht₁).symm

/-! ### Power of Bonferroni, Holm and BH on the Lehmann family -/

/-- **Bonferroni power, exactly.** The probability that Bonferroni at level `α ∈ [0, 1]` rejects
endpoint `j` is `(α / m) ^ (1 / θ j)`. -/
theorem measure_mem_bonferroniRejections_lehmannPValue {μ : Measure Ω} {U : Fin k → Ω → ℝ}
    {c : Fin m → Fin k} {θ : Fin m → ℝ} {j : Fin m}
    (hU : HasLaw (U (c j)) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ) (hθ : 0 < θ j) {α : ℝ}
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    μ {ω | j ∈ bonferroniRejections α fun i => lehmannPValue U c θ i ω} =
      ENNReal.ofReal ((α / m) ^ (θ j)⁻¹) := by
  have hm : (1 : ℝ) ≤ m := Nat.one_le_cast.2 j.pos
  have h₁ : α / m ≤ 1 := (div_le_one (by linarith)).2 (hα₁.trans hm)
  simp only [bonferroniRejections, Finset.mem_filter, Finset.mem_univ, true_and]
  exact measure_lehmannPValue_le hU hθ (div_nonneg hα₀ (by linarith)) h₁

/-- **Holm power, lower bound.** Holm at level `α ∈ [0, 1]` rejects endpoint `j` with probability
at least `(α / m) ^ (1 / θ j)`, the Bonferroni power. -/
theorem ofReal_le_measure_mem_holmRejections_lehmannPValue {μ : Measure Ω}
    {U : Fin k → Ω → ℝ} {c : Fin m → Fin k} {θ : Fin m → ℝ} {j : Fin m}
    (hU : HasLaw (U (c j)) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ) (hθ : 0 < θ j) {α : ℝ}
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    ENNReal.ofReal ((α / m) ^ (θ j)⁻¹) ≤
      μ {ω | j ∈ holmRejections α fun i => lehmannPValue U c θ i ω} := by
  rw [← measure_mem_bonferroniRejections_lehmannPValue hU hθ hα₀ hα₁]
  exact measure_mono fun ω hω => bonferroniRejections_subset_holmRejections hα₀ _ hω

/-- **BH power, lower bound.** BH at level `q ∈ [0, 1]` rejects endpoint `j` with probability at
least `(q / m) ^ (1 / θ j)`, the Bonferroni power. -/
theorem ofReal_le_measure_mem_bhRejections_lehmannPValue {μ : Measure Ω}
    {U : Fin k → Ω → ℝ} {c : Fin m → Fin k} {θ : Fin m → ℝ} {j : Fin m}
    (hU : HasLaw (U (c j)) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ) (hθ : 0 < θ j) {q : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ENNReal.ofReal ((q / m) ^ (θ j)⁻¹) ≤
      μ {ω | j ∈ bhRejections q fun i => lehmannPValue U c θ i ω} := by
  rw [← measure_mem_bonferroniRejections_lehmannPValue hU hθ hq₀ hq₁]
  exact measure_mono fun ω hω => bonferroniRejections_subset_bhRejections hq₀ _ hω

/-- **BH consistency.** For a probability measure, along exponents `θ n j → ∞` the probability
that BH at level `q ∈ (0, 1]` rejects endpoint `j` tends to `1`. -/
theorem tendsto_measure_mem_bhRejections_lehmannPValue {ι : Type*} {l : Filter ι}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U : Fin k → Ω → ℝ} {c : Fin m → Fin k}
    {θ : ι → Fin m → ℝ} {j : Fin m}
    (hU : HasLaw (U (c j)) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ)
    (hθ : Tendsto (fun n => θ n j) l atTop) {q : ℝ} (hq₀ : 0 < q) (hq₁ : q ≤ 1) :
    Tendsto (fun n => μ {ω | j ∈ bhRejections q fun i => lehmannPValue U c (θ n) i ω}) l
      (𝓝 1) := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.2 j.pos
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_ofReal_rpow_inv hθ
    (div_pos hq₀ hm)) tendsto_const_nhds ?_ (Eventually.of_forall fun _ => prob_le_one)
  filter_upwards [hθ.eventually_gt_atTop 0] with n hn
  exact ofReal_le_measure_mem_bhRejections_lehmannPValue hU hn hq₀.le hq₁

/-- **Holm consistency.** For a probability measure, along exponents `θ n j → ∞` the probability
that Holm at level `α ∈ (0, 1]` rejects endpoint `j` tends to `1`. -/
theorem tendsto_measure_mem_holmRejections_lehmannPValue {ι : Type*} {l : Filter ι}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U : Fin k → Ω → ℝ} {c : Fin m → Fin k}
    {θ : ι → Fin m → ℝ} {j : Fin m}
    (hU : HasLaw (U (c j)) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ)
    (hθ : Tendsto (fun n => θ n j) l atTop) {α : ℝ} (hα₀ : 0 < α) (hα₁ : α ≤ 1) :
    Tendsto (fun n => μ {ω | j ∈ holmRejections α fun i => lehmannPValue U c (θ n) i ω}) l
      (𝓝 1) := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.2 j.pos
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_ofReal_rpow_inv hθ
    (div_pos hα₀ hm)) tendsto_const_nhds ?_ (Eventually.of_forall fun _ => prob_le_one)
  filter_upwards [hθ.eventually_gt_atTop 0] with n hn
  exact ofReal_le_measure_mem_holmRejections_lehmannPValue hU hn hα₀.le hα₁

/-! ### The Lehmann family for zero-ATE endpoints -/

/-- The **ATE Lehmann exponents** with scales `κ`: endpoint `j` gets
`θ j = exp (κ j * ipwContrast μ T X (Y j))`. The scale `κ j > 0` plays the role of
`√n / σ j` in a Wald statistic; the exponent is `1` exactly when the observed IPW contrast
vanishes, and exceeds `1` when it is positive. It depends on the observed-data law only. -/
noncomputable def ateLehmannExponent (μ : Measure Ω) (T : Set Ω) (X : Ω → 𝒳)
    (Y : Fin m → Ω → ℝ) (κ : Fin m → ℝ) : Fin m → ℝ :=
  fun j => Real.exp (κ j * ipwContrast μ T X (Y j))

/-- The **ATE Lehmann p-values**: the clustered Lehmann p-values (`lehmannPValue`) with null
noise `U`, clusters `c` and the ATE Lehmann exponents. Endpoint `j` reports
`max (U (c j)) 0 ^ exp (κ j * ipwContrast μ T X (Y j))`: the null p-value of its cluster when
the observed IPW contrast vanishes, a stochastically smaller one when it is positive (a
one-sided test against a positive effect), and a larger one when it is negative. -/
noncomputable def ateLehmannPValue (μ : Measure Ω) (T : Set Ω) (X : Ω → 𝒳)
    (Y : Fin m → Ω → ℝ) (κ : Fin m → ℝ) (U : Fin k → Ω → ℝ) (c : Fin m → Fin k) :
    Fin m → Ω → ℝ :=
  lehmannPValue U c (ateLehmannExponent μ T X Y κ)

section ATE

variable {μ : Measure Ω} {T : Set Ω} {X : Ω → 𝒳} {Y : Fin m → Ω → ℝ} {κ : Fin m → ℝ}
  {U : Fin k → Ω → ℝ}

/-- The ATE Lehmann exponents are positive. -/
theorem ateLehmannExponent_pos (j : Fin m) : 0 < ateLehmannExponent μ T X Y κ j :=
  Real.exp_pos _

/-- **Calibration for the observed-data IPW null.** If every cluster noise is uniform on
`[0, 1]`, the ATE Lehmann p-values are calibrated for the observed-data IPW null: on an
endpoint with `IsIPWNull`, the exponent is `1` and the p-value is the null noise. -/
theorem isIPWNullCalibrated_ateLehmannPValue
    (hU : ∀ b, HasLaw (U b) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ) (c : Fin m → Fin k) :
    IsIPWNullCalibrated μ T X Y (ateLehmannPValue μ T X Y κ U c) := fun j hj =>
  isValidPValue_lehmannPValue_of_eq_one (hU (c j)) (by simp [ateLehmannExponent, hj.2])

/-- **The ATE Lehmann p-values are PRDS on every set of endpoints**, in particular on the causal
nulls `ateNulls μ Y₀ Y₁`, when the cluster noises are measurable and independent. -/
theorem isPRDSOn_ateLehmannPValue [IsProbabilityMeasure μ] (hUm : ∀ b, Measurable (U b))
    (hind : iIndepFun U μ) (c : Fin m → Fin k) (H0 : Finset (Fin m)) :
    IsPRDSOn μ (ateLehmannPValue μ T X Y κ U c) H0 :=
  isPRDSOn_lehmannPValue hUm hind c ateLehmannExponent_pos H0

/-- **Power of one ATE Lehmann test.** With a uniform noise for the cluster of `j`, the test
rejecting when `p j ≤ t` has power `t ^ exp (-(κ j * ipwContrast μ T X (Y j)))`, for
`t ∈ [0, 1]`. -/
theorem measure_ateLehmannPValue_le {c : Fin m → Fin k} {j : Fin m}
    (hU : HasLaw (U (c j)) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ) {t : ℝ} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) :
    μ {ω | ateLehmannPValue μ T X Y κ U c j ω ≤ t} =
      ENNReal.ofReal (t ^ Real.exp (-(κ j * ipwContrast μ T X (Y j)))) := by
  rw [ateLehmannPValue, measure_lehmannPValue_le hU (ateLehmannExponent_pos j) ht₀ ht₁,
    ateLehmannExponent, ← Real.exp_neg]

/-- **Consistency of BH on the ATE Lehmann family.** If `κ j > 0` and the observed IPW contrast of
`j` is positive, then as the common scale `s → ∞` (e.g. `κ = √n · (1 / σ)`), the probability that
BH at level `q ∈ (0, 1]` rejects `j` tends to `1`. -/
theorem tendsto_measure_mem_bhRejections_ateLehmannPValue [IsProbabilityMeasure μ]
    {c : Fin m → Fin k} {j : Fin m}
    (hU : HasLaw (U (c j)) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ) (hκ : 0 < κ j)
    (hpos : 0 < ipwContrast μ T X (Y j)) {q : ℝ} (hq₀ : 0 < q) (hq₁ : q ≤ 1) :
    Tendsto (fun s : ℝ => μ {ω | j ∈ bhRejections q fun i =>
      ateLehmannPValue μ T X Y (s • κ) U c i ω}) atTop (𝓝 1) := by
  refine tendsto_measure_mem_bhRejections_lehmannPValue (θ := fun s => ateLehmannExponent μ T X Y
    (s • κ)) hU ?_ hq₀ hq₁
  have h : Tendsto (fun s : ℝ => s * (κ j * ipwContrast μ T X (Y j))) atTop atTop :=
    tendsto_id.atTop_mul_const (mul_pos hκ hpos)
  refine (Real.tendsto_exp_atTop.comp h).congr fun s => ?_
  simp [ateLehmannExponent, mul_assoc]

section Identification

variable [Finite 𝒳] [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] [IsProbabilityMeasure μ]

/-- **Power in terms of the average treatment effect.** If endpoint `j` is strongly ignorable
given `X` (with measurable, integrable potential outcomes), the power of its ATE Lehmann test at
level `t ∈ [0, 1]` is `t ^ exp (-(κ j * E[Y₁ j - Y₀ j]))`: identification
(`ipwContrast_observed_eq_integral`) turns the observed contrast into the ATE. -/
theorem measure_ateLehmannPValue_observed_le (hT : MeasurableSet T) (hX : Measurable X)
    {Y₀ Y₁ : Fin m → Ω → ℝ} {c : Fin m → Fin k} {j : Fin m} (hY₀ : Measurable (Y₀ j))
    (hY₁ : Measurable (Y₁ j)) (hY₀i : Integrable (Y₀ j) μ) (hY₁i : Integrable (Y₁ j) μ)
    (hign : StronglyIgnorable μ T (fun ω => (Y₀ j ω, Y₁ j ω)) X)
    (hU : HasLaw (U (c j)) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ) {t : ℝ} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) :
    μ {ω | ateLehmannPValue μ T X (fun i => observed T (Y₀ i) (Y₁ i)) κ U c j ω ≤ t} =
      ENNReal.ofReal (t ^ Real.exp (-(κ j * ∫ ω, (Y₁ j ω - Y₀ j ω) ∂μ))) := by
  rw [measure_ateLehmannPValue_le hU ht₀ ht₁,
    ipwContrast_observed_eq_integral hT hX hY₀ hY₁ hY₀i hY₁i hign]

/-- **BH power in terms of the average treatment effect.** If endpoint `j` is strongly ignorable
given `X`, BH at level `q ∈ [0, 1]` on the ATE Lehmann p-values rejects `j` with probability at
least `(q / m) ^ exp (-(κ j * E[Y₁ j - Y₀ j]))`. For a positive effect and `κ j > 0` this is at
least the per-endpoint Bonferroni level `q / m`, strictly larger exactly when `0 < q / m < 1`. -/
theorem ofReal_le_measure_mem_bhRejections_ateLehmannPValue_observed (hT : MeasurableSet T)
    (hX : Measurable X) {Y₀ Y₁ : Fin m → Ω → ℝ} {c : Fin m → Fin k} {j : Fin m}
    (hY₀ : Measurable (Y₀ j)) (hY₁ : Measurable (Y₁ j)) (hY₀i : Integrable (Y₀ j) μ)
    (hY₁i : Integrable (Y₁ j) μ) (hign : StronglyIgnorable μ T (fun ω => (Y₀ j ω, Y₁ j ω)) X)
    (hU : HasLaw (U (c j)) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ) {q : ℝ} (hq₀ : 0 ≤ q)
    (hq₁ : q ≤ 1) :
    ENNReal.ofReal ((q / m) ^ Real.exp (-(κ j * ∫ ω, (Y₁ j ω - Y₀ j ω) ∂μ))) ≤
      μ {ω | j ∈ bhRejections q fun i =>
        ateLehmannPValue μ T X (fun i => observed T (Y₀ i) (Y₁ i)) κ U c i ω} := by
  have h := ofReal_le_measure_mem_bhRejections_lehmannPValue hU (ateLehmannExponent_pos
    (μ := μ) (T := T) (X := X) (Y := fun i => observed T (Y₀ i) (Y₁ i)) (κ := κ) j) hq₀ hq₁
  rwa [ateLehmannExponent, ← Real.exp_neg,
    ipwContrast_observed_eq_integral hT hX hY₀ hY₁ hY₀i hY₁i hign] at h

/-- **FDR control by BH on the explicit ATE Lehmann family.** Under strong ignorability given `X`
of every endpoint with zero average treatment effect, with independent, measurable cluster
noises uniform on `[0, 1]`, BH at level `q ∈ [0, 1]` applied to the ATE Lehmann p-values has FDR
over the causal nulls at most `q |ateNulls| / m`. Every p-value hypothesis of
`integral_falseDiscoveryProportion_bhRejections_ateNulls_le_of_isPRDSOn` (measurability, PRDS on
the causal nulls, observed-null calibration) is discharged by the construction; the p-values
within a cluster are dependent. -/
theorem integral_falseDiscoveryProportion_bhRejections_ateNulls_ateLehmannPValue_le
    (hT : MeasurableSet T) (hX : Measurable X) {Y₀ Y₁ : Fin m → Ω → ℝ}
    (hY₀ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₀ j))
    (hY₁ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₁ j))
    (hY₀i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₀ j) μ)
    (hY₁i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₁ j) μ)
    (hign : ∀ j ∈ ateNulls μ Y₀ Y₁, StronglyIgnorable μ T (fun ω => (Y₀ j ω, Y₁ j ω)) X)
    (hU : ∀ b, HasLaw (U b) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ)
    (hUm : ∀ b, Measurable (U b)) (hind : iIndepFun U μ) (c : Fin m → Fin k) (q : ℝ)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion (ateNulls μ Y₀ Y₁) (bhRejections q fun i =>
        ateLehmannPValue μ T X (fun i => observed T (Y₀ i) (Y₁ i)) κ U c i ω) ∂μ ≤
      q * (ateNulls μ Y₀ Y₁).card / m :=
  integral_falseDiscoveryProportion_bhRejections_ateNulls_le_of_isPRDSOn hT hX hY₀ hY₁ hY₀i hY₁i
    hign (measurable_lehmannPValue hUm c _) (isPRDSOn_ateLehmannPValue hUm hind c _)
    (isIPWNullCalibrated_ateLehmannPValue hU c) q hq₀ hq₁

/-- **FWER control by Holm on the explicit ATE Lehmann family.** Under strong ignorability given
`X` of every endpoint with zero average treatment effect, with cluster noises uniform on
`[0, 1]` (no independence needed), Holm at level `α ∈ [0, 1]` applied to the ATE Lehmann p-values
rejects some causal null with probability at most `α`. -/
theorem measure_holm_ateNulls_familywiseError_ateLehmannPValue_le (hT : MeasurableSet T)
    (hX : Measurable X) {Y₀ Y₁ : Fin m → Ω → ℝ}
    (hY₀ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₀ j))
    (hY₁ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₁ j))
    (hY₀i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₀ j) μ)
    (hY₁i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₁ j) μ)
    (hign : ∀ j ∈ ateNulls μ Y₀ Y₁, StronglyIgnorable μ T (fun ω => (Y₀ j ω, Y₁ j ω)) X)
    (hU : ∀ b, HasLaw (U b) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ) (c : Fin m → Fin k)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    μ {ω | (holmRejections α (fun i =>
        ateLehmannPValue μ T X (fun i => observed T (Y₀ i) (Y₁ i)) κ U c i ω) ∩
          ateNulls μ Y₀ Y₁).Nonempty} ≤ ENNReal.ofReal α :=
  measure_holm_ateNulls_familywiseError_le hT hX hY₀ hY₁ hY₀i hY₁i hign
    (isIPWNullCalibrated_ateLehmannPValue hU c) hα₀ hα₁

end Identification

end ATE

end MathlibExt.Probability.Statistics.MultipleTesting
