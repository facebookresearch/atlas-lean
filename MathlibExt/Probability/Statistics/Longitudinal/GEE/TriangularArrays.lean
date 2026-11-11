/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.StrongLaw
public import MathlibExt.Probability.LindebergFeller

/-!
# Cluster estimating equations: iid clusters versus triangular arrays

Asymptotics of a cluster estimating equation `Ψₙ(β) = ∑_{i<n} ψ_{n,i}(β)` come in two regimes,
with different hypotheses and different normalizations.

## (a) iid clusters

Cluster `i` contributes a score `S i` and all clusters share one law. Then the cluster size
law is fixed too (identically distributed clusters cannot grow), and the classical
`√n`-theory applies with the fixed variance `Var[S 0]`. For the linear cluster estimating
equation `Ψₙ(β) = ∑_{i<n} (S i - m β)` with common cluster size `m ≠ 0`:

* `linearEE_eq_zero_iff`: its unique root is `β̂ₙ = (∑_{i<n} S i) / (n m)`;
* `linearEERoot_tendsto_ae` (consistency, strong law): `β̂ₙ → 𝔼[S 0] / m` almost surely;
* `linearEERoot_clt` (CLT, normalization `√n`): `√n (β̂ₙ - 𝔼[S 0] / m) ⇒ Y / m` with
  `Y ~ N(0, Var[S 0])`.

## (b) Nonidentically distributed triangular arrays

Cluster `i` of row `n` has score `U n i` (law `P_{n,i}`, allowed to vary with `n`) and size
`m n i`; the number of clusters in row `n` is `n`. The normalization is not `√n` but the row
standard deviation `Bₙ = √(∑_{i<n} 𝔼[U n i²])` (`rowVariance`), and the hypothesis is the
Lindeberg condition of `MathlibExt.Probability.LindebergFeller` instead of identical laws.

**Allowed growth of cluster sizes.** Suppose each within-cluster residual is bounded by `K`,
so `|U n i| ≤ K · m n i` with arbitrary within-cluster dependence (`abs_clusterScore_le`).
Write `Mₙ = maxᵢ m n i` (`maxClusterSize`) and `Nₙ = ∑ᵢ m n i` (`totalSize`).

* `lindeberg_of_bounded_cluster_growth`: if `K · Mₙ / Bₙ → 0` then the Lindeberg condition
  holds for `U n i / Bₙ`. **This is where cluster growth enters the proof**: once
  `K Mₙ / Bₙ < ε`, every normalized cluster score is below `ε`, so every truncated second
  moment in the Lindeberg sum vanishes.
* `triangular_cluster_clt`: under `K · Mₙ / Bₙ → 0`, `∑ᵢ U n i / Bₙ ⇒ N(0, 1)`.
* `triangular_cluster_clt_of_growth`: if each cluster carries at least `c > 0` units of
  variance per observation (`c · m n i ≤ 𝔼[U n i²]`), the explicit growth condition is
  `ClusterGrowth m`: `Mₙ² / Nₙ → 0`, i.e. **the largest cluster is `o(√Nₙ)`**.
* `clusterGrowth_balanced`: for balanced clusters of size `sₙ` the condition reads
  `sₙ / n → 0`; cluster sizes may grow, but slower than the number of clusters.
  `clusterGrowth_const` recovers the fixed-size (iid-compatible) case.

## Boundary cases

* **Growing dominant cluster.** `lindeberg_tendsto_zero_of_mem` shows Lindeberg forces every
  single normalized cluster variance to `0`, so `not_lindeberg_of_dominant_cluster`: a cluster
  holding a fixed share `δ > 0` of the row variance breaks Lindeberg. With sizes
  `dominantSizes` (cluster `0` has size `n`, the others size `1`) and variance proportional to
  size, cluster `0` keeps at least half the variance (`not_lindeberg_dominantSizes`) and the
  growth condition fails (`not_clusterGrowth_dominantSizes`).
* **No estimating-equation root.** For the binary-response (logistic-mean) cluster estimating
  function `binaryEE`, if every observation is a success the function is strictly positive,
  so it has no zero (`binaryEE_no_root`) and no root-defined estimator exists.

## Source

Reuse search (API-00 gate, base `53666a3c1`): the Lindeberg condition and the triangular CLT are
`ProbabilityTheory.LindebergConditionTriangular` and
`ProbabilityTheory.lindeberg_feller_clt_triangular` in `MathlibExt.Probability.LindebergFeller`;
the iid CLT is Mathlib's `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`
(`Mathlib.Probability.CentralLimitTheorem`) and the strong law is
`ProbabilityTheory.strong_law_ae` (`Mathlib.Probability.StrongLaw`). No cluster-size,
estimating-equation or GEE asymptotics existed in Mathlib or the repository.
Mathematical reference: K.-Y. Liang and S. L. Zeger, *Longitudinal data analysis using
generalized linear models*, Biometrika 73 (1986) 13–22 (iid-cluster regime); P. Billingsley,
*Probability and Measure*, 3rd ed., Theorem 27.2 (Lindeberg–Feller) and its bounded-summand
corollary; the `o(√N)` largest-cluster condition is the standard Lindeberg sufficient condition
for sums of bounded cluster totals (cf. Xie and Yang, *Asymptotics for generalized estimating
equations with large cluster sizes*, Ann. Statist. 31 (2003) 310–347).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology BoundedContinuousFunction NNReal

namespace ProbabilityTheory.GEE.Triangular

variable {Ω : Type*}

/-! ### Cluster sizes and the growth condition -/

/-- Size of the largest cluster in row `n`: `Mₙ = max_{i<n} m n i`. -/
def maxClusterSize (m : ℕ → ℕ → ℕ) (n : ℕ) : ℕ := (range n).sup (m n)

/-- Total number of observations in row `n`: `Nₙ = ∑_{i<n} m n i`. -/
def totalSize (m : ℕ → ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ range n, m n i

lemma le_maxClusterSize {m : ℕ → ℕ → ℕ} {n i : ℕ} (hi : i ∈ range n) :
    m n i ≤ maxClusterSize m n :=
  Finset.le_sup hi

/-- **Allowed growth of cluster sizes**: the largest cluster is `o(√Nₙ)`, stated as
`Mₙ² / Nₙ → 0`. -/
def ClusterGrowth (m : ℕ → ℕ → ℕ) : Prop :=
  Tendsto (fun n => (maxClusterSize m n : ℝ) ^ 2 / totalSize m n) atTop (𝓝 0)

/-- Balanced clusters of size `sₙ` satisfy the growth condition iff `sₙ / n → 0`; here the
sufficient direction: cluster sizes may grow, as long as they grow slower than the number of
clusters. -/
theorem clusterGrowth_balanced (s : ℕ → ℕ) (hs : ∀ n, 0 < s n)
    (h : Tendsto (fun n => (s n : ℝ) / n) atTop (𝓝 0)) :
    ClusterGrowth (fun n _ => s n) := by
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hne : (range n).Nonempty := nonempty_range_iff.2 (by omega)
  have hM : maxClusterSize (fun n _ => s n) n = s n := Finset.sup_const hne _
  have hN : totalSize (fun n _ => s n) n = n * s n := by simp [totalSize]
  have hs0 : (s n : ℝ) ≠ 0 := by have := hs n; positivity
  rw [hM, hN]
  push_cast
  field_simp

/-- Fixed cluster size (the only option for iid clusters) satisfies the growth condition. -/
theorem clusterGrowth_const (s : ℕ) (hs : 0 < s) : ClusterGrowth (fun _ _ => s) := by
  refine clusterGrowth_balanced (fun _ => s) (fun _ => hs) ?_
  simpa [div_eq_mul_inv] using
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (s : ℝ)

/-- One growing dominant cluster: cluster `0` of row `n` has size `n`, all others size `1`. -/
def dominantSizes (n i : ℕ) : ℕ := if i = 0 then n else 1

lemma totalSize_dominantSizes (k : ℕ) : totalSize dominantSizes (k + 1) = 2 * k + 1 := by
  simp only [totalSize, dominantSizes]
  rw [sum_range_succ']
  simp
  ring

lemma maxClusterSize_dominantSizes (k : ℕ) : maxClusterSize dominantSizes (k + 1) = k + 1 := by
  apply le_antisymm
  · refine Finset.sup_le fun i _ => ?_
    simp only [dominantSizes]
    split_ifs <;> omega
  · simpa [dominantSizes] using
      le_maxClusterSize (m := dominantSizes) (n := k + 1) (i := 0) (by simp)

/-- The dominant cluster violates the growth condition: `Mₙ² / Nₙ ≥ n / 2 → ∞`. -/
theorem not_clusterGrowth_dominantSizes : ¬ ClusterGrowth dominantSizes := by
  intro h
  obtain ⟨n, hlt, hn⟩ := ((h.eventually (gt_mem_nhds one_pos)).and
    (eventually_ge_atTop 2)).exists
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [maxClusterSize_dominantSizes, totalSize_dominantSizes] at hlt
  have hpos : (0 : ℝ) < 2 * k + 1 := by positivity
  push_cast at hlt
  rw [div_lt_one hpos] at hlt
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  nlinarith

/-! ### Cluster scores from bounded within-cluster residuals -/

/-- Cluster score as the sum of the within-cluster residuals `ε n i j`, `j < m n i`. -/
def clusterScore (ε : ℕ → ℕ → ℕ → Ω → ℝ) (m : ℕ → ℕ → ℕ) (n i : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ range (m n i), ε n i j ω

/-- Bounded residuals give a cluster score bounded by `K` times the cluster size, whatever the
within-cluster dependence. -/
lemma abs_clusterScore_le {ε : ℕ → ℕ → ℕ → Ω → ℝ} {m : ℕ → ℕ → ℕ} {K : ℝ} {n i : ℕ}
    (hK : ∀ j < m n i, ∀ ω, |ε n i j ω| ≤ K) (ω : Ω) :
    |clusterScore ε m n i ω| ≤ K * m n i := by
  calc |clusterScore ε m n i ω| ≤ ∑ j ∈ range (m n i), |ε n i j ω| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range (m n i), K := sum_le_sum fun j hj => hK j (mem_range.1 hj) ω
    _ = K * m n i := by rw [sum_const, card_range, nsmul_eq_mul, mul_comm]

variable [MeasurableSpace Ω]

/-! ### (a) The iid-cluster regime -/

section IID

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- Linear cluster estimating function with common cluster size `m`:
`Ψₙ(β) = ∑_{i<n} (S i - m β)`. -/
def linearEE (S : ℕ → Ω → ℝ) (m : ℝ) (n : ℕ) (β : ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ range n, (S i ω - m * β)

/-- The root of the linear cluster estimating equation, `β̂ₙ = (∑_{i<n} S i) / (n m)`. -/
noncomputable def linearEERoot (S : ℕ → Ω → ℝ) (m : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ range n, S i ω) / (n * m)

omit [MeasurableSpace Ω] in
/-- `β̂ₙ` is the unique root of `Ψₙ` once there is at least one cluster and `m ≠ 0`. -/
theorem linearEE_eq_zero_iff {S : ℕ → Ω → ℝ} {m β : ℝ} {n : ℕ} {ω : Ω}
    (hm : m ≠ 0) (hn : 0 < n) :
    linearEE S m n β ω = 0 ↔ β = linearEERoot S m n ω := by
  have hnm : (n : ℝ) * m ≠ 0 := mul_ne_zero (by exact_mod_cast hn.ne') hm
  rw [linearEE, linearEERoot, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul,
    eq_div_iff hnm]
  constructor <;> intro h <;> linarith

/-- **iid regime, consistency**: for iid integrable cluster scores the root of the linear
cluster estimating equation converges almost surely to `𝔼[S 0] / m`. -/
theorem linearEERoot_tendsto_ae {μ : Measure Ω} {S : ℕ → Ω → ℝ} {m : ℝ}
    (hint : Integrable (S 0) μ) (hindep : iIndepFun S μ)
    (hident : ∀ i, IdentDistrib (S i) (S 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => linearEERoot S m n ω) atTop (𝓝 (μ[S 0] / m)) := by
  filter_upwards [strong_law_ae S hint (fun i j hij => hindep.indepFun hij) hident] with ω hω
  refine (hω.div_const m).congr fun n => ?_
  simp only [linearEERoot, smul_eq_mul]
  ring

/-- **iid regime, CLT** (normalization `√n`, fixed limit variance): for iid square-integrable
cluster scores, `√n (β̂ₙ - 𝔼[S 0] / m)` converges in distribution to `Y / m` where
`Y ~ N(0, Var[S 0])`. -/
theorem linearEERoot_clt {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {S : ℕ → Ω → ℝ} {Y : Ω' → ℝ} {m : ℝ} (hm : m ≠ 0)
    (hY : HasLaw Y (gaussianReal 0 Var[S 0; μ].toNNReal) μ')
    (hS : MemLp (S 0) 2 μ) (hindep : iIndepFun S μ)
    (hident : ∀ i, IdentDistrib (S i) (S 0) μ μ) :
    TendstoInDistribution (fun (n : ℕ) ω => √n * (linearEERoot S m n ω - μ[S 0] / m)) atTop
      (fun ω' => Y ω' / m) (fun _ => μ) μ' := by
  have h := (tendstoInDistribution_inv_sqrt_mul_sum_sub hY hS hindep hident).continuous_comp
    (g := fun x => x / m) (by fun_prop)
  convert h using 1
  swap; · rfl
  funext n ω
  simp only [Function.comp_apply, linearEERoot]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  generalize hs : √(n : ℝ) = s
  have hs0 : 0 < s := hs ▸ Real.sqrt_pos.2 hn'
  have hns : (n : ℝ) = s * s := by rw [← hs, Real.mul_self_sqrt hn'.le]
  rw [hns]
  field_simp

end IID

/-! ### (b) The triangular-array regime -/

/-- Row variance `Bₙ² = ∑_{i<n} 𝔼[U n i²]` of a triangular array of mean-zero cluster scores. -/
noncomputable def rowVariance (U : ℕ → ℕ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, ∫ ω, (U n i ω) ^ 2 ∂μ

/-- **Where cluster growth enters.** If `|U n i| ≤ K · m n i` and the largest cluster is small
against the normalization, `K · Mₙ / Bₙ → 0`, then the normalized array `U n i / Bₙ` satisfies
the Lindeberg condition: eventually every normalized cluster score is below any fixed `ε`, so
every truncated second moment vanishes. -/
theorem lindeberg_of_bounded_cluster_growth (μ : Measure Ω) (U : ℕ → ℕ → Ω → ℝ)
    (m : ℕ → ℕ → ℕ) {K : ℝ} (hK : 0 ≤ K) (B : ℕ → ℝ) (hB : ∀ᶠ n in atTop, 0 < B n)
    (hbound : ∀ n, ∀ i ∈ range n, ∀ ω, |U n i ω| ≤ K * m n i)
    (hgrowth : Tendsto (fun n => K * maxClusterSize m n / B n) atTop (𝓝 0)) :
    LindebergConditionTriangular (fun n i ω => U n i ω / B n) μ := by
  intro ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hgrowth.eventually (gt_mem_nhds hε), hB] with n hn hBn
  symm
  refine sum_eq_zero fun i hi => ?_
  have hzero : ∀ ω, Set.indicator {ω' | ε < |U n i ω' / B n|} (1 : Ω → ℝ) ω = 0 := by
    intro ω
    refine Set.indicator_of_notMem (fun hmem => ?_) _
    change ε < |U n i ω / B n| at hmem
    refine (not_lt.2 ?_) hmem
    rw [abs_div, abs_of_pos hBn, div_le_iff₀ hBn]
    rw [div_lt_iff₀ hBn] at hn
    calc |U n i ω| ≤ K * m n i := hbound n i hi ω
      _ ≤ K * maxClusterSize m n := by gcongr; exact_mod_cast le_maxClusterSize hi
      _ ≤ ε * B n := hn.le
  simp [hzero]

/-- **Triangular-array regime, CLT.** Rows of independent, mean-zero, measurable cluster scores
with `|U n i| ≤ K · m n i`, normalized by the row standard deviation `Bₙ = √(rowVariance)`
(not by `√n`). If the largest cluster is negligible, `K · Mₙ / Bₙ → 0`, then
`∑_{i<n} U n i / Bₙ ⇒ N(0, 1)`. -/
theorem triangular_cluster_clt {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → ℕ → Ω → ℝ) (m : ℕ → ℕ → ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hind : ∀ n, iIndepFun ((range n).restrict (U n)) μ)
    (hmeas : ∀ n, ∀ i ∈ range n, Measurable (U n i))
    (hmean : ∀ n, ∀ i ∈ range n, ∫ ω, U n i ω ∂μ = 0)
    (hbound : ∀ n, ∀ i ∈ range n, ∀ ω, |U n i ω| ≤ K * m n i)
    (hpos : ∀ᶠ n in atTop, 0 < rowVariance U μ n)
    (hgrowth : Tendsto (fun n => K * maxClusterSize m n / √(rowVariance U μ n)) atTop (𝓝 0)) :
    ∀ f : ℝ →ᵇ ℝ,
      Tendsto (fun n => ∫ x, f x ∂(μ.map
          (fun ω => ∑ i ∈ range n, U n i ω / √(rowVariance U μ n))))
        atTop (𝓝 (∫ x, f x ∂(gaussianReal 0 1))) := by
  set B : ℕ → ℝ := fun n => √(rowVariance U μ n) with hBdef
  have hU2 : ∀ n, ∀ i ∈ range n, Integrable (fun ω => (U n i ω) ^ 2) μ := by
    intro n i hi
    refine Integrable.of_bound ((hmeas n i hi).pow_const 2).aestronglyMeasurable
      ((K * m n i) ^ 2) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hbound n i hi ω) 2
  have hint2 : ∀ n, ∀ i ∈ range n, Integrable (fun ω => (U n i ω / B n) ^ 2) μ := by
    intro n i hi
    simpa only [div_pow] using (hU2 n i hi).div_const (B n ^ 2)
  have hvar : Tendsto (fun n => ∑ i ∈ range n, ∫ ω, (U n i ω / B n) ^ 2 ∂μ) atTop
      (𝓝 ((1 : ℝ) ^ 2)) := by
    rw [one_pow]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hpos] with n hn
    simp only [div_pow, integral_div, ← sum_div, hBdef, Real.sq_sqrt hn.le]
    exact (div_self hn.ne').symm
  have hL : LindebergConditionTriangular (fun n i ω => U n i ω / B n) μ :=
    lindeberg_of_bounded_cluster_growth μ U m hK B
      (hpos.mono fun n hn => Real.sqrt_pos.2 hn) hbound hgrowth
  intro f
  have h := lindeberg_feller_clt_triangular (μ := μ) (fun n i ω => U n i ω / B n)
    (fun n => (hind n).comp (fun _ x => x / B n) (fun _ => measurable_id.div_const _))
    (fun n i hi => (hmeas n i hi).div_const _)
    (fun n i hi => by simp [integral_div, hmean n i hi])
    hint2 1 one_pos hvar hL f
  have e : (⟨(1 : ℝ) ^ 2, sq_nonneg 1⟩ : ℝ≥0) = 1 := by ext; simp
  rw [e] at h
  exact h

/-- **Triangular-array regime with the explicit growth condition.** If every observation
carries at least `c > 0` units of variance (`c · m n i ≤ 𝔼[U n i²]`, e.g. independent or
nonnegatively correlated residuals), clusters are nonempty and the largest cluster is
`o(√Nₙ)` (`ClusterGrowth m`), then `∑_{i<n} U n i / Bₙ ⇒ N(0, 1)`. -/
theorem triangular_cluster_clt_of_growth {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → ℕ → Ω → ℝ) (m : ℕ → ℕ → ℕ) {K c : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (hind : ∀ n, iIndepFun ((range n).restrict (U n)) μ)
    (hmeas : ∀ n, ∀ i ∈ range n, Measurable (U n i))
    (hmean : ∀ n, ∀ i ∈ range n, ∫ ω, U n i ω ∂μ = 0)
    (hbound : ∀ n, ∀ i ∈ range n, ∀ ω, |U n i ω| ≤ K * m n i)
    (hvarlb : ∀ n, ∀ i ∈ range n, c * m n i ≤ ∫ ω, (U n i ω) ^ 2 ∂μ)
    (hne : ∀ n, ∀ i ∈ range n, 0 < m n i)
    (hgrowth : ClusterGrowth m) :
    ∀ f : ℝ →ᵇ ℝ,
      Tendsto (fun n => ∫ x, f x ∂(μ.map
          (fun ω => ∑ i ∈ range n, U n i ω / √(rowVariance U μ n))))
        atTop (𝓝 (∫ x, f x ∂(gaussianReal 0 1))) := by
  have hVN : ∀ n, c * totalSize m n ≤ rowVariance U μ n := by
    intro n
    rw [totalSize, Nat.cast_sum, mul_sum]
    exact sum_le_sum fun i hi => hvarlb n i hi
  have hNpos : ∀ n, 1 ≤ n → (0 : ℝ) < totalSize m n := by
    intro n hn
    have h0 : 0 ∈ range n := mem_range.2 (by omega)
    have : m n 0 ≤ totalSize m n := single_le_sum (fun _ _ => Nat.zero_le _) h0
    exact_mod_cast (hne n 0 h0).trans_le this
  have hpos : ∀ᶠ n in atTop, 0 < rowVariance U μ n :=
    (eventually_ge_atTop 1).mono fun n hn => (mul_pos hc (hNpos n hn)).trans_le (hVN n)
  refine triangular_cluster_clt U m hK hind hmeas hmean hbound hpos ?_
  have hlim : Tendsto (fun n => K / √c *
      √((maxClusterSize m n : ℝ) ^ 2 / totalSize m n)) atTop (𝓝 0) := by
    simpa using (hgrowth.sqrt).const_mul (K / √c)
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hN := hNpos n hn
  have hsc : 0 < √c := Real.sqrt_pos.2 hc
  have hsN : 0 < √(totalSize m n : ℝ) := Real.sqrt_pos.2 hN
  have hM : (0 : ℝ) ≤ maxClusterSize m n := Nat.cast_nonneg _
  calc K * maxClusterSize m n / √(rowVariance U μ n)
      ≤ K * maxClusterSize m n / √(c * totalSize m n) := by
        exact div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 (mul_pos hc hN))
          (Real.sqrt_le_sqrt (hVN n))
    _ = K / √c * √((maxClusterSize m n : ℝ) ^ 2 / totalSize m n) := by
        rw [Real.sqrt_mul hc.le, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hM]
        field_simp

/-! ### Boundary case: a growing dominant cluster -/

/-- **Lindeberg forces negligibility of every single cluster**: under the Lindeberg condition,
the second moment of any one entry `X n (k n)` of the row tends to `0`. -/
theorem lindeberg_tendsto_zero_of_mem {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℝ) (hmeas : ∀ n, ∀ k ∈ range n, Measurable (X n k))
    (hint2 : ∀ n, ∀ k ∈ range n, Integrable (fun ω => (X n k ω) ^ 2) μ)
    (hL : LindebergConditionTriangular X μ) (k : ℕ → ℕ) (hk : ∀ᶠ n in atTop, k n ∈ range n) :
    Tendsto (fun n => ∫ ω, (X n (k n) ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n =>
    ha.trans_le (integral_nonneg fun ω => sq_nonneg _), fun b hb => ?_⟩
  set ε : ℝ := √(b / 2) with hεdef
  have hε : 0 < ε := Real.sqrt_pos.2 (by positivity)
  have hε2 : ε ^ 2 = b / 2 := Real.sq_sqrt (by positivity)
  filter_upwards [hk, (hL ε hε).eventually (gt_mem_nhds (half_pos hb))] with n hkn hLn
  set Y := X n (k n)
  have hS : MeasurableSet {ω | ε < |Y ω|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hmeas n (k n) hkn))
  have hind_eq : (fun ω => (Y ω) ^ 2 * Set.indicator {ω' | ε < |Y ω'|} (1 : Ω → ℝ) ω) =
      Set.indicator {ω' | ε < |Y ω'|} (fun ω => (Y ω) ^ 2) := by
    funext ω
    by_cases h : ω ∈ {ω' | ε < |Y ω'|} <;> simp [Set.indicator_of_mem, h]
  have hTint : Integrable
      (fun ω => (Y ω) ^ 2 * Set.indicator {ω' | ε < |Y ω'|} (1 : Ω → ℝ) ω) μ := by
    rw [hind_eq]; exact (hint2 n (k n) hkn).indicator hS
  have hpt : ∀ ω, (Y ω) ^ 2 ≤
      ε ^ 2 + (Y ω) ^ 2 * Set.indicator {ω' | ε < |Y ω'|} (1 : Ω → ℝ) ω := by
    intro ω
    by_cases h : ε < |Y ω|
    · simp [Set.indicator_of_mem, h, sq_nonneg]
    · have h' : |Y ω| ≤ ε := not_lt.1 h
      have : (Y ω) ^ 2 ≤ ε ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h' 2
      simp [h, this]
  have hsingle : ∫ ω, (Y ω) ^ 2 * Set.indicator {ω' | ε < |Y ω'|} (1 : Ω → ℝ) ω ∂μ ≤
      ∑ j ∈ range n, ∫ ω, (X n j ω) ^ 2 * Set.indicator {ω' | ε < |X n j ω'|} 1 ω ∂μ :=
    single_le_sum (f := fun j => ∫ ω, (X n j ω) ^ 2 *
        Set.indicator {ω' | ε < |X n j ω'|} (1 : Ω → ℝ) ω ∂μ)
      (fun j _ => integral_nonneg fun ω => mul_nonneg (sq_nonneg _)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) hkn
  calc ∫ ω, (Y ω) ^ 2 ∂μ
      ≤ ∫ ω, (ε ^ 2 + (Y ω) ^ 2 * Set.indicator {ω' | ε < |Y ω'|} (1 : Ω → ℝ) ω) ∂μ :=
        integral_mono (hint2 n (k n) hkn) ((integrable_const _).add hTint) hpt
    _ = ε ^ 2 + ∫ ω, (Y ω) ^ 2 * Set.indicator {ω' | ε < |Y ω'|} (1 : Ω → ℝ) ω ∂μ := by
        rw [integral_add (integrable_const _) hTint]; simp
    _ < b / 2 + b / 2 := by rw [hε2]; linarith
    _ = b := add_halves b

/-- **A dominant cluster breaks Lindeberg.** If some cluster `k n` keeps at least a fixed share
`δ > 0` of the normalized row variance, the Lindeberg condition fails. -/
theorem not_lindeberg_of_dominant_cluster {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℝ) (hmeas : ∀ n, ∀ k ∈ range n, Measurable (X n k))
    (hint2 : ∀ n, ∀ k ∈ range n, Integrable (fun ω => (X n k ω) ^ 2) μ)
    (k : ℕ → ℕ) (hk : ∀ᶠ n in atTop, k n ∈ range n) {δ : ℝ} (hδ : 0 < δ)
    (hdom : ∀ᶠ n in atTop, δ ≤ ∫ ω, (X n (k n) ω) ^ 2 ∂μ) :
    ¬ LindebergConditionTriangular X μ := by
  intro hL
  obtain ⟨n, hn1, hn2⟩ := ((lindeberg_tendsto_zero_of_mem X hmeas hint2 hL k hk).eventually
    (gt_mem_nhds hδ)).and hdom |>.exists
  linarith

/-- **Growing dominant cluster, cluster-size form.** With sizes `dominantSizes` (cluster `0`
of row `n` has size `n`, the rest size `1`) and cluster variance proportional to size,
`𝔼[U n i²] = c · m n i`, cluster `0` keeps at least half of the row variance, so the normalized
array `U n i / Bₙ` fails the Lindeberg condition. -/
theorem not_lindeberg_dominantSizes {μ : Measure Ω} [IsProbabilityMeasure μ]
    (U : ℕ → ℕ → Ω → ℝ) {c : ℝ} (hc : 0 < c)
    (hmeas : ∀ n, ∀ i ∈ range n, Measurable (U n i))
    (hint2 : ∀ n, ∀ i ∈ range n, Integrable (fun ω => (U n i ω) ^ 2) μ)
    (hvar : ∀ n, ∀ i ∈ range n, ∫ ω, (U n i ω) ^ 2 ∂μ = c * dominantSizes n i) :
    ¬ LindebergConditionTriangular (fun n i ω => U n i ω / √(rowVariance U μ n)) μ := by
  have hV : ∀ n, rowVariance U μ n = c * totalSize dominantSizes n := by
    intro n
    rw [rowVariance, totalSize, Nat.cast_sum, mul_sum]
    exact sum_congr rfl fun i hi => hvar n i hi
  refine not_lindeberg_of_dominant_cluster _ (fun n i hi => (hmeas n i hi).div_const _)
    (fun n i hi => by simpa only [div_pow] using (hint2 n i hi).div_const _) (fun _ => 0)
    ((eventually_ge_atTop 1).mono fun n hn => mem_range.2 (by omega))
    (by norm_num : (0 : ℝ) < 1 / 2) ((eventually_ge_atTop 1).mono fun n hn => ?_)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hVpos : 0 < rowVariance U μ (k + 1) := by
    rw [hV, totalSize_dominantSizes]; positivity
  simp only [div_pow, integral_div, Real.sq_sqrt hVpos.le]
  rw [hvar (k + 1) 0 (by simp), hV, totalSize_dominantSizes, le_div_iff₀ (by positivity)]
  simp only [dominantSizes, ↓reduceIte]
  push_cast
  nlinarith

/-! ### Boundary case: no estimating-equation root -/

/-- Logistic mean function `g(β) = e^β / (1 + e^β)`, with values in `(0, 1)`. -/
noncomputable def logisticMean (β : ℝ) : ℝ := Real.exp β / (1 + Real.exp β)

lemma logisticMean_lt_one (β : ℝ) : logisticMean β < 1 :=
  (div_lt_one (by positivity)).2 (lt_one_add _)

/-- Binary-response cluster estimating function: cluster `i` has `S i` successes out of `m i`
trials, `Ψₙ(β) = ∑_{i<n} (S i - m i · g(β))`. -/
noncomputable def binaryEE (S : ℕ → ℝ) (m : ℕ → ℕ) (n : ℕ) (β : ℝ) : ℝ :=
  ∑ i ∈ range n, (S i - m i * logisticMean β)

/-- **No root.** If every observation is a success (`S i = m i`) and some cluster is
nonempty, the binary cluster estimating function is strictly positive, so it has no zero and no
root-defined estimator exists. -/
theorem binaryEE_no_root {S : ℕ → ℝ} {m : ℕ → ℕ} {n : ℕ} (hall : ∀ i ∈ range n, S i = m i)
    (hne : ∃ i ∈ range n, 0 < m i) (β : ℝ) : binaryEE S m n β ≠ 0 := by
  refine (sum_pos' (fun i hi => ?_) ?_).ne'
  · rw [hall i hi]
    have := logisticMean_lt_one β
    have : (0 : ℝ) ≤ m i := Nat.cast_nonneg _
    nlinarith
  · obtain ⟨i, hi, hmi⟩ := hne
    refine ⟨i, hi, ?_⟩
    rw [hall i hi]
    have := logisticMean_lt_one β
    have : (0 : ℝ) < m i := by exact_mod_cast hmi
    nlinarith

end ProbabilityTheory.GEE.Triangular
