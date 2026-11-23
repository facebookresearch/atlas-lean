/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.StoreyBH
public import MathlibExt.Probability.Statistics.MultipleTesting.BenjaminiHochberg

/-!
# The Storey-BH procedure under PRDS

`MultipleTesting.Adaptive.StoreyBH` proves that Storey-BH at level `q`
(`storeyBHRejections q lam`) has false discovery rate at most `q` when every true-null p-value is
valid and independent of all the other p-values
(`integral_falseDiscoveryProportion_storeyBHRejections_le`). That file states that PRDS is not
enough for its proof and makes no claim under PRDS. This file supplies what does hold under PRDS.

Under the PRDS condition of `MultipleTesting.BenjaminiHochberg` (`IsPRDSOn`, Benjamini–Yekutieli
2001), with valid true-null p-values and a fixed `lam < 1`, Storey-BH at level `q` has

`E[FDP] ≤ q (1 - lam) |H0|`

(`integral_falseDiscoveryProportion_storeyBHRejections_le_of_isPRDSOn`). This is not `q`, and the
level-`q` guarantee of the independent case is false under PRDS: the test file has two identical
valid null p-values (perfect positive dependence, which is PRDS by `isPRDSOn_of_monotone_comp`)
on which Storey-BH with `q = 1/5`, `lam = 2/5` has `FDR = 6/25 > 1/5`. There
`q (1 - lam) |H0| = 6/25`, so the bound above is attained.

## Proof

* *Monotonicity* (`storeyBHIndex_antitone`): making p-values larger raises Storey's estimator
  `π̂₀(lam)` and lowers every threshold, so the number `K` of Storey-BH rejections is a
  nonincreasing function of the p-value vector. Hence each `{K ≤ j}` is an increasing set, which
  is what PRDS speaks about.
* *Pointwise comparison*: since `π̂₀(lam) ≥ 1 / ((1 - lam) m)`, the `K`-th threshold is at most
  `q (1 - lam) K`, so the contribution `1{i ∈ R} / |R|` of a true null `i` is at most
  `1{p i ≤ c K} / K` with `c = q (1 - lam)`.
* *PRDS dependency control* (`integral_indicator_le_of_isPRDSOn`): for a valid true null `i` of a
  PRDS vector and any measurable nonincreasing `κ ≤ m`, `E[1{p i ≤ c κ(P), κ(P) ≥ 1} / κ(P)] ≤ c`.
  This is the Benjamini–Yekutieli telescoping argument, for a general count `κ` in place of the
  leave-one-out BH index.

The `+ 1` in `π̂₀` is what bounds the adaptive factor `1 / π̂₀ ≤ (1 - lam) m`; the cap at `lam`
is not used. The estimator property `∑_{i ∈ H0} E[1 / π̂₀⁽ⁱ⁾] ≤ m` of the independent proof
(`sum_integral_inv_storeyPi0Plus1_update_le`) is what fails under positive dependence:
`π̂₀⁽ⁱ⁾` tends to be small exactly when `p i` is small.

## Main results

* `storeyPi0Plus1_mono`, `storeyPi0Plus1_pos`, `storeyThreshold_antitone`,
  `storeyBHIndex_antitone`, `measurable_storeyBHIndex`.
* `integral_indicator_le_of_isPRDSOn`: PRDS dependency control for a nonincreasing count.
* `integral_falseDiscoveryProportion_storeyBHRejections_le_of_isPRDSOn`:
  `E[FDP] ≤ q (1 - lam) |H0|` under PRDS.

## Not covered

Adaptive procedures designed to control the FDR at `q` under PRDS or arbitrary dependence (for
example the two-stage procedures of Blanchard and Roquain 2009, §4) are not formalized.

## References

* Y. Benjamini and D. Yekutieli, *The control of the false discovery rate in multiple testing
  under dependency*, Ann. Statist. 29 (2001), 1165–1188, §1.3 and the proof of Theorem 1.2.
* J. D. Storey, J. E. Taylor and D. Siegmund, *Strong control, conservative point estimation and
  simultaneous conservative consistency of false discovery rates: a unified approach*,
  J. R. Statist. Soc. B 66 (2004), 187–205.
* G. Blanchard and É. Roquain, *Two simple sufficient conditions for FDR control*, Electron. J.
  Statist. 2 (2008), 963–992.
* G. Blanchard and É. Roquain, *Adaptive false discovery rate control under independence and
  dependence*, J. Mach. Learn. Res. 10 (2009), 2837–2871.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory ProbabilityTheory

variable {m : ℕ}

/-! ### Monotonicity of Storey-BH in the p-values -/

/-- Storey's estimator is nondecreasing in the p-values (coordinatewise), for `lam ≤ 1`. -/
theorem storeyPi0Plus1_mono {lam : ℝ} (hlam : lam ≤ 1) {x y : Fin m → ℝ} (hxy : x ≤ y) :
    storeyPi0Plus1 lam x ≤ storeyPi0Plus1 lam y := by
  unfold storeyPi0Plus1
  have h1 : 0 ≤ 1 - lam := by linarith
  have hc : ((Finset.univ.filter fun j => lam < x j).card : ℝ) ≤
      (Finset.univ.filter fun j => lam < y j).card := by
    exact_mod_cast Finset.card_le_card fun j hj => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact hj.trans_le (hxy j)
  exact div_le_div_of_nonneg_right (by linarith) (mul_nonneg h1 (Nat.cast_nonneg m))

/-- Storey's estimator is strictly positive for `m ≠ 0` and `lam < 1`: it is at least
`1 / ((1 - lam) m)`. -/
theorem storeyPi0Plus1_pos (hm : m ≠ 0) {lam : ℝ} (hlam : lam < 1) (p : Fin m → ℝ) :
    0 < storeyPi0Plus1 lam p := by
  unfold storeyPi0Plus1
  have h1 : 0 < 1 - lam := sub_pos.mpr hlam
  have hm' : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  exact div_pos (by positivity) (mul_pos h1 hm')

/-- The Storey-BH thresholds are nonincreasing in the p-values (coordinatewise), for `0 ≤ q` and
`lam < 1`: larger p-values raise `π̂₀` and so lower the adaptive level `q / π̂₀`. -/
theorem storeyThreshold_antitone {q lam : ℝ} (hq : 0 ≤ q) (hlam : lam < 1) {x y : Fin m → ℝ}
    (hxy : x ≤ y) (k : ℕ) : storeyThreshold q lam y k ≤ storeyThreshold q lam x k := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp [storeyThreshold]
  · unfold storeyThreshold
    refine min_le_min le_rfl ?_
    have h : q / storeyPi0Plus1 lam y ≤ q / storeyPi0Plus1 lam x :=
      div_le_div_of_nonneg_left hq (storeyPi0Plus1_pos hm.ne' hlam x)
        (storeyPi0Plus1_mono hlam.le hxy)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg k))
      (Nat.cast_nonneg m)

/-- **The number of Storey-BH rejections is nonincreasing in the p-values** (coordinatewise), for
`0 ≤ q` and `lam < 1`. So `{x | storeyBHIndex q lam x ≤ j}` is an increasing set in the sense of
PRDS. -/
theorem storeyBHIndex_antitone {q lam : ℝ} (hq : 0 ≤ q) (hlam : lam < 1) :
    Antitone (storeyBHIndex q lam : (Fin m → ℝ) → ℕ) := by
  intro x y hxy
  refine le_storeyBHIndex (storeyBHIndex_le q lam y)
    ((storeyBHIndex_le_numBelow q lam y).trans ?_)
  exact Finset.card_le_card fun j hj => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact (hxy j).trans (hj.trans (storeyThreshold_antitone hq hlam hxy _))

/-- The Storey-BH index is a measurable function of the p-value vector. -/
theorem measurable_storeyBHIndex (q lam : ℝ) :
    Measurable (storeyBHIndex q lam : (Fin m → ℝ) → ℕ) :=
  measurable_storeyBHIndex_comp q lam id measurable_pi_apply

/-! ### Dependency control under PRDS -/

private theorem sum_Icc_sub_le_of_le_succ' {u : ℕ → ℕ → ℝ} (hu : ∀ k, u k k ≤ u k (k + 1))
    (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, (u k k - u (k - 1) k) ≤ u n n - u 0 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
    linarith [hu n]

/-- Truncated form of `integral_indicator_le_of_isPRDSOn`: the contribution of the values
`k ∈ [1, m]` of `κ(P)`, with no bound on `κ` assumed. -/
private theorem integral_sum_Icc_indicator_le_of_isPRDSOn {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    {H0 : Finset (Fin m)} (hprds : IsPRDSOn μ p H0) {i : Fin m} (hi : i ∈ H0)
    (hnull : IsValidPValue μ (p i)) {κ : (Fin m → ℝ) → ℕ} (hκ : Measurable κ)
    (hanti : Antitone κ) {c : ℝ} (hc : 0 ≤ c) :
    ∫ ω, (∑ k ∈ Finset.Icc 1 m,
      {ω | p i ω ≤ c * k ∧ κ (fun j => p j ω) = k}.indicator (fun _ => 1 / (k : ℝ)) ω) ∂μ ≤
      c := by
  classical
  let t : ℕ → ℝ := fun k => c * k
  let D : ℕ → Set (Fin m → ℝ) := fun j => {x | κ x ≤ j}
  have hD (j : ℕ) : MeasurableSet (D j) := measurableSet_le hκ measurable_const
  have hDup (j : ℕ) : IsUpperSet (D j) := fun x y hxy hx => (hanti hxy).trans hx
  have hP : Measurable (fun ω j => p j ω) := Measurable.of_eval hp
  let a : ℕ → ℝ → ℝ := fun j s => μ.real ({ω | (fun l => p l ω) ∈ D j} ∩ {ω | p i ω ≤ s})
  let π : ℝ → ℝ := fun s => μ.real {ω | p i ω ≤ s}
  let ρ : ℕ → ℝ → ℝ := fun j s => a j s / π s
  have ha_le (j : ℕ) (s : ℝ) : a j s ≤ π s := measureReal_mono Set.inter_subset_right
  have ha_nonneg (j : ℕ) (s : ℝ) : 0 ≤ a j s := measureReal_nonneg
  have hcross (j : ℕ) {s u : ℝ} (hsu : s ≤ u) : a j s * π u ≤ a j u * π s := by
    have h := hprds.measure_inter_mul_le hp hi (hD j) (hDup j) hsu
    simp only [a, π, measureReal_def, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) h
  have hρ_mono (j : ℕ) {s u : ℝ} (hsu : s ≤ u) : ρ j s ≤ ρ j u := by
    rcases (measureReal_nonneg : 0 ≤ π s).eq_or_lt with h0 | hpos
    · have : a j s = 0 := le_antisymm ((ha_le j s).trans h0.symm.le) (ha_nonneg j s)
      simp only [ρ, this, zero_div]
      exact div_nonneg (ha_nonneg j u) measureReal_nonneg
    · have hpos' : 0 < π u :=
        hpos.trans_le (measureReal_mono fun ω (hω : p i ω ≤ s) => hω.trans hsu)
      exact (div_le_div_iff₀ hpos hpos').mpr (hcross j hsu)
  have hA (k : ℕ) (hk : 1 ≤ k) (s : ℝ) :
      μ.real {ω | p i ω ≤ s ∧ κ (fun j => p j ω) = k} = a k s - a (k - 1) s := by
    have hunion : {ω | (fun l => p l ω) ∈ D k} ∩ {ω | p i ω ≤ s} =
        {ω | p i ω ≤ s ∧ κ (fun j => p j ω) = k} ∪
          ({ω | (fun l => p l ω) ∈ D (k - 1)} ∩ {ω | p i ω ≤ s}) := by
      ext ω
      simp only [D, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_ge (κ (fun j => p j ω)) k with h | h
        · exact Or.inr ⟨by omega, h2⟩
        · exact Or.inl ⟨h2, by omega⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h2.le, h1⟩
        · exact ⟨by omega, h2⟩
    have hdisj : Disjoint {ω | p i ω ≤ s ∧ κ (fun j => p j ω) = k}
        ({ω | (fun l => p l ω) ∈ D (k - 1)} ∩ {ω | p i ω ≤ s}) := by
      refine Set.disjoint_left.mpr fun ω h1 h2 => ?_
      simp only [D, Set.mem_inter_iff, Set.mem_ofPred_eq] at h1 h2
      omega
    have h := measureReal_union (μ := μ) hdisj ((hP (hD (k - 1))).inter
      (measurableSet_le (hp i) measurable_const))
    simp only [a]
    rw [hunion, h]
    ring
  have hterm (k : ℕ) (hk : k ∈ Finset.Icc 1 m) :
      μ.real {ω | p i ω ≤ c * k ∧ κ (fun j => p j ω) = k} * (1 / (k : ℝ)) ≤
        c * (ρ k (t k) - ρ (k - 1) (t k)) := by
    obtain ⟨hk1, -⟩ := Finset.mem_Icc.mp hk
    set A := μ.real {ω | p i ω ≤ c * k ∧ κ (fun j => p j ω) = k} with hAdef
    have hΔ : ρ k (t k) - ρ (k - 1) (t k) = A / π (t k) := by
      simp only [ρ]
      rw [← sub_div]
      exact congrArg (· / π (t k)) (hA k hk1 (t k)).symm
    rw [hΔ]
    have hAle : A ≤ π (t k) := measureReal_mono fun ω hω => hω.1
    have htk : 0 ≤ t k := mul_nonneg hc (Nat.cast_nonneg k)
    have hπt : π (t k) ≤ t k := by
      rcases le_or_gt (t k) 1 with h1 | h1
      · exact valid_measureReal_le hnull htk h1
      · exact (ENNReal.toReal_le_of_le_ofReal zero_le_one
          (by rw [ENNReal.ofReal_one]; exact prob_le_one)).trans h1.le
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hA0 : 0 ≤ A := measureReal_nonneg
    rcases (measureReal_nonneg : 0 ≤ π (t k)).eq_or_lt with h0 | hpos
    · have : A = 0 := le_antisymm (hAle.trans h0.symm.le) hA0
      simp [this]
    · have hπ0 : π (t k) ≠ 0 := hpos.ne'
      have hq0 : 0 ≤ A / π (t k) := div_nonneg hA0 hpos.le
      calc A * (1 / (k : ℝ)) = A / π (t k) * π (t k) / k := by field_simp
        _ ≤ A / π (t k) * t k / k := by gcongr
        _ = c * (A / π (t k)) := by
          simp only [t]
          field_simp
  have hevent (k : ℕ) : MeasurableSet {ω | p i ω ≤ c * k ∧ κ (fun j => p j ω) = k} :=
    (measurableSet_le (hp i) measurable_const).inter
      (measurableSet_eq_fun (hκ.comp hP) measurable_const)
  have hρm : ρ m (t m) ≤ 1 := div_le_one_of_le₀ (ha_le m (t m)) measureReal_nonneg
  have hρ0 : 0 ≤ ρ 0 (t 0) := div_nonneg (ha_nonneg 0 _) measureReal_nonneg
  have ht_mono (k : ℕ) : t k ≤ t (k + 1) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ k) hc
  rw [integral_finsetSum (Finset.Icc 1 m) (fun (k : ℕ) _ =>
    (integrable_const (μ := μ) (1 / (k : ℝ))).indicator (hevent k))]
  simp_rw [integral_indicator_const _ (hevent _), smul_eq_mul]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 m, c * (ρ k (t k) - ρ (k - 1) (t k)) :=
      Finset.sum_le_sum hterm
    _ = c * ∑ k ∈ Finset.Icc 1 m, (ρ k (t k) - ρ (k - 1) (t k)) := by rw [Finset.mul_sum]
    _ ≤ c * (ρ m (t m) - ρ 0 (t 0)) := mul_le_mul_of_nonneg_left
      (sum_Icc_sub_le_of_le_succ' (u := fun k l => ρ k (t l))
        (fun k => hρ_mono k (ht_mono k)) m) hc
    _ ≤ c * 1 := by
      gcongr
      linarith
    _ = c := mul_one _

/-- On `κ ≤ m`, the indicator `1{X ≤ c K, K ≥ 1} / K` is the sum over the values `k ∈ [1, m]`
of `K`. -/
private theorem indicator_eq_sum_Icc {Ω : Type*} (X : Ω → ℝ) (K : Ω → ℕ) (c : ℝ) {ω : Ω}
    (hK : K ω ≤ m) :
    {ω | X ω ≤ c * K ω ∧ 1 ≤ K ω}.indicator (fun ω => 1 / (K ω : ℝ)) ω =
      ∑ k ∈ Finset.Icc 1 m, {ω | X ω ≤ c * k ∧ K ω = k}.indicator (fun _ => 1 / (k : ℝ)) ω := by
  rcases Nat.eq_zero_or_pos (K ω) with h0 | hpos
  · rw [Set.indicator_of_notMem (by simp [h0])]
    refine (Finset.sum_eq_zero fun k hk => Set.indicator_of_notMem ?_ _).symm
    have := (Finset.mem_Icc.mp hk).1
    simp only [Set.mem_ofPred_eq, h0]
    omega
  · rw [Finset.sum_eq_single (K ω)]
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, and_true]
      simp [Nat.one_le_iff_ne_zero.mpr hpos.ne']
    · intro k _ hk
      exact Set.indicator_of_notMem (fun h => hk h.2.symm) _
    · intro h
      exact absurd (Finset.mem_Icc.mpr ⟨hpos, hK⟩) h

/-- **PRDS dependency control for a nonincreasing count** (Benjamini–Yekutieli 2001, proof of
Theorem 1.2; Blanchard–Roquain 2008, Lemma 3.2). Let `p` be PRDS on `H0`, let `i ∈ H0` have a
valid p-value, and let `κ` be a measurable function of the p-value vector that is nonincreasing
coordinatewise and at most `m`. Then for every `c ≥ 0`,
`E[1{p i ≤ c κ(P), κ(P) ≥ 1} / κ(P)] ≤ c`. With `ρ_j(t) = P(κ(P) ≤ j | p i ≤ t)`, nondecreasing
in `t` by PRDS, the left side is at most `c ∑_{k ∈ [1, m]} (ρ_k(c k) - ρ_{k-1}(c k)) ≤
c ρ_m(c m) ≤ c`. -/
theorem integral_indicator_le_of_isPRDSOn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    {H0 : Finset (Fin m)} (hprds : IsPRDSOn μ p H0) {i : Fin m} (hi : i ∈ H0)
    (hnull : IsValidPValue μ (p i)) {κ : (Fin m → ℝ) → ℕ} (hκ : Measurable κ)
    (hanti : Antitone κ) (hκm : ∀ x, κ x ≤ m) {c : ℝ} (hc : 0 ≤ c) :
    ∫ ω, {ω | p i ω ≤ c * κ (fun j => p j ω) ∧ 1 ≤ κ (fun j => p j ω)}.indicator
      (fun ω => 1 / (κ (fun j => p j ω) : ℝ)) ω ∂μ ≤ c := by
  refine (integral_congr_ae (Filter.Eventually.of_forall fun ω =>
    indicator_eq_sum_Icc (p i) (fun ω => κ (fun j => p j ω)) c (hκm _))).trans_le ?_
  exact integral_sum_Icc_indicator_le_of_isPRDSOn μ p hp hprds hi hnull hκ hanti hc

/-! ### FDR of Storey-BH under PRDS -/

/-- **Storey-BH under PRDS: `E[FDP] ≤ q (1 - lam) |H0|`.** Let `H0` be the set of true nulls and
assume

* every true-null p-value is valid (super-uniform: `μ {p i ≤ t} ≤ t` for `t ∈ [0, 1]`);
* the p-values are PRDS on `H0` (`IsPRDSOn`, Benjamini–Yekutieli 2001);
* the tuning parameter `lam < 1` is fixed.

Then Storey-BH at level `q ≥ 0` (`storeyBHRejections q lam`) has false discovery rate at most
`q (1 - lam) |H0|`. This is weaker than the bound `q` that holds when each true-null p-value is
independent of the others (`integral_falseDiscoveryProportion_storeyBHRejections_le`), and the
weakening is necessary: with two identical valid null p-values, `q = 1/5` and `lam = 2/5`, the
FDR is `6/25 = q (1 - lam) |H0| > q` (test file). Independent p-values are PRDS
(`isPRDSOn_of_iIndepFun`), so the theorem also applies to them, with the weaker bound.

Proof: the number `K` of rejections is nonincreasing in the p-values
(`storeyBHIndex_antitone`), and since `π̂₀ ≥ 1 / ((1 - lam) m)`, a rejected true null has
`p i ≤ q (1 - lam) K`; PRDS dependency control (`integral_indicator_le_of_isPRDSOn`) bounds
each null's expected contribution by `q (1 - lam)`. -/
theorem integral_falseDiscoveryProportion_storeyBHRejections_le_of_isPRDSOn {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ)
    (hp : ∀ i, Measurable (p i)) (H0 : Finset (Fin m)) (hprds : IsPRDSOn μ p H0)
    (hnull : ∀ i ∈ H0, IsValidPValue μ (p i)) {q lam : ℝ} (hq : 0 ≤ q) (hlam1 : lam < 1) :
    ∫ ω, falseDiscoveryProportion H0 (storeyBHRejections q lam fun i => p i ω) ∂μ ≤
      q * (1 - lam) * H0.card := by
  classical
  have hc : 0 ≤ q * (1 - lam) := mul_nonneg hq (by linarith)
  have hP : Measurable (fun ω j => p j ω) := Measurable.of_eval hp
  let K : Ω → ℕ := fun ω => storeyBHIndex q lam (fun j => p j ω)
  let g : Fin m → Ω → ℝ := fun i ω =>
    {ω | p i ω ≤ q * (1 - lam) * K ω ∧ 1 ≤ K ω}.indicator (fun ω => 1 / (K ω : ℝ)) ω
  have hg_int (i : Fin m) : Integrable (g i) μ := by
    have hg : g i = fun ω => ∑ k ∈ Finset.Icc 1 m,
        {ω | p i ω ≤ q * (1 - lam) * k ∧ K ω = k}.indicator (fun _ => 1 / (k : ℝ)) ω :=
      funext fun ω => indicator_eq_sum_Icc (p i) K _ (storeyBHIndex_le q lam _)
    rw [hg]
    exact integrable_finsetSum _ fun k _ => (integrable_const _).indicator
      ((measurableSet_le (hp i) measurable_const).inter
        (measurableSet_eq_fun ((measurable_storeyBHIndex q lam).comp hP) measurable_const))
  have hpt (ω : Ω) (i : Fin m) :
      (if i ∈ storeyBHRejections q lam (fun j => p j ω) then
        1 / max ((storeyBHRejections q lam (fun j => p j ω)).card : ℝ) 1 else 0) ≤ g i ω := by
    have hnn : 0 ≤ g i ω := Set.indicator_nonneg (fun _ _ => by positivity) _
    split_ifs with hi
    · have hm : m ≠ 0 := by have := i.isLt; omega
      have hcard := card_storeyBHRejections hq hlam1.le (fun j => p j ω)
      have hK1 : 1 ≤ storeyBHIndex q lam (fun j => p j ω) :=
        hcard ▸ Finset.card_pos.mpr ⟨i, hi⟩
      have hpi : p i ω ≤ q * (1 - lam) * storeyBHIndex q lam (fun j => p j ω) := by
        have h := mem_storeyBHRejections.mp hi
        rw [storeyThreshold_eq hm] at h
        refine (h.trans (min_le_right _ _)).trans
          (div_le_self (mul_nonneg hc (Nat.cast_nonneg _)) ?_)
        have : (0 : ℝ) ≤ (Finset.univ.filter fun j => lam < p j ω).card := Nat.cast_nonneg _
        linarith
      rw [hcard, max_eq_left (by exact_mod_cast hK1)]
      exact (Set.indicator_of_mem (s := {ω | p i ω ≤ q * (1 - lam) * K ω ∧ 1 ≤ K ω})
        (show ω ∈ _ from ⟨hpi, hK1⟩) (fun ω => 1 / (K ω : ℝ))).ge
    · exact hnn
  calc ∫ ω, falseDiscoveryProportion H0 (storeyBHRejections q lam fun i => p i ω) ∂μ
      = ∫ ω, ∑ i ∈ H0, (if i ∈ storeyBHRejections q lam (fun j => p j ω) then
          1 / max ((storeyBHRejections q lam (fun j => p j ω)).card : ℝ) 1 else 0) ∂μ := by
        congr 1; funext ω; exact fdp_eq_sum _ _
    _ ≤ ∫ ω, ∑ i ∈ H0, g i ω ∂μ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_)
          (integrable_finsetSum _ fun i _ => hg_int i)
          (Filter.Eventually.of_forall fun ω => Finset.sum_le_sum fun i _ => hpt ω i)
        exact Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
    _ = ∑ i ∈ H0, ∫ ω, g i ω ∂μ := integral_finsetSum _ fun i _ => hg_int i
    _ ≤ ∑ _i ∈ H0, q * (1 - lam) := Finset.sum_le_sum fun i hi =>
        integral_indicator_le_of_isPRDSOn μ p hp hprds hi (hnull i hi)
          (measurable_storeyBHIndex q lam) (storeyBHIndex_antitone hq hlam1)
          (storeyBHIndex_le q lam) hc
    _ = q * (1 - lam) * H0.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end MathlibExt.Probability.Statistics.MultipleTesting
