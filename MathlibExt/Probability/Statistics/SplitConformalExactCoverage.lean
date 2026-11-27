/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.SplitConformal
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Exact split-conformal coverage without ties, and the upper bound

`MathlibExt.Probability.Statistics.SplitConformal` proves that the split conformal threshold
covers the test score with probability at least `k / (n + 1) ≥ 1 - α`, where
`k = ⌈(1 - α)(n + 1)⌉`, under any permutation-invariant law of the score vector. This module adds
the matching upper bound: if moreover the scores are almost surely distinct (no ties), the
coverage probability is exactly `k / (n + 1)`, hence at most `1 - α + 1 / (n + 1)`.

The argument is the one in the proof of Lemma 1 of R. J. Tibshirani, R. F. Barber, E. J. Candès
and A. Ramdas, *Conformal prediction under covariate shift*, NeurIPS 2019, arXiv:1904.06019: the
test score is covered iff it is among the `k` smallest of all `n + 1` scores, and when the scores
are distinct exactly `k` of the `n + 1` positions have that property; averaging over the
permutation group (`measure_eq_card_div_of_ae_card_filter_smul_mem_eq`) turns this count into
the probability `k / (n + 1)`.

## Main definitions

* `rankCount ω i`: the number of coordinates of `ω` strictly below `ω i`.

## Main results

* `card_filter_rankCount_lt_of_injective`: for distinct values and `k ≤ |ι|`, exactly `k`
  coordinates have fewer than `k` coordinates strictly below them.
* `measurable_strictLowerCount`: the strict lower count is measurable.
* `measurableSet_setOf_injective`: having distinct scores is a measurable event.
* `strictLowerCount_eq_rankCount_last`: the strict lower count of the test score is its rank among
  all `n + 1` scores.
* `measure_coe_le_splitConformalThreshold_eq_of_ae_injective`: without ties the coverage
  probability is exactly `k / (n + 1)` for every `1 ≤ k ≤ n + 1`.
* `measure_coe_le_splitConformalThreshold_le`: without ties, coverage at level
  `k = ⌈(1 - α)(n + 1)⌉` is at most `1 - α + 1 / (n + 1)` (Tibshirani et al. 2019, Lemma 1).
-/

@[expose] public section

open MeasureTheory Finset
open MathlibExt.Probability.Statistics.MultipleTesting
open MathlibExt.Probability.Statistics.SplitConformal

namespace MathlibExt.Probability.Statistics.SplitConformalExactCoverage

section Rank

variable {ι : Type*} [Fintype ι]

/-- **Strict rank count.** The number of coordinates `j` with `ω j < ω i`; with distinct values,
`rankCount ω i + 1` is the rank of `ω i` among the values of `ω`. -/
noncomputable def rankCount (ω : ι → ℝ) (i : ι) : ℕ :=
  (univ.filter fun j => ω j < ω i).card

/-- **The rank count is below the number of coordinates.** `rankCount ω i < |ι|`, since `i` itself
is not counted. -/
theorem rankCount_lt_card (ω : ι → ℝ) (i : ι) : rankCount ω i < Fintype.card ι := by
  refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h => ?_⟩
  have := h (Finset.mem_univ i)
  simp at this

/-- **Distinct values have distinct rank counts.** If `ω` is injective, so is `rankCount ω`. -/
theorem rankCount_injective {ω : ι → ℝ} (hω : Function.Injective ω) :
    Function.Injective (rankCount ω) := by
  have key : ∀ i i', ω i < ω i' → rankCount ω i < rankCount ω i' := by
    intro i i' h
    refine Finset.card_lt_card ⟨fun j hj => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact hj.trans h
    · have := hsub (by simp [h] : i ∈ univ.filter fun j => ω j < ω i')
      simp at this
  intro i i' hii'
  rcases lt_trichotomy (ω i) (ω i') with h | h | h
  · exact absurd hii' (key i i' h).ne
  · exact hω h
  · exact absurd hii' (key i' i h).ne'

/-- **Exactly `k` coordinates have rank count below `k`.** If the values of `ω` are distinct and
`k ≤ |ι|`, then exactly `k` coordinates `i` have fewer than `k` coordinates strictly below them:
the rank counts are a permutation of `0, …, |ι| - 1`. This is the deterministic counting step in
the proof of Lemma 1 of Tibshirani, Barber, Candès and Ramdas (2019, arXiv:1904.06019). -/
theorem card_filter_rankCount_lt_of_injective {ω : ι → ℝ} (hω : Function.Injective ω) {k : ℕ}
    (hk : k ≤ Fintype.card ι) :
    (univ.filter fun i => rankCount ω i < k).card = k := by
  classical
  have hinj := rankCount_injective hω
  have himage : univ.image (rankCount ω) = range (Fintype.card ι) := by
    refine Finset.eq_of_subset_of_card_le (fun v hv => ?_) ?_
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      exact Finset.mem_range.2 (rankCount_lt_card ω i)
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_range, Finset.card_univ]
  calc (univ.filter fun i => rankCount ω i < k).card
      = ((univ.filter fun i => rankCount ω i < k).image (rankCount ω)).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ = ((univ.image (rankCount ω)).filter fun v => v < k).card := by
        rw [Finset.filter_image]
    _ = k := by
        have : (range (Fintype.card ι)).filter (fun v => v < k) = range k := by
          ext v; simp only [Finset.mem_filter, Finset.mem_range]; omega
        rw [himage, this, Finset.card_range]

end Rank

section Coverage

variable {n : ℕ}

/-- **The strict lower count is the rank among all scores.** The number of calibration scores
strictly below the test score equals the number of all `n + 1` scores strictly below it. -/
theorem strictLowerCount_eq_rankCount_last (ω : Fin (n + 1) → ℝ) :
    strictLowerCount ω = rankCount ω (Fin.last n) := by
  rw [strictLowerCount, rankCount, Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp

private theorem rankCount_comp_perm (ω : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) : rankCount (fun j => ω (σ j)) i = rankCount ω (σ i) := by
  unfold rankCount
  refine Finset.card_bij (fun j _ => σ j) (fun j hj => by simpa using hj)
    (fun _ _ _ _ h => σ.injective h) (fun j hj => ⟨σ.symm j, by simpa using hj, by simp⟩)

private theorem card_fiber_eq (a i : Fin (n + 1)) :
    (univ.filter fun σ : Equiv.Perm (Fin (n + 1)) => σ⁻¹ a = i).card =
      (univ.filter fun σ : Equiv.Perm (Fin (n + 1)) => σ⁻¹ a = a).card := by
  refine Finset.card_bij' (fun σ _ => σ * Equiv.swap i a) (fun σ _ => σ * Equiv.swap i a)
    (fun σ hσ => ?_) (fun σ hσ => ?_) (fun σ _ => ?_) (fun σ _ => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply, hσ, Equiv.swap_apply_left]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply, hσ, Equiv.swap_apply_right]
  · simp [mul_assoc]
  · simp [mul_assoc]

private theorem card_fiber_eq_factorial (a i : Fin (n + 1)) :
    (univ.filter fun σ : Equiv.Perm (Fin (n + 1)) => σ⁻¹ a = i).card = n.factorial := by
  have htot : Fintype.card (Equiv.Perm (Fin (n + 1))) =
      ∑ j : Fin (n + 1), (univ.filter fun σ : Equiv.Perm (Fin (n + 1)) => σ⁻¹ a = j).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  simp_rw [card_fiber_eq a _ ] at htot
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Fintype.card_perm,
    Fintype.card_fin, Nat.factorial_succ] at htot
  rw [card_fiber_eq a i]
  exact (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) htot).symm

private theorem card_filter_perm (P : Fin (n + 1) → Prop) [DecidablePred P] (a : Fin (n + 1)) :
    (univ.filter fun σ : Equiv.Perm (Fin (n + 1)) => P (σ⁻¹ a)).card =
      (univ.filter P).card * n.factorial := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm (Fin (n + 1)) => σ⁻¹ a)
    (t := univ.filter P) (fun σ hσ => by simpa using hσ)]
  rw [Finset.card_eq_sum_ones (univ.filter P), Finset.sum_mul, one_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← card_fiber_eq_factorial a i]
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h ▸ hi, h⟩

/-- **The strict lower count is measurable.** `ω ↦ strictLowerCount ω` is a measurable map from
score vectors to `ℕ`, as a finite sum of indicators of the measurable sets
`{ω | ω i.castSucc < ω (Fin.last n)}`. -/
theorem measurable_strictLowerCount :
    Measurable (strictLowerCount : (Fin (n + 1) → ℝ) → ℕ) := by
  have h : (strictLowerCount : (Fin (n + 1) → ℝ) → ℕ) = fun ω =>
      ∑ i : Fin n, if ω i.castSucc < ω (Fin.last n) then 1 else 0 := by
    funext ω; rw [strictLowerCount, Finset.card_filter]
  rw [h]
  exact Finset.measurable_sum _ fun i _ => Measurable.ite
    (measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _)) measurable_const
    measurable_const

/-- **Distinctness is a measurable event.** The set of score vectors with pairwise distinct
entries is measurable. -/
theorem measurableSet_setOf_injective :
    MeasurableSet {ω : Fin (n + 1) → ℝ | Function.Injective ω} := by
  have : {ω : Fin (n + 1) → ℝ | Function.Injective ω} =
      ⋂ i : Fin (n + 1), ⋂ j : Fin (n + 1), {ω | ω i = ω j → i = j} := by
    ext ω; simp [Function.Injective]
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  by_cases hij : i = j
  · simp [hij]
  · have : {ω : Fin (n + 1) → ℝ | ω i = ω j → i = j} = {ω | ω i = ω j}ᶜ := by
      ext ω; simp [hij]
    rw [this]
    exact (measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)).compl

/-- **Exact split conformal coverage without ties.** If the law `μ` of the score vector is a
probability measure invariant under every coordinate permutation and the `n + 1` scores are
almost surely distinct, then for every `1 ≤ k ≤ n + 1` the test score is covered by the `k`-th
smallest calibration score (`⊤` if `k = n + 1`) with probability exactly `k / (n + 1)`.

Source: R. J. Tibshirani, R. F. Barber, E. J. Candès and A. Ramdas, *Conformal prediction under
covariate shift*, NeurIPS 2019, arXiv:1904.06019, proof of Lemma 1 ("when there are almost surely
no ties, it holds with probability exactly `⌈β(n+1)⌉/(n+1)`"). -/
theorem measure_coe_le_splitConformalThreshold_eq_of_ae_injective
    (μ : Measure (Fin (n + 1) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ σ : Equiv.Perm (Fin (n + 1)), μ.map (fun ω => ω ∘ σ) = μ)
    (hinj : ∀ᵐ ω ∂μ, Function.Injective ω) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n + 1) :
    μ {ω | (ω (Fin.last n) : WithTop ℝ) ≤ splitConformalThreshold k ω} =
      (k : ENNReal) / (n + 1) := by
  classical
  have := smulInvariantMeasure_of_map_comp_eq hμ
  have hset : {ω : Fin (n + 1) → ℝ | (ω (Fin.last n) : WithTop ℝ) ≤ splitConformalThreshold k ω}
      = strictLowerCount ⁻¹' Set.Iio k := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iio]
    exact coe_le_splitConformalThreshold_iff hk1 ω
  rw [hset]
  have hmeas : MeasurableSet (strictLowerCount ⁻¹' Set.Iio k : Set (Fin (n + 1) → ℝ)) :=
    measurable_strictLowerCount (MeasurableSet.of_discrete)
  rw [measure_eq_card_div_of_ae_card_filter_smul_mem_eq (G := Equiv.Perm (Fin (n + 1))) μ
    (fun σ => Measurable.of_eval fun i => by exact measurable_pi_apply (σ⁻¹ i)) hmeas
    (c := k * n.factorial) ?_]
  · rw [Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ]
    push_cast
    rw [ENNReal.mul_div_mul_right _ _ (by exact_mod_cast n.factorial_ne_zero)
      (ENNReal.natCast_ne_top _)]
  · filter_upwards [hinj] with ω hω
    have hcount : ∀ σ : Equiv.Perm (Fin (n + 1)),
        σ • ω ∈ (strictLowerCount ⁻¹' Set.Iio k : Set (Fin (n + 1) → ℝ)) ↔
          rankCount ω (σ⁻¹ (Fin.last n)) < k := by
      intro σ
      simp only [Set.mem_preimage, Set.mem_Iio]
      rw [strictLowerCount_eq_rankCount_last]
      have : (σ • ω) = fun j => ω (σ⁻¹ j) := rfl
      rw [this, rankCount_comp_perm ω σ⁻¹]
    simp_rw [hcount]
    rw [card_filter_perm (fun i => rankCount ω i < k) (Fin.last n),
      card_filter_rankCount_lt_of_injective hω (by simpa using hkn)]

/-- **Upper bound on split conformal coverage without ties.** If the law of the score vector is a
probability measure invariant under every coordinate permutation and the scores are almost surely
distinct, then for `0 ≤ α < 1` the test score is covered by the split conformal threshold at
`k = ⌈(1 - α)(n + 1)⌉` with probability at most `1 - α + 1 / (n + 1)`. Together with
`ofReal_one_sub_le_measure_coe_le_splitConformalThreshold` this pins the coverage between `1 - α`
and `1 - α + 1 / (n + 1)`.

Source: R. J. Tibshirani, R. F. Barber, E. J. Candès and A. Ramdas, *Conformal prediction under
covariate shift*, NeurIPS 2019, arXiv:1904.06019, Lemma 1 (with `β = 1 - α`), which states this
bound for `β ∈ (0, 1)`; the Lean statement also admits the trivial endpoint `α = 0`. Lemma 2 of
Y. Romano, E. Patterson and E. J. Candès, *Conformalized quantile regression*, NeurIPS 2019,
arXiv:1905.03222, is stated with the term `1 / n`; the bound here is the sharper `1 / (n + 1)`. -/
theorem measure_coe_le_splitConformalThreshold_le
    (μ : Measure (Fin (n + 1) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ σ : Equiv.Perm (Fin (n + 1)), μ.map (fun ω => ω ∘ σ) = μ)
    (hinj : ∀ᵐ ω ∂μ, Function.Injective ω) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    μ {ω | (ω (Fin.last n) : WithTop ℝ) ≤ splitConformalThreshold ⌈(1 - α) * (n + 1)⌉₊ ω} ≤
      ENNReal.ofReal (1 - α + 1 / (n + 1)) := by
  set k := ⌈(1 - α) * (n + 1)⌉₊ with hkdef
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hk1 : 1 ≤ k := Nat.one_le_ceil_iff.2 (mul_pos (sub_pos.2 hα1) hN)
  have hkn : k ≤ n + 1 := Nat.ceil_le.2 (by push_cast; nlinarith)
  rw [measure_coe_le_splitConformalThreshold_eq_of_ae_injective μ hμ hinj hk1 hkn]
  have hlt : (k : ℝ) < (1 - α) * (n + 1) + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (by linarith) hN.le)
  have hle : (k : ℝ) / (n + 1) ≤ 1 - α + 1 / (n + 1) := by
    rw [div_le_iff₀ hN]
    have : (1 - α + 1 / (n + 1)) * (n + 1) = (1 - α) * (n + 1) + 1 := by field_simp
    rw [this]; exact hlt.le
  calc (k : ENNReal) / (n + 1) = ENNReal.ofReal ((k : ℝ) / (n + 1)) := by
        rw [ENNReal.ofReal_div_of_pos hN]
        congr 1
        · exact (ENNReal.ofReal_natCast k).symm
        · rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
            ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (1 - α + 1 / (n + 1)) := ENNReal.ofReal_le_ofReal hle

end Coverage

end MathlibExt.Probability.Statistics.SplitConformalExactCoverage
