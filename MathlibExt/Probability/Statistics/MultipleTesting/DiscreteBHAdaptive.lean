/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.DiscreteBH

/-!
# Adaptive discrete Benjamini–Hochberg: [A-DBH-SU]

The discrete BH procedure [DBH-SU] of Döhler, Durand and Roquain (2018), formalized in
`MultipleTesting.DiscreteBH`, chooses its `k`-th critical value from a sum over **all** `m`
hypotheses of the corrected null CDFs `ξ_i(t) = F_i(t) / (1 - F_i(τ_m))`. That sum bounds the
contribution of the unknown set of true nulls by the worst case `m₀ = m`. The adaptive version
**[A-DBH-SU]** replaces it by the sum of the `m - k + 1` largest `ξ_i(t)`:

* `τ_m` is the last critical value of [DBH-SU] (`dbhSULastCritical`),
* `τ_k = max {t ∈ 𝒜 : t ≤ τ_m, Σ_{i ≤ m-k+1} ξ_(i)(t) ≤ α k}`, where `ξ_(1)(t) ≥ ξ_(2)(t) ≥ ⋯`
  are the `ξ_i(t)` in decreasing order,

and rejects every hypothesis with `p_i ≤ τ_k̂`, `k̂ = stepUpIndex τ p`. The count `m - k + 1` acts
as an estimate of the number of true nulls: in the leave-one-out proof, a true null `i`
contributes to the FDR only through the event `p_i > τ_m`, and when the step-up index computed
with `p_i := 0` equals `k`, at most `m - k + 1` p-values exceed `τ_m`. The procedure therefore
needs no tuning parameter and no separate `π₀` estimator, and since it only drops terms from the
[DBH-SU] sum it rejects at least as much as [DBH-SU] (`dbhSURejections_subset_adbhSURejections`).

## Conventions

* `maxSubsetSum x r` is the largest `∑_{i ∈ S} x i` over sets `S` with `|S| ≤ r`; for nonnegative
  `x` this is the sum of the `r` largest values, and it equals the maximum over sets of size
  exactly `min r m` used by Döhler–Durand–Roquain.
* As in `MultipleTesting.DiscreteBH`, the null CDFs are inputs `F : Fin m → ℝ → ℝ`, the support is
  a `Finset` `A`, `0` is adjoined to the defining set as a sentinel for the empty maximum, and the
  defining inequality is written `(1/m) · (…) ≤ α k / m` so that it reads as the [DBH-SU] one with
  the full sum replaced. `adbhSUCritical α F A k` is defined by the second formula for every `k`;
  at `k = m` it equals `τ_m` (`adbhSUCritical_self`).

## Main results

* `integral_falseDiscoveryProportion_stepUp_le_adaptive`: for independent p-values and any
  nondecreasing nonnegative critical values `c` with `F_i(c m) < 1` on the true nulls,
  `E[FDP] ≤ max_{1 ≤ k ≤ m} max_{S ⊆ H0, |S| ≤ m - k + 1} (1/k) ∑_{i ∈ S} F_i(c k) / (1 - F_i(c m))`
  (Döhler–Durand–Roquain 2018, Theorem 3.1, adaptive form of the second bound), stated with an
  explicit bound `B`.
* `integral_falseDiscoveryProportion_adbhSURejections_le`: **[A-DBH-SU] controls the FDR at
  level `α`** for independent p-values.
* `dbhSURejections_subset_adbhSURejections`: [A-DBH-SU] rejects every hypothesis that [DBH-SU]
  rejects.

The test file has a three-hypothesis example on which [A-DBH-SU] rejects two hypotheses and
[DBH-SU] rejects none.

## Not covered

Plug-in adaptive procedures with an explicit estimator of `π₀` (Storey-type estimators with a tuning
parameter `λ` for discrete p-values, as in Chen, Doerge and Heyse 2018), the step-down versions
[DBH-SD] and [A-DBH-SD], and any result under PRDS or arbitrary dependence are not formalized.
Independence is assumed throughout, as in Döhler–Durand–Roquain.

## References

* S. Döhler, G. Durand and E. Roquain, *New FDR bounds for discrete and heterogeneous tests*,
  Electron. J. Statist. 12 (2018), 1867–1900 (arXiv:1706.08250), §2 and Theorem 3.1.
* X. Chen, R. W. Doerge and J. F. Heyse, *Multiple testing with discrete data: proportion of true
  null hypotheses and two adaptive FDR procedures*, Biometrical J. 60 (2018).
* A. Gavrilov, Y. Benjamini and S. K. Sarkar, *An adaptive step-down procedure with proven FDR
  control under independence*, Ann. Statist. 37 (2009), 619–629.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory ProbabilityTheory

variable {m : ℕ}

/-! ### Largest sum over a bounded number of coordinates -/

/-- The largest sum `∑_{i ∈ S} x i` over sets `S` of at most `r` coordinates. For nonnegative `x`
this is the sum of the `r` largest values of `x`. -/
noncomputable def maxSubsetSum (x : Fin m → ℝ) (r : ℕ) : ℝ :=
  ((Finset.univ : Finset (Fin m)).powerset.filter fun S => S.card ≤ r).sup'
    ⟨∅, by simp⟩ fun S => ∑ i ∈ S, x i

/-- Every sum over at most `r` coordinates is at most `maxSubsetSum x r`. -/
theorem sum_le_maxSubsetSum (x : Fin m → ℝ) {r : ℕ} {S : Finset (Fin m)} (hS : S.card ≤ r) :
    ∑ i ∈ S, x i ≤ maxSubsetSum x r :=
  Finset.le_sup' (fun S : Finset (Fin m) => ∑ i ∈ S, x i) (by simp [hS])

/-- `maxSubsetSum x r` is the least upper bound of the sums over at most `r` coordinates. -/
theorem maxSubsetSum_le {x : Fin m → ℝ} {r : ℕ} {b : ℝ}
    (h : ∀ S : Finset (Fin m), S.card ≤ r → ∑ i ∈ S, x i ≤ b) : maxSubsetSum x r ≤ b :=
  Finset.sup'_le _ _ fun S hS => h S (Finset.mem_filter.mp hS).2

/-- `maxSubsetSum x r ≥ 0`, from the empty set. -/
theorem maxSubsetSum_nonneg (x : Fin m → ℝ) (r : ℕ) : 0 ≤ maxSubsetSum x r := by
  simpa using sum_le_maxSubsetSum x (S := ∅) (Nat.zero_le r)

/-- `maxSubsetSum x r` is nondecreasing in `r`. -/
theorem maxSubsetSum_mono_right (x : Fin m → ℝ) {r s : ℕ} (hrs : r ≤ s) :
    maxSubsetSum x r ≤ maxSubsetSum x s :=
  maxSubsetSum_le fun _ hS => sum_le_maxSubsetSum x (hS.trans hrs)

/-- For nonnegative `x`, `maxSubsetSum x r` is at most the full sum. -/
theorem maxSubsetSum_le_sum {x : Fin m → ℝ} (hx : ∀ i, 0 ≤ x i) (r : ℕ) :
    maxSubsetSum x r ≤ ∑ i, x i :=
  maxSubsetSum_le fun S _ =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun i _ _ => hx i

/-- For nonnegative `x` and `r ≥ m`, `maxSubsetSum x r` is the full sum. -/
theorem maxSubsetSum_eq_sum {x : Fin m → ℝ} (hx : ∀ i, 0 ≤ x i) {r : ℕ} (hr : m ≤ r) :
    maxSubsetSum x r = ∑ i, x i :=
  le_antisymm (maxSubsetSum_le_sum hx r)
    (sum_le_maxSubsetSum x (by simpa using hr))

/-- The zero vector has `maxSubsetSum` zero. -/
theorem maxSubsetSum_zero (r : ℕ) : maxSubsetSum (fun _ : Fin m => (0 : ℝ)) r = 0 :=
  le_antisymm (maxSubsetSum_le fun _ _ => by simp) (maxSubsetSum_nonneg _ r)

/-! ### The adaptive step-up FDR bound -/

/-- **Adaptive step-up FDR bound with the discrete correction** (Döhler–Durand–Roquain 2018,
Theorem 3.1, adaptive form of the second bound). For independent p-values and nondecreasing
nonnegative critical values `c`, if each true-null p-value satisfies `μ.real {p i ≤ t} ≤ F i t`
with `F i (c m) < 1`, and `B ≥ 0` dominates `(1/k) ∑_{i ∈ S} F i (c k) / (1 - F i (c m))` for
`1 ≤ k ≤ m` and every set `S` of true nulls with `|S| ≤ m - k + 1`, then the step-up procedure
rejecting `{j | p j ≤ c (stepUpIndex c p)}` has `E[FDP] ≤ B`.

The proof is that of `integral_falseDiscoveryProportion_stepUp_le`, with one extra count in the
pointwise step: on `{p_i > c m}` the leave-one-out index equals `L + 1`, `L` the shifted step-up
index, and at least `L` p-values are at most `c (L + 1) ≤ c m`, so at most `m - (L + 1) + 1`
true nulls have `p_i > c m`. -/
theorem integral_falseDiscoveryProportion_stepUp_le_adaptive {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    (hindep : iIndepFun p μ) (H0 : Finset (Fin m)) (c : ℕ → ℝ) (hc : Monotone c)
    (hc0 : ∀ k, 0 ≤ c k) (F : Fin m → ℝ → ℝ)
    (hnull : ∀ i ∈ H0, ∀ t, μ.real {ω | p i ω ≤ t} ≤ F i t)
    (hFm : ∀ i ∈ H0, F i (c m) < 1) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ k ∈ Finset.Icc 1 m, ∀ S ⊆ H0, S.card ≤ m - k + 1 →
      (∑ i ∈ S, F i (c k) / (1 - F i (c m))) / k ≤ B) :
    ∫ ω, falseDiscoveryProportion H0
        (Finset.univ.filter fun j => p j ω ≤ c (stepUpIndex c fun j => p j ω)) ∂μ ≤ B := by
  classical
  let K : Fin m → Ω → ℕ := fun i ω => stepUpIndex c (Function.update (fun j => p j ω) i 0)
  let b : Fin m → ℕ → ℝ := fun i k => F i (c k) / (1 - F i (c m)) / k
  have hKmem (i : Fin m) (ω : Ω) : K i ω ∈ Finset.Icc 1 m :=
    Finset.mem_Icc.mpr ⟨one_le_stepUpIndex_update hc0 _ i, stepUpIndex_le c _⟩
  have hF0 (i : Fin m) (hi : i ∈ H0) (t : ℝ) : 0 ≤ F i t :=
    measureReal_nonneg.trans (hnull i hi t)
  have hb0 (i : Fin m) (hi : i ∈ H0) (k : ℕ) : 0 ≤ b i k :=
    div_nonneg (div_nonneg (hF0 i hi _) (sub_nonneg.mpr (hFm i hi).le)) (Nat.cast_nonneg _)
  have hEg (i : Fin m) (k : ℕ) : MeasurableSet {ω | c m < p i ω ∧ K i ω = k} :=
    (measurableSet_lt measurable_const (hp i)).inter
      (measurableSet_eq_fun (measurable_stepUpIndex_update p hp c i) measurable_const)
  let g : Fin m → Ω → ℝ := fun i ω =>
    ∑ k ∈ Finset.Icc 1 m, {ω | c m < p i ω ∧ K i ω = k}.indicator (fun _ => b i k) ω
  -- per-hypothesis step: insert the indicator of `{p i > c m}`
  have hstep (i : Fin m) (hi : i ∈ H0) :
      ∑ k ∈ Finset.Icc 1 m, μ.real {ω | K i ω = k} * (F i (c k) / k) ≤ ∫ ω, g i ω ∂μ := by
    rw [integral_sum_indicator_const μ _ (hEg i)]
    refine Finset.sum_le_sum fun k _ => ?_
    have hind := indepFun_stepUpIndex_update μ p hp hindep c i
    have hr : μ.real {ω | c m < p i ω ∧ K i ω = k} =
        μ.real {ω | c m < p i ω} * μ.real {ω | K i ω = k} := by
      have h := hind.measure_inter_preimage_eq_mul (Set.Ioi (c m)) {k} measurableSet_Ioi
        (measurableSet_singleton k)
      simpa [K, Set.preimage, Set.inter_def, measureReal_def, ENNReal.toReal_mul]
        using congrArg ENNReal.toReal h
    have hgt : 1 - F i (c m) ≤ μ.real {ω | c m < p i ω} := by
      have hc : {ω | c m < p i ω} = {ω | p i ω ≤ c m}ᶜ := by
        ext ω
        simp
      rw [hc, probReal_compl_eq_one_sub (measurableSet_le (hp i) measurable_const)]
      linarith [hnull i hi (c m)]
    have hpos : 0 < 1 - F i (c m) := sub_pos.mpr (hFm i hi)
    have hratio : 1 ≤ μ.real {ω | c m < p i ω} / (1 - F i (c m)) :=
      (one_le_div hpos).mpr hgt
    have hnn : 0 ≤ μ.real {ω | K i ω = k} * (F i (c k) / k) :=
      mul_nonneg measureReal_nonneg (div_nonneg (hF0 i hi _) (Nat.cast_nonneg _))
    rw [hr]
    calc μ.real {ω | K i ω = k} * (F i (c k) / k)
        ≤ μ.real {ω | c m < p i ω} / (1 - F i (c m)) *
            (μ.real {ω | K i ω = k} * (F i (c k) / k)) := le_mul_of_one_le_left hnn hratio
      _ = μ.real {ω | c m < p i ω} * μ.real {ω | K i ω = k} * b i k := by
        simp only [b]
        field_simp
  -- pointwise bound on the sum over the true nulls, using the count `m - k + 1`
  have hpt (ω : Ω) : ∑ i ∈ H0, g i ω ≤ B := by
    have hgi (i : Fin m) : g i ω = if c m < p i ω then b i (K i ω) else 0 :=
      sum_indicator_eq_ite (fun ω => c m < p i ω) (K i) (b i) ω (hKmem i ω)
    simp_rw [hgi]
    by_cases hex : ∃ j ∈ H0, c m < p j ω
    · obtain ⟨j, -, hj⟩ := hex
      set L := stepUpIndex (fun k => c (min (k + 1) m)) fun j => p j ω with hL
      have hshift (i : Fin m) (hi : c m < p i ω) : K i ω = L + 1 :=
        stepUpIndex_update_eq_shift hc hc0 (fun j => p j ω) i hi
      have hLm : L + 1 ∈ Finset.Icc 1 m := hshift j hj ▸ hKmem j ω
      set S := H0.filter fun i => c m < p i ω with hS
      have hcard : S.card ≤ m - (L + 1) + 1 := by
        have h1 : S.card ≤ (Finset.univ.filter fun i => c m < p i ω).card :=
          Finset.card_le_card fun i hi => by
            simp only [hS, Finset.mem_filter] at hi
            simp [hi.2]
        have h2 : (Finset.univ.filter fun i => c m < p i ω).card +
            numBelow (fun j => p j ω) (c m) = m := by
          rw [numBelow]
          have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
            (fun i : Fin m => c m < p i ω)
          simpa [not_lt] using h
        have h3 : L ≤ numBelow (fun j => p j ω) (c m) := by
          have hLle : L ≤ numBelow (fun j => p j ω) (c (min (L + 1) m)) :=
            stepUpIndex_le_numBelow (fun k => c (min (k + 1) m)) (fun j => p j ω)
          exact hLle.trans (numBelow_mono _ (hc (min_le_right _ _)))
        have h4 : L + 1 ≤ m := (Finset.mem_Icc.mp hLm).2
        omega
      calc ∑ i ∈ H0, (if c m < p i ω then b i (K i ω) else 0)
          = ∑ i ∈ S, b i (L + 1) := by
            rw [hS, Finset.sum_filter]
            refine Finset.sum_congr rfl fun i _ => ?_
            by_cases h : c m < p i ω
            · simp [h, hshift i h]
            · simp [h]
        _ = (∑ i ∈ S, F i (c (L + 1)) / (1 - F i (c m))) / ((L + 1 : ℕ) : ℝ) := by
            simp only [b]
            rw [Finset.sum_div]
        _ ≤ B := hB _ hLm S (Finset.filter_subset _ _) hcard
    · push Not at hex
      calc ∑ i ∈ H0, (if c m < p i ω then b i (K i ω) else 0) = 0 :=
            Finset.sum_eq_zero fun i hi => by simp [not_lt.mpr (hex i hi)]
        _ ≤ B := hB0
  have hgint (i : Fin m) : Integrable (g i) μ := integrable_sum_indicator_const μ _ (hEg i) _
  rw [integral_fdp_stepUp_eq_sum μ p hp H0 hc hc0]
  calc ∑ i ∈ H0, ∫ ω, (∑ k ∈ Finset.Icc 1 m,
        {ω | p i ω ≤ c k ∧ stepUpIndex c (Function.update (fun j => p j ω) i 0) = k}.indicator
          (fun _ => 1 / (k : ℝ)) ω) ∂μ
      ≤ ∑ i ∈ H0, ∫ ω, g i ω ∂μ := Finset.sum_le_sum fun i hi =>
        (integral_stepUp_contribution_le μ p hp hindep c i (hnull i hi)).trans (hstep i hi)
    _ = ∫ ω, ∑ i ∈ H0, g i ω ∂μ := (integral_finsetSum H0 fun i _ => hgint i).symm
    _ ≤ ∫ _ω, B ∂μ := integral_mono (integrable_finsetSum H0 fun i _ => hgint i)
        (integrable_const B) hpt
    _ = B := by simp

/-- Pointwise larger critical values give a larger step-up index. -/
theorem stepUpIndex_le_stepUpIndex_of_le {c c' : ℕ → ℝ} (h : ∀ k, c k ≤ c' k)
    (p : Fin m → ℝ) : stepUpIndex c p ≤ stepUpIndex c' p :=
  le_stepUpIndex (stepUpIndex_le c p)
    ((stepUpIndex_le_numBelow c p).trans (numBelow_mono p (h _)))

/-! ### The [A-DBH-SU] procedure -/

/-- The `k`-th critical value of the adaptive discrete BH procedure [A-DBH-SU] at level `α` with
null CDFs `F` and support `A`: the largest `t ∈ A ∪ {0}` with `t ≤ τ_m` (`dbhSULastCritical`) and
`(1/m) · maxSubsetSum (F · t / (1 - F · τ_m)) (m - k + 1) ≤ α k / m`, i.e. the sum of the
`m - k + 1` largest corrected null CDFs is at most `α k` (`0` if no `t ∈ A` qualifies). At `k = m`
this is `τ_m` (`adbhSUCritical_self`). -/
noncomputable def adbhSUCritical (α : ℝ) (F : Fin m → ℝ → ℝ) (A : Finset ℝ) (k : ℕ) : ℝ :=
  (insert 0 (A.filter fun t => t ≤ dbhSULastCritical α F A ∧
    (1 / m : ℝ) * maxSubsetSum (fun i => F i t / (1 - F i (dbhSULastCritical α F A))) (m - k + 1) ≤
      α * k / m)).max' (Finset.insert_nonempty _ _)

/-- The hypotheses rejected by [A-DBH-SU]: the step-up procedure with critical values
`adbhSUCritical α F A` rejects every `i` with `p i ≤ τ_k̂`, `k̂ = stepUpIndex τ p`. -/
noncomputable def adbhSURejections (α : ℝ) (F : Fin m → ℝ → ℝ) (A : Finset ℝ) (p : Fin m → ℝ) :
    Finset (Fin m) :=
  Finset.univ.filter fun i => p i ≤ adbhSUCritical α F A (stepUpIndex (adbhSUCritical α F A) p)

variable {α : ℝ} {F : Fin m → ℝ → ℝ} {A : Finset ℝ}

/-- Every [A-DBH-SU] critical value is nonnegative. -/
theorem adbhSUCritical_nonneg (k : ℕ) : 0 ≤ adbhSUCritical α F A k :=
  Finset.le_max' _ 0 (Finset.mem_insert_self _ _)

/-- Every [A-DBH-SU] critical value is at most `τ_m`. -/
theorem adbhSUCritical_le_last (k : ℕ) : adbhSUCritical α F A k ≤ dbhSULastCritical α F A := by
  apply Finset.max'_le
  intro t ht
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact dbhSULastCritical_nonneg
  · exact (Finset.mem_filter.mp ht).2.1

/-- For `α ≥ 0` the [A-DBH-SU] critical values are nondecreasing: raising `k` lowers the number
`m - k + 1` of summed terms and raises the bound `α k`. -/
theorem monotone_adbhSUCritical (hα : 0 ≤ α) : Monotone (adbhSUCritical α F A) := by
  intro k l hkl
  apply Finset.max'_le
  intro t ht
  apply Finset.le_max'
  simp only [Finset.mem_insert, Finset.mem_filter] at ht ⊢
  rcases ht with rfl | ⟨htA, ht₁, ht₂⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨htA, ht₁, le_trans ?_ (ht₂.trans ?_)⟩
    · exact mul_le_mul_of_nonneg_left (maxSubsetSum_mono_right _ (by omega)) (by positivity)
    · exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hkl) hα) (Nat.cast_nonneg _)

/-- With nonnegative null CDFs vanishing at `0`, each [A-DBH-SU] critical value is at least the
corresponding [DBH-SU] critical value: the sum of the `m - k + 1` largest terms is at most the
full sum. -/
theorem dbhSUCritical_le_adbhSUCritical (hFnn : ∀ i t, 0 ≤ F i t) (hF0 : ∀ i, F i 0 = 0)
    (k : ℕ) : dbhSUCritical α F A k ≤ adbhSUCritical α F A k := by
  apply Finset.max'_le
  intro t ht
  apply Finset.le_max'
  simp only [Finset.mem_insert, Finset.mem_filter] at ht ⊢
  rcases ht with rfl | ⟨htA, ht₁, ht₂⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨htA, ht₁, le_trans ?_ ht₂⟩
    refine mul_le_mul_of_nonneg_left (maxSubsetSum_le_sum (fun i => ?_) _) (by positivity)
    exact div_nonneg (hFnn _ _)
      (sub_nonneg.mpr (lt_one_of_dbhSULastCritical (α := α) (A := A) hF0 i).le)

/-- At `k = m` the [A-DBH-SU] critical value is `τ_m`. -/
theorem adbhSUCritical_self (hFnn : ∀ i t, 0 ≤ F i t) (hF0 : ∀ i, F i 0 = 0) :
    adbhSUCritical α F A m = dbhSULastCritical α F A :=
  le_antisymm (adbhSUCritical_le_last m)
    ((dbhSUCritical_self (α := α) (F := F) (A := A)).symm.le.trans
      (dbhSUCritical_le_adbhSUCritical hFnn hF0 m))

/-- With `F i 0 = 0` and `α ≥ 0`, every [A-DBH-SU] critical value satisfies its defining
inequality. -/
theorem adbhSUCritical_spec (hF0 : ∀ i, F i 0 = 0) (hα : 0 ≤ α) (k : ℕ) :
    (1 / m : ℝ) * maxSubsetSum
        (fun i => F i (adbhSUCritical α F A k) / (1 - F i (dbhSULastCritical α F A))) (m - k + 1) ≤
      α * k / m := by
  rcases Finset.mem_insert.mp (Finset.max'_mem _ (Finset.insert_nonempty 0 (A.filter fun t =>
      t ≤ dbhSULastCritical α F A ∧ (1 / m : ℝ) * maxSubsetSum
        (fun i => F i t / (1 - F i (dbhSULastCritical α F A))) (m - k + 1) ≤ α * k / m))) with h | h
  · rw [adbhSUCritical, h]
    simp only [hF0, zero_div, maxSubsetSum_zero, mul_zero]
    positivity
  · exact (Finset.mem_filter.mp h).2.2

/-- **FDR control of the adaptive discrete BH procedure [A-DBH-SU].** Let the p-values be
independent, let the null CDFs satisfy `0 ≤ F i t` and `F i 0 = 0`, and let every true-null
p-value satisfy `μ.real {p i ≤ t} ≤ F i t`. Then [A-DBH-SU] at level `α ≥ 0`, with any finite
support set `A`, has false discovery rate at most `α`. As for [DBH-SU], nothing is assumed about
the false-null p-values beyond measurability and independence. -/
theorem integral_falseDiscoveryProportion_adbhSURejections_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    (hindep : iIndepFun p μ) (H0 : Finset (Fin m)) (F : Fin m → ℝ → ℝ)
    (hFnn : ∀ i t, 0 ≤ F i t) (hF0 : ∀ i, F i 0 = 0)
    (hnull : ∀ i ∈ H0, ∀ t, μ.real {ω | p i ω ≤ t} ≤ F i t) (A : Finset ℝ) (α : ℝ)
    (hα : 0 ≤ α) :
    ∫ ω, falseDiscoveryProportion H0 (adbhSURejections α F A fun i => p i ω) ∂μ ≤ α := by
  have hself := adbhSUCritical_self (α := α) (A := A) hFnn hF0
  refine integral_falseDiscoveryProportion_stepUp_le_adaptive μ p hp hindep H0
    (adbhSUCritical α F A) (monotone_adbhSUCritical hα) adbhSUCritical_nonneg F hnull
    (fun i _ => hself ▸ lt_one_of_dbhSULastCritical (α := α) (A := A) hF0 i) α hα
    fun k hk S _ hS => ?_
  obtain ⟨hk1, hkm⟩ := Finset.mem_Icc.mp hk
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hspec := adbhSUCritical_spec (A := A) hF0 hα k
  rw [← hself] at hspec
  have hall : maxSubsetSum (fun i => F i (adbhSUCritical α F A k) /
      (1 - F i (adbhSUCritical α F A m))) (m - k + 1) ≤ α * k := by
    have h := mul_le_mul_of_nonneg_left hspec hm.le
    rwa [← mul_assoc, mul_one_div_cancel hm.ne', one_mul, mul_div_cancel₀ _ hm.ne'] at h
  rw [div_le_iff₀ hk0]
  exact (sum_le_maxSubsetSum _ hS).trans hall

/-- **[A-DBH-SU] is at least as powerful as [DBH-SU]**: with nonnegative null CDFs vanishing at
`0` and `α ≥ 0`, every hypothesis rejected by [DBH-SU] is rejected by [A-DBH-SU]. -/
theorem dbhSURejections_subset_adbhSURejections (hFnn : ∀ i t, 0 ≤ F i t)
    (hF0 : ∀ i, F i 0 = 0) (hα : 0 ≤ α) (p : Fin m → ℝ) :
    dbhSURejections α F A p ⊆ adbhSURejections α F A p := by
  intro i hi
  simp only [dbhSURejections, adbhSURejections, Finset.mem_filter, Finset.mem_univ,
    true_and] at hi ⊢
  exact hi.trans ((dbhSUCritical_le_adbhSUCritical hFnn hF0 _).trans
    (monotone_adbhSUCritical hα (stepUpIndex_le_stepUpIndex_of_le
      (c := dbhSUCritical α F A) (c' := adbhSUCritical α F A)
      (fun k => dbhSUCritical_le_adbhSUCritical hFnn hF0 k) p)))

end MathlibExt.Probability.Statistics.MultipleTesting
