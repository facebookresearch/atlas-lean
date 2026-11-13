/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.Independence.Basic

/-!
# Discrete Benjamini–Hochberg: FDR control with discrete null distributions

For discrete tests (Fisher's exact test, binomial or permutation tests) the true-null p-values are
valid but not uniform. Writing `F_i(t) = P_{H_i}(p_i ≤ t)` for the (known) null CDF of the `i`-th
p-value, typically `F_i(t) = t` only on the finite support `𝒜_i` of `p_i`; on the overall support
`𝒜 = ⋃ᵢ 𝒜_i` many `F_i(t)` are much smaller than `t`, and some vanish when hypothesis `i` cannot
reach significance `t`. The Benjamini–Hochberg (BH) procedure, with critical values `α k / m`,
only uses `F_i(t) ≤ t` and is then conservative.

Heyse (2011) replaced `t` by the average `(1/m) ∑ᵢ F_i(t)` in the BH adjusted p-values; Heller and
Gur (2011, §2.2) showed by an explicit counterexample (two independent discrete p-values,
`α = 0.05`, FDR `0.050025`) that this does not control the FDR. Döhler, Durand and Roquain
(2018) corrected it. Their step-up procedure **[DBH-SU]** at level `α` uses the critical values

* `τ_m = max {t ∈ 𝒜 : (1/m) ∑ᵢ F_i(t) / (1 - F_i(t)) ≤ α}`,
* `τ_k = max {t ∈ 𝒜 : t ≤ τ_m, (1/m) ∑ᵢ F_i(t) / (1 - F_i(τ_m)) ≤ α k / m}` for `k < m`,

and rejects every hypothesis with `p_i ≤ τ_k̂`, where `k̂` is the largest `k` with
`p₍ₖ₎ ≤ τ_k` (`stepUpIndex τ p`). Hypotheses whose null distribution puts little mass below `t`
contribute little to the sums, which is how the discreteness is exploited.

## Conventions

* The null CDFs are inputs `F : Fin m → ℝ → ℝ` and the support is a `Finset` `A`. The data constrain
  only the true nulls: for `i ∈ H0`, `μ.real {p i ≤ t} ≤ F i t` (equality is the exact null
  distribution; `≤` covers composite nulls through their least favourable configuration). The
  false-null p-values are arbitrary apart from measurability and independence.
* `F_i(t) / (1 - F_i(t)) = ∞` when `F_i(t) = 1`, so the defining set of `τ_m` also requires
  `F_i(t) < 1` for every `i`; Lean's `x / 0 = 0` would otherwise accept such `t`.
* `0` is adjoined to both defining sets as a sentinel, not as a point of the support: it
  implements the convention that the maximum of an empty candidate set is `0`, and makes the
  maxima total. With `F_i(0) = 0` (so `0` carries no null mass and is not a support point),
  `t = 0` satisfies both defining inequalities (`dbhSUCritical_spec`). `dbhSUCritical α F A k` is
  defined by the second formula for every `k`; at `k = m` it equals `τ_m` (`dbhSUCritical_self`),
  as the first formula requires.

## Main results

* `stepUpIndex_update_eq_shift`: if `p_i > c m`, the step-up index with `p_i` replaced by `0`
  equals one plus the step-up index for the shifted critical values `(c 2, …, c m, c m)`
  (Döhler–Durand–Roquain, Lemma A.1, last assertion).
* `integral_falseDiscoveryProportion_stepUp_le_sum`: for independent p-values and any
  nondecreasing nonnegative critical values `c`, `E[FDP] ≤ ∑_{i ∈ H0} max_{1 ≤ k ≤ m} F_i(c k) / k`
  (Döhler–Durand–Roquain, Theorem 3.1, first bound in (3.1)).
* `integral_falseDiscoveryProportion_stepUp_le`: for the same procedures,
  `E[FDP] ≤ max_{1 ≤ k ≤ m} (1/k) ∑_{i ∈ H0} F_i(c k) / (1 - F_i(c m))`
  (Döhler–Durand–Roquain, (3.6), the non-adaptive form of the second bound of Theorem 3.1; the sum
  over `H0` is at most their sum over all `m` hypotheses).
* `integral_falseDiscoveryProportion_dbhSURejections_le`: **[DBH-SU] controls the FDR at level
  `α`** for independent p-values (Döhler–Durand–Roquain, Corollary 3.3).

Both FDR bounds are stated with an explicit bound (`b i`, resp. `B`) dominating the maximum. The
adaptive refinement of Theorem 3.1 (maximum over subsets of size `m - k + 1`), its step-down half,
and the comparison of [DBH-SU] with BH at level `α / (1 + α)` (Lemma 2.3) are not formalized.
Döhler–Durand–Roquain assume independence throughout; no PRDS or arbitrary-dependence version is
claimed.

## References

* S. Döhler, G. Durand and E. Roquain, *New FDR bounds for discrete and heterogeneous tests*,
  Electron. J. Statist. 12 (2018), 1867–1900 (arXiv:1706.08250), §2.3, Theorem 3.1, (3.6),
  Corollary 3.3, Lemma A.1.
* R. Heller and H. Gur, *False discovery rate controlling procedures for discrete tests*,
  arXiv:1112.4627v2 (2012), §2.2.
* J. F. Heyse, *A false discovery rate procedure for categorical data*, in *Recent Advances in
  Biostatistics*, World Scientific (2011), 43–58.
* Y. Benjamini and Y. Hochberg, *Controlling the false discovery rate: a practical and powerful
  approach to multiple testing*, J. R. Statist. Soc. B 57 (1995), 289–300.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory ProbabilityTheory

variable {m : ℕ}

/-! ### Combinatorics of step-up procedures -/

/-- Replacing a p-value `p i > t` by `0` raises the count below `t ≥ 0` by one. -/
private theorem numBelow_update_eq_succ (p : Fin m → ℝ) (i : Fin m) {t : ℝ} (ht : 0 ≤ t)
    (hti : t < p i) : numBelow (Function.update p i 0) t = numBelow p t + 1 := by
  classical
  unfold numBelow
  have h : (Finset.univ.filter fun j => Function.update p i 0 j ≤ t) =
      insert i (Finset.univ.filter fun j => p j ≤ t) := by
    ext j
    by_cases hji : j = i
    · subst hji; simp [ht]
    · simp [hji]
  rw [h, Finset.card_insert_of_notMem (by simp [not_le.mpr hti])]

/-- If some p-value exceeds `t`, fewer than `m` p-values are at most `t`. -/
private theorem numBelow_lt (p : Fin m → ℝ) (i : Fin m) {t : ℝ} (hti : t < p i) :
    numBelow p t < m := by
  classical
  have h := Finset.card_lt_card
    (Finset.filter_ssubset.mpr ⟨i, Finset.mem_univ _, not_le.mpr hti⟩ :
      (Finset.univ.filter fun j => p j ≤ t) ⊂ Finset.univ)
  simpa [numBelow] using h

/-- **Shifted leave-one-out identity** (Döhler–Durand–Roquain 2018, Lemma A.1, last assertion).
For nondecreasing nonnegative critical values `c` and `p i > c m`, the step-up index of `p` with
`p i` replaced by `0` is one more than the step-up index of `p` for the shifted critical values
`(c 2, …, c m, c m)`. The right-hand side does not depend on `i`. -/
theorem stepUpIndex_update_eq_shift {c : ℕ → ℝ} (hc : Monotone c) (hc0 : ∀ k, 0 ≤ c k)
    (p : Fin m → ℝ) (i : Fin m) (hpi : c m < p i) :
    stepUpIndex c (Function.update p i 0) = stepUpIndex (fun k => c (min (k + 1) m)) p + 1 := by
  set c' : ℕ → ℝ := fun k => c (min (k + 1) m) with hc'
  set K := stepUpIndex c (Function.update p i 0) with hK
  set L := stepUpIndex c' p with hL
  have hlt (k : ℕ) (hk : k ≤ m) : c k < p i := (hc hk).trans_lt hpi
  have hLm : L < m := lt_of_le_of_lt (stepUpIndex_le_numBelow c' p)
    (numBelow_lt p i (hlt (min (L + 1) m) (min_le_right _ _)))
  have hK1 : 1 ≤ K := one_le_stepUpIndex_update hc0 p i
  have hKm : K ≤ m := stepUpIndex_le c _
  apply le_antisymm
  · have h : K - 1 ≤ L := by
      apply le_stepUpIndex (by omega)
      have hmin : min (K - 1 + 1) m = K := by omega
      have hKle : K ≤ numBelow (Function.update p i 0) (c K) :=
        stepUpIndex_le_numBelow c (Function.update p i 0)
      rw [numBelow_update_eq_succ p i (hc0 _) (hlt K hKm)] at hKle
      simp only [hc', hmin]
      omega
    omega
  · apply le_stepUpIndex (by omega)
    rw [numBelow_update_eq_succ p i (hc0 _) (hlt _ (by omega))]
    have h : L ≤ numBelow p (c' L) := stepUpIndex_le_numBelow c' p
    have hmin : min (L + 1) m = L + 1 := by omega
    simp only [hc', hmin] at h
    omega

/-- Leave-one-out decomposition of the FDP contribution of hypothesis `i` for a step-up procedure
with nondecreasing nonnegative critical values. -/
private theorem stepUp_contribution_eq_sum {c : ℕ → ℝ} (hc : Monotone c) (hc0 : ∀ k, 0 ≤ c k)
    (p : Fin m → ℝ) (i : Fin m) :
    (if i ∈ Finset.univ.filter (fun j => p j ≤ c (stepUpIndex c p)) then
        1 / max ((Finset.univ.filter fun j => p j ≤ c (stepUpIndex c p)).card : ℝ) 1 else 0) =
      ∑ k ∈ Finset.Icc 1 m,
        if p i ≤ c k ∧ stepUpIndex c (Function.update p i 0) = k then 1 / (k : ℝ) else 0 := by
  classical
  have hcard : (Finset.univ.filter fun j => p j ≤ c (stepUpIndex c p)).card = stepUpIndex c p :=
    numBelow_stepUpIndex hc p
  rw [hcard]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp_rw [← stepUp_leave_one_out hc hc0 p i]
  by_cases hi : p i ≤ c (stepUpIndex c p)
  · have hpos : 1 ≤ stepUpIndex c p := by
      have h : 0 < numBelow p (c (stepUpIndex c p)) :=
        Finset.card_pos.mpr ⟨i, by simp [hi]⟩
      rw [numBelow_stepUpIndex hc p] at h
      omega
    rw [Finset.sum_eq_single (stepUpIndex c p)]
    · simp [hi, max_eq_left (show (1 : ℝ) ≤ stepUpIndex c p by exact_mod_cast hpos)]
    · intro k _ hk
      simp [Ne.symm hk]
    · intro h
      exact (h (Finset.mem_Icc.mpr ⟨hpos, stepUpIndex_le c p⟩)).elim
  · simp [hi]

/-! ### Independence and measurability of the leave-one-out index -/

private theorem measurable_stepUpIndex_update {Ω : Type*} [MeasurableSpace Ω]
    (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i)) (c : ℕ → ℝ) (i : Fin m) :
    Measurable fun ω => stepUpIndex c (Function.update (fun j => p j ω) i 0) := by
  classical
  apply measurable_stepUpIndex_comp (fun _ => c) _ (fun _ => measurable_const)
  intro j
  by_cases hji : j = i <;> simp only [Function.update_apply, hji, ite_true, ite_false]
  · exact measurable_const
  · exact hp j

private theorem indepFun_stepUpIndex_update {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    (hindep : iIndepFun p μ) (c : ℕ → ℝ) (i : Fin m) :
    IndepFun (p i) (fun ω => stepUpIndex c (Function.update (fun j => p j ω) i 0)) μ := by
  classical
  let S : Set (Fin m) := {i}
  let T : Set (Fin m) := {j | j ≠ i}
  let g : (T → ℝ) → ℕ := fun x => stepUpIndex c (fun j => if h : j = i then 0 else x ⟨j, h⟩)
  have hg : Measurable g := by
    refine measurable_stepUpIndex_comp (fun _ => c)
      (fun (x : T → ℝ) j => if h : j = i then 0 else x ⟨j, h⟩) (fun _ => measurable_const) ?_
    intro j
    by_cases h : j = i
    · simp only [h, dite_true]
      exact measurable_const
    · simp only [h, dite_false]
      exact measurable_pi_apply (⟨j, h⟩ : T)
  have hST : Disjoint S T :=
    Set.disjoint_left.mpr fun j hj hj' => hj' (Set.mem_singleton_iff.mp hj)
  have h := (iIndepFun.indepFun_set S T hST hindep hp).comp
    (measurable_pi_apply (⟨i, Set.mem_singleton i⟩ : S)) hg
  have heq : (fun ω => stepUpIndex c (Function.update (fun j => p j ω) i 0)) =
      g ∘ (fun ω (j : T) => p j ω) := by
    funext ω
    dsimp [g]
    congr 1
    funext j
    by_cases hji : j = i <;> simp [hji]
  rw [heq]
  exact h

/-- The expectation of a finite sum of indicators of constants. -/
private theorem integral_sum_indicator_const {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (s : Finset ℕ) {E : ℕ → Set Ω} (hE : ∀ k, MeasurableSet (E k))
    (a : ℕ → ℝ) :
    ∫ ω, ∑ k ∈ s, (E k).indicator (fun _ => a k) ω ∂μ = ∑ k ∈ s, μ.real (E k) * a k := by
  rw [integral_finsetSum s fun k _ => (integrable_const (a k)).indicator (hE k)]
  simp_rw [integral_indicator_const _ (hE _), smul_eq_mul]

private theorem integrable_sum_indicator_const {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (s : Finset ℕ) {E : ℕ → Set Ω} (hE : ∀ k, MeasurableSet (E k))
    (a : ℕ → ℝ) : Integrable (fun ω => ∑ k ∈ s, (E k).indicator (fun _ => a k) ω) μ :=
  integrable_finsetSum s fun k _ => (integrable_const (a k)).indicator (hE k)

/-- The leave-one-out index takes values in `{1, …, m}`, so its law sums to one there. -/
private theorem sum_measureReal_stepUpIndex_update {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    {c : ℕ → ℝ} (hc0 : ∀ k, 0 ≤ c k) (i : Fin m) :
    ∑ k ∈ Finset.Icc 1 m,
      μ.real {ω | stepUpIndex c (Function.update (fun j => p j ω) i 0) = k} = 1 := by
  have hK := measurable_stepUpIndex_update p hp c i
  have hpre : (fun ω => stepUpIndex c (Function.update (fun j => p j ω) i 0)) ⁻¹'
      (↑(Finset.Icc 1 m) : Set ℕ) = Set.univ := by
    ext ω
    simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_univ, iff_true]
    exact ⟨one_le_stepUpIndex_update hc0 _ i, stepUpIndex_le c _⟩
  have h := sum_measureReal_preimage_singleton (μ := μ) (Finset.Icc 1 m)
    (fun k _ => hK (measurableSet_singleton k))
  rw [hpre] at h
  simpa [Set.preimage, measureReal_def] using h

/-- The step-up FDR as a sum over true nulls of the expected leave-one-out contributions. -/
private theorem integral_fdp_stepUp_eq_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    (H0 : Finset (Fin m)) {c : ℕ → ℝ} (hc : Monotone c) (hc0 : ∀ k, 0 ≤ c k) :
    ∫ ω, falseDiscoveryProportion H0
        (Finset.univ.filter fun j => p j ω ≤ c (stepUpIndex c fun j => p j ω)) ∂μ =
      ∑ i ∈ H0, ∫ ω, (∑ k ∈ Finset.Icc 1 m,
        {ω | p i ω ≤ c k ∧ stepUpIndex c (Function.update (fun j => p j ω) i 0) = k}.indicator
          (fun _ => 1 / (k : ℝ)) ω) ∂μ := by
  classical
  have hE (i : Fin m) (k : ℕ) : MeasurableSet
      {ω | p i ω ≤ c k ∧ stepUpIndex c (Function.update (fun j => p j ω) i 0) = k} :=
    (measurableSet_le (hp i) measurable_const).inter
      (measurableSet_eq_fun (measurable_stepUpIndex_update p hp c i) measurable_const)
  rw [← integral_finsetSum H0 fun i _ => integrable_sum_indicator_const μ _ (hE i) _]
  congr 1
  funext ω
  rw [fdp_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := stepUp_contribution_eq_sum hc hc0 (fun j => p j ω) i
  rw [h]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

/-- For a true null `i` with `μ.real {p i ≤ t} ≤ F t`, the expected contribution is at most
`∑ₖ P(K = k) F(c k) / k`, `K` the leave-one-out index (independent of `p i`). -/
private theorem integral_stepUp_contribution_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    (hindep : iIndepFun p μ) (c : ℕ → ℝ) (i : Fin m) {F : ℝ → ℝ}
    (hnull : ∀ t, μ.real {ω | p i ω ≤ t} ≤ F t) :
    ∫ ω, (∑ k ∈ Finset.Icc 1 m,
        {ω | p i ω ≤ c k ∧ stepUpIndex c (Function.update (fun j => p j ω) i 0) = k}.indicator
          (fun _ => 1 / (k : ℝ)) ω) ∂μ ≤
      ∑ k ∈ Finset.Icc 1 m,
        μ.real {ω | stepUpIndex c (Function.update (fun j => p j ω) i 0) = k} * (F (c k) / k) := by
  classical
  have hK := measurable_stepUpIndex_update p hp c i
  have hind := indepFun_stepUpIndex_update μ p hp hindep c i
  have hE (k : ℕ) : MeasurableSet
      {ω | p i ω ≤ c k ∧ stepUpIndex c (Function.update (fun j => p j ω) i 0) = k} :=
    (measurableSet_le (hp i) measurable_const).inter (measurableSet_eq_fun hK measurable_const)
  rw [integral_sum_indicator_const μ _ hE]
  refine Finset.sum_le_sum fun k _ => ?_
  have hr : μ.real {ω | p i ω ≤ c k ∧
        stepUpIndex c (Function.update (fun j => p j ω) i 0) = k} =
      μ.real {ω | p i ω ≤ c k} *
        μ.real {ω | stepUpIndex c (Function.update (fun j => p j ω) i 0) = k} := by
    have h := hind.measure_inter_preimage_eq_mul (Set.Iic (c k)) {k} measurableSet_Iic
      (measurableSet_singleton k)
    simpa [Set.preimage, Set.inter_def, measureReal_def, ENNReal.toReal_mul]
      using congrArg ENNReal.toReal h
  rw [hr]
  have hk : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  calc μ.real {ω | p i ω ≤ c k} *
        μ.real {ω | stepUpIndex c (Function.update (fun j => p j ω) i 0) = k} * (1 / k)
      ≤ F (c k) * μ.real {ω | stepUpIndex c (Function.update (fun j => p j ω) i 0) = k} *
          (1 / k) := by
        gcongr
        exact hnull _
    _ = _ := by ring

/-- **Step-up FDR bound, heterogeneous form** (Döhler–Durand–Roquain 2018, Theorem 3.1, first
bound in (3.1)). For independent p-values and nondecreasing nonnegative critical values `c`, if
each true-null p-value satisfies `μ.real {p i ≤ t} ≤ F i t` and `b i` dominates
`F i (c k) / k` for `1 ≤ k ≤ m` (so `b i = max_k F i (c k) / k` is allowed), the step-up procedure
rejecting `{j | p j ≤ c (stepUpIndex c p)}` has `E[FDP] ≤ ∑_{i ∈ H0} b i`. With `F i t = t` and
`c k = α k / m` this is the BH bound `α |H0| / m`. -/
theorem integral_falseDiscoveryProportion_stepUp_le_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    (hindep : iIndepFun p μ) (H0 : Finset (Fin m)) (c : ℕ → ℝ) (hc : Monotone c)
    (hc0 : ∀ k, 0 ≤ c k) (F : Fin m → ℝ → ℝ)
    (hnull : ∀ i ∈ H0, ∀ t, μ.real {ω | p i ω ≤ t} ≤ F i t) (b : Fin m → ℝ)
    (hb : ∀ i ∈ H0, ∀ k ∈ Finset.Icc 1 m, F i (c k) / k ≤ b i) :
    ∫ ω, falseDiscoveryProportion H0
        (Finset.univ.filter fun j => p j ω ≤ c (stepUpIndex c fun j => p j ω)) ∂μ ≤
      ∑ i ∈ H0, b i := by
  rw [integral_fdp_stepUp_eq_sum μ p hp H0 hc hc0]
  refine Finset.sum_le_sum fun i hi => (integral_stepUp_contribution_le μ p hp hindep c i
    (hnull i hi)).trans ?_
  calc ∑ k ∈ Finset.Icc 1 m,
        μ.real {ω | stepUpIndex c (Function.update (fun j => p j ω) i 0) = k} * (F i (c k) / k)
      ≤ ∑ k ∈ Finset.Icc 1 m,
        μ.real {ω | stepUpIndex c (Function.update (fun j => p j ω) i 0) = k} * b i :=
        Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hb i hi k hk) measureReal_nonneg
    _ = b i := by rw [← Finset.sum_mul, sum_measureReal_stepUpIndex_update μ p hp hc0 i, one_mul]

private theorem sum_indicator_eq_ite {Ω : Type*} (P : Ω → Prop) [DecidablePred P] (K : Ω → ℕ)
    (a : ℕ → ℝ) (ω : Ω) (hK : K ω ∈ Finset.Icc 1 m) :
    ∑ k ∈ Finset.Icc 1 m, {ω | P ω ∧ K ω = k}.indicator (fun _ => a k) ω =
      if P ω then a (K ω) else 0 := by
  classical
  rw [Finset.sum_eq_single (K ω)]
  · by_cases h : P ω <;> simp [h]
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact (h hK).elim

/-- **Step-up FDR bound with the discrete correction** (Döhler–Durand–Roquain 2018, (3.6), the
non-adaptive form of the second bound of Theorem 3.1). For independent p-values and
nondecreasing nonnegative critical values `c`, if each true-null p-value satisfies
`μ.real {p i ≤ t} ≤ F i t` with `F i (c m) < 1`, and `B ≥ 0` dominates
`(1/k) ∑_{i ∈ H0} F i (c k) / (1 - F i (c m))` for `1 ≤ k ≤ m`, then the step-up procedure
rejecting `{j | p j ≤ c (stepUpIndex c p)}` has `E[FDP] ≤ B`.

The proof follows Döhler–Durand–Roquain: by independence, the contribution of a true null `i` is
at most `E[F_i(c K) / K] ≤ E[F_i(c K) / K · 1{p_i > c m}] / (1 - F_i(c m))`, `K` the leave-one-out
index; on `{p_i > c m}` the index `K` equals the shifted index plus one
(`stepUpIndex_update_eq_shift`), which no longer depends on `i`, so the sum over `i ∈ H0` can be
bounded pointwise. -/
theorem integral_falseDiscoveryProportion_stepUp_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    (hindep : iIndepFun p μ) (H0 : Finset (Fin m)) (c : ℕ → ℝ) (hc : Monotone c)
    (hc0 : ∀ k, 0 ≤ c k) (F : Fin m → ℝ → ℝ)
    (hnull : ∀ i ∈ H0, ∀ t, μ.real {ω | p i ω ≤ t} ≤ F i t)
    (hFm : ∀ i ∈ H0, F i (c m) < 1) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ k ∈ Finset.Icc 1 m, (∑ i ∈ H0, F i (c k) / (1 - F i (c m))) / k ≤ B) :
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
  -- pointwise bound on the sum over the true nulls
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
      calc ∑ i ∈ H0, (if c m < p i ω then b i (K i ω) else 0)
          ≤ ∑ i ∈ H0, b i (L + 1) := Finset.sum_le_sum fun i hi => by
            split_ifs with h
            · rw [hshift i h]
            · exact hb0 i hi _
        _ = (∑ i ∈ H0, F i (c (L + 1)) / (1 - F i (c m))) / ((L + 1 : ℕ) : ℝ) := by
            simp only [b]
            rw [Finset.sum_div]
        _ ≤ B := hB _ hLm
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

/-! ### The [DBH-SU] procedure -/

/-- The last critical value `τ_m` of [DBH-SU] at level `α` with null CDFs `F` and support `A`: the
largest `t ∈ A ∪ {0}` such that `F i t < 1` for every `i` and
`(1/m) ∑ᵢ F i t / (1 - F i t) ≤ α` (`0` if no `t ∈ A` qualifies). -/
noncomputable def dbhSULastCritical (α : ℝ) (F : Fin m → ℝ → ℝ) (A : Finset ℝ) : ℝ :=
  (insert 0 (A.filter fun t =>
    (∀ i, F i t < 1) ∧ (1 / m : ℝ) * ∑ i, F i t / (1 - F i t) ≤ α)).max'
    (Finset.insert_nonempty _ _)

/-- The `k`-th critical value `τ_k` of [DBH-SU]: the largest `t ∈ A ∪ {0}` with `t ≤ τ_m` and
`(1/m) ∑ᵢ F i t / (1 - F i τ_m) ≤ α k / m` (`0` if no `t ∈ A` qualifies). At `k = m` this is
`τ_m` (`dbhSUCritical_self`). -/
noncomputable def dbhSUCritical (α : ℝ) (F : Fin m → ℝ → ℝ) (A : Finset ℝ) (k : ℕ) : ℝ :=
  (insert 0 (A.filter fun t => t ≤ dbhSULastCritical α F A ∧
    (1 / m : ℝ) * ∑ i, F i t / (1 - F i (dbhSULastCritical α F A)) ≤ α * k / m)).max'
    (Finset.insert_nonempty _ _)

/-- The hypotheses rejected by [DBH-SU]: the step-up procedure with critical values
`dbhSUCritical α F A` rejects every `i` with `p i ≤ τ_k̂`, `k̂ = stepUpIndex τ p`. -/
noncomputable def dbhSURejections (α : ℝ) (F : Fin m → ℝ → ℝ) (A : Finset ℝ) (p : Fin m → ℝ) :
    Finset (Fin m) :=
  Finset.univ.filter fun i => p i ≤ dbhSUCritical α F A (stepUpIndex (dbhSUCritical α F A) p)

variable {α : ℝ} {F : Fin m → ℝ → ℝ} {A : Finset ℝ}

/-- `τ_m ≥ 0`. -/
theorem dbhSULastCritical_nonneg : 0 ≤ dbhSULastCritical α F A :=
  Finset.le_max' _ 0 (Finset.mem_insert_self _ _)

/-- Every [DBH-SU] critical value is nonnegative. -/
theorem dbhSUCritical_nonneg (k : ℕ) : 0 ≤ dbhSUCritical α F A k :=
  Finset.le_max' _ 0 (Finset.mem_insert_self _ _)

/-- Every [DBH-SU] critical value is at most `τ_m`. -/
theorem dbhSUCritical_le_last (k : ℕ) : dbhSUCritical α F A k ≤ dbhSULastCritical α F A := by
  apply Finset.max'_le
  intro t ht
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact dbhSULastCritical_nonneg
  · exact (Finset.mem_filter.mp ht).2.1

/-- For `α ≥ 0` the [DBH-SU] critical values are nondecreasing. -/
theorem monotone_dbhSUCritical (hα : 0 ≤ α) : Monotone (dbhSUCritical α F A) := by
  intro k l hkl
  apply Finset.max'_le
  intro t ht
  apply Finset.le_max'
  simp only [Finset.mem_insert, Finset.mem_filter] at ht ⊢
  rcases ht with rfl | ⟨htA, ht₁, ht₂⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨htA, ht₁, ht₂.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hkl) hα) (Nat.cast_nonneg _))⟩

/-- At `k = m` the second formula gives back `τ_m`. -/
theorem dbhSUCritical_self : dbhSUCritical α F A m = dbhSULastCritical α F A := by
  refine le_antisymm (dbhSUCritical_le_last m) (Finset.le_max' _ _ ?_)
  rcases Finset.mem_insert.mp (Finset.max'_mem _ (Finset.insert_nonempty 0 (A.filter fun t =>
      (∀ i, F i t < 1) ∧ (1 / m : ℝ) * ∑ i, F i t / (1 - F i t) ≤ α))) with h | h
  · rw [dbhSULastCritical, h]
    exact Finset.mem_insert_self _ _
  · rw [Finset.mem_filter] at h
    refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h.1, le_rfl, ?_⟩)
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp
    · rw [mul_div_assoc, div_self (by exact_mod_cast hm.ne'), mul_one]
      exact h.2.2

/-- With `F i 0 = 0`, every null CDF stays below `1` at `τ_m`. -/
theorem lt_one_of_dbhSULastCritical (hF0 : ∀ i, F i 0 = 0) (i : Fin m) :
    F i (dbhSULastCritical α F A) < 1 := by
  rcases Finset.mem_insert.mp (Finset.max'_mem _ (Finset.insert_nonempty 0 (A.filter fun t =>
      (∀ i, F i t < 1) ∧ (1 / m : ℝ) * ∑ i, F i t / (1 - F i t) ≤ α))) with h | h
  · rw [dbhSULastCritical, h, hF0]
    exact one_pos
  · exact (Finset.mem_filter.mp h).2.1 i

/-- With `F i 0 = 0` and `α ≥ 0`, every [DBH-SU] critical value satisfies its defining
inequality. -/
theorem dbhSUCritical_spec (hF0 : ∀ i, F i 0 = 0) (hα : 0 ≤ α) (k : ℕ) :
    (1 / m : ℝ) * ∑ i, F i (dbhSUCritical α F A k) / (1 - F i (dbhSULastCritical α F A)) ≤
      α * k / m := by
  rcases Finset.mem_insert.mp (Finset.max'_mem _ (Finset.insert_nonempty 0 (A.filter fun t =>
      t ≤ dbhSULastCritical α F A ∧ (1 / m : ℝ) *
        ∑ i, F i t / (1 - F i (dbhSULastCritical α F A)) ≤ α * k / m))) with h | h
  · rw [dbhSUCritical, h]
    simp only [hF0, zero_div, Finset.sum_const_zero, mul_zero]
    positivity
  · exact (Finset.mem_filter.mp h).2.2

/-- **FDR control of the discrete BH procedure [DBH-SU]** (Döhler–Durand–Roquain 2018,
Corollary 3.3). Let the p-values be independent, let the null CDFs satisfy `0 ≤ F i t` and
`F i 0 = 0`, and let every true-null p-value satisfy `μ.real {p i ≤ t} ≤ F i t`. Then [DBH-SU] at
level `α ≥ 0`, with any finite support set `A`, has false discovery rate at most `α`. Nothing is
assumed about the false-null p-values beyond measurability and independence, and super-uniformity
`F i t ≤ t` is not needed. -/
theorem integral_falseDiscoveryProportion_dbhSURejections_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    (hindep : iIndepFun p μ) (H0 : Finset (Fin m)) (F : Fin m → ℝ → ℝ)
    (hFnn : ∀ i t, 0 ≤ F i t) (hF0 : ∀ i, F i 0 = 0)
    (hnull : ∀ i ∈ H0, ∀ t, μ.real {ω | p i ω ≤ t} ≤ F i t) (A : Finset ℝ) (α : ℝ)
    (hα : 0 ≤ α) :
    ∫ ω, falseDiscoveryProportion H0 (dbhSURejections α F A fun i => p i ω) ∂μ ≤ α := by
  refine integral_falseDiscoveryProportion_stepUp_le μ p hp hindep H0 (dbhSUCritical α F A)
    (monotone_dbhSUCritical hα) dbhSUCritical_nonneg F hnull
    (fun i _ => dbhSUCritical_self (α := α) (F := F) (A := A) ▸
      lt_one_of_dbhSULastCritical hF0 i) α hα fun k hk => ?_
  obtain ⟨hk1, hkm⟩ := Finset.mem_Icc.mp hk
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hterm (i : Fin m) : 0 ≤ F i (dbhSUCritical α F A k) /
      (1 - F i (dbhSUCritical α F A m)) := by
    rw [dbhSUCritical_self]
    exact div_nonneg (hFnn _ _) (sub_nonneg.mpr (lt_one_of_dbhSULastCritical hF0 i).le)
  have hsub : ∑ i ∈ H0, F i (dbhSUCritical α F A k) / (1 - F i (dbhSUCritical α F A m)) ≤
      ∑ i, F i (dbhSUCritical α F A k) / (1 - F i (dbhSUCritical α F A m)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hterm i
  have hspec := dbhSUCritical_spec (A := A) hF0 hα k
  rw [← dbhSUCritical_self (α := α) (F := F) (A := A)] at hspec
  have hall : ∑ i, F i (dbhSUCritical α F A k) / (1 - F i (dbhSUCritical α F A m)) ≤ α * k := by
    have h := mul_le_mul_of_nonneg_left hspec hm.le
    rwa [← mul_assoc, mul_one_div_cancel hm.ne', one_mul, mul_div_cancel₀ _ hm.ne'] at h
  rw [div_le_iff₀ hk0]
  exact hsub.trans hall

end MathlibExt.Probability.Statistics.MultipleTesting
