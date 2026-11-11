/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.NumberTheory.Harmonic.Defs

/-!
# False discovery rate control by the Benjamini–Hochberg procedure

Given p-values `p 0, …, p (m - 1)`, the Benjamini–Hochberg (BH) step-up procedure at level `q`
finds the largest `k ≤ m` such that at least `k` p-values are `≤ q k / m` (equivalently the
`k`-th smallest p-value is `≤ q k / m`) and rejects every hypothesis whose p-value is
`≤ q k / m`. With `H0` the set of true null hypotheses, the false discovery proportion is
`|R ∩ H0| / max |R| 1`, and the false discovery rate (FDR) is its expectation.

Benjamini and Hochberg proved that for independent p-values, with the true-null p-values
super-uniform (valid: `P(p_i ≤ t) ≤ t` for `t ∈ [0, 1]`, as for uniform or properly calibrated
discrete p-values), the procedure controls the FDR at level `q |H0| / m ≤ q`, whatever the
distribution of the false-null p-values. This is the multiple-testing guarantee used for
genome-wide association and differential-expression analyses. Benjamini and Yekutieli showed
that, with no assumption on the dependence among the p-values, running BH at the smaller level
`q / H_m` (`H_m = ∑_{k=1}^m 1/k` the harmonic number) still controls the FDR at `q |H0| / m`.

## Main results

* `bhIndex_le_numBelow`, `le_bhIndex`: `bhIndex q p` is the largest qualifying `k`.
* `card_bhRejections`: BH at level `q ≥ 0` rejects exactly `bhIndex q p` hypotheses.
* `integral_falseDiscoveryProportion_bhRejections_le_of_isValidPValue`: `E[FDP] ≤ q |H0| / m`
  for independent p-values whose true-null p-values are valid (super-uniform)
  (Benjamini–Hochberg 1995, Theorem 1).
* `integral_falseDiscoveryProportion_bhRejections_le`: the special case of uniform true-null
  p-values.
* `integral_falseDiscoveryProportion_bhRejections_le_of_arbitrary_dependence`: BH at level
  `q / H_m` has `E[FDP] ≤ q |H0| / m` for arbitrarily dependent p-values whose true-null p-values
  are valid (Benjamini–Yekutieli 2001, Theorem 1.3).
* `one_le_harmonic`: Mathlib's harmonic number satisfies `1 ≤ H_m` for `m ≥ 1`.

## References

* Y. Benjamini and Y. Hochberg, *Controlling the false discovery rate: a practical and
  powerful approach to multiple testing*, J. R. Statist. Soc. B 57 (1995), 289–300,
  Theorem 1.
* Y. Benjamini and D. Yekutieli, *The control of the false discovery rate in multiple testing
  under dependency*, Ann. Statist. 29 (2001), 1165–1188, Theorem 1.3.
* B. Efron, *Large-Scale Inference*, Cambridge University Press (2010), §4.2.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory ProbabilityTheory

variable {m : ℕ}

/-- The Benjamini–Hochberg step-up index: the largest `k ∈ {0, …, m}` such that at least `k`
p-values are at most `q k / m` (`k = 0` always qualifies). -/
noncomputable def bhIndex (q : ℝ) (p : Fin m → ℝ) : ℕ :=
  ((Finset.range (m + 1)).filter fun k : ℕ => k ≤ numBelow p (q * (k : ℝ) / m)).max'
    ⟨0, by simp⟩

/-- The hypotheses rejected by the Benjamini–Hochberg procedure at level `q`: those whose
p-value is at most `q * bhIndex q p / m`. -/
noncomputable def bhRejections (q : ℝ) (p : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i => p i ≤ q * bhIndex q p / m

/-- The BH step-up index is at most `m`. -/
theorem bhIndex_le (q : ℝ) (p : Fin m → ℝ) : bhIndex q p ≤ m := by
  have h := Finset.max'_mem ((Finset.range (m + 1)).filter fun k : ℕ =>
    k ≤ numBelow p (q * (k : ℝ) / m)) ⟨0, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_range] at h
  exact Nat.lt_succ_iff.1 h.1

/-- At the BH step-up index `k`, at least `k` p-values are at most `q k / m`. -/
theorem bhIndex_le_numBelow (q : ℝ) (p : Fin m → ℝ) :
    bhIndex q p ≤ numBelow p (q * bhIndex q p / m) := by
  have h := Finset.max'_mem ((Finset.range (m + 1)).filter fun k : ℕ =>
    k ≤ numBelow p (q * (k : ℝ) / m)) ⟨0, by simp⟩
  simp only [Finset.mem_filter] at h
  exact h.2

/-- The BH step-up index is the largest `k ≤ m` with at least `k` p-values at most `q k / m`. -/
theorem le_bhIndex {q : ℝ} {p : Fin m → ℝ} {k : ℕ} (hk : k ≤ m)
    (h : k ≤ numBelow p (q * k / m)) : k ≤ bhIndex q p :=
  Finset.le_max' _ k (by simpa [Nat.lt_succ_iff] using ⟨hk, h⟩)

/-- The BH procedure at level `q ≥ 0` rejects exactly `bhIndex q p` hypotheses. -/
theorem card_bhRejections {q : ℝ} (hq : 0 ≤ q) (p : Fin m → ℝ) :
    (bhRejections q p).card = bhIndex q p := by
  change numBelow p (q * bhIndex q p / m) = bhIndex q p
  refine le_antisymm ?_ (bhIndex_le_numBelow q p)
  by_contra! hlt
  have hle : numBelow p (q * bhIndex q p / m) ≤ bhIndex q p :=
    le_bhIndex (numBelow_le p _) (numBelow_mono p (by gcongr))
  omega

private theorem threshold_mono {m k l : ℕ} {q : ℝ} (hq : 0 ≤ q) (hkl : k ≤ l) :
    q * (k : ℝ) / m ≤ q * (l : ℝ) / m := by
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hkl) hq)
    (Nat.cast_nonneg m)

private theorem threshold_nonneg {m k : ℕ} {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ q * (k : ℝ) / m := by positivity

private theorem numBelow_update_le {m : ℕ} (p : Fin m → ℝ) (i : Fin m) {t : ℝ}
    (ht : 0 ≤ t) : numBelow p t ≤ numBelow (Function.update p i 0) t := by
  classical
  apply Finset.card_le_card
  intro j hj
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  by_cases hji : j = i
  · simpa [hji] using ht
  · simpa [Function.update_of_ne hji] using (Finset.mem_filter.mp hj).2

private theorem numBelow_update_eq {m : ℕ} (p : Fin m → ℝ) (i : Fin m) {t : ℝ}
    (ht : 0 ≤ t) (hpi : p i ≤ t) : numBelow (Function.update p i 0) t = numBelow p t := by
  classical
  unfold numBelow
  congr 1
  ext j
  by_cases hji : j = i
  · simp [hji, ht, hpi]
  · simp [Function.update_of_ne hji]

private theorem bhIndex_le_update {m : ℕ} {q : ℝ} (hq : 0 ≤ q) (p : Fin m → ℝ)
    (i : Fin m) : bhIndex q p ≤ bhIndex q (Function.update p i 0) := by
  exact le_bhIndex (bhIndex_le q p) ((bhIndex_le_numBelow q p).trans
    (numBelow_update_le p i (threshold_nonneg hq)))

private theorem bhIndex_update_pos {m : ℕ} {q : ℝ} (hq : 0 ≤ q) (p : Fin m → ℝ)
    (i : Fin m) : 1 ≤ bhIndex q (Function.update p i 0) := by
  apply le_bhIndex (by have := i.isLt; omega)
  apply Finset.card_pos.mpr
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    simpa using (threshold_nonneg (m := m) (k := 1) hq)⟩⟩

private theorem bhIndex_update_eq {m : ℕ} {q : ℝ} (hq : 0 ≤ q) (p : Fin m → ℝ)
    (i : Fin m) (hpi : p i ≤ q * bhIndex q (Function.update p i 0) / m) :
    bhIndex q p = bhIndex q (Function.update p i 0) := by
  apply Nat.le_antisymm (bhIndex_le_update hq p i)
  apply le_bhIndex (bhIndex_le q _)
  rw [← numBelow_update_eq p i (threshold_nonneg hq) hpi]
  exact bhIndex_le_numBelow q _

private theorem bh_leave_one_out {m k : ℕ} {q : ℝ} (hq : 0 ≤ q) (p : Fin m → ℝ)
    (i : Fin m) :
    i ∈ bhRejections q p ∧ (bhRejections q p).card = k ↔
      p i ≤ q * (k : ℝ) / m ∧ (bhRejections q (Function.update p i 0)).card = k := by
  classical
  rw [card_bhRejections hq, card_bhRejections hq]
  simp only [bhRejections, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hpi, hk⟩
    have heq := bhIndex_update_eq hq p i (hpi.trans
      (threshold_mono hq (bhIndex_le_update hq p i)))
    exact ⟨by simpa [hk] using hpi, heq.symm.trans hk⟩
  · rintro ⟨hpi, hk⟩
    have heq := bhIndex_update_eq hq p i (by simpa [hk] using hpi)
    exact ⟨by simpa [heq, hk] using hpi, heq.trans hk⟩

private theorem measurable_numBelow {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i)) (t : ℝ) :
    Measurable (fun ω => numBelow (fun i => p i ω) t) := by
  classical
  simp only [numBelow, Finset.card_filter]
  exact Finset.measurable_sum _ fun i _ => Measurable.ite
    (measurableSet_le (hp i) measurable_const) measurable_const measurable_const

private theorem bhIndex_eq_sup {m : ℕ} (q : ℝ) (p : Fin m → ℝ) :
    bhIndex q p = (Finset.range (m + 1)).sup
      (fun k => if k ≤ numBelow p (q * (k : ℝ) / m) then k else 0) := by
  classical
  apply Nat.le_antisymm
  · have h := Finset.le_sup (f := fun (k : ℕ) =>
      if k ≤ numBelow p (q * (k : ℝ) / m) then k else 0)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (bhIndex_le q p)))
    simpa [bhIndex_le_numBelow q p] using h
  · apply Finset.sup_le
    intro k hk
    split_ifs with h
    · exact le_bhIndex (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) h
    · exact Nat.zero_le _

private theorem measurable_bhIndex {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i)) (q : ℝ) :
    Measurable (fun ω => bhIndex q (fun i => p i ω)) := by
  classical
  simp_rw [bhIndex_eq_sup]
  have h : ∀ s : Finset ℕ, Measurable (fun ω => s.sup
      (fun k => if k ≤ numBelow (fun i => p i ω) (q * (k : ℝ) / m) then k else 0)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih =>
      simp only [Finset.sup_insert]
      exact (Measurable.ite (measurableSet_le measurable_const
        (measurable_numBelow p hp _)) measurable_const measurable_const).max ih
  exact h _

private theorem indep_bhIndex_update {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    (hindep : iIndepFun p μ) (q : ℝ) (i : Fin m) :
    IndepFun (p i) (fun ω => bhIndex q (Function.update (fun j => p j ω) i 0)) μ := by
  classical
  let S : Set (Fin m) := {i}
  let T : Set (Fin m) := {j | j ≠ i}
  let g : (T → ℝ) → ℕ := fun x => bhIndex q (fun j => if h : j = i then 0 else x ⟨j, h⟩)
  have hg : Measurable g := by
    refine measurable_bhIndex
      (fun j (x : T → ℝ) => if h : j = i then 0 else x ⟨j, h⟩) ?_ q
    intro j
    by_cases h : j = i
    · simp only [h, dite_true]
      exact measurable_const
    · simp only [h, dite_false]
      exact measurable_pi_apply (⟨j, h⟩ : T)
  have hST : Disjoint S T := by
    apply Set.disjoint_left.mpr
    intro j hj hj'
    exact hj' (Set.mem_singleton_iff.mp hj)
  have h := (iIndepFun.indepFun_set S T hST hindep hp).comp
    (measurable_pi_apply (⟨i, Set.mem_singleton i⟩ : S)) hg
  have heq : (fun ω => bhIndex q (Function.update (fun j => p j ω) i 0)) =
      g ∘ (fun ω (j : T) => p j ω) := by
    funext ω
    dsimp [g]
    congr 1
    funext j
    by_cases hji : j = i <;> simp [hji]
  rw [heq]
  exact h

private theorem valid_measureReal_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hX : IsValidPValue μ X) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    μ.real {ω | X ω ≤ t} ≤ t :=
  ENNReal.toReal_le_of_le_ofReal ht₀ (hX t ⟨ht₀, ht₁⟩)

private theorem threshold_le_one {m k : ℕ} {q : ℝ} (hq₁ : q ≤ 1)
    (hm : 0 < m) (hkm : k ≤ m) : q * (k : ℝ) / m ≤ 1 := by
  apply (div_le_one (by exact_mod_cast hm)).mpr
  calc
    q * (k : ℝ) ≤ 1 * (k : ℝ) := mul_le_mul_of_nonneg_right hq₁ (Nat.cast_nonneg _)
    _ ≤ m := by simpa using (show (k : ℝ) ≤ m by exact_mod_cast hkm)

private theorem fdp_eq_sum {m : ℕ} (H0 R : Finset (Fin m)) :
    falseDiscoveryProportion H0 R =
      ∑ i ∈ H0, if i ∈ R then 1 / max (R.card : ℝ) 1 else 0 := by
  classical
  have hc : ((R ∩ H0).card : ℝ) = ∑ i ∈ H0, if i ∈ R then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp [Finset.filter_mem_eq_inter, Finset.inter_comm]
  rw [falseDiscoveryProportion, hc, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

private theorem bh_contribution_eq_sum {m : ℕ} {q : ℝ} (hq : 0 ≤ q)
    (p : Fin m → ℝ) (i : Fin m) :
    (if i ∈ bhRejections q p then 1 / max ((bhRejections q p).card : ℝ) 1 else 0) =
      ∑ k ∈ Finset.Icc 1 m,
        if p i ≤ q * (k : ℝ) / m ∧ bhIndex q (Function.update p i 0) = k
          then 1 / (k : ℝ) else 0 := by
  classical
  simp_rw [← card_bhRejections hq (Function.update p i 0), ← bh_leave_one_out hq p i]
  by_cases hi : i ∈ bhRejections q p
  · have hrpos : 1 ≤ (bhRejections q p).card := Finset.card_pos.mpr ⟨i, hi⟩
    have hrle : (bhRejections q p).card ≤ m := by
      rw [card_bhRejections hq]
      exact bhIndex_le q p
    rw [Finset.sum_eq_single (bhRejections q p).card]
    · simp [hi, max_eq_left (show (1 : ℝ) ≤ (bhRejections q p).card by
        exact_mod_cast hrpos)]
    · intro k hk hkr
      simp [Ne.symm hkr]
    · intro hr
      exact (hr (Finset.mem_Icc.mpr ⟨hrpos, hrle⟩)).elim
  · simp [hi]

private theorem measurable_bh_update {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i)) (q : ℝ) (i : Fin m) :
    Measurable (fun ω => bhIndex q (Function.update (fun j => p j ω) i 0)) := by
  classical
  apply measurable_bhIndex
  intro j
  by_cases hji : j = i <;> simp only [Function.update_apply, hji, ite_true, ite_false]
  · exact measurable_const
  · exact hp j

private theorem integral_bh_contribution_le {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ)
    (hp : ∀ i, Measurable (p i)) (hindep : iIndepFun p μ) (i : Fin m)
    (hnull : IsValidPValue μ (p i))
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hm : 0 < m) :
    ∫ ω, (∑ k ∈ Finset.Icc 1 m,
      {ω | p i ω ≤ q * (k : ℝ) / m ∧
        bhIndex q (Function.update (fun j => p j ω) i 0) = k}.indicator
        (fun _ => 1 / (k : ℝ)) ω) ∂μ ≤ q / m := by
  classical
  let K := fun ω => bhIndex q (Function.update (fun j => p j ω) i 0)
  have hK : Measurable K := measurable_bh_update p hp q i
  have hevent (k : ℕ) : MeasurableSet {ω | p i ω ≤ q * (k : ℝ) / m ∧ K ω = k} :=
    (measurableSet_le (hp i) measurable_const).inter (measurableSet_eq_fun hK measurable_const)
  have hind := indep_bhIndex_update μ p hp hindep q i
  have hprob (k : ℕ) (hk : k ∈ Finset.Icc 1 m) :
      μ.real {ω | p i ω ≤ q * (k : ℝ) / m ∧ K ω = k} ≤
        (q * (k : ℝ) / m) * μ.real {ω | K ω = k} := by
    have h := hind.measure_inter_preimage_eq_mul (Set.Iic (q * (k : ℝ) / m)) {k}
      measurableSet_Iic (measurableSet_singleton k)
    have hr : μ.real {ω | p i ω ≤ q * (k : ℝ) / m ∧ K ω = k} =
        μ.real {ω | p i ω ≤ q * (k : ℝ) / m} * μ.real {ω | K ω = k} := by
      simpa [K, Set.preimage, Set.inter_def, measureReal_def, ENNReal.toReal_mul]
        using congrArg ENNReal.toReal h
    rw [hr]
    exact mul_le_mul_of_nonneg_right (valid_measureReal_le μ (p i) hnull (threshold_nonneg hq₀)
      (threshold_le_one hq₁ hm (Finset.mem_Icc.mp hk).2)) measureReal_nonneg
  have hsum : (∑ k ∈ Finset.Icc 1 m, μ.real {ω | K ω = k}) = 1 := by
    have hpre : K ⁻¹' (↑(Finset.Icc 1 m) : Set ℕ) = Set.univ := by
      ext ω
      simp only [Set.mem_preimage, Finset.mem_coe, Finset.mem_Icc, Set.mem_univ, iff_true]
      exact ⟨bhIndex_update_pos hq₀ _ i, bhIndex_le q _⟩
    have h := sum_measureReal_preimage_singleton (μ := μ) (Finset.Icc 1 m)
      (fun k _ => hK (measurableSet_singleton k))
    rw [hpre] at h
    simpa [Set.preimage, measureReal_def] using h
  rw [integral_finsetSum (Finset.Icc 1 m) (fun (k : ℕ) _ =>
    (integrable_const (μ := μ) (1 / (k : ℝ))).indicator
    (hevent k))]
  simp_rw [integral_indicator_const _ (hevent _), smul_eq_mul]
  calc
    (∑ k ∈ Finset.Icc 1 m, μ.real {ω | p i ω ≤ q * (k : ℝ) / m ∧ K ω = k} *
        (1 / (k : ℝ))) ≤ ∑ k ∈ Finset.Icc 1 m, (q / m) * μ.real {ω | K ω = k} := by
      apply Finset.sum_le_sum
      intro k hk
      have hk₀ : (k : ℝ) ≠ 0 := by exact_mod_cast (by
        have := (Finset.mem_Icc.mp hk).1; omega : k ≠ 0)
      calc
        μ.real {ω | p i ω ≤ q * (k : ℝ) / m ∧ K ω = k} * (1 / (k : ℝ)) ≤
            (q * (k : ℝ) / m) * μ.real {ω | K ω = k} * (1 / (k : ℝ)) :=
          mul_le_mul_of_nonneg_right (hprob k hk) (by positivity)
        _ = (q / m) * μ.real {ω | K ω = k} := by field_simp
    _ = q / m := by rw [← Finset.mul_sum, hsum, mul_one]

/-- **Benjamini–Hochberg FDR control for super-uniform nulls.** If the p-values are independent
and every true-null p-value is valid (super-uniform: `μ {p i ≤ t} ≤ t` for `t ∈ [0, 1]`), the BH
procedure at level `q ∈ [0, 1]` has false discovery rate at most `q |H0| / m`. Properly
calibrated discrete p-values, such as those of permutation or exact tests, are included. Nothing
is assumed about the false-null p-values beyond measurability and independence. (For `m = 0`
both sides are `0`.)

Source: Benjamini & Hochberg (1995), Theorem 1, whose proof uses only `P(p_i ≤ t) ≤ t` for the
true nulls. -/
theorem integral_falseDiscoveryProportion_bhRejections_le_of_isValidPValue {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ)
    (hp : ∀ i, Measurable (p i)) (hindep : iIndepFun p μ) (H0 : Finset (Fin m))
    (hnull : ∀ i ∈ H0, IsValidPValue μ (p i))
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion H0 (bhRejections q fun i => p i ω) ∂μ ≤ q * H0.card / m := by
  classical
  by_cases hm : m = 0
  · subst m
    simp [falseDiscoveryProportion, bhRejections]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    let F : Fin m → Ω → ℝ := fun i ω => ∑ k ∈ Finset.Icc 1 m,
      {ω | p i ω ≤ q * (k : ℝ) / m ∧
        bhIndex q (Function.update (fun j => p j ω) i 0) = k}.indicator
        (fun _ => 1 / (k : ℝ)) ω
    have hF (i : Fin m) : Integrable (F i) μ := by
      apply integrable_finsetSum
      intro k hk
      exact (integrable_const (1 / (k : ℝ))).indicator
        ((measurableSet_le (hp i) measurable_const).inter
          (measurableSet_eq_fun (measurable_bh_update p hp q i) measurable_const))
    have heq (ω : Ω) : falseDiscoveryProportion H0 (bhRejections q (fun i => p i ω)) =
        ∑ i ∈ H0, F i ω := by
      rw [fdp_eq_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [bh_contribution_eq_sum hq₀]
      simp only [F, Set.indicator_apply, Set.mem_ofPred_eq]
    calc
      (∫ ω, falseDiscoveryProportion H0 (bhRejections q fun i => p i ω) ∂μ) =
          ∫ ω, ∑ i ∈ H0, F i ω ∂μ := integral_congr_ae (Filter.Eventually.of_forall heq)
      _ = ∑ i ∈ H0, ∫ ω, F i ω ∂μ := integral_finsetSum H0 (fun i _ => hF i)
      _ ≤ ∑ i ∈ H0, q / m := by
        apply Finset.sum_le_sum
        intro i hi
        exact integral_bh_contribution_le μ p hp hindep i (hnull i hi) q hq₀ hq₁ hmpos
      _ = q * H0.card / m := by simp [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Benjamini–Hochberg FDR control.** If the p-values are independent and every true-null
p-value is uniformly distributed on `[0, 1]`, the BH procedure at level `q ∈ [0, 1]` has false
discovery rate at most `q |H0| / m`. Nothing is assumed about the false-null p-values beyond
measurability and independence. (For `m = 0` both sides are `0`.) This is the uniform case of
`integral_falseDiscoveryProportion_bhRejections_le_of_isValidPValue`.

Source: Benjamini & Hochberg (1995), Theorem 1. -/
theorem integral_falseDiscoveryProportion_bhRejections_le {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ)
    (hp : ∀ i, Measurable (p i)) (hindep : iIndepFun p μ) (H0 : Finset (Fin m))
    (hnull : ∀ i ∈ H0, HasLaw (p i) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion H0 (bhRejections q fun i => p i ω) ∂μ ≤ q * H0.card / m :=
  integral_falseDiscoveryProportion_bhRejections_le_of_isValidPValue μ p hp hindep H0
    (fun i hi => isValidPValue_of_hasLaw_uniform (hnull i hi)) q hq₀ hq₁

/-- The harmonic number `H_m` is at least `1` for `m ≥ 1`. -/
theorem one_le_harmonic (hm : 0 < m) : (1 : ℝ) ≤ harmonic m := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    push_cast [harmonic_succ]
    have : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
    linarith

/-- Abel summation against `1 / k`: partial sums at most `C K` give `∑ a k / k ≤ C H_m`. -/
private theorem sum_div_le_mul_harmonic {a : ℕ → ℝ} {C : ℝ} {m : ℕ}
    (h : ∀ K ∈ Finset.Icc 1 m, ∑ k ∈ Finset.Icc 1 K, a k ≤ C * K) :
    ∑ k ∈ Finset.Icc 1 m, a k / k ≤ C * harmonic m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have key : ∀ n, 1 ≤ n → n ≤ m → ∑ k ∈ Finset.Icc 1 n, a k / k ≤
      C * ((harmonic n : ℝ) - 1) + (∑ k ∈ Finset.Icc 1 n, a k) / n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => intro _; simp
    | succ n hn ih =>
      intro hnm
      have ih := ih (by omega)
      have hS := h n (Finset.mem_Icc.mpr ⟨hn, by omega⟩)
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      push_cast [harmonic_succ]
      set S := ∑ k ∈ Finset.Icc 1 n, a k
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 : S / n - S / (n + 1) = S / (n * (n + 1)) := by field_simp; ring
      have h2 : S / (n * (n + 1)) ≤ C * n / (n * (n + 1)) :=
        div_le_div_of_nonneg_right hS (by positivity)
      have h3 : C * n / (n * (n + 1)) = C * ((n : ℝ) + 1)⁻¹ := by field_simp
      rw [add_div]
      have h4 : a (n + 1) / ((n : ℝ) + 1) = a (n + 1) / ((n + 1 : ℕ) : ℝ) := by push_cast; rfl
      linarith
  have hm1 := h m (Finset.mem_Icc.mpr ⟨hm, le_rfl⟩)
  have hS : (∑ k ∈ Finset.Icc 1 m, a k) / m ≤ C := by
    rw [div_le_iff₀ (by exact_mod_cast hm)]
    exact hm1
  linarith [key m hm le_rfl]

private theorem integral_bh_contribution_le_of_arbitrary {m : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ)
    (hp : ∀ i, Measurable (p i)) (i : Fin m) (hnull : IsValidPValue μ (p i))
    (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hm : 0 < m) :
    ∫ ω, (∑ k ∈ Finset.Icc 1 m,
      {ω | p i ω ≤ α * (k : ℝ) / m ∧
        bhIndex α (Function.update (fun j => p j ω) i 0) = k}.indicator
        (fun _ => 1 / (k : ℝ)) ω) ∂μ ≤ α / m * harmonic m := by
  classical
  let K := fun ω => bhIndex α (Function.update (fun j => p j ω) i 0)
  have hK : Measurable K := measurable_bh_update p hp α i
  let A : ℕ → Set Ω := fun k => {ω | p i ω ≤ α * (k : ℝ) / m ∧ K ω = k}
  have hA (k : ℕ) : MeasurableSet (A k) :=
    (measurableSet_le (hp i) measurable_const).inter (measurableSet_eq_fun hK measurable_const)
  rw [integral_finsetSum (Finset.Icc 1 m) (fun (k : ℕ) _ =>
    (integrable_const (μ := μ) (1 / (k : ℝ))).indicator (hA k))]
  simp_rw [integral_indicator_const _ (hA _), smul_eq_mul, mul_one_div]
  apply sum_div_le_mul_harmonic
  intro N hN
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 N) : Set ℕ) A := by
    intro k _ l _ hkl
    exact Set.disjoint_left.mpr fun ω h1 h2 => hkl (h1.2.symm.trans h2.2)
  calc
    ∑ k ∈ Finset.Icc 1 N, μ.real (A k) = μ.real (⋃ k ∈ Finset.Icc 1 N, A k) :=
      (measureReal_biUnion_finset hdisj fun k _ => hA k).symm
    _ ≤ μ.real {ω | p i ω ≤ α * (N : ℝ) / m} := by
      refine measureReal_mono (Set.iUnion₂_subset fun k hk ω hω => ?_)
      exact hω.1.trans (threshold_mono hα₀ (Finset.mem_Icc.mp hk).2)
    _ ≤ α * (N : ℝ) / m := valid_measureReal_le μ (p i) hnull (threshold_nonneg hα₀)
      (threshold_le_one hα₁ hm (Finset.mem_Icc.mp hN).2)
    _ = α / m * N := by ring

/-- **Benjamini–Yekutieli FDR control under arbitrary dependence.** If every true-null p-value is
valid (super-uniform: `μ {p i ≤ t} ≤ t` for `t ∈ [0, 1]`), then the BH procedure run at the
corrected level `q / H_m`, where `H_m = ∑_{k=1}^m 1/k` is the harmonic number, has false discovery
rate at most `q |H0| / m`, for any `q ∈ [0, 1]`. No independence, PRDS, or other assumption on the
joint law of the p-values is made: they may be arbitrarily dependent. The factor `H_m ≈ log m` is
the price paid relative to `integral_falseDiscoveryProportion_bhRejections_le_of_isValidPValue`,
which runs BH at level `q` but needs independence. (For `m = 0` both sides are `0`.)

Source: Benjamini & Yekutieli, *The control of the false discovery rate in multiple testing under
dependency*, Ann. Statist. 29 (2001), 1165–1188, Theorem 1.3. -/
theorem integral_falseDiscoveryProportion_bhRejections_le_of_arbitrary_dependence {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ)
    (hp : ∀ i, Measurable (p i)) (H0 : Finset (Fin m))
    (hnull : ∀ i ∈ H0, IsValidPValue μ (p i))
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion H0 (bhRejections (q / harmonic m) fun i => p i ω) ∂μ ≤
      q * H0.card / m := by
  classical
  by_cases hm : m = 0
  · subst m
    simp [falseDiscoveryProportion, bhRejections]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hH : (1 : ℝ) ≤ harmonic m := one_le_harmonic hmpos
    set α : ℝ := q / harmonic m with hαdef
    have hα₀ : 0 ≤ α := div_nonneg hq₀ (by linarith)
    have hα₁ : α ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    let F : Fin m → Ω → ℝ := fun i ω => ∑ k ∈ Finset.Icc 1 m,
      {ω | p i ω ≤ α * (k : ℝ) / m ∧
        bhIndex α (Function.update (fun j => p j ω) i 0) = k}.indicator
        (fun _ => 1 / (k : ℝ)) ω
    have hF (i : Fin m) : Integrable (F i) μ := by
      apply integrable_finsetSum
      intro k hk
      exact (integrable_const (1 / (k : ℝ))).indicator
        ((measurableSet_le (hp i) measurable_const).inter
          (measurableSet_eq_fun (measurable_bh_update p hp α i) measurable_const))
    have heq (ω : Ω) : falseDiscoveryProportion H0 (bhRejections α (fun i => p i ω)) =
        ∑ i ∈ H0, F i ω := by
      rw [fdp_eq_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [bh_contribution_eq_sum hα₀]
      simp only [F, Set.indicator_apply, Set.mem_ofPred_eq]
    calc
      (∫ ω, falseDiscoveryProportion H0 (bhRejections α fun i => p i ω) ∂μ) =
          ∫ ω, ∑ i ∈ H0, F i ω ∂μ := integral_congr_ae (Filter.Eventually.of_forall heq)
      _ = ∑ i ∈ H0, ∫ ω, F i ω ∂μ := integral_finsetSum H0 (fun i _ => hF i)
      _ ≤ ∑ i ∈ H0, q / m := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          ∫ ω, F i ω ∂μ ≤ α / m * harmonic m :=
            integral_bh_contribution_le_of_arbitrary μ p hp i (hnull i hi) α hα₀ hα₁ hmpos
          _ = q / m := by rw [hαdef]; field_simp
      _ = q * H0.card / m := by simp [Finset.sum_const, nsmul_eq_mul]; ring

end MathlibExt.Probability.Statistics.MultipleTesting
