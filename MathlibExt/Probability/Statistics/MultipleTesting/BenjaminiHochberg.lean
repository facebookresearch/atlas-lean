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

/-!
# False discovery rate control by the Benjamini–Hochberg procedure

Given p-values `p 0, …, p (m - 1)`, the Benjamini–Hochberg (BH) step-up procedure at level `q`
finds the largest `k ≤ m` such that at least `k` p-values are `≤ q k / m` (equivalently the
`k`-th smallest p-value is `≤ q k / m`) and rejects every hypothesis whose p-value is
`≤ q k / m`. With `H0` the set of true null hypotheses, the false discovery proportion is
`|R ∩ H0| / max |R| 1`, and the false discovery rate (FDR) is its expectation.

Benjamini and Hochberg proved that for independent p-values, with the true-null p-values
uniform on `[0, 1]`, the procedure controls the FDR at level `q |H0| / m ≤ q`, whatever the
distribution of the false-null p-values. This is the multiple-testing guarantee used for
genome-wide association and differential-expression analyses.

## Main results

* `bhIndex_le_numBelow`, `le_bhIndex`: `bhIndex q p` is the largest qualifying `k`.
* `card_bhRejections`: BH at level `q ≥ 0` rejects exactly `bhIndex q p` hypotheses.
* `integral_falseDiscoveryProportion_bhRejections_le`: `E[FDP] ≤ q |H0| / m`
  (Benjamini–Hochberg 1995, Theorem 1).

## References

* Y. Benjamini and Y. Hochberg, *Controlling the false discovery rate: a practical and
  powerful approach to multiple testing*, J. R. Statist. Soc. B 57 (1995), 289–300,
  Theorem 1.
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

private theorem uniform_measure_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hX : HasLaw X (volume.restrict (Set.Icc (0 : ℝ) 1)) μ)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) : μ.real {ω | X ω ≤ t} = t := by
  rw [hX.measureReal_eq measurableSet_Iic]
  change (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Iic t) = t
  rw [measureReal_restrict_apply measurableSet_Iic]
  have hset : Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 t := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · tauto
    · rintro ⟨hx₀, hxt⟩
      exact ⟨hxt, hx₀, hxt.trans ht₁⟩
  rw [hset, Real.volume_real_Icc_of_le ht₀, sub_zero]

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

private theorem integral_bh_contribution {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ)
    (hp : ∀ i, Measurable (p i)) (hindep : iIndepFun p μ) (i : Fin m)
    (hnull : HasLaw (p i) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hm : 0 < m) :
    ∫ ω, (∑ k ∈ Finset.Icc 1 m,
      {ω | p i ω ≤ q * (k : ℝ) / m ∧
        bhIndex q (Function.update (fun j => p j ω) i 0) = k}.indicator
        (fun _ => 1 / (k : ℝ)) ω) ∂μ = q / m := by
  classical
  let K := fun ω => bhIndex q (Function.update (fun j => p j ω) i 0)
  have hK : Measurable K := measurable_bh_update p hp q i
  have hevent (k : ℕ) : MeasurableSet {ω | p i ω ≤ q * (k : ℝ) / m ∧ K ω = k} :=
    (measurableSet_le (hp i) measurable_const).inter (measurableSet_eq_fun hK measurable_const)
  have hind := indep_bhIndex_update μ p hp hindep q i
  have hprob (k : ℕ) (hk : k ∈ Finset.Icc 1 m) :
      μ.real {ω | p i ω ≤ q * (k : ℝ) / m ∧ K ω = k} =
        (q * (k : ℝ) / m) * μ.real {ω | K ω = k} := by
    have h := hind.measure_inter_preimage_eq_mul (Set.Iic (q * (k : ℝ) / m)) {k}
      measurableSet_Iic (measurableSet_singleton k)
    have hr : μ.real {ω | p i ω ≤ q * (k : ℝ) / m ∧ K ω = k} =
        μ.real {ω | p i ω ≤ q * (k : ℝ) / m} * μ.real {ω | K ω = k} := by
      simpa [K, Set.preimage, Set.inter_def, measureReal_def, ENNReal.toReal_mul]
        using congrArg ENNReal.toReal h
    rw [hr, uniform_measure_le μ (p i) hnull (threshold_nonneg hq₀)
      (threshold_le_one hq₁ hm (Finset.mem_Icc.mp hk).2)]
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
        (1 / (k : ℝ))) = ∑ k ∈ Finset.Icc 1 m, (q / m) * μ.real {ω | K ω = k} := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hprob k hk]
      have hk₀ : (k : ℝ) ≠ 0 := by exact_mod_cast (by
        have := (Finset.mem_Icc.mp hk).1; omega : k ≠ 0)
      field_simp
    _ = q / m := by rw [← Finset.mul_sum, hsum, mul_one]

/-- **Benjamini–Hochberg FDR control.** If the p-values are independent and every true-null
p-value is uniformly distributed on `[0, 1]`, the BH procedure at level `q ∈ [0, 1]` has false
discovery rate at most `q |H0| / m`. Nothing is assumed about the false-null p-values beyond
measurability and independence. (For `m = 0` both sides are `0`.)

Source: Benjamini & Hochberg (1995), Theorem 1. -/
theorem integral_falseDiscoveryProportion_bhRejections_le {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ)
    (hp : ∀ i, Measurable (p i)) (hindep : iIndepFun p μ) (H0 : Finset (Fin m))
    (hnull : ∀ i ∈ H0, HasLaw (p i) (volume.restrict (Set.Icc (0 : ℝ) 1)) μ)
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
    apply le_of_eq
    calc
      (∫ ω, falseDiscoveryProportion H0 (bhRejections q fun i => p i ω) ∂μ) =
          ∫ ω, ∑ i ∈ H0, F i ω ∂μ := integral_congr_ae (Filter.Eventually.of_forall heq)
      _ = ∑ i ∈ H0, ∫ ω, F i ω ∂μ := integral_finsetSum H0 (fun i _ => hF i)
      _ = ∑ i ∈ H0, q / m := by
        apply Finset.sum_congr rfl
        intro i hi
        exact integral_bh_contribution μ p hp hindep i (hnull i hi) q hq₀ hq₁ hmpos
      _ = q * H0.card / m := by simp [Finset.sum_const, nsmul_eq_mul]; ring

end MathlibExt.Probability.Statistics.MultipleTesting
