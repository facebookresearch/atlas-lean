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
public import Mathlib.Probability.Kernel.CondDistrib

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
`q / H_m` (`H_m = ∑_{k=1}^m 1/k` the harmonic number) still controls the FDR at `q |H0| / m`, and
that the unmodified procedure at level `q` keeps this guarantee when the p-values are positively
regression dependent on the true nulls (PRDS).

## The PRDS condition

Benjamini and Yekutieli (2001, §1.3) call a set `D ⊆ ℝ^m` *increasing* if `x ∈ D` and `y ≥ x`
(coordinatewise) imply `y ∈ D`, and say that `X` is *PRDS on `I0`* if for every increasing `D`
and every `i ∈ I0`, `P(X ∈ D | X_i = x)` is nondecreasing in `x`. They state it for test
statistics and observe (§2.2) that it is invariant under comonotone coordinatewise
transformations, so it passes to the p-values whether they are right- or left-tailed. We state it
directly for the p-value vector `P = (p 0, …, p (m - 1))`, as `IsPRDSOn μ p H0`:

* increasing sets are Mathlib's `IsUpperSet` for the coordinatewise order on `Fin m → ℝ`, so they
  are closed under making p-values *larger* (less significant), and must be measurable;
* `P(P ∈ D | p i = x)` is Mathlib's regular conditional distribution
  `condDistrib P (p i) μ x D`, which is determined only `μ.map (p i)`-almost everywhere, so the
  condition asks for a nondecreasing `ℝ≥0∞`-valued version `g =ᵐ[μ.map (p i)] …`. A function that
  is nondecreasing on a full-measure set extends to a nondecreasing function on `ℝ`, so this loses
  nothing.

`isPRDSOn_iff_setLIntegral` restates the condition without kernels: `g` is a nondecreasing version
of the conditional probability in Kolmogorov's sense,
`μ (P ∈ D, p i ∈ B) = ∫⁻ x in B, g x ∂(μ.map (p i))` for all Borel `B`.
`IsPRDSOn.measure_inter_mul_le` is the consequence used in the proof (Benjamini–Yekutieli,
eq. (13)): `t ↦ P(P ∈ D | p i ≤ t)` is nondecreasing. PRDS is a hypothesis on the joint law;
nothing here asserts that any applied setting (for example, linkage-disequilibrium-correlated
GWAS p-values) satisfies it.

## Main results

* `bhIndex_le_numBelow`, `le_bhIndex`: `bhIndex q p` is the largest qualifying `k`.
* `card_bhRejections`: BH at level `q ≥ 0` rejects exactly `bhIndex q p` hypotheses.
* `measurable_numBelow`, `measurable_bhIndex`,
  `measurable_falseDiscoveryProportion_bhRejections`: for measurable p-values, the count below a
  threshold, the BH index and the false discovery proportion of the BH rejections are measurable.
* `integral_falseDiscoveryProportion_bhRejections_le_of_isValidPValue`: `E[FDP] ≤ q |H0| / m`
  for independent p-values whose true-null p-values are valid (super-uniform)
  (Benjamini–Hochberg 1995, Theorem 1).
* `integral_falseDiscoveryProportion_bhRejections_le`: the special case of uniform true-null
  p-values.
* `integral_falseDiscoveryProportion_bhRejections_le_of_arbitrary_dependence`: BH at level
  `q / H_m` has `E[FDP] ≤ q |H0| / m` for arbitrarily dependent p-values whose true-null p-values
  are valid (Benjamini–Yekutieli 2001, Theorem 1.3).
* `one_le_harmonic`: Mathlib's harmonic number satisfies `1 ≤ H_m` for `m ≥ 1`.
* `IsPRDSOn`: PRDS of the p-values on the true nulls; `isPRDSOn_iff_setLIntegral`,
  `IsPRDSOn.measure_inter_mul_le`.
* `isPRDSOn_of_iIndepFun`, `isPRDSOn_of_monotone_comp`, `isPRDSOn_empty`: independent p-values,
  deterministic positive dependence (e.g. identical p-values) and the empty null set are PRDS.
* `integral_falseDiscoveryProportion_bhRejections_le_of_isPRDSOn`: BH at level `q` has
  `E[FDP] ≤ q |H0| / m` when the p-values are PRDS on `H0` and the true-null p-values are valid
  (Benjamini–Yekutieli 2001, Theorem 1.2).

## References

* Y. Benjamini and Y. Hochberg, *Controlling the false discovery rate: a practical and
  powerful approach to multiple testing*, J. R. Statist. Soc. B 57 (1995), 289–300,
  Theorem 1.
* Y. Benjamini and D. Yekutieli, *The control of the false discovery rate in multiple testing
  under dependency*, Ann. Statist. 29 (2001), 1165–1188, §1.3 (Property PRDS), §2.2,
  Theorem 1.2 and its proof in §4, Theorem 1.3.
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

/-- The number of measurable p-values below a fixed threshold is a measurable function. -/
theorem measurable_numBelow {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i)) (t : ℝ) :
    Measurable (fun ω => numBelow (fun i => p i ω) t) := by
  classical
  simp only [numBelow, Finset.card_filter]
  exact Finset.measurable_sum _ fun i _ => Measurable.ite
    (measurableSet_le (hp i) measurable_const) measurable_const measurable_const

/-- The BH step-up index as a finite supremum, the form used to prove measurability. -/
theorem bhIndex_eq_sup {m : ℕ} (q : ℝ) (p : Fin m → ℝ) :
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

/-- The BH step-up index of measurable p-values is a measurable function. -/
theorem measurable_bhIndex {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
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

/-- The false discovery proportion of the BH rejection set is a measurable function of
measurable p-values. -/
theorem measurable_falseDiscoveryProportion_bhRejections {Ω : Type*} [MeasurableSpace Ω]
    (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i)) (H0 : Finset (Fin m)) (q : ℝ) :
    Measurable fun ω => falseDiscoveryProportion H0 (bhRejections q fun i => p i ω) := by
  classical
  have hK : Measurable fun ω => q * (bhIndex q (fun i => p i ω) : ℝ) / m :=
    (measurable_const.mul (measurable_from_nat.comp (measurable_bhIndex p hp q))).div_const _
  have hE (i : Fin m) : MeasurableSet {ω | p i ω ≤ q * (bhIndex q (fun i => p i ω) : ℝ) / m} :=
    measurableSet_le (hp i) hK
  have hcount (s : Finset (Fin m)) : Measurable fun ω =>
      ((s.filter fun i => p i ω ≤ q * (bhIndex q (fun i => p i ω) : ℝ) / m).card : ℝ) := by
    simp_rw [Finset.natCast_card_filter]
    exact Finset.measurable_sum _ fun i _ =>
      Measurable.ite (hE i) measurable_const measurable_const
  have heq : (fun ω => falseDiscoveryProportion H0 (bhRejections q fun i => p i ω)) =
      fun ω => ((H0.filter fun i => p i ω ≤ q * (bhIndex q (fun i => p i ω) : ℝ) / m).card : ℝ) /
        max ((Finset.univ.filter fun i => p i ω ≤
          q * (bhIndex q (fun i => p i ω) : ℝ) / m).card : ℝ) 1 := by
    funext ω
    unfold falseDiscoveryProportion bhRejections
    congr 3
    ext i
    simp [and_comm]
  rw [heq]
  exact (hcount H0).div ((hcount Finset.univ).max measurable_const)

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

/-- The leave-one-out decomposition of the BH false discovery rate: if the BH contribution of each
true null has expectation at most `c`, the FDR is at most `|H0| c`. -/
private theorem integral_fdp_bhRejections_le_card_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    (H0 : Finset (Fin m)) {α : ℝ} (hα₀ : 0 ≤ α) {c : ℝ}
    (hc : ∀ i ∈ H0, ∫ ω, (∑ k ∈ Finset.Icc 1 m,
      {ω | p i ω ≤ α * (k : ℝ) / m ∧
        bhIndex α (Function.update (fun j => p j ω) i 0) = k}.indicator
        (fun _ => 1 / (k : ℝ)) ω) ∂μ ≤ c) :
    ∫ ω, falseDiscoveryProportion H0 (bhRejections α fun i => p i ω) ∂μ ≤ H0.card * c := by
  classical
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
    _ ≤ ∑ i ∈ H0, c := Finset.sum_le_sum hc
    _ = H0.card * c := by simp [Finset.sum_const, nsmul_eq_mul]

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
  calc
    _ ≤ H0.card * (q / m) := integral_fdp_bhRejections_le_card_mul μ p hp H0 hq₀ fun i hi =>
      integral_bh_contribution_le μ p hp hindep i (hnull i hi) q hq₀ hq₁ i.pos
    _ = q * H0.card / m := by ring

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
  have hα₀ : 0 ≤ q / harmonic m := div_nonneg hq₀ (by
    have : (0 : ℚ) ≤ harmonic m := Finset.sum_nonneg fun _ _ => by positivity
    exact_mod_cast this)
  calc
    _ ≤ H0.card * (q / m) := integral_fdp_bhRejections_le_card_mul μ p hp H0 hα₀ fun i hi => by
      have hH : (1 : ℝ) ≤ harmonic m := one_le_harmonic i.pos
      calc
        _ ≤ q / harmonic m / m * harmonic m :=
          integral_bh_contribution_le_of_arbitrary μ p hp i (hnull i hi) _ hα₀
            ((div_le_one (by linarith)).mpr (by linarith)) i.pos
        _ = q / m := by field_simp
    _ = q * H0.card / m := by ring

/-! ### Positive regression dependency on the true nulls (PRDS) -/

/-- **PRDS on `H0`** (Benjamini–Yekutieli 2001, §2.2), stated for the p-value vector
`P = (p 0, …, p (m - 1))`: for every true null `i ∈ H0` and every measurable increasing set
`D ⊆ ℝ^m` (`IsUpperSet D` for the coordinatewise order), the conditional probability
`x ↦ P(P ∈ D | p i = x)` has a nondecreasing version. The conditional probability is Mathlib's
regular conditional distribution `condDistrib P (p i) μ`, which is determined only up to
`μ.map (p i)`-null sets, hence the "version" (`=ᵐ`) quantifier. Larger p-values are less
significant, so `D` increasing means "closed under making p-values larger". -/
def IsPRDSOn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (p : Fin m → Ω → ℝ) (H0 : Finset (Fin m)) : Prop :=
  ∀ i ∈ H0, ∀ D : Set (Fin m → ℝ), MeasurableSet D → IsUpperSet D →
    ∃ g : ℝ → ENNReal, Monotone g ∧
      g =ᵐ[μ.map (p i)] fun x => condDistrib (fun ω j => p j ω) (p i) μ x D

private theorem measure_inter_eq_setLIntegral_condDistrib {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    (i : Fin m) {D : Set (Fin m → ℝ)} (hD : MeasurableSet D) {B : Set ℝ} (hB : MeasurableSet B) :
    μ ({ω | (fun j => p j ω) ∈ D} ∩ p i ⁻¹' B) =
      ∫⁻ x in B, condDistrib (fun ω j => p j ω) (p i) μ x D ∂(μ.map (p i)) := by
  have hP : Measurable (fun ω j => p j ω) := Measurable.of_eval hp
  rw [← Measure.compProd_apply_prod hB hD,
    compProd_map_condDistrib (hp i).aemeasurable hP.aemeasurable,
    Measure.map_apply ((hp i).prodMk hP) (hB.prod hD), Set.mk_preimage_prod, Set.inter_comm]
  rfl

/-- **PRDS as a monotone version of a conditional probability.** For measurable p-values,
`IsPRDSOn μ p H0` holds iff for every `i ∈ H0` and measurable increasing `D` there is a
nondecreasing `g` with `μ (P ∈ D, p i ∈ B) = ∫⁻ x in B, g x ∂(law of p i)` for every Borel `B`,
i.e. `g` is a nondecreasing version of `x ↦ P(P ∈ D | p i = x)` in the classical
(Kolmogorov) sense, with no reference to a chosen kernel. -/
theorem isPRDSOn_iff_setLIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i)) (H0 : Finset (Fin m)) :
    IsPRDSOn μ p H0 ↔ ∀ i ∈ H0, ∀ D : Set (Fin m → ℝ), MeasurableSet D → IsUpperSet D →
      ∃ g : ℝ → ENNReal, Monotone g ∧ ∀ B : Set ℝ, MeasurableSet B →
        μ ({ω | (fun j => p j ω) ∈ D} ∩ p i ⁻¹' B) = ∫⁻ x in B, g x ∂(μ.map (p i)) := by
  constructor
  · intro h i hi D hD hup
    obtain ⟨g, hg, hae⟩ := h i hi D hD hup
    refine ⟨g, hg, fun B hB => ?_⟩
    rw [measure_inter_eq_setLIntegral_condDistrib μ p hp i hD hB]
    exact (setLIntegral_congr_fun_ae hB (hae.mono fun x hx _ => hx)).symm
  · intro h i hi D hD hup
    obtain ⟨g, hg, hint⟩ := h i hi D hD hup
    refine ⟨g, hg, ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hg.measurable
      (Kernel.measurable_coe _ hD) fun B hB _ => ?_⟩
    rw [← hint B hB, measure_inter_eq_setLIntegral_condDistrib μ p hp i hD hB]

/-- **Monotone conditional tail under PRDS.** If `p` is PRDS on `H0`, `i ∈ H0`, `D` is a
measurable increasing set and `s ≤ t`, then
`μ (P ∈ D, p i ≤ s) * μ (p i ≤ t) ≤ μ (P ∈ D, p i ≤ t) * μ (p i ≤ s)`, i.e. (when the
denominators are positive) `t ↦ P(P ∈ D | p i ≤ t)` is nondecreasing. This cross-multiplied form
is the step of the Benjamini–Yekutieli proof that uses PRDS. -/
theorem IsPRDSOn.measure_inter_mul_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {p : Fin m → Ω → ℝ} {H0 : Finset (Fin m)} (h : IsPRDSOn μ p H0)
    (hp : ∀ i, Measurable (p i)) {i : Fin m} (hi : i ∈ H0) {D : Set (Fin m → ℝ)}
    (hD : MeasurableSet D) (hup : IsUpperSet D) {s t : ℝ} (hst : s ≤ t) :
    μ ({ω | (fun j => p j ω) ∈ D} ∩ {ω | p i ω ≤ s}) * μ {ω | p i ω ≤ t} ≤
      μ ({ω | (fun j => p j ω) ∈ D} ∩ {ω | p i ω ≤ t}) * μ {ω | p i ω ≤ s} := by
  obtain ⟨g, hg, hint⟩ := (isPRDSOn_iff_setLIntegral μ p hp H0).mp h i hi D hD hup
  set ν := μ.map (p i)
  have hν (u : ℝ) : μ {ω | p i ω ≤ u} = ν (Set.Iic u) := by
    rw [Measure.map_apply (hp i) measurableSet_Iic]; rfl
  have hh (u : ℝ) : μ ({ω | (fun j => p j ω) ∈ D} ∩ {ω | p i ω ≤ u}) =
      ∫⁻ x in Set.Iic u, g x ∂ν := hint _ measurableSet_Iic
  have hdisj : Disjoint (Set.Iic s) (Set.Ioc s t) :=
    Set.disjoint_left.mpr fun x hx hx' => (not_le.mpr hx'.1) hx
  have hunion := Set.Iic_union_Ioc_eq_Iic hst
  have hνt : ν (Set.Iic t) = ν (Set.Iic s) + ν (Set.Ioc s t) := by
    rw [← hunion, measure_union hdisj measurableSet_Ioc]
  have hht : ∫⁻ x in Set.Iic t, g x ∂ν =
      ∫⁻ x in Set.Iic s, g x ∂ν + ∫⁻ x in Set.Ioc s t, g x ∂ν := by
    rw [← hunion, lintegral_union measurableSet_Ioc hdisj]
  have hle : ∫⁻ x in Set.Iic s, g x ∂ν ≤ g s * ν (Set.Iic s) := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_Iic fun x hx => hg hx
  have hge : g s * ν (Set.Ioc s t) ≤ ∫⁻ x in Set.Ioc s t, g x ∂ν := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_Ioc fun x hx => hg hx.1.le
  rw [hν, hν, hh, hh, hνt, hht]
  set a := ∫⁻ x in Set.Iic s, g x ∂ν
  set b := ∫⁻ x in Set.Ioc s t, g x ∂ν
  calc a * (ν (Set.Iic s) + ν (Set.Ioc s t))
      = a * ν (Set.Iic s) + a * ν (Set.Ioc s t) := mul_add _ _ _
    _ ≤ a * ν (Set.Iic s) + g s * ν (Set.Iic s) * ν (Set.Ioc s t) := by gcongr
    _ = a * ν (Set.Iic s) + g s * ν (Set.Ioc s t) * ν (Set.Iic s) := by ring
    _ ≤ a * ν (Set.Iic s) + b * ν (Set.Iic s) := by gcongr
    _ = (a + b) * ν (Set.Iic s) := (add_mul _ _ _).symm

/-- Every family is PRDS on the empty set of true nulls. -/
theorem isPRDSOn_empty {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (p : Fin m → Ω → ℝ) : IsPRDSOn μ p ∅ := by
  intro i hi
  simp at hi

/-- **Deterministic positive dependence is PRDS.** If for each true null `i` the whole p-value
vector is a coordinatewise nondecreasing function `F` of `p i`, then `p` is PRDS on `H0`: the
conditional probability of an increasing set is the indicator of the upper set `F ⁻¹' D`. The
comonotone family `p j = U` for all `j` (perfect positive dependence) is the main instance. -/
theorem isPRDSOn_of_monotone_comp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i)) (H0 : Finset (Fin m))
    (hF : ∀ i ∈ H0, ∃ F : ℝ → Fin m → ℝ, Monotone F ∧ ∀ ω, (fun j => p j ω) = F (p i ω)) :
    IsPRDSOn μ p H0 := by
  classical
  rw [isPRDSOn_iff_setLIntegral μ p hp H0]
  intro i hi D hD hup
  obtain ⟨F, hFm, hFeq⟩ := hF i hi
  have hFmeas : Measurable F :=
    Measurable.of_eval fun j => (show Monotone fun x => F x j from fun _ _ h => hFm h j).measurable
  have hE : MeasurableSet (F ⁻¹' D) := hFmeas hD
  refine ⟨(F ⁻¹' D).indicator 1, ?_, fun B hB => ?_⟩
  · intro x y hxy
    by_cases hx : x ∈ F ⁻¹' D
    · simp [Set.indicator_of_mem hx, Set.indicator_of_mem ((hup.preimage hFm) hxy hx)]
    · simp [Set.indicator_of_notMem hx]
  · rw [lintegral_indicator_one hE, Measure.restrict_apply hE,
      Measure.map_apply (hp i) (hE.inter hB)]
    congr 1
    ext ω
    simp [hFeq ω, and_comm]

/-- **Independent p-values are PRDS** on every `H0`. Given `p i = x`, the other coordinates keep
their joint law, so `P(P ∈ D | p i = x)` is the probability that the vector with its `i`-th
coordinate set to `x` lies in `D`, which is nondecreasing in `x` when `D` is increasing. -/
theorem isPRDSOn_of_iIndepFun {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    (hindep : iIndepFun p μ) (H0 : Finset (Fin m)) : IsPRDSOn μ p H0 := by
  classical
  rw [isPRDSOn_iff_setLIntegral μ p hp H0]
  intro i _ D hD hup
  let S : Set (Fin m) := {i}
  let T : Set (Fin m) := {j | j ≠ i}
  let W : Ω → T → ℝ := fun ω j => p j ω
  let G : ℝ × (T → ℝ) → Fin m → ℝ := fun z j => if h : j = i then z.1 else z.2 ⟨j, h⟩
  have hW : Measurable W := Measurable.of_eval fun j => hp j
  have hG : Measurable G := by
    refine Measurable.of_eval fun j => ?_
    by_cases h : j = i
    · simp only [G, h, dite_true]
      exact measurable_fst
    · simp only [G, h, dite_false]
      exact (measurable_pi_apply (⟨j, h⟩ : T)).comp measurable_snd
  have hPG (ω : Ω) : (fun j => p j ω) = G (p i ω, W ω) := by
    funext j
    by_cases h : j = i
    · subst h; simp [G]
    · simp [G, W, h]
  have hSet : MeasurableSet (G ⁻¹' D) := hG hD
  have hST : Disjoint S T := Set.disjoint_left.mpr fun j hj hj' => hj' (Set.mem_singleton_iff.mp hj)
  have hind : IndepFun (p i) W μ :=
    (iIndepFun.indepFun_set S T hST hindep hp).comp
      (measurable_pi_apply (⟨i, Set.mem_singleton i⟩ : S)) measurable_id
  let ρ := μ.map W
  refine ⟨fun x => ρ (Prod.mk x ⁻¹' (G ⁻¹' D)), ?_, fun B hB => ?_⟩
  · intro x y hxy
    refine measure_mono fun w hw => hup ?_ hw
    intro j
    by_cases h : j = i
    · simp [G, h, hxy]
    · simp [G, h]
  · have hpre : {ω | (fun j => p j ω) ∈ D} ∩ p i ⁻¹' B =
        (fun ω => (p i ω, W ω)) ⁻¹' ((B ×ˢ Set.univ) ∩ G ⁻¹' D) := by
      ext ω
      simp [hPG ω, and_comm]
    have hslice (x : ℝ) : ρ (Prod.mk x ⁻¹' ((B ×ˢ Set.univ) ∩ G ⁻¹' D)) =
        B.indicator (fun x => ρ (Prod.mk x ⁻¹' (G ⁻¹' D))) x := by
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

private theorem bhIndex_antitone {q : ℝ} {x y : Fin m → ℝ} (hxy : x ≤ y) :
    bhIndex q y ≤ bhIndex q x :=
  le_bhIndex (bhIndex_le q y) ((bhIndex_le_numBelow q y).trans
    (Finset.card_le_card fun j hj => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact (hxy j).trans hj))

private theorem sum_Icc_sub_le_of_le_succ {u : ℕ → ℕ → ℝ} (hu : ∀ k, u k k ≤ u k (k + 1))
    (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, (u k k - u (k - 1) k) ≤ u n n - u 0 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
    linarith [hu n]

/-- The PRDS step of the Benjamini–Yekutieli proof: under PRDS the BH contribution of a valid
true null `i` has expectation at most `q / m`. With `K` the leave-`i`-out BH index (nonincreasing
in the p-values, so `{K ≤ j}` is increasing), `t_k = q k / m` and
`ρ_j(t) = P(K ≤ j | p i ≤ t)`, the contribution is at most
`(q / m) ∑_k (ρ_k(t_k) - ρ_{k-1}(t_k)) ≤ (q / m) ρ_m(t_m) ≤ q / m`, the first step by validity
and the second by telescoping, since PRDS makes each `ρ_j` nondecreasing. -/
private theorem integral_bh_contribution_le_of_isPRDSOn {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    {H0 : Finset (Fin m)} (hprds : IsPRDSOn μ p H0) {i : Fin m} (hi : i ∈ H0)
    (hnull : IsValidPValue μ (p i)) {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, (∑ k ∈ Finset.Icc 1 m,
      {ω | p i ω ≤ q * (k : ℝ) / m ∧
        bhIndex q (Function.update (fun j => p j ω) i 0) = k}.indicator
        (fun _ => 1 / (k : ℝ)) ω) ∂μ ≤ q / m := by
  classical
  have hm : 0 < m := i.pos
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  let t : ℕ → ℝ := fun k => q * (k : ℝ) / m
  let κ : (Fin m → ℝ) → ℕ := fun x => bhIndex q (Function.update x i 0)
  have hκ : Measurable κ :=
    measurable_bh_update (fun j (x : Fin m → ℝ) => x j) (fun j => measurable_pi_apply j) q i
  let D : ℕ → Set (Fin m → ℝ) := fun j => {x | κ x ≤ j}
  have hD (j : ℕ) : MeasurableSet (D j) := measurableSet_le hκ measurable_const
  have hDup (j : ℕ) : IsUpperSet (D j) := by
    intro x y hxy hx
    refine le_trans (bhIndex_antitone ?_) hx
    intro l
    by_cases hl : l = i
    · simp [hl]
    · simp [Function.update_of_ne hl, hxy l]
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
      μ.real {ω | p i ω ≤ s ∧ bhIndex q (Function.update (fun j => p j ω) i 0) = k} =
        a k s - a (k - 1) s := by
    have hunion : {ω | (fun l => p l ω) ∈ D k} ∩ {ω | p i ω ≤ s} =
        {ω | p i ω ≤ s ∧ bhIndex q (Function.update (fun j => p j ω) i 0) = k} ∪
          ({ω | (fun l => p l ω) ∈ D (k - 1)} ∩ {ω | p i ω ≤ s}) := by
      ext ω
      simp only [D, κ, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_ge (bhIndex q (Function.update (fun j => p j ω) i 0)) k with h | h
        · exact Or.inr ⟨by omega, h2⟩
        · exact Or.inl ⟨h2, by omega⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h2.le, h1⟩
        · exact ⟨by omega, h2⟩
    have hdisj : Disjoint
        {ω | p i ω ≤ s ∧ bhIndex q (Function.update (fun j => p j ω) i 0) = k}
        ({ω | (fun l => p l ω) ∈ D (k - 1)} ∩ {ω | p i ω ≤ s}) := by
      refine Set.disjoint_left.mpr fun ω h1 h2 => ?_
      simp only [D, κ, Set.mem_inter_iff, Set.mem_ofPred_eq] at h1 h2
      omega
    have h := measureReal_union (μ := μ) hdisj ((hP (hD (k - 1))).inter
      (measurableSet_le (hp i) measurable_const))
    simp only [a]
    rw [hunion, h]
    ring
  have hterm (k : ℕ) (hk : k ∈ Finset.Icc 1 m) :
      μ.real {ω | p i ω ≤ q * (k : ℝ) / m ∧
          bhIndex q (Function.update (fun j => p j ω) i 0) = k} * (1 / (k : ℝ)) ≤
        q / m * (ρ k (t k) - ρ (k - 1) (t k)) := by
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    set A := μ.real {ω | p i ω ≤ q * (k : ℝ) / m ∧
      bhIndex q (Function.update (fun j => p j ω) i 0) = k} with hAdef
    have hΔ : ρ k (t k) - ρ (k - 1) (t k) = A / π (t k) := by
      simp only [ρ]
      rw [← sub_div]
      exact congrArg (· / π (t k)) (hA k hk1 (t k)).symm
    rw [hΔ]
    have hAle : A ≤ π (t k) := measureReal_mono fun ω hω => hω.1
    have hπt : π (t k) ≤ t k := valid_measureReal_le μ (p i) hnull (threshold_nonneg hq₀)
      (threshold_le_one hq₁ hm hk2)
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hA0 : 0 ≤ A := measureReal_nonneg
    rcases (measureReal_nonneg : 0 ≤ π (t k)).eq_or_lt with h0 | hpos
    · have : A = 0 := le_antisymm (hAle.trans h0.symm.le) hA0
      simp [this]
    · have hπ0 : π (t k) ≠ 0 := hpos.ne'
      calc A * (1 / (k : ℝ)) = A / π (t k) * π (t k) / k := by field_simp
        _ ≤ A / π (t k) * t k / k := by gcongr
        _ = q / m * (A / π (t k)) := by simp only [t]; field_simp
  have hevent (k : ℕ) : MeasurableSet {ω | p i ω ≤ q * (k : ℝ) / m ∧
      bhIndex q (Function.update (fun j => p j ω) i 0) = k} :=
    (measurableSet_le (hp i) measurable_const).inter
      (measurableSet_eq_fun (measurable_bh_update p hp q i) measurable_const)
  have hρ0 (s : ℝ) : ρ 0 s = 0 := by
    have : a 0 s = 0 := by
      simp only [a]
      convert measureReal_empty (μ := μ)
      refine Set.eq_empty_of_forall_notMem fun ω hω => ?_
      have h1 := bhIndex_update_pos hq₀ (fun j => p j ω) i
      simp only [D, κ, Set.mem_inter_iff, Set.mem_ofPred_eq] at hω
      omega
    simp [ρ, this]
  have hρm : ρ m (t m) ≤ 1 := div_le_one_of_le₀ (ha_le m (t m)) measureReal_nonneg
  rw [integral_finsetSum (Finset.Icc 1 m) (fun (k : ℕ) _ =>
    (integrable_const (μ := μ) (1 / (k : ℝ))).indicator (hevent k))]
  simp_rw [integral_indicator_const _ (hevent _), smul_eq_mul]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 m, q / m * (ρ k (t k) - ρ (k - 1) (t k)) :=
      Finset.sum_le_sum hterm
    _ = q / m * ∑ k ∈ Finset.Icc 1 m, (ρ k (t k) - ρ (k - 1) (t k)) := by rw [Finset.mul_sum]
    _ ≤ q / m * (ρ m (t m) - ρ 0 (t 0)) := mul_le_mul_of_nonneg_left
      (sum_Icc_sub_le_of_le_succ (u := fun k l => ρ k (t l))
        (fun k => hρ_mono k (threshold_mono hq₀ (Nat.le_succ k))) m) (by positivity)
    _ ≤ q / m * 1 := by
      gcongr
      rw [hρ0]
      linarith
    _ = q / m := mul_one _

/-- **Benjamini–Yekutieli FDR control under PRDS.** If the p-values are PRDS on the set `H0` of
true nulls (`IsPRDSOn`) and every true-null p-value is valid (super-uniform:
`μ {p i ≤ t} ≤ t` for `t ∈ [0, 1]`), then the unmodified BH procedure at level `q ∈ [0, 1]` has
false discovery rate at most `q |H0| / m`. Nothing is assumed about the false-null p-values beyond
measurability and the joint PRDS condition. Independent p-values are PRDS
(`isPRDSOn_of_iIndepFun`), so this generalizes
`integral_falseDiscoveryProportion_bhRejections_le_of_isValidPValue`. (For `m = 0` both sides
are `0`.)

Source: Benjamini & Yekutieli, *The control of the false discovery rate in multiple testing under
dependency*, Ann. Statist. 29 (2001), 1165–1188, Theorem 1.2. -/
theorem integral_falseDiscoveryProportion_bhRejections_le_of_isPRDSOn {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Fin m → Ω → ℝ)
    (hp : ∀ i, Measurable (p i)) (H0 : Finset (Fin m)) (hprds : IsPRDSOn μ p H0)
    (hnull : ∀ i ∈ H0, IsValidPValue μ (p i)) (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion H0 (bhRejections q fun i => p i ω) ∂μ ≤ q * H0.card / m := by
  calc
    _ ≤ H0.card * (q / m) := integral_fdp_bhRejections_le_card_mul μ p hp H0 hq₀ fun i hi =>
      integral_bh_contribution_le_of_isPRDSOn μ p hp hprds hi (hnull i hi) hq₀ hq₁
    _ = q * H0.card / m := by ring

end MathlibExt.Probability.Statistics.MultipleTesting
