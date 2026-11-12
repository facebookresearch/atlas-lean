/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.ConditionalProbability

/-!
# Multiple testing: p-values, counts below a threshold, false discoveries

Common vocabulary for the multiple-testing procedures in this directory. A family of `m`
hypotheses is tested through p-values `p : Fin m → Ω → ℝ` on a probability space `(Ω, μ)`;
`H0 : Finset (Fin m)` is the (unknown) set of true null hypotheses. A procedure maps the
observed p-values `fun i => p i ω` to a rejection set `R : Finset (Fin m)`.

* `IsValidPValue μ X`: the p-value `X` is *valid* (super-uniform) under `μ`:
  `μ {X ≤ t} ≤ t` for every `t ∈ [0, 1]`. A p-value uniform on `[0, 1]` is valid
  (`isValidPValue_of_hasLaw_uniform`); valid p-values arise from discrete tests.
* `numBelow p t`: the number of p-values that are at most `t`. For the order statistics
  `p₍₁₎ ≤ ⋯ ≤ p₍ₘ₎` and `1 ≤ k ≤ m`, `p₍ₖ₎ ≤ t ↔ k ≤ numBelow p t` (with ties counted with
  multiplicity), which lets step-up and step-down procedures be stated without sorting.
* `falseDiscoveryProportion H0 R = |R ∩ H0| / max |R| 1`.

A rejection set `R` commits a *family-wise error* when `R ∩ H0` is nonempty; the family-wise
error rate (FWER) is the probability of this event.

## Main results

* `isValidPValue_of_hasLaw_uniform`: a p-value with law `Uniform[0, 1]` is valid.
* `isValidPValue_of_forall_cond`: a p-value that is valid conditionally on each value of a
  bounded count is valid unconditionally.
* `falseDiscoveryProportion_nonneg`, `falseDiscoveryProportion_le_one`, `fdp_eq_sum`.
* `valid_measureReal_le`: the real-valued form of validity.
* `suIdx`: the step-up index for a fixed threshold sequence `c`, with `suIdx_le`,
  `suIdx_le_numBelow`, `le_suIdx`, `numBelow_suIdx`, `suIdx_eq_sup`.
* `numBelow_update_le`, `numBelow_update_eq`, `su_leave_one_out`: replacing one p-value by `0`
  (the leave-one-out step of the BH and Storey-BH FDR proofs).
* `measurable_numBelow`, `measurable_numBelow_comp`, `measurable_suIdx_comp`: measurability of
  the count below a threshold and of the step-up index.

## References

* E. L. Lehmann and J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Springer (2005),
  §3.3 (p-values) and §9.1 (multiple testing).
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}

/-- A real random variable `X` is a *valid* (super-uniform) p-value under `μ` if
`μ {X ≤ t} ≤ t` for every level `t ∈ [0, 1]`. Uniform p-values are the equality case. -/
def IsValidPValue (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, μ {ω | X ω ≤ t} ≤ ENNReal.ofReal t

/-- A p-value distributed uniformly on `[0, 1]` is valid. -/
theorem isValidPValue_of_hasLaw_uniform {μ : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (volume.restrict (Set.Icc (0 : ℝ) 1)) μ) : IsValidPValue μ X := by
  intro t ht
  have h : μ {ω | X ω ≤ t} = volume.restrict (Set.Icc (0 : ℝ) 1) (Set.Iic t) := by
    rw [← hX.map_eq, Measure.map_apply_of_aemeasurable hX.aemeasurable measurableSet_Iic]
    rfl
  rw [h, Measure.restrict_apply measurableSet_Iic]
  calc volume (Set.Iic t ∩ Set.Icc 0 1) ≤ volume (Set.Icc 0 t) :=
        measure_mono fun x hx => ⟨hx.2.1, hx.1⟩
    _ = ENNReal.ofReal t := by simp

/-- **Validity from conditional validity.** Let `S` be a measurable count that is at most `N`
almost surely, and let `P` agree with `q (S ω)` wherever `S ω ≤ N`. If each `q t` is a valid
p-value conditionally on `S = t` (for `t ≤ N`), then `P` is valid under `μ`.

This is the law of total probability: `μ {P ≤ s} ≤ ∑ₜ μ {S = t} μ[P ≤ s | S = t] ≤ s`. -/
theorem isValidPValue_of_forall_cond {μ : Measure Ω} [IsProbabilityMeasure μ] {S : Ω → ℕ}
    (hS : Measurable S) {N : ℕ} (hSN : ∀ᵐ ω ∂μ, S ω ≤ N) {P : Ω → ℝ} {q : ℕ → Ω → ℝ}
    (hPq : ∀ ω, S ω ≤ N → P ω = q (S ω) ω)
    (hq : ∀ t ≤ N, IsValidPValue (μ[|S ⁻¹' {t}]) (q t)) : IsValidPValue μ P := by
  intro s hs
  have hsub : {ω | P ω ≤ s} ≤ᵐ[μ]
      (⋃ t ∈ Finset.range (N + 1), S ⁻¹' {t} ∩ {ω | q t ω ≤ s} : Set Ω) := by
    filter_upwards [hSN] with ω hω hP
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_ofPred_eq, Finset.mem_range, exists_prop]
    exact ⟨S ω, Nat.lt_succ_of_le hω, rfl, by rwa [← hPq ω hω]⟩
  have hdisj : (Finset.range (N + 1) : Set ℕ).PairwiseDisjoint fun t => S ⁻¹' {t} :=
    fun a _ b _ hab => Set.disjoint_left.2 fun ω ha hb => hab (ha.symm.trans hb)
  calc μ {ω | P ω ≤ s}
      ≤ μ (⋃ t ∈ Finset.range (N + 1), S ⁻¹' {t} ∩ {ω | q t ω ≤ s}) := measure_mono_ae hsub
    _ ≤ ∑ t ∈ Finset.range (N + 1), μ (S ⁻¹' {t} ∩ {ω | q t ω ≤ s}) := measure_biUnion_finset_le _ _
    _ = ∑ t ∈ Finset.range (N + 1), μ[{ω | q t ω ≤ s} | S ⁻¹' {t}] * μ (S ⁻¹' {t}) :=
        Finset.sum_congr rfl fun t _ =>
          (cond_mul_eq_inter (hS (measurableSet_singleton t)) _ μ).symm
    _ ≤ ∑ t ∈ Finset.range (N + 1), ENNReal.ofReal s * μ (S ⁻¹' {t}) := by
        gcongr with t ht
        exact hq t (Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)) s hs
    _ = ENNReal.ofReal s * μ (⋃ t ∈ Finset.range (N + 1), S ⁻¹' {t}) := by
        rw [← Finset.mul_sum,
          measure_biUnion_finset hdisj fun t _ => hS (measurableSet_singleton t)]
    _ ≤ ENNReal.ofReal s * 1 := by gcongr; exact prob_le_one
    _ = ENNReal.ofReal s := mul_one _

/-- The number of p-values that are at most `t`. -/
noncomputable def numBelow (p : Fin m → ℝ) (t : ℝ) : ℕ :=
  (Finset.univ.filter fun i => p i ≤ t).card

/-- At most `m` p-values lie below any threshold. -/
theorem numBelow_le (p : Fin m → ℝ) (t : ℝ) : numBelow p t ≤ m := by
  simpa [numBelow] using Finset.card_filter_le Finset.univ fun i => p i ≤ t

/-- `numBelow p` is monotone in the threshold. -/
theorem numBelow_mono (p : Fin m → ℝ) {s t : ℝ} (hst : s ≤ t) : numBelow p s ≤ numBelow p t :=
  Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.trans hst

/-- The false discovery proportion of a rejection set `R` when `H0` is the set of true nulls:
`|R ∩ H0| / max |R| 1` (zero when nothing is rejected). -/
noncomputable def falseDiscoveryProportion (H0 R : Finset (Fin m)) : ℝ :=
  ((R ∩ H0).card : ℝ) / max (R.card : ℝ) 1

/-- The false discovery proportion is nonnegative. -/
theorem falseDiscoveryProportion_nonneg (H0 R : Finset (Fin m)) :
    0 ≤ falseDiscoveryProportion H0 R := by
  unfold falseDiscoveryProportion
  positivity

/-- The false discovery proportion is at most one. -/
theorem falseDiscoveryProportion_le_one (H0 R : Finset (Fin m)) :
    falseDiscoveryProportion H0 R ≤ 1 := by
  unfold falseDiscoveryProportion
  rw [div_le_one (by positivity)]
  exact le_max_of_le_left (by exact_mod_cast Finset.card_le_card Finset.inter_subset_left)

/-- Rounding a valid p-value upward (a.e.) preserves validity. -/
theorem IsValidPValue.mono_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {p p' : Ω → ℝ}
    (hp : IsValidPValue μ p) (hle : ∀ᵐ ω ∂μ, p ω ≤ p' ω) :
    IsValidPValue μ p' := by
  intro t ht
  have hsub : {ω | p' ω ≤ t} ≤ᵐ[μ] {ω | p ω ≤ t} :=
    hle.mono fun ω hω hp' => le_trans hω hp'
  exact (measure_mono_ae hsub).trans (hp t ht)

/-- A valid p-value is below `t` with real probability at most `t`, for `t ∈ [0, 1]`. -/
theorem valid_measureReal_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : IsValidPValue μ X) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    μ.real {ω | X ω ≤ t} ≤ t :=
  ENNReal.toReal_le_of_le_ofReal ht₀ (hX t ⟨ht₀, ht₁⟩)

/-- The FDP as a sum over true nulls of the per-hypothesis contributions
`1[i ∈ R] / max |R| 1`. -/
theorem fdp_eq_sum (H0 R : Finset (Fin m)) :
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

/-! ### Leave-one-out: replacing one p-value by `0` -/

/-- Replacing a p-value by `0` does not decrease the number of p-values below a threshold
`t ≥ 0`. -/
theorem numBelow_update_le (p : Fin m → ℝ) (i : Fin m) {t : ℝ}
    (ht : 0 ≤ t) : numBelow p t ≤ numBelow (Function.update p i 0) t := by
  classical
  apply Finset.card_le_card
  intro j hj
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  by_cases hji : j = i
  · simpa [hji] using ht
  · simpa [Function.update_of_ne hji] using (Finset.mem_filter.mp hj).2

/-- Replacing a p-value `p i ≤ t` by `0` does not change the number of p-values below a
threshold `t ≥ 0`. -/
theorem numBelow_update_eq (p : Fin m → ℝ) (i : Fin m) {t : ℝ}
    (ht : 0 ≤ t) (hpi : p i ≤ t) : numBelow (Function.update p i 0) t = numBelow p t := by
  classical
  unfold numBelow
  congr 1
  ext j
  by_cases hji : j = i
  · simp [hji, ht, hpi]
  · simp [Function.update_of_ne hji]

/-! ### Step-up procedures with a fixed threshold sequence -/

/-- Step-up index for an arbitrary threshold sequence `c`: the largest `k ∈ {0, …, m}` such that
at least `k` p-values are at most `c k` (`k = 0` always qualifies). The Benjamini–Hochberg index
is the case `c k = q k / m`. -/
noncomputable def suIdx (c : ℕ → ℝ) (p : Fin m → ℝ) : ℕ :=
  ((Finset.range (m + 1)).filter fun k : ℕ => k ≤ numBelow p (c k)).max' ⟨0, by simp⟩

/-- The step-up index lies in the set of qualifying indices it maximizes over. -/
theorem suIdx_mem (c : ℕ → ℝ) (p : Fin m → ℝ) :
    suIdx c p ∈ (Finset.range (m + 1)).filter fun k : ℕ => k ≤ numBelow p (c k) :=
  Finset.max'_mem _ _

/-- The step-up index is at most `m`. -/
theorem suIdx_le (c : ℕ → ℝ) (p : Fin m → ℝ) : suIdx c p ≤ m := by
  have h := suIdx_mem c p
  simp only [Finset.mem_filter, Finset.mem_range] at h
  omega

/-- At the step-up index `k`, at least `k` p-values are at most `c k`. -/
theorem suIdx_le_numBelow (c : ℕ → ℝ) (p : Fin m → ℝ) :
    suIdx c p ≤ numBelow p (c (suIdx c p)) := by
  have h := suIdx_mem c p
  simp only [Finset.mem_filter] at h
  exact h.2

/-- The step-up index is the largest `k ≤ m` with at least `k` p-values at most `c k`. -/
theorem le_suIdx {c : ℕ → ℝ} {p : Fin m → ℝ} {k : ℕ} (hk : k ≤ m)
    (h : k ≤ numBelow p (c k)) : k ≤ suIdx c p :=
  Finset.le_max' _ k (by simpa [Nat.lt_succ_iff] using ⟨hk, h⟩)

/-- For nondecreasing thresholds, exactly `suIdx c p` p-values are at most `c (suIdx c p)`. -/
theorem numBelow_suIdx {c : ℕ → ℝ} (hc : Monotone c) (p : Fin m → ℝ) :
    numBelow p (c (suIdx c p)) = suIdx c p := by
  refine le_antisymm ?_ (suIdx_le_numBelow c p)
  by_contra! hlt
  have hle : numBelow p (c (suIdx c p)) ≤ suIdx c p :=
    le_suIdx (numBelow_le p _) (numBelow_mono p (hc hlt.le))
  omega

/-- For nonnegative thresholds, replacing a p-value by `0` does not decrease the step-up
index. -/
theorem suIdx_le_update {c : ℕ → ℝ} (hc0 : ∀ k, 0 ≤ c k) (p : Fin m → ℝ)
    (i : Fin m) : suIdx c p ≤ suIdx c (Function.update p i 0) :=
  le_suIdx (suIdx_le c p) ((suIdx_le_numBelow c p).trans (numBelow_update_le p i (hc0 _)))

/-- For nonnegative thresholds, the step-up index is positive once some p-value is `0`. -/
theorem one_le_suIdx_update {c : ℕ → ℝ} (hc0 : ∀ k, 0 ≤ c k) (p : Fin m → ℝ)
    (i : Fin m) : 1 ≤ suIdx c (Function.update p i 0) := by
  apply le_suIdx (by have := i.isLt; omega)
  apply Finset.card_pos.mpr
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hc0 1⟩⟩

/-- For nonnegative thresholds, if `p i` is at most the threshold at the step-up index of the
vector with `p i` replaced by `0`, the replacement does not change the step-up index. -/
theorem suIdx_update_eq {c : ℕ → ℝ} (hc0 : ∀ k, 0 ≤ c k) (p : Fin m → ℝ)
    (i : Fin m) (hpi : p i ≤ c (suIdx c (Function.update p i 0))) :
    suIdx c p = suIdx c (Function.update p i 0) := by
  apply le_antisymm (suIdx_le_update hc0 p i)
  apply le_suIdx (suIdx_le c _)
  rw [← numBelow_update_eq p i (hc0 _) hpi]
  exact suIdx_le_numBelow c _

/-- Leave-one-out property of step-up procedures (with a threshold sequence that does not depend
on the data): `i` is rejected and `k` hypotheses are rejected iff `p i ≤ c k` and the procedure
applied with `p i` replaced by `0` rejects `k` hypotheses. -/
theorem su_leave_one_out {c : ℕ → ℝ} (hc : Monotone c) (hc0 : ∀ k, 0 ≤ c k)
    (p : Fin m → ℝ) (i : Fin m) (k : ℕ) :
    (p i ≤ c (suIdx c p) ∧ suIdx c p = k) ↔
      (p i ≤ c k ∧ suIdx c (Function.update p i 0) = k) := by
  constructor
  · rintro ⟨hpi, hk⟩
    have heq := suIdx_update_eq hc0 p i (hpi.trans (hc (suIdx_le_update hc0 p i)))
    exact ⟨hk ▸ hpi, heq.symm.trans hk⟩
  · rintro ⟨hpi, hk⟩
    have heq := suIdx_update_eq hc0 p i (by rwa [hk])
    exact ⟨by rw [heq, hk]; exact hpi, heq.trans hk⟩

/-! ### Measurability -/

/-- The number of measurable p-values below a fixed threshold is a measurable function. -/
theorem measurable_numBelow {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i)) (t : ℝ) :
    Measurable (fun ω => numBelow (fun i => p i ω) t) := by
  classical
  simp only [numBelow, Finset.card_filter]
  exact Finset.measurable_sum _ fun i _ => Measurable.ite
    (measurableSet_le (hp i) measurable_const) measurable_const measurable_const

/-- The number of measurable p-values below a measurable threshold is a measurable function. -/
theorem measurable_numBelow_comp {Y : Type*} [MeasurableSpace Y] (x : Y → Fin m → ℝ)
    (hx : ∀ j, Measurable fun y => x y j) {t : Y → ℝ} (ht : Measurable t) :
    Measurable fun y => numBelow (x y) (t y) := by
  classical
  simp only [numBelow, Finset.card_filter]
  exact Finset.measurable_sum _ fun j _ => Measurable.ite
    (measurableSet_le (hx j) ht) measurable_const measurable_const

/-- The step-up index as a finite supremum, the form used to prove measurability. -/
theorem suIdx_eq_sup (c : ℕ → ℝ) (p : Fin m → ℝ) :
    suIdx c p = (Finset.range (m + 1)).sup
      (fun k => if k ≤ numBelow p (c k) then k else 0) := by
  classical
  apply le_antisymm
  · have h := Finset.le_sup (f := fun (k : ℕ) => if k ≤ numBelow p (c k) then k else 0)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (suIdx_le c p)))
    simpa [suIdx_le_numBelow c p] using h
  · apply Finset.sup_le
    intro k hk
    split_ifs with h
    · exact le_suIdx (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) h
    · exact Nat.zero_le _

/-- The step-up index is measurable when both the thresholds and the p-values depend
measurably on a parameter `y`. -/
theorem measurable_suIdx_comp {Y : Type*} [MeasurableSpace Y] (c : Y → ℕ → ℝ)
    (x : Y → Fin m → ℝ) (hc : ∀ k, Measurable fun y => c y k)
    (hx : ∀ j, Measurable fun y => x y j) : Measurable fun y => suIdx (c y) (x y) := by
  classical
  simp_rw [suIdx_eq_sup]
  have h : ∀ s : Finset ℕ, Measurable (fun y => s.sup
      (fun k => if k ≤ numBelow (x y) (c y k) then k else 0)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih =>
      simp only [Finset.sup_insert]
      exact (Measurable.ite (measurableSet_le measurable_const
        (measurable_numBelow_comp x hx (hc k))) measurable_const measurable_const).max ih
  exact h _

end MathlibExt.Probability.Statistics.MultipleTesting
