/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.PermutationPValue
public import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Fin

/-!
# Split-conformal coverage through the permutation p-value

Let `ω : Fin (n + 1) → ℝ` be a vector of scores: `n` calibration scores `ω i.castSucc` and one
test score `ω (Fin.last n)`. For a miscoverage level `α`, put `k = ⌈(1 - α)(n + 1)⌉`. The split
conformal threshold `q̂` is the `k`-th smallest calibration score (counted with multiplicity) when
`k ≤ n`, and `+∞` otherwise. If the law of `ω` is invariant under all coordinate permutations,
the test score is covered, `ω (Fin.last n) ≤ q̂`, with probability at least
`k / (n + 1) ≥ 1 - α`.

The recorded scope of this result is `0 < α < 1`. The coverage theorems assume only `0 ≤ α < 1`:
the endpoint `α = 0` (`k = n + 1`, `q̂ = +∞`, coverage `1`) is a derived trivial case, not
attributed to the sources.

The proof goes through the existing permutation p-value
`MathlibExt.Probability.Statistics.MultipleTesting.permutationPValue`, with the coordinate
permutation action of `Equiv.Perm (Fin (n + 1))` and the test coordinate as the statistic.
Writing `L` for the number of calibration scores strictly below the test score, the p-value is
`(n + 1 - L) / (n + 1)`, and `ω (Fin.last n) ≤ q̂ ↔ L < k ↔ α < p`. Validity of the permutation
p-value at the grid level `(n + 1 - k) / (n + 1)` then gives the coverage bound. Ties are allowed
throughout, and the test score is covered when it equals `q̂`.

## Main definitions

* `orderStatistic f k`: the `k`-th smallest value of `f : ι → ℝ` counted with multiplicity, in
  `WithTop ℝ`; it is `⊤` when `k` exceeds the number of values.
* `coordinatePermAction`: the scoped action `(σ • ω) i = ω (σ⁻¹ i)` of `Equiv.Perm ι` on `ι → β`
  (`arrowAction`).
* `strictLowerCount ω`: the number `L` of calibration scores strictly below the test score.
* `splitConformalThreshold k ω`: the threshold `q̂`, the `k`-th smallest calibration score.

## Main results

* `coe_le_orderStatistic_iff`, `orderStatistic_eq_coe_iff`, `orderStatistic_eq_top_iff`: the
  order statistic is characterised by strict and weak counts.
* `orderStatistic_le_coe_iff`: `orderStatistic f k ≤ x ↔ k ≤ #{i | f i ≤ x}`, the weak-count dual.
* `permutationPValue_eval_last`: the coordinate-permutation p-value of the test coordinate is
  `(n + 1 - L) / (n + 1)`.
* `coe_le_splitConformalThreshold_iff`: `ω (Fin.last n) ≤ q̂ ↔ L < k`.
* `coe_le_splitConformalThreshold_iff_lt_permutationPValue`: `ω (Fin.last n) ≤ q̂ ↔ α < p`.
* `ofReal_ceil_div_le_measure_coe_le_splitConformalThreshold`: coverage is at least
  `⌈(1 - α)(n + 1)⌉ / (n + 1)`.
* `ofReal_one_sub_le_measure_coe_le_splitConformalThreshold`: coverage is at least `1 - α`.

This is the conservative marginal guarantee only. Exact coverage `k / (n + 1)` without ties,
weighted or conditional variants, and efficiency are not formalized here.

## References

* V. Vovk, A. Gammerman and G. Shafer, *Algorithmic Learning in a Random World*, Springer (2005).
* J. Lei, M. G'Sell, A. Rinaldo, R. J. Tibshirani and L. Wasserman, *Distribution-free predictive
  inference for regression*, J. Amer. Statist. Assoc. 113 (2018), 1094–1111.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.SplitConformal

open MeasureTheory Finset MathlibExt.Probability.Statistics.MultipleTesting

section OrderStatistic

variable {ι : Type*} [Fintype ι]

/-- **Order statistic with multiplicity.** The `k`-th smallest value of `f`, counted with
multiplicity: the least value `f i` such that at least `k` indices `j` satisfy `f j ≤ f i`. It
is `⊤` when no value qualifies, which for `1 ≤ k` happens exactly when `k > Fintype.card ι`
(`orderStatistic_eq_top_iff`). For `k = 0` it is the minimum of `f` (a junk value; the results
below assume `1 ≤ k`). -/
noncomputable def orderStatistic (f : ι → ℝ) (k : ℕ) : WithTop ℝ :=
  (univ.filter fun i => k ≤ (univ.filter fun j => f j ≤ f i).card).inf fun i => (f i : WithTop ℝ)

/-- **Strict-count criterion for the order statistic.** For `1 ≤ k`, a real `x` lies below the
`k`-th smallest value of `f` iff fewer than `k` values of `f` are strictly below `x`. -/
theorem coe_le_orderStatistic_iff {f : ι → ℝ} {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    (x : WithTop ℝ) ≤ orderStatistic f k ↔ (univ.filter fun i => f i < x).card < k := by
  constructor
  · intro hx
    by_contra hcon
    push Not at hcon
    have hne : (univ.filter fun i => f i < x).Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image _ f hne
    have hsub : (univ.filter fun i => f i < x) ⊆ univ.filter fun j => f j ≤ f i₀ := by
      intro j hj
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hmax j hj⟩
    have hmem : i₀ ∈ univ.filter fun i => k ≤ (univ.filter fun j => f j ≤ f i).card :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hcon.trans (Finset.card_le_card hsub)⟩
    have h₁ : orderStatistic f k ≤ (f i₀ : WithTop ℝ) := Finset.inf_le hmem
    have h₂ : f i₀ < x := (Finset.mem_filter.1 hi₀).2
    exact absurd (WithTop.coe_le_coe.1 (hx.trans h₁)) (not_le.2 h₂)
  · intro hx
    refine Finset.le_inf fun i hi => ?_
    rw [WithTop.coe_le_coe]
    by_contra hlt
    push Not at hlt
    have hsub : (univ.filter fun j => f j ≤ f i) ⊆ univ.filter fun j => f j < x := by
      intro j hj
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hj).2.trans_lt hlt⟩
    exact absurd ((Finset.mem_filter.1 hi).2.trans (Finset.card_le_card hsub)) (not_le.2 hx)

/-- **Weak-count criterion for the order statistic.** For `1 ≤ k`, the `k`-th smallest value of
`f` is at most a real `x` iff at least `k` values of `f` are at most `x`. This is the dual of
`coe_le_orderStatistic_iff`; it fails for `k = 0`. -/
theorem orderStatistic_le_coe_iff {f : ι → ℝ} {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    orderStatistic f k ≤ (x : WithTop ℝ) ↔ k ≤ (univ.filter fun i => f i ≤ x).card := by
  constructor
  · intro h
    set s := univ.filter fun i => k ≤ (univ.filter fun j => f j ≤ f i).card
    rcases s.eq_empty_or_nonempty with hs | hs
    · have htop : orderStatistic f k = ⊤ := by simp [orderStatistic, s, hs]
      rw [htop] at h
      exact absurd h (by simp)
    obtain ⟨i, hi, hinf⟩ := Finset.exists_mem_eq_inf s hs fun i => (f i : WithTop ℝ)
    have hfi : f i ≤ x := by
      have h' : (f i : WithTop ℝ) ≤ x := by
        rw [← hinf]
        exact h
      exact WithTop.coe_le_coe.1 h'
    refine (Finset.mem_filter.1 hi).2.trans (Finset.card_le_card fun j hj => ?_)
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hj).2.trans hfi⟩
  · intro h
    have hne : (univ.filter fun i => f i ≤ x).Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image _ f hne
    have hsub : (univ.filter fun i => f i ≤ x) ⊆ univ.filter fun j => f j ≤ f i₀ := by
      intro j hj
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hmax j hj⟩
    have hmem : i₀ ∈ univ.filter fun i => k ≤ (univ.filter fun j => f j ≤ f i).card :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, h.trans (Finset.card_le_card hsub)⟩
    exact (Finset.inf_le hmem).trans (WithTop.coe_le_coe.2 (Finset.mem_filter.1 hi₀).2)

/-- **Characterisation of the order statistic.** For `1 ≤ k`, the `k`-th smallest value of `f`
is `x` iff fewer than `k` values are strictly below `x` and at least `k` values are at most `x`:
the usual characterisation of the `k`-th order statistic with multiplicity. -/
theorem orderStatistic_eq_coe_iff {f : ι → ℝ} {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    orderStatistic f k = x ↔
      (univ.filter fun i => f i < x).card < k ∧ k ≤ (univ.filter fun i => f i ≤ x).card := by
  constructor
  · intro h
    refine ⟨(coe_le_orderStatistic_iff hk x).1 h.ge, ?_⟩
    set s := univ.filter fun i => k ≤ (univ.filter fun j => f j ≤ f i).card
    have hs : s.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro hs
      simp [orderStatistic, s, hs] at h
    obtain ⟨i, hi, hinf⟩ := Finset.exists_mem_eq_inf s hs fun i => (f i : WithTop ℝ)
    have hfi : f i = x := WithTop.coe_injective (hinf.symm.trans h)
    simpa [hfi] using (Finset.mem_filter.1 hi).2
  · rintro ⟨hlt, hle⟩
    have hnot : ∀ y : ℝ, x < y → ¬ ((y : WithTop ℝ) ≤ orderStatistic f k) := by
      intro y hxy hy
      rw [coe_le_orderStatistic_iff hk] at hy
      refine absurd (hle.trans (Finset.card_le_card ?_)) (not_le.2 hy)
      intro j hj
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hj).2.trans_lt hxy⟩
    have hge := (coe_le_orderStatistic_iff hk x).2 hlt
    revert hnot hge
    generalize orderStatistic f k = q
    intro hnot hge
    induction q with
    | top => exact absurd le_top (hnot (x + 1) (by linarith))
    | coe r =>
      rw [WithTop.coe_le_coe] at hge
      rcases hge.lt_or_eq with h | h
      · exact absurd le_rfl (hnot r h)
      · rw [h]

/-- **The order statistic is infinite exactly past the sample size.** For `1 ≤ k`, the `k`-th
smallest value of `f` is `⊤` exactly when `f` has fewer than `k` values. -/
theorem orderStatistic_eq_top_iff (f : ι → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    orderStatistic f k = ⊤ ↔ Fintype.card ι < k := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
    have hall : (univ.filter fun i => f i < M + 1) = univ :=
      Finset.filter_true_of_mem fun i _ => (hM ⟨i, rfl⟩).trans_lt (lt_add_one M)
    have := (coe_le_orderStatistic_iff hk (M + 1)).1 (h ▸ le_top)
    rw [hall, Finset.card_univ] at this
    omega
  · intro h
    have hall : ∀ x : ℝ, (x : WithTop ℝ) ≤ orderStatistic f k := fun x =>
      (coe_le_orderStatistic_iff hk x).2 ((Finset.card_le_univ _).trans_lt h)
    revert hall
    generalize orderStatistic f k = q
    intro hall
    induction q with
    | top => rfl
    | coe r =>
      have := WithTop.coe_le_coe.1 (hall (r + 1))
      linarith

end OrderStatistic

section SplitConformal

/-- **Coordinate-permutation action.** The action of `Equiv.Perm ι` on vectors `ι → β`,
`(σ • ω) i = ω (σ⁻¹ i)`. This is `arrowAction`, made available as a scoped instance. -/
scoped instance coordinatePermAction (ι β : Type*) : MulAction (Equiv.Perm ι) (ι → β) :=
  arrowAction

/-- **Entries of a permuted vector.** The coordinate-permutation action moves the entry at
`σ⁻¹ i` to position `i`. -/
theorem coordinatePermAction_smul_apply {ι β : Type*} (σ : Equiv.Perm ι) (ω : ι → β) (i : ι) :
    (σ • ω) i = ω (σ⁻¹ i) :=
  rfl

/-- **Permutation-invariant laws are invariant under the action.** A law on `ι → β` that is
invariant under every coordinate permutation `ω ↦ ω ∘ σ` is invariant under the
coordinate-permutation action. -/
theorem smulInvariantMeasure_of_map_comp_eq {ι β : Type*} [MeasurableSpace β]
    {μ : Measure (ι → β)} (hμ : ∀ σ : Equiv.Perm ι, μ.map (fun ω => ω ∘ σ) = μ) :
    SMulInvariantMeasure (Equiv.Perm ι) (ι → β) μ := by
  refine ⟨fun σ s hs => ?_⟩
  have hmeas : Measurable fun ω : ι → β => ω ∘ ⇑σ⁻¹ :=
    Measurable.of_eval fun i => measurable_pi_apply _
  have h := congrArg (fun ν : Measure (ι → β) => ν s) (hμ σ⁻¹)
  simp only [Measure.map_apply hmeas hs] at h
  exact h

variable {n : ℕ}

/-- **Strict lower count of the test score.** The number of calibration scores `ω i.castSucc`
strictly below the test score `ω (Fin.last n)`. -/
noncomputable def strictLowerCount (ω : Fin (n + 1) → ℝ) : ℕ :=
  (univ.filter fun i : Fin n => ω i.castSucc < ω (Fin.last n)).card

/-- **Split conformal threshold.** The `k`-th smallest calibration score `ω i.castSucc` (with
multiplicity), and `⊤` when `k > n`. -/
noncomputable def splitConformalThreshold (k : ℕ) (ω : Fin (n + 1) → ℝ) : WithTop ℝ :=
  orderStatistic (fun i : Fin n => ω i.castSucc) k

/-- **Coverage through the strict lower count.** For `1 ≤ k`, the test score is covered by the
threshold iff fewer than `k` calibration scores lie strictly below it, i.e. `L ≤ k - 1`. -/
theorem coe_le_splitConformalThreshold_iff {k : ℕ} (hk : 1 ≤ k) (ω : Fin (n + 1) → ℝ) :
    (ω (Fin.last n) : WithTop ℝ) ≤ splitConformalThreshold k ω ↔ strictLowerCount ω < k :=
  coe_le_orderStatistic_iff hk _

private theorem card_filter_le_last_add_strictLowerCount (ω : Fin (n + 1) → ℝ) :
    (univ.filter fun i : Fin (n + 1) => ω (Fin.last n) ≤ ω i).card + strictLowerCount ω =
      n + 1 := by
  rw [strictLowerCount, Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [le_refl, ite_true]
  rw [add_right_comm, ← Finset.sum_add_distrib]
  have h : ∀ i : Fin n, ((if ω (Fin.last n) ≤ ω i.castSucc then 1 else 0) +
      (if ω i.castSucc < ω (Fin.last n) then 1 else 0) : ℕ) = 1 := by
    intro i
    by_cases hi : ω (Fin.last n) ≤ ω i.castSucc
    · simp [hi, not_lt.2 hi]
    · simp [hi, lt_of_not_ge hi]
  simp [h]

private theorem card_filter_inv_apply_eq {N : ℕ} (t i j : Fin N) :
    (univ.filter fun σ : Equiv.Perm (Fin N) => σ⁻¹ t = i).card =
      (univ.filter fun σ : Equiv.Perm (Fin N) => σ⁻¹ t = j).card := by
  refine Finset.card_bij' (fun σ _ => σ * Equiv.swap i j) (fun σ _ => σ * Equiv.swap i j)
    (fun σ hσ => ?_) (fun σ hσ => ?_) (fun σ _ => ?_) (fun σ _ => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply, hσ, Equiv.swap_apply_left]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply, hσ, Equiv.swap_apply_right]
  · simp [mul_assoc]
  · simp [mul_assoc]

/-- **Permutation p-value of the test score.** With the coordinate-permutation action
`(σ • ω) i = ω (σ⁻¹ i)` and the statistic `ω ↦ ω (Fin.last n)`, the permutation p-value is
`(n + 1 - L) / (n + 1)`, where `L` is the number of calibration scores strictly below the test
score. Each coordinate is moved to the test position by `n!` permutations. -/
theorem permutationPValue_eval_last (ω : Fin (n + 1) → ℝ) :
    permutationPValue (Equiv.Perm (Fin (n + 1))) (fun ω : Fin (n + 1) → ℝ => ω (Fin.last n)) ω =
      (n + 1 - strictLowerCount ω : ℝ) / (n + 1) := by
  set t := Fin.last n
  set c := (univ.filter fun σ : Equiv.Perm (Fin (n + 1)) => σ⁻¹ t = t).card
  set B := univ.filter fun i : Fin (n + 1) => ω t ≤ ω i
  have hfib : ∀ (s : Finset (Fin (n + 1))),
      ((univ.filter fun σ : Equiv.Perm (Fin (n + 1)) => σ⁻¹ t ∈ s)).card = s.card * c := by
    intro s
    rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm (Fin (n + 1)) => σ⁻¹ t)
      (s := univ.filter fun σ : Equiv.Perm (Fin (n + 1)) => σ⁻¹ t ∈ s) (t := s)
      (fun σ hσ => (Finset.mem_filter.1 (Finset.mem_coe.1 hσ)).2)]
    rw [Finset.card_eq_sum_ones s, Finset.sum_mul, one_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.filter_filter]
    refine Eq.trans ?_ (card_filter_inv_apply_eq t i t)
    congr 1
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hi, h⟩⟩
  have hA : (univ.filter fun σ : Equiv.Perm (Fin (n + 1)) =>
      ω t ≤ (σ • ω) t).card = B.card * c := by
    rw [← hfib B]
    congr 1
    ext σ
    simp [B, coordinatePermAction_smul_apply]
  have hU : (n + 1).factorial = (n + 1) * c := by
    have := hfib univ
    simp only [Finset.mem_univ, Finset.filter_true, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin] at this
    exact this
  have hc : (c : ℝ) ≠ 0 := by
    have : 0 < (n + 1).factorial := Nat.factorial_pos _
    rw [hU] at this
    exact_mod_cast (Nat.pos_of_mul_pos_left this).ne'
  have hB : (B.card : ℝ) = n + 1 - strictLowerCount ω := by
    have := card_filter_le_last_add_strictLowerCount ω
    have h' : (B.card : ℝ) + strictLowerCount ω = n + 1 := by exact_mod_cast this
    linarith
  unfold permutationPValue
  rw [hA, Fintype.card_perm, Fintype.card_fin, hU]
  push_cast
  rw [hB]
  field_simp

/-- **Rank threshold versus p-value threshold.** The strict lower count is below
`⌈(1 - α)(n + 1)⌉` iff `α` is below the coordinate-permutation p-value `(n + 1 - L) / (n + 1)`.
No restriction on `α` is needed. -/
theorem strictLowerCount_lt_ceil_iff_lt_permutationPValue (α : ℝ) (ω : Fin (n + 1) → ℝ) :
    strictLowerCount ω < ⌈(1 - α) * (n + 1)⌉₊ ↔
      α < permutationPValue (Equiv.Perm (Fin (n + 1)))
        (fun ω : Fin (n + 1) → ℝ => ω (Fin.last n)) ω := by
  rw [permutationPValue_eval_last, Nat.lt_ceil, lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

/-- **Split conformal coverage as a permutation test.** For `α < 1` and `k = ⌈(1 - α)(n + 1)⌉`,
the test score is covered by the threshold `q̂` (the `k`-th smallest calibration score, or `⊤` if
`k > n`) iff the coordinate-permutation p-value of the test coordinate exceeds `α`. Ties are
allowed. -/
theorem coe_le_splitConformalThreshold_iff_lt_permutationPValue {α : ℝ} (hα : α < 1)
    (ω : Fin (n + 1) → ℝ) :
    (ω (Fin.last n) : WithTop ℝ) ≤ splitConformalThreshold ⌈(1 - α) * (n + 1)⌉₊ ω ↔
      α < permutationPValue (Equiv.Perm (Fin (n + 1)))
        (fun ω : Fin (n + 1) → ℝ => ω (Fin.last n)) ω := by
  have hk : 1 ≤ ⌈(1 - α) * (n + 1)⌉₊ :=
    Nat.one_le_ceil_iff.2 (mul_pos (sub_pos.2 hα) (by positivity))
  rw [coe_le_splitConformalThreshold_iff hk, strictLowerCount_lt_ceil_iff_lt_permutationPValue]

/-- **Split conformal coverage at the grid level.** If the law `μ` of the score vector is a
probability measure invariant under every coordinate permutation, then with
`k = ⌈(1 - α)(n + 1)⌉` the test score is covered by the `k`-th smallest calibration score (`⊤` if
`k > n`) with probability at least `k / (n + 1)` (Vovk, Gammerman and Shafer 2005; Lei et al.
2018). The proof applies validity of the permutation p-value at the grid level
`(n + 1 - k) / (n + 1)`. The recorded scope is `0 < α < 1`; the statement assumes only
`0 ≤ α < 1`, and the endpoint `α = 0` (`k = n + 1`, coverage `1`) is a derived trivial case, not
attributed to the sources. -/
theorem ofReal_ceil_div_le_measure_coe_le_splitConformalThreshold
    (μ : Measure (Fin (n + 1) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ σ : Equiv.Perm (Fin (n + 1)), μ.map (fun ω => ω ∘ σ) = μ) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    ENNReal.ofReal (⌈(1 - α) * (n + 1)⌉₊ / (n + 1)) ≤
      μ {ω | (ω (Fin.last n) : WithTop ℝ) ≤ splitConformalThreshold ⌈(1 - α) * (n + 1)⌉₊ ω} := by
  set k := ⌈(1 - α) * (n + 1)⌉₊
  set C := {ω : Fin (n + 1) → ℝ |
    (ω (Fin.last n) : WithTop ℝ) ≤ splitConformalThreshold k ω}
  have hk1 : 1 ≤ k := Nat.one_le_ceil_iff.2 (mul_pos (sub_pos.2 hα1) (by positivity))
  have hkN : (k : ℝ) ≤ n + 1 := by
    have : k ≤ n + 1 := Nat.ceil_le.2 (by push_cast; nlinarith)
    exact_mod_cast this
  have hN : (0 : ℝ) < n + 1 := by positivity
  set t : ℝ := (n + 1 - k) / (n + 1)
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (by linarith) hN.le, (div_le_one hN).2 ?_⟩
    linarith [k.cast_nonneg (α := ℝ)]
  have := smulInvariantMeasure_of_map_comp_eq hμ
  have hvalid := isValidPValue_permutationPValue (G := Equiv.Perm (Fin (n + 1))) μ
    (fun σ => Measurable.of_eval fun i => by exact measurable_pi_apply (σ⁻¹ i))
    (measurable_pi_apply (Fin.last n))
  have hsub : Cᶜ ⊆ {ω | permutationPValue (Equiv.Perm (Fin (n + 1)))
      (fun ω : Fin (n + 1) → ℝ => ω (Fin.last n)) ω ≤ t} := by
    intro ω hω
    have hL : k ≤ strictLowerCount ω := by
      have := (not_congr (coe_le_splitConformalThreshold_iff hk1 ω)).1 hω
      omega
    have hL' : (k : ℝ) ≤ strictLowerCount ω := by exact_mod_cast hL
    simp only [Set.mem_ofPred_eq, permutationPValue_eval_last, t]
    exact div_le_div_of_nonneg_right (by linarith) hN.le
  have hcompl : μ Cᶜ ≤ ENNReal.ofReal t := (measure_mono hsub).trans (hvalid t ht)
  have h1 : (1 : ENNReal) ≤ μ C + ENNReal.ofReal t := by
    calc (1 : ENNReal) = μ (C ∪ Cᶜ) := by rw [Set.union_compl_self, measure_univ]
      _ ≤ μ C + μ Cᶜ := measure_union_le _ _
      _ ≤ μ C + ENNReal.ofReal t := by gcongr
  have hkt : (k : ℝ) / (n + 1) = 1 - t := by
    simp only [t]
    field_simp
    ring
  rw [hkt, ENNReal.ofReal_sub _ ht.1, ENNReal.ofReal_one]
  exact tsub_le_iff_right.2 h1

/-- **Split conformal coverage.** If the law of the score vector is a probability measure
invariant under every coordinate permutation, the test score is covered by the split conformal
threshold with probability at least `1 - α`. The recorded scope is `0 < α < 1`; the statement
assumes only `0 ≤ α < 1`, and the endpoint `α = 0` (coverage `1`) is a derived trivial case, not
attributed to the sources. -/
theorem ofReal_one_sub_le_measure_coe_le_splitConformalThreshold
    (μ : Measure (Fin (n + 1) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ σ : Equiv.Perm (Fin (n + 1)), μ.map (fun ω => ω ∘ σ) = μ) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    ENNReal.ofReal (1 - α) ≤
      μ {ω | (ω (Fin.last n) : WithTop ℝ) ≤ splitConformalThreshold ⌈(1 - α) * (n + 1)⌉₊ ω} := by
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (ofReal_ceil_div_le_measure_coe_le_splitConformalThreshold μ hμ hα0 hα1)
  rw [le_div_iff₀ (by positivity)]
  exact Nat.le_ceil _

end SplitConformal

end MathlibExt.Probability.Statistics.SplitConformal
