/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.ScoreSignificance.GumbelTail
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Process.HittingTime

/-!
# Ladder input from the Cramér conditions

Scores `X 0, X 1, …` satisfying `CramerScores` (i.i.d., `E X < 0`, Cramér root `θ > 0`) are
cut at the strict descending ladder epochs of their walk `S_k = X 0 + ⋯ + X (k - 1)`. This file
proves that the resulting excursions have the regenerative structure that `GumbelTail` takes as
the hypothesis `LadderInput`, and so turns that hypothesis into a theorem.

## Main results

* Pathwise. `descLadderEpoch` is `τ₋ = min {k ≥ 1 | S_k < 0}`; `ladderEpoch k` is the `k`-th
  epoch `T_k`, `excursionHeight i` the height `Yᵢ = max_{T_i ≤ j ≤ T_{i+1}} (S_j - S_{T_i})`,
  and `ladderCount n` the number `Nₙ` of excursions completed by time `n`. On ladder-good paths
  (`IsLadderGood`), `excursionHeight_le_maxSegmentScore` and `maxSegmentScore_le_of_forall` give
  the sandwich `max_{i < Nₙ} Yᵢ ≤ Mₙ ≤ max_{i ≤ Nₙ} Yᵢ` for the maximal segment score.
* Stopping time. `measurableSet_descLadderEpoch_eq`: `{τ₋ = t}` is determined by the first `t`
  scores; `descLadderEpoch_eq_hittingAfter`: `τ₋` (with value `⊤` if it is infinite) is
  Mathlib's `hittingAfter` of `(-∞, 0)` after time `1`; `isStoppingTime_descLadderEpoch`: it is
  a stopping time for the natural filtration of the score process.
* Strong Markov property. `infinitePi_strongMarkov` (canonical i.i.d. space) and
  `CramerScores.strongMarkov`: the path restarted at `τ₋` is independent of every event
  determined before `τ₋` and has the law of the original path
  (`CramerScores.map_pathShift_descLadderEpoch`).
* Finiteness. `mgf_half_lt_one`: `E e^{θX/2} < 1`. Chernoff then gives
  `P(τ₋ > k) ≤ P(S_k ≥ 0) ≤ (E e^{θX/2})^k`, so `τ₋ < ∞` almost surely, almost every path is
  ladder-good (`CramerScores.ae_isLadderGood`), and `E τ₋ < ∞`
  (`CramerScores.integrable_descLadderEpoch`), with `E τ₋ ≥ 1`.
* I.i.d. excursions. `iIndepFun_iterLadder`: any functional of the pre-`τ₋` path, evaluated on
  successive excursions, gives an i.i.d. sequence. Hence `CramerScores.iIndepFun_excursionHeight`
  and `CramerScores.identDistrib_excursionHeight` (heights i.i.d. with the law of the first
  excursion maximum) and i.i.d. excursion lengths.
* Renewal law of large numbers. `tendsto_ladderCount_div` (pathwise) and
  `CramerScores.ae_tendsto_ladderCount_div`: `Nₙ / n → 1 / A` almost surely, where
  `A = E τ₋` is the mean descending ladder epoch, by the strong law for `T_k / k`.
* **`CramerScores.toLadderInput`** and **`CramerScores.nonempty_ladderInput`**: the Cramér
  conditions imply `LadderInput P (maxSegmentScoreRV X)`, with `Y`, `N`, `F` and `A = E τ₋` as
  above (`toLadderInput_Y`, `toLadderInput_N`, `toLadderInput_F`, `toLadderInput_A`).

## Conventions

The ladder epochs are *strict descending* epochs, matching `LadderInput`, where `A` is the mean
length of a descending ladder excursion. The single-sequence file `SingleSequence` (T49) uses
*ascending* ladder epochs (`IsFirstLadder`) and a finite-alphabet product model, so its results
are not reused here; this file works with arbitrary real i.i.d. scores on a measure space.

## Implementation notes

All ladder quantities are functions of the path `x : ℕ → ℝ`, evaluated at `fun k => X k ω`.
The law of that path is the infinite product `Measure.infinitePi` of the score law
(`CramerScores.map_path`, from Mathlib's `iIndepFun.map_fun_eq_infinitePi_map`); stationarity
under shifts and independence of past and future come from `iIndepFun_infinitePi` and
`indep_iSup_of_disjoint`. Successive excursions are produced by `iterLadder`, which restarts
the path at `τ₋`, so the i.i.d. property follows from the strong Markov property by induction.
`ladderCount` is `Nat.findGreatest`, and `descLadderEpoch` takes the junk value `0` off the
null event `¬ HasDescLadder`.

Reuse search (base `547b71899`): Mathlib v4.35.0, CSLib and the Atlas libraries were searched
for ladder epochs, strong Markov property of random walks, renewal counting processes and
stopping times of i.i.d. sequences. Mathlib has `IsStoppingTime`, `Filtration.natural`, the
hitting time `hittingAfter` with `Adapted.isStoppingTime_hittingAfter`, `Measure.infinitePi`,
`strong_law_ae`, Chernoff (`measure_ge_le_exp_mul_mgf`) and `indep_iSup_of_disjoint`, all
reused. `descLadderEpoch` is the `ℕ`-valued form of the hitting time of `(-∞, 0)` after time
`1` by the walk (`descLadderEpoch_eq_hittingAfter`); the `ℕ`-valued form is kept because the
shift recursion `iterLadder` and the sums `T_k` need finite values. Mathlib has no strong
Markov property for random walks and no renewal theorem. `segmentScore`, `maxSegmentScore`,
`CramerScores` and `LadderInput` come from `GumbelTail`.

Not covered: the renewal theorem for the excursion-height tail `P(Y > t) ~ C e^{-θ t}` (the
remaining hypothesis of `NonlatticeRenewalInput` / `LatticeRenewalInput`), and the
identification of `C`.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II, 2nd ed.,
  Wiley (1971), Chapters XI (renewal theory) and XII (ladder variables).
* S. Asmussen, *Applied Probability and Queues*, 2nd ed., Springer (2003) (renewal theory,
  ladder heights of random walks).
* R. Durrett, *Probability: Theory and Examples*, 4th ed., Cambridge (2010), §2.4 (renewal
  counting) and §4.1 (stopping times and the strong Markov property for random walks).
* S. Karlin and A. Dembo, *Limit distributions of maximal segmental score among Markov-dependent
  partial sums*, Adv. Appl. Probab. 24 (1992), 113–140.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Alignment.ScoreSignificance.LadderDerivation

open MeasureTheory ProbabilityTheory Filter Topology Finset

/-! ## Pathwise layer -/

/-- The path `x t, x (t + 1), …` seen from time `t`: the score sequence after its first `t`
scores. -/
def pathShift (t : ℕ) (x : ℕ → ℝ) : ℕ → ℝ := fun j => x (t + j)

@[simp] theorem pathShift_apply (t : ℕ) (x : ℕ → ℝ) (j : ℕ) : pathShift t x j = x (t + j) := rfl

@[simp] theorem pathShift_zero (x : ℕ → ℝ) : pathShift 0 x = x := by
  ext j; simp

theorem pathShift_pathShift (s t : ℕ) (x : ℕ → ℝ) :
    pathShift s (pathShift t x) = pathShift (t + s) x := by
  ext j; simp [add_assoc]

/-- Partial sums of a shifted path are increments of the original walk. -/
theorem sum_range_pathShift (t k : ℕ) (x : ℕ → ℝ) :
    ∑ i ∈ range k, pathShift t x i = ∑ i ∈ range (t + k), x i - ∑ i ∈ range t, x i := by
  rw [sum_range_add]; simp

/-- The walk `S_k = x 0 + ⋯ + x (k - 1)` eventually drops strictly below its start `S₀ = 0`:
there is a strict descending ladder epoch. -/
def HasDescLadder (x : ℕ → ℝ) : Prop := ∃ k, 0 < k ∧ ∑ i ∈ range k, x i < 0

/-- The **first strict descending ladder epoch** `τ₋ = min {k ≥ 1 | S_k < 0}` of the walk
`S_k = x 0 + ⋯ + x (k - 1)`; it is `0` (a junk value) when the walk never drops below `0`
(`¬ HasDescLadder x`). -/
noncomputable def descLadderEpoch (x : ℕ → ℝ) : ℕ :=
  sInf {k | 0 < k ∧ ∑ i ∈ range k, x i < 0}

section Epoch

variable {x : ℕ → ℝ}

theorem descLadderEpoch_spec (h : HasDescLadder x) :
    0 < descLadderEpoch x ∧ ∑ i ∈ range (descLadderEpoch x), x i < 0 :=
  Nat.sInf_mem h

theorem descLadderEpoch_pos (h : HasDescLadder x) : 0 < descLadderEpoch x :=
  (descLadderEpoch_spec h).1

theorem sum_range_descLadderEpoch_neg (h : HasDescLadder x) :
    ∑ i ∈ range (descLadderEpoch x), x i < 0 :=
  (descLadderEpoch_spec h).2

/-- Before the first descending ladder epoch the walk stays `≥ 0`. -/
theorem sum_range_nonneg_of_lt_descLadderEpoch {j : ℕ} (hj : j < descLadderEpoch x) :
    0 ≤ ∑ i ∈ range j, x i := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  · by_contra hneg
    exact Nat.notMem_of_lt_sInf hj ⟨hj0, lt_of_not_ge hneg⟩

theorem descLadderEpoch_eq_zero (h : ¬ HasDescLadder x) : descLadderEpoch x = 0 := by
  have : {k | 0 < k ∧ ∑ i ∈ range k, x i < 0} = ∅ := by
    ext k; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hk => h ⟨k, hk⟩
  rw [descLadderEpoch, this, Nat.sInf_empty]

/-- Characterization of the event `{τ₋ = t}` for `t ≥ 1`: it depends only on the first `t`
scores. -/
theorem hasDescLadder_and_descLadderEpoch_eq_iff {t : ℕ} :
    (HasDescLadder x ∧ descLadderEpoch x = t) ↔
      0 < t ∧ ∑ i ∈ range t, x i < 0 ∧ ∀ j, 0 < j → j < t → 0 ≤ ∑ i ∈ range j, x i := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨descLadderEpoch_pos h, sum_range_descLadderEpoch_neg h,
      fun j _ hj => sum_range_nonneg_of_lt_descLadderEpoch hj⟩
  · rintro ⟨ht, hneg, hnn⟩
    have h : HasDescLadder x := ⟨t, ht, hneg⟩
    refine ⟨h, le_antisymm (Nat.sInf_le ⟨ht, hneg⟩) ?_⟩
    by_contra hlt
    push Not at hlt
    exact absurd (hnn _ (descLadderEpoch_pos h) hlt) (not_le.2 (sum_range_descLadderEpoch_neg h))

end Epoch

/-- The **maximal height of the first descending ladder excursion**
`max_{0 ≤ j ≤ τ₋} S_j`, where `S_j = x 0 + ⋯ + x (j - 1)`. It is `≥ 0` (`j = 0`). -/
noncomputable def excursionMax (x : ℕ → ℝ) : ℝ :=
  (range (descLadderEpoch x + 1)).sup' nonempty_range_add_one fun j => ∑ i ∈ range j, x i

theorem sum_range_le_excursionMax {x : ℕ → ℝ} {j : ℕ} (hj : j ≤ descLadderEpoch x) :
    ∑ i ∈ range j, x i ≤ excursionMax x :=
  le_sup' (s := range (descLadderEpoch x + 1)) (fun j => ∑ i ∈ range j, x i)
    (mem_range.2 (Nat.lt_succ_of_le hj))

theorem excursionMax_nonneg (x : ℕ → ℝ) : 0 ≤ excursionMax x := by
  simpa using sum_range_le_excursionMax (x := x) (j := 0) (Nat.zero_le _)

theorem exists_sum_range_eq_excursionMax (x : ℕ → ℝ) :
    ∃ j ≤ descLadderEpoch x, ∑ i ∈ range j, x i = excursionMax x := by
  obtain ⟨j, hj, h⟩ := exists_mem_eq_sup' (s := range (descLadderEpoch x + 1))
    nonempty_range_add_one fun j => ∑ i ∈ range j, x i
  exact ⟨j, Nat.lt_succ_iff.1 (mem_range.1 hj), h.symm⟩

/-- A functional `φ` evaluated on the `i`-th ladder excursion, defined by restarting the path at
the first descending ladder epoch: `iterLadder φ 0 x = φ x` and
`iterLadder φ (i + 1) x = iterLadder φ i (pathShift (descLadderEpoch x) x)`. By
`iterLadder_eq`, `iterLadder φ i x = φ (pathShift (ladderEpoch i x) x)`. -/
noncomputable def iterLadder {α : Type*} (φ : (ℕ → ℝ) → α) : ℕ → (ℕ → ℝ) → α
  | 0, x => φ x
  | i + 1, x => iterLadder φ i (pathShift (descLadderEpoch x) x)

/-- The length `τ₋⁽ⁱ⁾` of the `i`-th descending ladder excursion. -/
noncomputable def excursionLength (i : ℕ) (x : ℕ → ℝ) : ℕ := iterLadder descLadderEpoch i x

/-- The maximal height `Yᵢ` of the `i`-th descending ladder excursion, measured from the
walk's value at the start of the excursion. -/
noncomputable def excursionHeight (i : ℕ) (x : ℕ → ℝ) : ℝ := iterLadder excursionMax i x

/-- The `k`-th descending ladder epoch `T_k = τ₋⁽⁰⁾ + ⋯ + τ₋⁽ᵏ⁻¹⁾` (`T₀ = 0`). -/
noncomputable def ladderEpoch (k : ℕ) (x : ℕ → ℝ) : ℕ := ∑ i ∈ range k, excursionLength i x

/-- The number `Nₙ = max {k ≤ n | T_k ≤ n}` of descending ladder excursions completed by
time `n`. -/
noncomputable def ladderCount (n : ℕ) (x : ℕ → ℝ) : ℕ :=
  Nat.findGreatest (fun k => ladderEpoch k x ≤ n) n

@[simp] theorem ladderEpoch_zero (x : ℕ → ℝ) : ladderEpoch 0 x = 0 := by simp [ladderEpoch]

theorem ladderEpoch_succ' (k : ℕ) (x : ℕ → ℝ) :
    ladderEpoch (k + 1) x =
      descLadderEpoch x + ladderEpoch k (pathShift (descLadderEpoch x) x) := by
  simp only [ladderEpoch, sum_range_succ']
  rw [add_comm]
  rfl

theorem iterLadder_eq {α : Type*} (φ : (ℕ → ℝ) → α) (i : ℕ) (x : ℕ → ℝ) :
    iterLadder φ i x = φ (pathShift (ladderEpoch i x) x) := by
  induction i generalizing x with
  | zero => simp [iterLadder]
  | succ i ih => rw [iterLadder, ih, pathShift_pathShift, ← ladderEpoch_succ']

theorem ladderEpoch_succ (k : ℕ) (x : ℕ → ℝ) :
    ladderEpoch (k + 1) x = ladderEpoch k x + descLadderEpoch (pathShift (ladderEpoch k x) x) := by
  rw [ladderEpoch, sum_range_succ, ← ladderEpoch, excursionLength, iterLadder_eq]

/-- A path is **ladder-good** if the walk restarted at any time `t` eventually drops strictly
below its starting value. On such paths all ladder epochs are finite and strictly increasing
(`strictMono_ladderEpoch`). Under the Cramér conditions almost every path is ladder-good. -/
def IsLadderGood (x : ℕ → ℝ) : Prop := ∀ t, HasDescLadder (pathShift t x)

section Good

variable {x : ℕ → ℝ}

theorem strictMono_ladderEpoch (hx : IsLadderGood x) : StrictMono fun k => ladderEpoch k x :=
  strictMono_nat_of_lt_succ fun k => by
    rw [ladderEpoch_succ]; exact Nat.lt_add_of_pos_right (descLadderEpoch_pos (hx _))

theorem le_ladderEpoch (hx : IsLadderGood x) (k : ℕ) : k ≤ ladderEpoch k x :=
  (strictMono_ladderEpoch hx).le_apply

/-- The walk strictly decreases from one descending ladder epoch to the next. -/
theorem sum_range_ladderEpoch_succ_lt (hx : IsLadderGood x) (k : ℕ) :
    ∑ i ∈ range (ladderEpoch (k + 1) x), x i < ∑ i ∈ range (ladderEpoch k x), x i := by
  have h := sum_range_descLadderEpoch_neg (hx (ladderEpoch k x))
  rw [sum_range_pathShift, ← ladderEpoch_succ] at h
  linarith

theorem sum_range_ladderEpoch_antitone (hx : IsLadderGood x) :
    Antitone fun k => ∑ i ∈ range (ladderEpoch k x), x i :=
  antitone_nat_of_succ_le fun k => (sum_range_ladderEpoch_succ_lt hx k).le

/-- Inside the `k`-th excursion the walk stays at or above its value at the start. -/
theorem sum_range_ladderEpoch_le {k a : ℕ} (hka : ladderEpoch k x ≤ a)
    (ha : a < ladderEpoch (k + 1) x) :
    ∑ i ∈ range (ladderEpoch k x), x i ≤ ∑ i ∈ range a, x i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hka
  rw [ladderEpoch_succ] at ha
  have h := sum_range_nonneg_of_lt_descLadderEpoch (x := pathShift (ladderEpoch k x) x)
    (j := j) (by omega)
  rw [sum_range_pathShift] at h
  linarith

theorem excursionHeight_eq (i : ℕ) (x : ℕ → ℝ) :
    excursionHeight i x = excursionMax (pathShift (ladderEpoch i x) x) :=
  iterLadder_eq _ _ _

theorem excursionHeight_nonneg (i : ℕ) (x : ℕ → ℝ) : 0 ≤ excursionHeight i x := by
  rw [excursionHeight_eq]; exact excursionMax_nonneg _

/-- Every increment of the walk inside the `k`-th excursion is at most its height. -/
theorem sum_range_sub_le_excursionHeight {k b : ℕ} (hkb : ladderEpoch k x ≤ b)
    (hb : b ≤ ladderEpoch (k + 1) x) :
    ∑ i ∈ range b, x i - ∑ i ∈ range (ladderEpoch k x), x i ≤ excursionHeight k x := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkb
  rw [ladderEpoch_succ] at hb
  have h := sum_range_le_excursionMax (x := pathShift (ladderEpoch k x) x) (j := j) (by omega)
  rwa [sum_range_pathShift, ← excursionHeight_eq] at h

/-- The height of the `k`-th excursion is an increment of the walk inside it. -/
theorem exists_sum_range_sub_eq_excursionHeight (k : ℕ) (x : ℕ → ℝ) :
    ∃ b, ladderEpoch k x ≤ b ∧ b ≤ ladderEpoch (k + 1) x ∧
      ∑ i ∈ range b, x i - ∑ i ∈ range (ladderEpoch k x), x i = excursionHeight k x := by
  obtain ⟨j, hj, h⟩ := exists_sum_range_eq_excursionMax (pathShift (ladderEpoch k x) x)
  refine ⟨ladderEpoch k x + j, by omega, by rw [ladderEpoch_succ]; omega, ?_⟩
  rw [excursionHeight_eq, ← h, sum_range_pathShift]

/-- `i ≤ Nₙ` iff the `i`-th ladder epoch is at most `n`. -/
theorem le_ladderCount_iff (hx : IsLadderGood x) {i n : ℕ} :
    i ≤ ladderCount n x ↔ ladderEpoch i x ≤ n := by
  constructor
  · intro hi
    have hN : ladderEpoch (ladderCount n x) x ≤ n :=
      Nat.findGreatest_spec (P := fun k => ladderEpoch k x ≤ n) (Nat.zero_le n) (by simp)
    exact ((strictMono_ladderEpoch hx).monotone hi).trans hN
  · intro hi
    exact Nat.le_findGreatest ((le_ladderEpoch hx i).trans hi) hi

theorem ladderEpoch_ladderCount_le (hx : IsLadderGood x) (n : ℕ) :
    ladderEpoch (ladderCount n x) x ≤ n :=
  (le_ladderCount_iff hx).1 le_rfl

theorem lt_ladderEpoch_ladderCount_succ (hx : IsLadderGood x) (n : ℕ) :
    n < ladderEpoch (ladderCount n x + 1) x :=
  lt_of_not_ge fun h => Nat.not_succ_le_self _ ((le_ladderCount_iff hx).2 h)

theorem segmentScore_eq_sub {a b : ℕ} (hab : a ≤ b) (x : ℕ → ℝ) :
    segmentScore x a b = ∑ i ∈ range b, x i - ∑ i ∈ range a, x i :=
  sum_Ico_eq_sub _ hab

/-- **Lower half of the ladder sandwich**: every excursion completed by time `n` has height at
most `Mₙ`. -/
theorem excursionHeight_le_maxSegmentScore (hx : IsLadderGood x) {n i : ℕ}
    (hi : i < ladderCount n x) : excursionHeight i x ≤ maxSegmentScore x n := by
  have hT : ladderEpoch (i + 1) x ≤ n := (le_ladderCount_iff hx).1 hi
  obtain ⟨b, hib, hb, h⟩ := exists_sum_range_sub_eq_excursionHeight i x
  rw [← h, ← segmentScore_eq_sub hib]
  exact segmentScore_le_maxSegmentScore
    (((strictMono_ladderEpoch hx).monotone (Nat.le_succ i)).trans hT) (hb.trans hT)

/-- **Upper half of the ladder sandwich**: `Mₙ ≤ max_{i ≤ Nₙ} Yᵢ`. A segment `[a, b)` starts in
some excursion `k` and ends in excursion `j ≥ k`, `j ≤ Nₙ`; since the walk does not go below
its value at the start of excursion `k` inside it, and ladder values decrease, the segment
score is at most `S_b - S_{T_j} ≤ Y_j`. -/
theorem maxSegmentScore_le_of_forall (hx : IsLadderGood x) {n : ℕ} {t : ℝ}
    (h : ∀ i ≤ ladderCount n x, excursionHeight i x ≤ t) : maxSegmentScore x n ≤ t := by
  refine sup'_le _ _ fun p hp => ?_
  simp only [mem_product, mem_range] at hp
  obtain ⟨a, b⟩ := p
  simp only at hp ⊢
  rcases le_or_gt b a with hba | hab
  · rw [segmentScore, Ico_eq_empty_of_le hba, sum_empty]
    exact (excursionHeight_nonneg 0 x).trans (h 0 (Nat.zero_le _))
  · set k := ladderCount a x
    set j := ladderCount b x
    have hkj : k ≤ j := (le_ladderCount_iff hx).2 ((ladderEpoch_ladderCount_le hx a).trans hab.le)
    have hjn : j ≤ ladderCount n x :=
      (le_ladderCount_iff hx).2 ((ladderEpoch_ladderCount_le hx b).trans (by omega))
    have h1 := sum_range_ladderEpoch_le (ladderEpoch_ladderCount_le hx a)
      (lt_ladderEpoch_ladderCount_succ hx a)
    have h2 := sum_range_ladderEpoch_antitone hx hkj
    have h3 := sum_range_sub_le_excursionHeight (ladderEpoch_ladderCount_le hx b)
      (lt_ladderEpoch_ladderCount_succ hx b).le
    rw [segmentScore_eq_sub hab.le]
    have := h j hjn
    simp only [k, j] at h1 h2 h3 this ⊢
    linarith

end Good

/-! ## Measurability; the ladder epoch is a stopping time -/

/-- The σ-algebra `σ(x 0, …, x (t - 1))` generated by the first `t` scores on path space. -/
@[instance_reducible]
def pastMeasurableSpace (t : ℕ) : MeasurableSpace (ℕ → ℝ) :=
  ⨆ j ∈ Set.Iio t, MeasurableSpace.comap (fun x : ℕ → ℝ => x j) inferInstance

theorem pastMeasurableSpace_le (t : ℕ) :
    pastMeasurableSpace t ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
  iSup₂_le fun j _ => (measurable_pi_apply j).comap_le

theorem measurable_past_apply {t j : ℕ} (hj : j < t) :
    Measurable[pastMeasurableSpace t] fun x : ℕ → ℝ => x j :=
  measurable_iff_comap_le.2 (le_iSup₂ (f := fun j (_ : j ∈ Set.Iio t) =>
    MeasurableSpace.comap (fun x : ℕ → ℝ => x j) inferInstance) j hj)

theorem measurable_past_sum {t k : ℕ} (hk : k ≤ t) :
    Measurable[pastMeasurableSpace t] fun x : ℕ → ℝ => ∑ i ∈ range k, x i :=
  Finset.measurable_sum (range k) fun i hi => measurable_past_apply (by simp at hi; omega)

/-- **The first descending ladder epoch is a stopping time**: for `t ≥ 1` the event
`{τ₋ = t}` is determined by the first `t` scores. -/
theorem measurableSet_descLadderEpoch_eq (t : ℕ) :
    MeasurableSet[pastMeasurableSpace t] {x | HasDescLadder x ∧ descLadderEpoch x = t} := by
  have hset : {x : ℕ → ℝ | HasDescLadder x ∧ descLadderEpoch x = t} =
      {_x | 0 < t} ∩ ({x | ∑ i ∈ range t, x i < 0} ∩
        ⋂ j ∈ Finset.Ioo 0 t, {x | 0 ≤ ∑ i ∈ range j, x i}) := by
    ext x
    simp only [hasDescLadder_and_descLadderEpoch_eq_iff, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_iInter, Finset.mem_Ioo]
    exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, fun j hj => c j hj.1 hj.2⟩,
      fun ⟨a, b, c⟩ => ⟨a, b, fun j h1 h2 => c j ⟨h1, h2⟩⟩⟩
  rw [hset]
  refine (MeasurableSet.const _).inter ((measurableSet_lt (measurable_past_sum le_rfl)
    measurable_const).inter (Finset.measurableSet_biInter _ fun j hj => ?_))
  exact measurableSet_le measurable_const (measurable_past_sum (Finset.mem_Ioo.1 hj).2.le)

theorem pastMeasurableSpace_mono : Monotone pastMeasurableSpace := fun _ t hst =>
  iSup₂_le fun j hj => le_iSup₂ (f := fun j (_ : j ∈ Set.Iio t) =>
    MeasurableSpace.comap (fun x : ℕ → ℝ => x j) inferInstance) j
      (lt_of_lt_of_le (Set.mem_Iio.1 hj) hst)

open Classical in
/-- `τ₋` is Mathlib's hitting time of `(-∞, 0)` after time `1` by the walk
`S_k = x 0 + ⋯ + x (k - 1)`, with value `⊤` when the walk never drops below `0`. -/
theorem descLadderEpoch_eq_hittingAfter (x : ℕ → ℝ) :
    (if HasDescLadder x then (descLadderEpoch x : WithTop ℕ) else ⊤) =
      hittingAfter (fun k (x : ℕ → ℝ) => ∑ i ∈ range k, x i) (Set.Iio 0) 1 x := by
  simp only [hittingAfter, HasDescLadder, descLadderEpoch, Set.mem_Iio, Nat.one_le_iff_ne_zero,
    Nat.pos_iff_ne_zero]
  split_ifs <;> rfl

open Classical in
/-- **The first descending ladder epoch is a stopping time** in Mathlib's sense, for the
natural filtration `σ(x 0, …, x t)` of the score process, with value `⊤` when the walk never
drops below `0`; derived from `Adapted.isStoppingTime_hittingAfter`. -/
theorem isStoppingTime_descLadderEpoch :
    IsStoppingTime (Filtration.natural (fun i (x : ℕ → ℝ) => x i)
      fun i => (measurable_pi_apply i).stronglyMeasurable)
      fun x => if HasDescLadder x then (descLadderEpoch x : WithTop ℕ) else ⊤ := by
  simp_rw [descLadderEpoch_eq_hittingAfter]
  refine Adapted.isStoppingTime_hittingAfter (fun k => ?_) measurableSet_Iio
  refine (measurable_past_sum (Nat.le_succ k)).mono ?_ le_rfl
  exact iSup₂_le fun j hj => le_iSup₂ (f := fun j (_ : j ≤ k) =>
    MeasurableSpace.comap (fun x : ℕ → ℝ => x j) inferInstance) j
      (Nat.lt_succ_iff.1 (Set.mem_Iio.1 hj))

theorem measurableSet_hasDescLadder : MeasurableSet {x : ℕ → ℝ | HasDescLadder x} := by
  have : {x : ℕ → ℝ | HasDescLadder x} =
      ⋃ k, {_x : ℕ → ℝ | 0 < k} ∩ {x | ∑ i ∈ range k, x i < 0} := by
    ext x; simp [HasDescLadder]
  rw [this]
  exact MeasurableSet.iUnion fun k => (MeasurableSet.const _).inter
    (measurableSet_lt (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_const)

theorem measurable_descLadderEpoch : Measurable descLadderEpoch := by
  refine measurable_to_countable' fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : descLadderEpoch ⁻¹' {0} = {x | HasDescLadder x}ᶜ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_ofPred_eq]
      exact ⟨fun h0 h => (descLadderEpoch_pos h).ne' h0, descLadderEpoch_eq_zero⟩
    rw [this]; exact measurableSet_hasDescLadder.compl
  · have : descLadderEpoch ⁻¹' {k} = {x | HasDescLadder x ∧ descLadderEpoch x = k} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
      by_contra hn
      rw [descLadderEpoch_eq_zero hn] at h
      omega
    rw [this]
    exact pastMeasurableSpace_le k _ (measurableSet_descLadderEpoch_eq k)

theorem measurable_pathShift (t : ℕ) : Measurable (pathShift t) :=
  measurable_pi_iff.2 fun j => measurable_pi_apply (t + j)

/-- A family `G k` of measurable maps evaluated at `k = τ₋ x` is measurable. -/
theorem measurable_comp_descLadderEpoch {β : Type*} [MeasurableSpace β]
    {G : ℕ → (ℕ → ℝ) → β} (hG : ∀ k, Measurable (G k)) :
    Measurable fun x => G (descLadderEpoch x) x := by
  intro B hB
  have : (fun x => G (descLadderEpoch x) x) ⁻¹' B =
      ⋃ k, descLadderEpoch ⁻¹' {k} ∩ G k ⁻¹' B := by
    ext x; simp
  rw [this]
  exact MeasurableSet.iUnion fun k =>
    (measurable_descLadderEpoch (measurableSet_singleton k)).inter (hG k hB)

theorem measurable_iterLadder {β : Type*} [MeasurableSpace β] {φ : (ℕ → ℝ) → β}
    (hφ : Measurable φ) (i : ℕ) : Measurable (iterLadder φ i) := by
  induction i with
  | zero => exact hφ
  | succ i ih =>
    exact measurable_comp_descLadderEpoch (G := fun k x => iterLadder φ i (pathShift k x))
      fun k => ih.comp (measurable_pathShift k)

theorem measurable_excursionMax : Measurable excursionMax :=
  measurable_comp_descLadderEpoch (G := fun k x =>
    (range (k + 1)).sup' nonempty_range_add_one fun j => ∑ i ∈ range j, x i)
    fun _ => Finset.measurable_range_sup'' fun _ _ =>
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i

theorem measurable_excursionHeight (i : ℕ) : Measurable (excursionHeight i) :=
  measurable_iterLadder measurable_excursionMax i

theorem measurable_excursionLength (i : ℕ) : Measurable (excursionLength i) :=
  measurable_iterLadder measurable_descLadderEpoch i

theorem measurable_ladderEpoch (k : ℕ) : Measurable (ladderEpoch k) := by
  have : ladderEpoch k = fun x => ∑ i ∈ range k, excursionLength i x := rfl
  rw [this]
  exact Finset.measurable_sum _ fun i _ => measurable_excursionLength i

theorem measurable_ladderCount (n : ℕ) : Measurable (ladderCount n) := by
  refine measurable_to_countable' fun m => ?_
  have : ladderCount n ⁻¹' {m} = {_x | m ≤ n} ∩ ({x | m ≠ 0 → ladderEpoch m x ≤ n} ∩
      ⋂ k ∈ Finset.Ioc m n, {x | ¬ ladderEpoch k x ≤ n}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, ladderCount, Nat.findGreatest_eq_iff,
      Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_Ioc]
    exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, fun k hk => c hk.1 hk.2⟩,
      fun ⟨a, b, c⟩ => ⟨a, b, fun k h1 h2 => c k ⟨h1, h2⟩⟩⟩
  rw [this]
  refine (MeasurableSet.const _).inter (MeasurableSet.inter ?_
    (Finset.measurableSet_biInter _ fun k _ =>
      (measurable_ladderEpoch k (measurableSet_Iic (a := n))).compl))
  by_cases hm : m = 0
  · simp [hm]
  · rw [show {x | m ≠ 0 → ladderEpoch m x ≤ n} = ladderEpoch m ⁻¹' Set.Iic n by ext; simp [hm]]
    exact measurable_ladderEpoch m measurableSet_Iic

/-! ## Strong Markov property at the ladder epoch on the canonical i.i.d. space -/

section Canonical

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- The i.i.d. score sequence with law `ν` is stationary: the shifted path has the same law. -/
theorem infinitePi_map_pathShift (t : ℕ) :
    (Measure.infinitePi fun _ : ℕ => ν).map (pathShift t) = Measure.infinitePi fun _ : ℕ => ν := by
  have hind : iIndepFun (fun j (x : ℕ → ℝ) => x (t + j)) (Measure.infinitePi fun _ : ℕ => ν) :=
    (iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ (y : ℝ) => y)
      fun _ => measurable_id).precomp (add_right_injective t)
  have h := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun j => measurable_pi_apply (t + j))).1 hind
  rw [show pathShift t = fun x j => x (t + j) from rfl, h]
  congr 1
  funext j
  exact Measure.infinitePi_map_eval _ (t + j)

/-- The first `t` scores are independent of the path after time `t`. -/
theorem indep_past_pathShift (t : ℕ) :
    Indep (pastMeasurableSpace t) (MeasurableSpace.comap (pathShift t) inferInstance)
      (Measure.infinitePi fun _ : ℕ => ν) := by
  have hind := iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ (y : ℝ) => y)
    fun _ => measurable_id
  rw [iIndepFun_iff_iIndep] at hind
  have h := indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) hind
    (Set.Iio_disjoint_Ici (le_refl t))
  refine indep_of_indep_of_le_right h ?_
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  refine iSup_le fun j => ?_
  rw [MeasurableSpace.comap_comp]
  exact le_iSup₂ (f := fun i (_ : i ∈ Set.Ici t) =>
    MeasurableSpace.comap (fun x : ℕ → ℝ => x i) inferInstance) (t + j) (by simp)

/-- **Strong Markov property at the first descending ladder epoch** on the canonical i.i.d.
space: if `E` is determined by the scores before `τ₋` (on each event `{τ₋ = t}`, by the first
`t` scores), then the post-`τ₋` path `pathShift τ₋ x` is independent of `E` and has the law of
the original path. -/
theorem infinitePi_strongMarkov {E : Set (ℕ → ℝ)}
    (hE : ∀ t, MeasurableSet[pastMeasurableSpace t]
      (E ∩ {x | HasDescLadder x ∧ descLadderEpoch x = t}))
    {B : Set (ℕ → ℝ)} (hB : MeasurableSet B) :
    (Measure.infinitePi fun _ : ℕ => ν)
        (E ∩ {x | HasDescLadder x} ∩ {x | pathShift (descLadderEpoch x) x ∈ B}) =
      (Measure.infinitePi fun _ : ℕ => ν) (E ∩ {x | HasDescLadder x}) *
        (Measure.infinitePi fun _ : ℕ => ν) B := by
  set μ := Measure.infinitePi fun _ : ℕ => ν
  set A : ℕ → Set (ℕ → ℝ) := fun t => E ∩ {x | HasDescLadder x ∧ descLadderEpoch x = t}
  have hAm : ∀ t, MeasurableSet (A t) := fun t => pastMeasurableSpace_le t _ (hE t)
  have hdisj : ∀ (C : ℕ → Set (ℕ → ℝ)), Pairwise (Function.onFun Disjoint fun t => A t ∩ C t) :=
    fun C s t hst => Set.disjoint_left.2 fun x hs ht => hst (hs.1.2.2.symm.trans ht.1.2.2)
  have h1 : E ∩ {x | HasDescLadder x} ∩ {x | pathShift (descLadderEpoch x) x ∈ B} =
      ⋃ t, A t ∩ pathShift t ⁻¹' B := by
    ext x
    simp only [A, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage]
    exact ⟨fun ⟨⟨hE, hH⟩, hB⟩ => ⟨_, ⟨hE, hH, rfl⟩, hB⟩, fun ⟨t, ⟨hE, hH, ht⟩, hB⟩ =>
      ⟨⟨hE, hH⟩, ht ▸ hB⟩⟩
  have h2 : E ∩ {x | HasDescLadder x} = ⋃ t, A t ∩ Set.univ := by
    ext x
    simp only [A, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_univ, and_true]
    exact ⟨fun ⟨hE, hH⟩ => ⟨_, hE, hH, rfl⟩, fun ⟨t, hE, hH, _⟩ => ⟨hE, hH⟩⟩
  have hterm : ∀ t, μ (A t ∩ pathShift t ⁻¹' B) = μ (A t) * μ B := fun t => by
    rw [(Indep_iff _ _ μ).1 (indep_past_pathShift t) _ _ (hE t) ⟨B, hB, rfl⟩,
      ← Measure.map_apply (measurable_pathShift t) hB, infinitePi_map_pathShift]
  rw [h1, h2, measure_iUnion (hdisj _) fun t => (hAm t).inter (measurable_pathShift t hB),
    measure_iUnion (hdisj _) fun t => (hAm t).inter MeasurableSet.univ, ← ENNReal.tsum_mul_right]
  simp only [hterm, Set.inter_univ]

/-- Joint law of the excursion functionals: if `φ` is determined by the scores before `τ₋` and
`τ₋ < ∞` almost surely, then `P(∀ i < k, φ(excursion i) ∈ Bᵢ) = ∏_{i < k} P(φ ∈ Bᵢ)`. -/
theorem infinitePi_iterLadder_inter {β : Type*} [MeasurableSpace β] {φ : (ℕ → ℝ) → β}
    (hφ : Measurable φ)
    (hpast : ∀ t (B : Set β), MeasurableSet B → MeasurableSet[pastMeasurableSpace t]
      ({x | HasDescLadder x ∧ descLadderEpoch x = t} ∩ φ ⁻¹' B))
    (hHas : ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => ν), HasDescLadder x)
    (k : ℕ) (B : ℕ → Set β) (hB : ∀ i, MeasurableSet (B i)) :
    (Measure.infinitePi fun _ : ℕ => ν) (⋂ i ∈ range k, iterLadder φ i ⁻¹' B i) =
      ∏ i ∈ range k, (Measure.infinitePi fun _ : ℕ => ν) (φ ⁻¹' B i) := by
  set μ := Measure.infinitePi fun _ : ℕ => ν
  have hHas' : μ {x | HasDescLadder x}ᶜ = 0 := ae_iff.1 hHas
  induction k generalizing B with
  | zero => simp
  | succ k ih =>
    set C := ⋂ i ∈ range k, iterLadder φ i ⁻¹' B (i + 1)
    have hC : MeasurableSet C :=
      Finset.measurableSet_biInter _ fun i _ => measurable_iterLadder hφ i (hB (i + 1))
    have hset : ⋂ i ∈ range (k + 1), iterLadder φ i ⁻¹' B i =
        φ ⁻¹' B 0 ∩ {x | pathShift (descLadderEpoch x) x ∈ C} := by
      ext x
      simp only [C, Set.mem_iInter, Set.mem_preimage, mem_range, Set.mem_inter_iff,
        Set.mem_ofPred_eq]
      constructor
      · intro h
        exact ⟨h 0 (by omega), fun i hi => h (i + 1) (by omega)⟩
      · rintro ⟨h0, h⟩ i hi
        cases i with
        | zero => exact h0
        | succ i => exact h i (by omega)
    have hE : ∀ t, MeasurableSet[pastMeasurableSpace t]
        (φ ⁻¹' B 0 ∩ {x | HasDescLadder x ∧ descLadderEpoch x = t}) := fun t => by
      rw [Set.inter_comm]; exact hpast t _ (hB 0)
    rw [hset, ← measure_inter_conull (s := φ ⁻¹' B 0 ∩ _) hHas', Set.inter_right_comm,
      infinitePi_strongMarkov hE hC, measure_inter_conull hHas', ih _ fun i => hB (i + 1),
      prod_range_succ' _ k, mul_comm]

/-- The excursion functionals `φ(excursion i)` are i.i.d. with the law of `φ`. -/
theorem iIndepFun_iterLadder {β : Type*} [MeasurableSpace β] {φ : (ℕ → ℝ) → β}
    (hφ : Measurable φ)
    (hpast : ∀ t (B : Set β), MeasurableSet B → MeasurableSet[pastMeasurableSpace t]
      ({x | HasDescLadder x ∧ descLadderEpoch x = t} ∩ φ ⁻¹' B))
    (hHas : ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => ν), HasDescLadder x) :
    iIndepFun (iterLadder φ) (Measure.infinitePi fun _ : ℕ => ν) ∧
      ∀ i, (Measure.infinitePi fun _ : ℕ => ν).map (iterLadder φ i) =
        (Measure.infinitePi fun _ : ℕ => ν).map φ := by
  classical
  set μ := Measure.infinitePi fun _ : ℕ => ν
  have hlaw : ∀ i (B : Set β), MeasurableSet B → μ (iterLadder φ i ⁻¹' B) = μ (φ ⁻¹' B) := by
    intro i B hB
    have h := infinitePi_iterLadder_inter hφ hpast hHas (i + 1)
      (fun j => if j = i then B else Set.univ) fun j => by split_ifs <;> simp [hB]
    have hl : ⋂ j ∈ range (i + 1), iterLadder φ j ⁻¹'
        (if j = i then B else Set.univ) = iterLadder φ i ⁻¹' B := by
      ext x; simp only [Set.mem_iInter, mem_range, Set.mem_preimage]
      constructor
      · intro hx; simpa using hx i (by omega)
      · intro hx j _; split_ifs with hj
        · exact hj ▸ hx
        · trivial
    rw [hl, prod_eq_single i (fun j _ hj => by simp [hj]) (fun h => by simp at h)] at h
    simpa using h
  refine ⟨?_, fun i => ?_⟩
  · rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets hsets
    set k := S.sup id + 1
    have hSk : ∀ j ∈ S, j < k := fun j hj => Nat.lt_succ_of_le (le_sup (f := id) hj)
    have h := infinitePi_iterLadder_inter hφ hpast hHas k
      (fun j => if j ∈ S then sets j else Set.univ) fun j => by
        split_ifs with hj
        · exact hsets j hj
        · exact MeasurableSet.univ
    have hl : ⋂ j ∈ range k, iterLadder φ j ⁻¹' (if j ∈ S then sets j else Set.univ) =
        ⋂ j ∈ S, iterLadder φ j ⁻¹' sets j := by
      ext x; simp only [Set.mem_iInter, mem_range, Set.mem_preimage]
      constructor
      · intro hx j hj; simpa [hj] using hx j (hSk j hj)
      · intro hx j _; split_ifs with hj
        · exact hx j hj
        · trivial
    rw [hl, ← prod_subset (s₁ := S) (fun j hj => mem_range.2 (hSk j hj))
      (fun j _ hj => by simp [hj])] at h
    rw [h]
    refine prod_congr rfl fun j hj => ?_
    simp only [hj, ite_true]
    exact (hlaw j _ (hsets j hj)).symm
  · ext B hB
    rw [Measure.map_apply (measurable_iterLadder hφ i) hB, Measure.map_apply hφ hB, hlaw i B hB]

end Canonical

/-! ## Exponential moments: the ladder epoch is a.s. finite with finite mean -/

/-- Under the Cramér conditions the moment generating function at half the root is `< 1`:
`E e^{θX/2} = 1 - E (1 - e^{θX/2})² / 2`, and `E (1 - e^{θX/2})² = 0` would force `X = 0`
almost surely, contradicting `E X < 0`. -/
theorem mgf_half_lt_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → ℝ} {θ : ℝ} (hneg : ∫ ω, Z ω ∂P < 0) (hθ : 0 < θ)
    (hmgf : mgf Z P θ = 1) : mgf Z P (θ / 2) < 1 := by
  have hexp : Integrable (fun ω => Real.exp (θ * Z ω)) P := by
    by_contra h
    simp [mgf, integral_undef h] at hmgf
  have hhalf : Integrable (fun ω => Real.exp (θ / 2 * Z ω)) P :=
    integrable_exp_mul_of_nonneg_of_le hexp (by positivity) (by linarith)
  set g : Ω → ℝ := fun ω => (1 - Real.exp (θ / 2 * Z ω)) ^ 2
  have hg : g = fun ω => 1 - 2 * Real.exp (θ / 2 * Z ω) + Real.exp (θ * Z ω) := by
    funext ω
    simp only [g]
    have : Real.exp (θ * Z ω) = Real.exp (θ / 2 * Z ω) ^ 2 := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [this]; ring
  have hgi : Integrable g P := by
    rw [hg]; exact ((integrable_const _).sub (hhalf.const_mul 2)).add hexp
  have hgint : ∫ ω, g ω ∂P = 2 - 2 * mgf Z P (θ / 2) := by
    have h1 : Integrable (fun ω => 1 - 2 * Real.exp (θ / 2 * Z ω)) P :=
      (integrable_const _).sub (hhalf.const_mul 2)
    simp only [hg]
    rw [integral_add h1 hexp, integral_sub (integrable_const _) (hhalf.const_mul 2),
      integral_const_mul]
    simp only [mgf] at hmgf ⊢
    rw [hmgf]; simp; ring
  by_contra hge
  push Not at hge
  have hg0 : 0 ≤ g := fun ω => sq_nonneg _
  have hzero : ∫ ω, g ω ∂P = 0 :=
    le_antisymm (by rw [hgint]; linarith) (integral_nonneg hg0)
  have hae : g =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg hg0 hgi).1 hzero
  have hZ0 : Z =ᵐ[P] 0 := by
    filter_upwards [hae] with ω hω
    simp only [g, Pi.zero_apply, sq_eq_zero_iff, sub_eq_zero] at hω
    have := Real.exp_eq_one_iff _ |>.1 hω.symm
    simp only [Pi.zero_apply]
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  rw [integral_congr_ae hZ0] at hneg
  simp at hneg

section Canonical

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- **Chernoff bound for the walk**: `P(S_k ≥ 0) ≤ (E e^{sX})^k` for `s ≥ 0`. -/
theorem infinitePi_real_sum_nonneg_le {s : ℝ} (hs : 0 ≤ s)
    (hexp : Integrable (fun y => Real.exp (s * y)) ν) (k : ℕ) :
    (Measure.infinitePi fun _ : ℕ => ν).real {x | 0 ≤ ∑ i ∈ range k, x i} ≤ mgf id ν s ^ k := by
  set μ := Measure.infinitePi fun _ : ℕ => ν
  have hind : iIndepFun (fun i (x : ℕ → ℝ) => x i) μ :=
    iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ (y : ℝ) => y) fun _ => measurable_id
  have hmeas : ∀ i, Measurable fun x : ℕ → ℝ => x i := measurable_pi_apply
  have hint : ∀ i, Integrable (fun x : ℕ → ℝ => Real.exp (s * x i)) μ := fun i => by
    have h : Integrable (fun y => Real.exp (s * y)) (μ.map fun x : ℕ → ℝ => x i) := by
      rwa [Measure.infinitePi_map_eval]
    exact h.comp_measurable (hmeas i)
  have hmgf : ∀ i, mgf (fun x : ℕ → ℝ => x i) μ s = mgf id ν s := fun i => by
    rw [← mgf_id_map (hmeas i).aemeasurable, Measure.infinitePi_map_eval]
  have hsum : (fun x : ℕ → ℝ => ∑ i ∈ range k, x i) = ∑ i ∈ range k, fun x : ℕ → ℝ => x i := by
    ext x; simp
  have h := measure_ge_le_exp_mul_mgf (μ := μ) (X := ∑ i ∈ range k, fun x : ℕ → ℝ => x i) 0 hs
    (hind.integrable_exp_mul_sum hmeas fun i _ => hint i)
  rw [hind.mgf_sum hmeas, mul_zero, Real.exp_zero, one_mul] at h
  simp only [hmgf, prod_const, card_range] at h
  convert h using 3
  simp

variable {s : ℝ}

theorem ae_hasDescLadder (hs : 0 ≤ s) (hexp : Integrable (fun y => Real.exp (s * y)) ν)
    (hρ : mgf id ν s < 1) : ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => ν), HasDescLadder x := by
  set μ := Measure.infinitePi fun _ : ℕ => ν
  have hle : ∀ k, μ.real {x | ¬ HasDescLadder x} ≤ mgf id ν s ^ k := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · refine (measureReal_mono fun x hx => ?_).trans (infinitePi_real_sum_nonneg_le hs hexp k)
      simp only [Set.mem_ofPred_eq] at hx ⊢
      by_contra hlt
      exact hx ⟨k, hk, lt_of_not_ge hlt⟩
  have h0 : μ.real {x | ¬ HasDescLadder x} ≤ 0 :=
    ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one mgf_nonneg hρ) hle
  rw [ae_iff]
  exact (measureReal_eq_zero_iff).1 (le_antisymm h0 measureReal_nonneg)

theorem ae_isLadderGood (hs : 0 ≤ s) (hexp : Integrable (fun y => Real.exp (s * y)) ν)
    (hρ : mgf id ν s < 1) : ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => ν), IsLadderGood x := by
  set μ := Measure.infinitePi fun _ : ℕ => ν
  refine ae_all_iff.2 fun t => ?_
  have h := ae_iff.1 (ae_hasDescLadder hs hexp hρ)
  rw [ae_iff, show {x | ¬ HasDescLadder (pathShift t x)} =
    pathShift t ⁻¹' {x | HasDescLadder x}ᶜ from rfl,
    ← Measure.map_apply (measurable_pathShift t) measurableSet_hasDescLadder.compl,
    infinitePi_map_pathShift]
  exact h

theorem measurable_descLadderEpoch_real : Measurable fun x : ℕ → ℝ => (descLadderEpoch x : ℝ) :=
  measurable_from_nat.comp measurable_descLadderEpoch

/-- **The first descending ladder epoch has finite mean**: `E τ₋ = ∑_k P(τ₋ > k) ≤ ∑_k ρ^k`,
since `{τ₋ > k} ⊆ {S_k ≥ 0}`. -/
theorem integrable_descLadderEpoch (hs : 0 ≤ s) (hexp : Integrable (fun y => Real.exp (s * y)) ν)
    (hρ : mgf id ν s < 1) :
    Integrable (fun x : ℕ → ℝ => (descLadderEpoch x : ℝ)) (Measure.infinitePi fun _ : ℕ => ν) := by
  set μ := Measure.infinitePi fun _ : ℕ => ν
  refine ⟨measurable_descLadderEpoch_real.aestronglyMeasurable, ?_⟩
  have hms : ∀ k, MeasurableSet {x : ℕ → ℝ | k < descLadderEpoch x} := fun k =>
    measurable_descLadderEpoch (MeasurableSet.of_discrete (s := Set.Ioi k))
  have hpt : ∀ x : ℕ → ℝ, ‖(descLadderEpoch x : ℝ)‖ₑ =
      ∑' k, Set.indicator {x : ℕ → ℝ | k < descLadderEpoch x} 1 x := by
    intro x
    rw [Real.enorm_natCast, tsum_eq_sum (s := range (descLadderEpoch x)) fun k hk => by
      simp only [mem_range, not_lt] at hk
      simp [not_lt.2 hk]]
    rw [sum_congr rfl fun k hk => by
      rw [Set.indicator_of_mem (by simpa using hk)]]
    simp
  have hbound : ∀ k, μ {x : ℕ → ℝ | k < descLadderEpoch x} ≤ ENNReal.ofReal (mgf id ν s ^ k) := by
    intro k
    refine (measure_mono (t := {x : ℕ → ℝ | 0 ≤ ∑ i ∈ range k, x i})
      fun x hx => ?_).trans ?_
    · exact sum_range_nonneg_of_lt_descLadderEpoch hx
    · rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal (infinitePi_real_sum_nonneg_le hs hexp k)
  change ∫⁻ x, ‖(descLadderEpoch x : ℝ)‖ₑ ∂μ < ⊤
  simp_rw [hpt]
  rw [lintegral_tsum (f := fun k => Set.indicator {x : ℕ → ℝ | k < descLadderEpoch x} 1)
    fun k => (measurable_const.indicator (hms k)).aemeasurable]
  simp_rw [lintegral_indicator_one (hms _)]
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hbound) ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => pow_nonneg mgf_nonneg k)
    (summable_geometric_of_lt_one mgf_nonneg hρ)]
  exact ENNReal.ofReal_lt_top

/-- The mean ladder epoch is at least `1`. -/
theorem one_le_integral_descLadderEpoch (hs : 0 ≤ s)
    (hexp : Integrable (fun y => Real.exp (s * y)) ν) (hρ : mgf id ν s < 1) :
    1 ≤ ∫ x, (descLadderEpoch x : ℝ) ∂(Measure.infinitePi fun _ : ℕ => ν) := by
  have h := integral_mono_ae (integrable_const (1 : ℝ)) (integrable_descLadderEpoch hs hexp hρ)
    (by
      filter_upwards [ae_hasDescLadder hs hexp hρ] with x hx
      exact_mod_cast descLadderEpoch_pos hx)
  simpa using h

end Canonical

/-! ## I.i.d. excursions and the renewal law of large numbers -/

theorem measurableSet_past_descLadderEpoch_preimage (t : ℕ) (B : Set ℕ) :
    MeasurableSet[pastMeasurableSpace t]
      ({x | HasDescLadder x ∧ descLadderEpoch x = t} ∩ descLadderEpoch ⁻¹' B) := by
  have : {x | HasDescLadder x ∧ descLadderEpoch x = t} ∩ descLadderEpoch ⁻¹' B =
      {x | HasDescLadder x ∧ descLadderEpoch x = t} ∩ {_x | t ∈ B} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    exact ⟨fun ⟨h, hB⟩ => ⟨h, h.2 ▸ hB⟩, fun ⟨h, hB⟩ => ⟨h, h.2 ▸ hB⟩⟩
  rw [this]
  exact (measurableSet_descLadderEpoch_eq t).inter (MeasurableSet.const _)

theorem measurableSet_past_excursionMax_preimage (t : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurableSet[pastMeasurableSpace t]
      ({x | HasDescLadder x ∧ descLadderEpoch x = t} ∩ excursionMax ⁻¹' B) := by
  set h : (ℕ → ℝ) → ℝ := fun x =>
    (range (t + 1)).sup' nonempty_range_add_one fun j => ∑ i ∈ range j, x i
  have hm : Measurable[pastMeasurableSpace t] h := by
    let _ : MeasurableSpace (ℕ → ℝ) := pastMeasurableSpace t
    exact Finset.measurable_range_sup'' fun _ hj => measurable_past_sum hj
  have : {x | HasDescLadder x ∧ descLadderEpoch x = t} ∩ excursionMax ⁻¹' B =
      {x | HasDescLadder x ∧ descLadderEpoch x = t} ∩ h ⁻¹' B := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    refine and_congr_right fun hx => ?_
    have : excursionMax x = h x := by
      obtain ⟨_, ht⟩ := hx
      subst ht
      rfl
    rw [this]
  rw [this]
  exact (measurableSet_descLadderEpoch_eq t).inter (hm hB)

section Canonical

variable {ν : Measure ℝ} [IsProbabilityMeasure ν] {s : ℝ}

/-- **The excursion heights are i.i.d.** on the canonical space, with the law of the first
excursion maximum. -/
theorem iIndepFun_excursionHeight (hs : 0 ≤ s) (hexp : Integrable (fun y => Real.exp (s * y)) ν)
    (hρ : mgf id ν s < 1) :
    iIndepFun excursionHeight (Measure.infinitePi fun _ : ℕ => ν) ∧
      ∀ i, (Measure.infinitePi fun _ : ℕ => ν).map (excursionHeight i) =
        (Measure.infinitePi fun _ : ℕ => ν).map excursionMax :=
  iIndepFun_iterLadder measurable_excursionMax
    (fun t _ hB => measurableSet_past_excursionMax_preimage t hB) (ae_hasDescLadder hs hexp hρ)

/-- **The excursion lengths are i.i.d.** on the canonical space, with the law of `τ₋`. -/
theorem iIndepFun_excursionLength (hs : 0 ≤ s) (hexp : Integrable (fun y => Real.exp (s * y)) ν)
    (hρ : mgf id ν s < 1) :
    iIndepFun excursionLength (Measure.infinitePi fun _ : ℕ => ν) ∧
      ∀ i, (Measure.infinitePi fun _ : ℕ => ν).map (excursionLength i) =
        (Measure.infinitePi fun _ : ℕ => ν).map descLadderEpoch :=
  iIndepFun_iterLadder measurable_descLadderEpoch
    (fun t B _ => measurableSet_past_descLadderEpoch_preimage t B) (ae_hasDescLadder hs hexp hρ)

/-- Strong law for the ladder epochs: `T_k / k → E τ₋` almost surely. -/
theorem ae_tendsto_ladderEpoch_div (hs : 0 ≤ s) (hexp : Integrable (fun y => Real.exp (s * y)) ν)
    (hρ : mgf id ν s < 1) :
    ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => ν), Tendsto (fun k : ℕ => (ladderEpoch k x : ℝ) / k)
      atTop (𝓝 (∫ y, (descLadderEpoch y : ℝ) ∂(Measure.infinitePi fun _ : ℕ => ν))) := by
  set μ := Measure.infinitePi fun _ : ℕ => ν
  obtain ⟨hind, hlaw⟩ := iIndepFun_excursionLength hs hexp hρ
  set L : ℕ → (ℕ → ℝ) → ℝ := fun i x => (excursionLength i x : ℝ)
  have hindL : iIndepFun L μ :=
    hind.comp (fun _ (n : ℕ) => (n : ℝ)) fun _ => measurable_from_nat
  have hLm : ∀ i, Measurable (L i) := fun i =>
    measurable_from_nat.comp (measurable_excursionLength i)
  have hident : ∀ i, IdentDistrib (L i) (L 0) μ μ := fun i =>
    { aemeasurable_fst := (hLm i).aemeasurable
      aemeasurable_snd := (hLm 0).aemeasurable
      map_eq := by
        rw [show L i = (fun n : ℕ => (n : ℝ)) ∘ excursionLength i from rfl,
          show L 0 = (fun n : ℕ => (n : ℝ)) ∘ excursionLength 0 from rfl,
          ← Measure.map_map measurable_from_nat (measurable_excursionLength i),
          ← Measure.map_map measurable_from_nat (measurable_excursionLength 0), hlaw i, hlaw 0] }
  have h := strong_law_ae L (integrable_descLadderEpoch hs hexp hρ)
    (fun i j hij => hindL.indepFun hij) hident
  filter_upwards [h] with x hx
  refine hx.congr fun k => ?_
  simp only [L, smul_eq_mul, ladderEpoch, Nat.cast_sum]
  rw [inv_mul_eq_div]

end Canonical

/-- **Renewal law of large numbers, pathwise**: if the ladder epochs satisfy `T_k / k → A > 0`
then the ladder count satisfies `Nₙ / n → 1 / A`, from `T_{Nₙ} ≤ n < T_{Nₙ + 1}`. -/
theorem tendsto_ladderCount_div {x : ℕ → ℝ} (hx : IsLadderGood x) {A : ℝ} (hA : 0 < A)
    (hT : Tendsto (fun k : ℕ => (ladderEpoch k x : ℝ) / k) atTop (𝓝 A)) :
    Tendsto (fun n : ℕ => (ladderCount n x : ℝ) / n) atTop (𝓝 A⁻¹) := by
  have hN : Tendsto (fun n => ladderCount n x) atTop atTop :=
    tendsto_atTop.2 fun m => eventually_atTop.2 ⟨ladderEpoch m x, fun n hn =>
      (le_ladderCount_iff hx).2 hn⟩
  have h1 : Tendsto (fun k : ℕ => (k : ℝ) / ladderEpoch k x) atTop (𝓝 A⁻¹) := by
    refine (hT.inv₀ hA.ne').congr fun k => ?_
    rw [inv_div]
  have h2 : Tendsto (fun k : ℕ => (k : ℝ) / ladderEpoch (k + 1) x) atTop (𝓝 A⁻¹) := by
    have h3 : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ) / ladderEpoch (k + 1) x) atTop (𝓝 A⁻¹) :=
      h1.comp (tendsto_add_atTop_nat 1)
    have h4 := (tendsto_natCast_div_add_atTop (1 : ℝ)).mul h3
    rw [one_mul] at h4
    refine h4.congr fun k => ?_
    rw [Nat.cast_add_one, div_mul_div_cancel₀ (by positivity)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (h2.comp hN) (h1.comp hN) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast hn)
      (by exact_mod_cast (lt_ladderEpoch_ladderCount_succ hx n).le)
  · filter_upwards [hN.eventually (eventually_ge_atTop 1)] with n hn
    have h5 := ladderEpoch_ladderCount_le hx n
    have h6 : 1 ≤ ladderEpoch (ladderCount n x) x := hn.trans (le_ladderEpoch hx _)
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast h6)
      (by exact_mod_cast h5)

end Cslib.Bioinformatics.Alignment.ScoreSignificance.LadderDerivation

/-! ## Back to the score sequence: `CramerScores` implies `LadderInput` -/

namespace Cslib.Bioinformatics.Alignment.ScoreSignificance

open MeasureTheory ProbabilityTheory Filter Topology LadderDerivation

namespace CramerScores

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ} {θ : ℝ}

theorem isProbabilityMeasure (h : CramerScores P X θ) : IsProbabilityMeasure P :=
  h.iIndepFun.isProbabilityMeasure

theorem measurable_path (h : CramerScores P X θ) : Measurable fun ω k => X k ω :=
  measurable_pi_iff.2 h.measurable

/-- The law of the score sequence is the infinite product of the score law. -/
theorem map_path (h : CramerScores P X θ) :
    P.map (fun ω k => X k ω) = Measure.infinitePi fun _ : ℕ => P.map (X 0) := by
  rw [h.iIndepFun.map_fun_eq_infinitePi_map h.measurable]
  congr 1
  funext i
  exact (h.identDistrib i).map_eq

theorem integrable_exp_half (h : CramerScores P X θ) :
    Integrable (fun y => Real.exp (θ / 2 * y)) (P.map (X 0)) := by
  have := h.isProbabilityMeasure
  have hexp : Integrable (fun ω => Real.exp (θ * X 0 ω)) P := by
    by_contra hn
    have h1 := h.mgf_eq_one
    simp [mgf, integral_undef hn] at h1
  have hhalf : Integrable (fun ω => Real.exp (θ / 2 * X 0 ω)) P :=
    integrable_exp_mul_of_nonneg_of_le hexp (by linarith [h.pos]) (by linarith [h.pos])
  rw [integrable_map_measure (by fun_prop) (h.measurable 0).aemeasurable]
  exact hhalf

theorem mgf_map_half_lt_one (h : CramerScores P X θ) : mgf id (P.map (X 0)) (θ / 2) < 1 := by
  have := h.isProbabilityMeasure
  rw [mgf_id_map (h.measurable 0).aemeasurable]
  exact mgf_half_lt_one h.integral_neg h.pos h.mgf_eq_one

theorem half_nonneg (h : CramerScores P X θ) : 0 ≤ θ / 2 := by linarith [h.pos]

/-- Almost every score path is ladder-good: every restart of the walk eventually drops below
its starting value. -/
theorem ae_isLadderGood (h : CramerScores P X θ) : ∀ᵐ ω ∂P, IsLadderGood fun k => X k ω := by
  have := h.isProbabilityMeasure
  have h1 := LadderDerivation.ae_isLadderGood h.half_nonneg h.integrable_exp_half
    h.mgf_map_half_lt_one
  rw [← h.map_path] at h1
  exact ae_of_ae_map h.measurable_path.aemeasurable h1

/-- **The first descending ladder epoch has finite mean** under the Cramér conditions. -/
theorem integrable_descLadderEpoch (h : CramerScores P X θ) :
    Integrable (fun ω => (descLadderEpoch fun k => X k ω : ℝ)) P := by
  have := h.isProbabilityMeasure
  have h1 := LadderDerivation.integrable_descLadderEpoch h.half_nonneg h.integrable_exp_half
    h.mgf_map_half_lt_one
  rw [← h.map_path, integrable_map_measure measurable_descLadderEpoch_real.aestronglyMeasurable
    h.measurable_path.aemeasurable] at h1
  exact h1

theorem integral_descLadderEpoch_map (h : CramerScores P X θ) :
    ∫ x, (descLadderEpoch x : ℝ) ∂(P.map fun ω k => X k ω) =
      ∫ ω, (descLadderEpoch fun k => X k ω : ℝ) ∂P :=
  integral_map h.measurable_path.aemeasurable measurable_descLadderEpoch_real.aestronglyMeasurable

/-- The mean descending ladder epoch is at least `1`. -/
theorem one_le_integral_descLadderEpoch (h : CramerScores P X θ) :
    1 ≤ ∫ ω, (descLadderEpoch fun k => X k ω : ℝ) ∂P := by
  have := h.isProbabilityMeasure
  have h1 := LadderDerivation.one_le_integral_descLadderEpoch h.half_nonneg
    h.integrable_exp_half h.mgf_map_half_lt_one
  rwa [← h.map_path, h.integral_descLadderEpoch_map] at h1

/-- **Renewal law of large numbers for the ladder count**: `Nₙ / n → 1 / A` almost surely, where
`A = E τ₋` is the mean descending ladder epoch. -/
theorem ae_tendsto_ladderCount_div (h : CramerScores P X θ) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (ladderCount n (fun k => X k ω) : ℝ) / n) atTop
      (𝓝 (∫ ω, (descLadderEpoch fun k => X k ω : ℝ) ∂P)⁻¹) := by
  have := h.isProbabilityMeasure
  have h1 := LadderDerivation.ae_tendsto_ladderEpoch_div h.half_nonneg h.integrable_exp_half
    h.mgf_map_half_lt_one
  have h2 := LadderDerivation.ae_isLadderGood h.half_nonneg h.integrable_exp_half
    h.mgf_map_half_lt_one
  rw [← h.map_path, h.integral_descLadderEpoch_map] at h1
  rw [← h.map_path] at h2
  have hA := h.one_le_integral_descLadderEpoch
  filter_upwards [ae_of_ae_map h.measurable_path.aemeasurable h1,
    ae_of_ae_map h.measurable_path.aemeasurable h2] with ω hT hx
  exact tendsto_ladderCount_div hx (by linarith) hT

/-- **Strong Markov property at the first descending ladder epoch** for i.i.d. scores: if the
event `E` on paths is determined by the scores before `τ₋`, then the restarted score sequence
`(X (τ₋ + j))_j` is independent of `{X ∈ E}` and has the law of the original sequence. -/
theorem strongMarkov (h : CramerScores P X θ) {E : Set (ℕ → ℝ)} (hEm : MeasurableSet E)
    (hE : ∀ t, MeasurableSet[pastMeasurableSpace t]
      (E ∩ {x | HasDescLadder x ∧ descLadderEpoch x = t}))
    {B : Set (ℕ → ℝ)} (hB : MeasurableSet B) :
    P {ω | (fun k => X k ω) ∈ E ∧
        pathShift (descLadderEpoch fun k => X k ω) (fun k => X k ω) ∈ B} =
      P {ω | (fun k => X k ω) ∈ E} * P {ω | (fun k => X k ω) ∈ B} := by
  have := h.isProbabilityMeasure
  have hHas := LadderDerivation.ae_hasDescLadder h.half_nonneg h.integrable_exp_half
    h.mgf_map_half_lt_one
  rw [← h.map_path] at hHas
  have hHas' : (P.map fun ω k => X k ω) {x | HasDescLadder x}ᶜ = 0 := ae_iff.1 hHas
  have hshift : Measurable fun x : ℕ → ℝ => pathShift (descLadderEpoch x) x :=
    measurable_comp_descLadderEpoch measurable_pathShift
  have h1 := infinitePi_strongMarkov (ν := P.map (X 0)) hE hB
  rw [← h.map_path, Set.inter_right_comm, measure_inter_conull hHas',
    measure_inter_conull hHas'] at h1
  have e1 : {ω | (fun k => X k ω) ∈ E ∧
      pathShift (descLadderEpoch fun k => X k ω) (fun k => X k ω) ∈ B} =
      (fun ω k => X k ω) ⁻¹' (E ∩ {x | pathShift (descLadderEpoch x) x ∈ B}) := rfl
  have hm : MeasurableSet (E ∩ {x | pathShift (descLadderEpoch x) x ∈ B}) := hEm.inter (hshift hB)
  rw [e1, ← Measure.map_apply h.measurable_path hm, h1,
    Measure.map_apply h.measurable_path hEm, Measure.map_apply h.measurable_path hB]
  rfl

/-- The restarted score sequence after `τ₋` has the law of the original sequence. -/
theorem map_pathShift_descLadderEpoch (h : CramerScores P X θ) :
    P.map (fun ω => pathShift (descLadderEpoch fun k => X k ω) (fun k => X k ω)) =
      P.map fun ω k => X k ω := by
  have hshift : Measurable fun x : ℕ → ℝ => pathShift (descLadderEpoch x) x :=
    measurable_comp_descLadderEpoch measurable_pathShift
  ext B hB
  have h1 := h.strongMarkov MeasurableSet.univ
    (fun t => by rw [Set.univ_inter]; exact measurableSet_descLadderEpoch_eq t) hB
  have := h.isProbabilityMeasure
  simp only [Set.mem_univ, true_and, Set.ofPred_true, measure_univ, one_mul] at h1
  rw [Measure.map_apply (f := fun ω => pathShift (descLadderEpoch fun k => X k ω) (fun k => X k ω))
      (hshift.comp h.measurable_path) hB,
    Measure.map_apply h.measurable_path hB]
  exact h1

/-- Precomposition with a measurable map preserves independence of the pushed-forward law. -/
private theorem iIndepFun_comp_path (h : CramerScores P X θ) {β : Type*} [MeasurableSpace β]
    {f : ℕ → (ℕ → ℝ) → β} (hf : ∀ i, Measurable (f i))
    (hind : ProbabilityTheory.iIndepFun f (P.map fun ω k => X k ω)) :
    ProbabilityTheory.iIndepFun (fun i ω => f i (fun k => X k ω)) P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hind ⊢
  intro S sets hsets
  have h1 := hind S hsets
  have e : ⋂ i ∈ S, (fun ω => f i (fun k => X k ω)) ⁻¹' sets i =
      (fun ω k => X k ω) ⁻¹' ⋂ i ∈ S, f i ⁻¹' sets i := by
    ext ω; simp
  rw [e, ← Measure.map_apply h.measurable_path
    (Finset.measurableSet_biInter _ fun i hi => hf i (hsets i hi)), h1]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Measure.map_apply h.measurable_path (hf i (hsets i hi))]
  rfl

/-- **The excursion heights of i.i.d. Cramér scores are independent.** -/
theorem iIndepFun_excursionHeight (h : CramerScores P X θ) :
    ProbabilityTheory.iIndepFun (fun i ω => excursionHeight i fun k => X k ω) P := by
  have := h.isProbabilityMeasure
  have h1 := (LadderDerivation.iIndepFun_excursionHeight h.half_nonneg h.integrable_exp_half
    h.mgf_map_half_lt_one).1
  rw [← h.map_path] at h1
  exact h.iIndepFun_comp_path measurable_excursionHeight h1

/-- **The excursion heights of i.i.d. Cramér scores are identically distributed**, with the law
of the first excursion maximum. -/
theorem identDistrib_excursionHeight (h : CramerScores P X θ) (i : ℕ) :
    IdentDistrib (fun ω => excursionHeight i fun k => X k ω)
      (fun ω => excursionMax fun k => X k ω) P P where
  aemeasurable_fst := ((measurable_excursionHeight i).comp h.measurable_path).aemeasurable
  aemeasurable_snd := (measurable_excursionMax.comp h.measurable_path).aemeasurable
  map_eq := by
    have := h.isProbabilityMeasure
    have h1 := (LadderDerivation.iIndepFun_excursionHeight h.half_nonneg h.integrable_exp_half
      h.mgf_map_half_lt_one).2 i
    rw [← h.map_path, Measure.map_map (measurable_excursionHeight i) h.measurable_path,
      Measure.map_map measurable_excursionMax h.measurable_path] at h1
    exact h1

/-- **The ladder input derived from the Cramér conditions.** The excursion heights are those of
the descending ladder excursions of the score walk (`excursionHeight`), `Nₙ` is the number of
excursions completed by time `n` (`ladderCount`), `F` is the distribution function of the first
excursion maximum, and `A = E τ₋` is the mean descending ladder epoch. -/
noncomputable def toLadderInput (h : CramerScores P X θ) :
    LadderInput P (maxSegmentScoreRV X) where
  Y i ω := excursionHeight i fun k => X k ω
  N n ω := ladderCount n fun k => X k ω
  F t := P.real {ω | excursionMax (fun k => X k ω) ≤ t}
  A := ∫ ω, (descLadderEpoch fun k => X k ω : ℝ) ∂P
  A_pos := lt_of_lt_of_le one_pos h.one_le_integral_descLadderEpoch
  measurable_Y i := (measurable_excursionHeight i).comp h.measurable_path
  iIndepFun_Y := h.iIndepFun_excursionHeight
  real_Y_le i t := by
    rw [measureReal_def, measureReal_def]
    congr 1
    exact (h.identDistrib_excursionHeight i).measure_mem_eq measurableSet_Iic
  count_lln ε hε := by
    have := h.isProbabilityMeasure
    have hmeas : ∀ n : ℕ, AEStronglyMeasurable
        (fun ω => (ladderCount n (fun k => X k ω) : ℝ) / n) P := fun n =>
      ((measurable_from_nat.comp ((measurable_ladderCount n).comp h.measurable_path)).div_const
        _).aestronglyMeasurable
    have h1 := tendstoInMeasure_of_tendsto_ae hmeas h.ae_tendsto_ladderCount_div
      (ENNReal.ofReal ε) (by simpa using hε)
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    rw [ENNReal.toReal_zero] at h2
    refine h2.congr fun n => ?_
    simp only [Function.comp_apply, measureReal_def, edist_dist, Real.dist_eq]
    congr 2
    ext ω
    simp only [Set.mem_ofPred_eq]
    exact ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)
  le_of_forall_le := by
    filter_upwards [h.ae_isLadderGood] with ω hω n t ht
    exact maxSegmentScore_le_of_forall hω ht
  le_of_lt_count := by
    filter_upwards [h.ae_isLadderGood] with ω hω n i hi
    exact excursionHeight_le_maxSegmentScore hω hi

@[simp] theorem toLadderInput_Y (h : CramerScores P X θ) (i : ℕ) (ω : Ω) :
    h.toLadderInput.Y i ω = excursionHeight i fun k => X k ω := rfl

@[simp] theorem toLadderInput_N (h : CramerScores P X θ) (n : ℕ) (ω : Ω) :
    h.toLadderInput.N n ω = ladderCount n fun k => X k ω := rfl

@[simp] theorem toLadderInput_A (h : CramerScores P X θ) :
    h.toLadderInput.A = ∫ ω, (descLadderEpoch fun k => X k ω : ℝ) ∂P := rfl

@[simp] theorem toLadderInput_F (h : CramerScores P X θ) (t : ℝ) :
    h.toLadderInput.F t = P.real {ω | excursionMax (fun k => X k ω) ≤ t} := rfl

/-- **The Cramér conditions imply the ladder input** that the Gumbel-tail theorems of
`GumbelTail` assume: i.i.d. scores with negative mean and a Cramér root `θ > 0` have a
`LadderInput` for their maximal segment score. -/
theorem nonempty_ladderInput (h : CramerScores P X θ) :
    Nonempty (LadderInput P (maxSegmentScoreRV X)) :=
  ⟨h.toLadderInput⟩

end CramerScores

end Cslib.Bioinformatics.Alignment.ScoreSignificance
