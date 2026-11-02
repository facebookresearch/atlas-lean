/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BranchingProcess.GaltonWatson
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Poisson.Basic

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Antidiag.Pi

/-!
# Total progeny of a Galton–Watson process: the hitting-time theorem and the Borel law

Explore a Galton–Watson forest started from `k` ancestors breadth first, and let `ξ_i` be the
number of children of the `i`-th explored individual. The number of individuals still waiting
to be explored after `j` steps is the random walk `k + ∑_{i < j} (ξ_i - 1)`, and the total
progeny `T` is the first time this walk hits `0` (the Łukasiewicz path; Dwass 1969, van der
Hofstad 2017, ch. 3). The steps `ξ_i` are i.i.d. with the offspring law `ν`.

This file works with the first `n` steps `x : Fin n → ℕ`, whose joint law is `ν^{⊗n}`.
The measure statements below assume only `[IsFiniteMeasure ν]`, so they are
finite-measure identities: the stated event masses need not be probabilities. When `ν`
is a probability measure they are the probabilities `P(T = n)` and `P(S_n = n - k)`.
The event `{T = n}` is `{x | ∑ x_i + k = n ∧ IsFirstPassage k n x}`, where `IsFirstPassage k n x`
says that the walk stays positive at the times `j < n`.

## Main results

* `card_filter_isFirstPassage_rotate`: the **cycle lemma** (Dvoretzky–Motzkin 1947) — if
  `∑ x_i + k = n` and `1 ≤ k`, exactly `k` of the `n` cyclic shifts of `x` are first-passage
  sequences.
* `natCast_mul_hittingWeight`: the **hitting-time theorem** in weighted form: for every weight
  `p : ℕ → R` on a commutative semiring, `n · H_p(k, n) = k · W_p(k, n)`, where `H_p` sums
  `∏ p(x_i)` over first-passage sequences ending at `0` at time `n` and `W_p` over all sequences
  ending at `0` at time `n`.
* `natCast_mul_measure_firstPassage`: **Otter–Dwass formula** `n · P(T = n) = k · P(S_n = n - k)`
  for i.i.d. offspring numbers with law `ν` (a probability measure; as stated it is the
  finite-measure identity), where `S_n = ξ_1 + ⋯ + ξ_n`.
* `hittingWeight_poisson_one`: the **Borel law** — for Poisson(`r`) offspring and one ancestor,
  `P(T = n) = e^{-rn} (rn)^{n-1} / n!` (`n ≥ 1`); `natCast_mul_hittingWeight_poisson` gives the
  Borel–Tanner law for `k` ancestors.
* `meanTotalProgeny_eq`: the mean total progeny `∑_n E Z_n` equals `(1 - m)⁻¹` in `[0, ∞]`, so it
  is `1 / (1 - m)` when `m < 1` and infinite when `m ≥ 1`.

## Scope

The identification of the total progeny with the hitting time of the exploration walk is the
standard breadth-first bijection (Dwass 1969); this file states the laws for the walk and does
not formalize the bijection with the generation sizes of `GaltonWatson.law`.

## References

* R. Otter, The multiplicative process, *Ann. Math. Statist.* 20 (1949), 206–224.
* M. Dwass, The total progeny in a branching process and a related random walk,
  *J. Appl. Probab.* 6 (1969), 682–686.
* A. Dvoretzky, Th. Motzkin, A problem of arrangements, *Duke Math. J.* 14 (1947), 305–313.
* R. van der Hofstad, M. Keane, An elementary proof of the hitting time theorem,
  *Amer. Math. Monthly* 115 (2008), 753–756.
* É. Borel, Sur l'emploi du théorème de Bernoulli pour faciliter le calcul d'une infinité de
  coefficients, *C. R. Acad. Sci. Paris* 214 (1942), 452–456.
* J. C. Tanner, A derivation of the Borel distribution, *Biometrika* 48 (1961), 222–224.
* F. A. Haight, M. A. Breuer, The Borel–Tanner distribution, *Biometrika* 47 (1960), 143–150.
* R. van der Hofstad, *Random Graphs and Complex Networks*, Vol. 1, Cambridge University Press
  (2017), ch. 3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal Nat

namespace MathlibExt.Probability.GaltonWatson

/-- The exploration walk started at `k` with steps `x_i - 1` stays positive at every time
`j < n`: `j < k + ∑_{i < j} x_i`. Together with `∑ x_i + k = n` this says that the walk first
hits `0` at time `n`. -/
def IsFirstPassage (k n : ℕ) (x : Fin n → ℕ) : Prop :=
  ∀ j ∈ range n, j < k + ∑ i with i.val < j, x i

instance (k n : ℕ) (x : Fin n → ℕ) : Decidable (IsFirstPassage k n x) := by
  unfold IsFirstPassage; infer_instance

/-- The cyclic shift `i ↦ x_{(i + r) mod n}` of a tuple. -/
def rotate {n : ℕ} (x : Fin n → ℕ) (r : ℕ) : Fin n → ℕ :=
  fun i => x ⟨(i.val + r) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- Sum over the `Fin n` indices below `t ≤ n` as a sum over `range t`. -/
private theorem sum_fin_lt_eq_sum_range {M : Type*} [AddCommMonoid M] {n t : ℕ} (ht : t ≤ n)
    (g : ℕ → M) : ∑ i : Fin n with i.val < t, g i.val = ∑ i ∈ range t, g i := by
  rw [sum_filter, Fin.sum_univ_eq_sum_range (fun i => if i < t then g i else 0) n,
    ← sum_filter]
  congr 1
  ext i; simp only [mem_filter, mem_range]; omega

section walk
variable {n : ℕ} (hn : 0 < n) (x : Fin n → ℕ)

/-- Periodic integer steps `x_{i mod n} - 1`. -/
private def stepZ (i : ℕ) : ℤ := (x ⟨i % n, Nat.mod_lt _ hn⟩ : ℤ) - 1

/-- Partial sums of the periodic steps. -/
private def walkZ (j : ℕ) : ℤ := ∑ i ∈ range j, stepZ hn x i

/-- Running minimum of the walk. -/
private def runMin : ℕ → ℤ
  | 0 => walkZ hn x 0
  | m + 1 => min (runMin m) (walkZ hn x (m + 1))

private theorem stepZ_add_n (i : ℕ) : stepZ hn x (i + n) = stepZ hn x i := by
  simp [stepZ, Nat.add_mod_right]

private theorem walkZ_add (a b : ℕ) :
    walkZ hn x (a + b) = walkZ hn x a + ∑ i ∈ range b, stepZ hn x (a + i) := by
  simp [walkZ, sum_range_add]

private theorem walkZ_add_n (j : ℕ) : walkZ hn x (j + n) = walkZ hn x j + walkZ hn x n := by
  rw [add_comm j n, walkZ_add]
  have : ∑ i ∈ range j, stepZ hn x (n + i) = walkZ hn x j := by
    simp_rw [add_comm n, stepZ_add_n]; rfl
  rw [this, add_comm]

private theorem walkZ_zero : walkZ hn x 0 = 0 := by simp [walkZ]

private theorem walkZ_succ (j : ℕ) : walkZ hn x (j + 1) = walkZ hn x j + stepZ hn x j := by
  simp [walkZ, sum_range_succ]

private theorem stepZ_ge (i : ℕ) : -1 ≤ stepZ hn x i := by
  simp only [stepZ]; omega

private theorem walkZ_n {k : ℕ} (hx : ∑ i, x i + k = n) : walkZ hn x n = -k := by
  have h1 : walkZ hn x n = ∑ i : Fin n, ((x i : ℤ) - 1) := by
    rw [walkZ, sum_range]
    refine sum_congr rfl fun i _ => ?_
    simp only [stepZ]
    congr 3
    exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
  rw [h1, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have : ((∑ i, x i : ℕ) : ℤ) + k = n := by exact_mod_cast hx
  push_cast at this
  linarith

private theorem runMin_le (m : ℕ) : ∀ j ≤ m, runMin hn x m ≤ walkZ hn x j := by
  induction m with
  | zero => intro j hj; rw [Nat.le_zero.1 hj]; simp [runMin]
  | succ m ih =>
    intro j hj
    rcases Nat.lt_or_eq_of_le hj with h | rfl
    · exact (min_le_left _ _).trans (ih j (by omega))
    · exact min_le_right _ _

private theorem runMin_attained (m : ℕ) : ∃ j ≤ m, runMin hn x m = walkZ hn x j := by
  induction m with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ m ih =>
    obtain ⟨j, hj, he⟩ := ih
    rcases le_total (runMin hn x m) (walkZ hn x (m + 1)) with h | h
    · exact ⟨j, by omega, by rw [runMin, min_eq_left h, he]⟩
    · exact ⟨m + 1, le_rfl, by simp [runMin, min_eq_right h]⟩

private theorem lt_runMin_iff (m : ℕ) :
    walkZ hn x (m + 1) < runMin hn x m ↔ ∀ j ≤ m, walkZ hn x (m + 1) < walkZ hn x j := by
  constructor
  · intro h j hj; exact h.trans_le (runMin_le hn x m j hj)
  · intro h
    obtain ⟨j, hj, he⟩ := runMin_attained hn x m
    rw [he]; exact h j hj

private theorem runMin_succ (m : ℕ) :
    runMin hn x (m + 1) =
      runMin hn x m - if walkZ hn x (m + 1) < runMin hn x m then 1 else 0 := by
  have hs : walkZ hn x m - 1 ≤ walkZ hn x (m + 1) := by
    rw [walkZ_succ]; linarith [stepZ_ge hn x m]
  have hm := runMin_le hn x m m le_rfl
  split_ifs with h
  · simp only [runMin, min_eq_right h.le]; omega
  · simp only [runMin, min_eq_left (not_lt.1 h), sub_zero]

private theorem sum_Ico_records {a b : ℕ} (hab : a ≤ b) :
    (∑ m ∈ Ico a b, if walkZ hn x (m + 1) < runMin hn x m then (1 : ℤ) else 0) =
      runMin hn x a - runMin hn x b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih => rw [sum_Ico_succ_top hab, ih, runMin_succ]; ring

private theorem runMin_n_add {k : ℕ} (hx : ∑ i, x i + k = n) (t : ℕ) :
    runMin hn x (n + t) = min (runMin hn x (n - 1)) (runMin hn x t - k) := by
  have hwn := walkZ_n hn x hx
  induction t with
  | zero =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, runMin]
    have := walkZ_add_n hn x 0
    rw [Nat.zero_add] at this
    rw [walkZ_zero, zero_add] at this
    simp [walkZ_zero, hwn]
  | succ t ih =>
    rw [← Nat.add_assoc, runMin, ih, runMin]
    have h := walkZ_add_n hn x (t + 1)
    rw [show t + 1 + n = n + t + 1 by omega, hwn] at h
    rw [h, ← min_sub_sub_right, ← sub_eq_add_neg, min_assoc]

private theorem sum_rotate {r t : ℕ} (ht : t ≤ n) :
    (∑ i : Fin n with i.val < t, (rotate x r i : ℤ)) = walkZ hn x (r + t) - walkZ hn x r + t := by
  have h1 : (∑ i : Fin n with i.val < t, (rotate x r i : ℤ)) =
      ∑ m ∈ range t, ((x ⟨(m + r) % n, Nat.mod_lt _ hn⟩ : ℕ) : ℤ) :=
    sum_fin_lt_eq_sum_range ht (fun m => ((x ⟨(m + r) % n, Nat.mod_lt _ hn⟩ : ℕ) : ℤ))
  rw [h1, walkZ_add]
  have h2 : ∀ m, ((x ⟨(m + r) % n, Nat.mod_lt _ hn⟩ : ℕ) : ℤ) = stepZ hn x (r + m) + 1 := by
    intro m; simp only [stepZ, add_comm m r]; ring
  simp_rw [h2, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
  ring

private theorem isFirstPassage_rotate_iff {k r : ℕ} (hx : ∑ i, x i + k = n) :
    IsFirstPassage k n (rotate x r) ↔ ∀ t < n, walkZ hn x (r + n) < walkZ hn x (r + t) := by
  have hrn : walkZ hn x (r + n) = walkZ hn x r - k := by
    rw [walkZ_add_n, walkZ_n hn x hx]; ring
  unfold IsFirstPassage
  refine forall_congr' fun t => ?_
  rw [mem_range]
  refine imp_congr_right fun ht => ?_
  have hs := sum_rotate hn x (r := r) ht.le
  rw [hrn]
  constructor
  · intro h
    have h' : ((t : ℕ) : ℤ) < ((k + ∑ i : Fin n with i.val < t, rotate x r i : ℕ) : ℤ) := by
      exact_mod_cast h
    push_cast at h'
    rw [hs] at h'
    linarith
  · intro h
    have h' : ((t : ℕ) : ℤ) < ((k + ∑ i : Fin n with i.val < t, rotate x r i : ℕ) : ℤ) := by
      push_cast; rw [hs]; linarith
    exact_mod_cast h'

private theorem window_iff {k r : ℕ} (hx : ∑ i, x i + k = n) (hr : r < n) :
    (∀ t < n, walkZ hn x (r + n) < walkZ hn x (r + t)) ↔
      ∀ j ≤ r + n - 1, walkZ hn x (r + n) < walkZ hn x j := by
  have hwn := walkZ_n hn x hx
  constructor
  · intro h j hj
    by_cases hjr : r ≤ j
    · have := h (j - r) (by omega)
      rwa [show r + (j - r) = j by omega] at this
    · have h1 := h (j + n - r) (by omega)
      rw [show r + (j + n - r) = j + n by omega] at h1
      have e1 := walkZ_add_n hn x j
      have e2 := walkZ_add_n hn x r
      have hk0 : (0 : ℤ) ≤ k := Nat.cast_nonneg k
      linarith
  · intro h t ht
    exact h (r + t) (by omega)

private theorem isFirstPassage_rotate_iff_record {k r : ℕ} (hx : ∑ i, x i + k = n)
    (hr : r < n) :
    IsFirstPassage k n (rotate x r) ↔ walkZ hn x (r + n - 1 + 1) < runMin hn x (r + n - 1) := by
  rw [isFirstPassage_rotate_iff hn x hx, window_iff hn x hx hr, lt_runMin_iff,
    show r + n - 1 + 1 = r + n by omega]

end walk

/-- **Cycle lemma** (Dvoretzky–Motzkin 1947). If `x : Fin n → ℕ` satisfies `∑ x_i + k = n` with
`1 ≤ k`, then exactly `k` of the `n` cyclic shifts of `x` (counted by shift `r < n`) are
first-passage sequences. -/
theorem card_filter_isFirstPassage_rotate {k n : ℕ} (hk : 1 ≤ k) (x : Fin n → ℕ)
    (hx : ∑ i, x i + k = n) :
    #{r ∈ range n | IsFirstPassage k n (rotate x r)} = k := by
  have hn : 0 < n := by omega
  have key : ((#{r ∈ range n | IsFirstPassage k n (rotate x r)} : ℕ) : ℤ) = k := by
    rw [card_filter, Nat.cast_sum]
    have h1 : ∀ r ∈ range n, (((if IsFirstPassage k n (rotate x r) then 1 else 0 : ℕ)) : ℤ) =
        if walkZ hn x (n - 1 + r + 1) < runMin hn x (n - 1 + r) then 1 else 0 := by
      intro r hr
      have := isFirstPassage_rotate_iff_record hn x hx (mem_range.1 hr)
      rw [show n - 1 + r = r + n - 1 by omega]
      by_cases h : IsFirstPassage k n (rotate x r)
      · simp [h, this.1 h]
      · simp [h, mt this.2 h]
    have h2 : (∑ m ∈ Ico (n - 1) (2 * n - 1),
        if walkZ hn x (m + 1) < runMin hn x m then (1 : ℤ) else 0) =
        ∑ r ∈ range n, if walkZ hn x (n - 1 + r + 1) < runMin hn x (n - 1 + r) then 1 else 0 := by
      rw [sum_Ico_eq_sum_range, show 2 * n - 1 - (n - 1) = n by omega]
    rw [sum_congr rfl h1, ← h2, sum_Ico_records hn x (by omega),
      show 2 * n - 1 = n + (n - 1) by omega, runMin_n_add hn x hx,
      min_eq_right (by omega)]
    ring
  exact_mod_cast key


/-- The weight `W_p(k, n) = ∑ ∏_i p(x_i)` over the step sequences `x : Fin n → ℕ` with
`∑ x_i + k = n` (the walk from `k` is at `0` at time `n`). For `p(j) = P(ξ = j)` this is
`P(ξ_1 + ⋯ + ξ_n = n - k)` when `k ≤ n`, and `0` when `k > n`. -/
def walkWeight {R : Type*} [CommSemiring R] (p : ℕ → R) (k n : ℕ) : R :=
  ∑ x ∈ (Nat.antidiagonalTuple n (n - k)).filter (fun x => ∑ i, x i + k = n), ∏ i, p (x i)

/-- The weight `H_p(k, n) = ∑ ∏_i p(x_i)` over the step sequences with `∑ x_i + k = n` along
which the walk from `k` first hits `0` at time `n`. For `p(j) = P(ξ = j)` this is the
probability `P(T = n)` that the total progeny of `k` ancestors is `n`. -/
def hittingWeight {R : Type*} [CommSemiring R] (p : ℕ → R) (k n : ℕ) : R :=
  ∑ x ∈ (Nat.antidiagonalTuple n (n - k)).filter
    (fun x => ∑ i, x i + k = n ∧ IsFirstPassage k n x), ∏ i, p (x i)

private theorem rotIndex_injective (n r : ℕ) :
    Function.Injective (fun i : Fin n => (⟨(i.val + r) % n,
      Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩ : Fin n)) := by
  intro a b hab
  have h : (a.val + r) % n = (b.val + r) % n := congrArg Fin.val hab
  have h' : a.val % n = b.val % n := Nat.ModEq.add_right_cancel' r h
  rwa [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt, ← Fin.ext_iff] at h'

/-- The index rotation `i ↦ (i + r) mod n` as a permutation of `Fin n`. -/
private noncomputable def rotEquiv (n r : ℕ) : Fin n ≃ Fin n :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (rotIndex_injective n r))

private theorem rotate_eq (n r : ℕ) (x : Fin n → ℕ) : rotate x r = x ∘ rotEquiv n r := rfl

/-- Precomposition with `rotEquiv n r` as a permutation of tuples. -/
private noncomputable def rotTupleEquiv (n r : ℕ) : (Fin n → ℕ) ≃ (Fin n → ℕ) where
  toFun x := x ∘ rotEquiv n r
  invFun y := y ∘ (rotEquiv n r).symm
  left_inv x := by funext i; simp
  right_inv y := by funext i; simp

/-- **Hitting-time theorem**, weighted form: `n · H_p(k, n) = k · W_p(k, n)` for every weight
`p` with values in a commutative semiring and all `k, n`. For probability weights this is the
hitting-time theorem of van der Hofstad–Keane (2008); the proof double counts cyclic shifts
with the cycle lemma. -/
theorem natCast_mul_hittingWeight {R : Type*} [CommSemiring R] (p : ℕ → R) (k n : ℕ) :
    (n : R) * hittingWeight p k n = k * walkWeight p k n := by
  set A := (Nat.antidiagonalTuple n (n - k)).filter (fun x => ∑ i, x i + k = n) with hA
  have hH : hittingWeight p k n =
      ∑ x ∈ A, if IsFirstPassage k n x then ∏ i, p (x i) else 0 := by
    rw [hittingWeight, hA, sum_filter, sum_filter]
    refine sum_congr rfl fun x _ => ?_
    by_cases h1 : ∑ i, x i + k = n <;> by_cases h2 : IsFirstPassage k n x <;> simp [h1, h2]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Nat.cast_zero, zero_mul]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [hH, sum_eq_zero fun x _ => ite_eq_right_iff.2 fun h => absurd h fun h => by
        have := h 0 (mem_range.2 hn); simp at this, mul_zero]
  · have key : ∀ x ∈ A, (k : R) * ∏ i, p (x i) =
        ∑ r ∈ range n, if IsFirstPassage k n (rotate x r) then ∏ i, p (x i) else 0 := by
      intro x hx
      rw [← sum_filter, sum_const, nsmul_eq_mul,
        card_filter_isFirstPassage_rotate hk x (mem_filter.1 hx).2]
    rw [walkWeight, ← hA, mul_sum, sum_congr rfl key, sum_comm, hH]
    rw [show ((n : R) * ∑ x ∈ A, if IsFirstPassage k n x then ∏ i, p (x i) else 0) =
        ∑ _r ∈ range n, ∑ x ∈ A, if IsFirstPassage k n x then ∏ i, p (x i) else 0 by
      rw [sum_const, card_range, nsmul_eq_mul]]
    refine sum_congr rfl fun r _ => ?_
    symm
    refine sum_equiv (rotTupleEquiv n r) (fun x => ?_) (fun x _ => ?_)
    · simp only [hA, mem_filter, Nat.mem_antidiagonalTuple, rotTupleEquiv, Equiv.coe_fn_mk,
        Function.comp_apply, Equiv.sum_comp (rotEquiv n r) x]
    · simp only [rotTupleEquiv, Equiv.coe_fn_mk, rotate_eq]
      congr 1
      exact (Equiv.prod_comp (rotEquiv n r) (fun i => p (x i))).symm


variable (ν : Measure ℕ) [IsFiniteMeasure ν]

/-- The measure of a finite set of tuples under `ν^{⊗n}`, written as a set `{x | P x}` that
coincides with `s.filter P`. -/
private theorem measure_pi_eq_sum_of_subset {n : ℕ} (s : Finset (Fin n → ℕ))
    {P : (Fin n → ℕ) → Prop} [DecidablePred P] (hP : ∀ x, P x → x ∈ s.filter P) :
    (Measure.pi fun _ : Fin n => ν) {x | P x} = ∑ x ∈ s.filter P, ∏ i, ν {x i} := by
  have : {x | P x} = ((s.filter P : Finset (Fin n → ℕ)) : Set (Fin n → ℕ)) := by
    ext x
    simp only [Set.mem_ofPred_eq, coe_filter]
    exact ⟨fun h => ⟨(mem_filter.1 (hP x h)).1, h⟩, fun h => h.2⟩
  rw [this, ← sum_measure_singleton]
  simp [Measure.pi_singleton]

/-- Under `ν^{⊗n}`, the event that the walk from `k` first hits `0` at time `n` has
measure `H_p(k, n)` with `p(j) = ν{j}`. When `ν` is a probability measure this is the
probability `P(T = n)`. -/
theorem measure_firstPassage (k n : ℕ) :
    (Measure.pi fun _ : Fin n => ν) {x | ∑ i, x i + k = n ∧ IsFirstPassage k n x} =
      hittingWeight (fun j => ν {j}) k n := by
  rw [hittingWeight, measure_pi_eq_sum_of_subset ν]
  intro x hx
  simp only [mem_filter, Nat.mem_antidiagonalTuple]
  exact ⟨by omega, hx⟩

/-- Under `ν^{⊗n}`, the event `ξ_1 + ⋯ + ξ_n + k = n` has measure `W_p(k, n)` with
`p(j) = ν{j}`. When `ν` is a probability measure this is the probability
`P(ξ_1 + ⋯ + ξ_n = n - k)`. -/
theorem measure_walk (k n : ℕ) :
    (Measure.pi fun _ : Fin n => ν) {x | ∑ i, x i + k = n} =
      walkWeight (fun j => ν {j}) k n := by
  rw [walkWeight, measure_pi_eq_sum_of_subset ν]
  intro x hx
  simp only [mem_filter, Nat.mem_antidiagonalTuple]
  exact ⟨by omega, hx⟩

/-- **Otter–Dwass formula.** For i.i.d. offspring numbers with law `ν` and `k` ancestors,
the finite-measure identity
`n · P(T = n) = k · P(ξ_1 + ⋯ + ξ_n = n - k)` holds as an identity of event masses
(Otter 1949; Dwass 1969); the two sides are probabilities when `ν` is a probability
measure. -/
theorem natCast_mul_measure_firstPassage (k n : ℕ) :
    (n : ℝ≥0∞) * (Measure.pi fun _ : Fin n => ν)
        {x | ∑ i, x i + k = n ∧ IsFirstPassage k n x} =
      k * (Measure.pi fun _ : Fin n => ν) {x | ∑ i, x i + k = n} := by
  rw [measure_firstPassage, measure_walk, natCast_mul_hittingWeight]

/-- Multinomial identity `∑_{x_1 + ⋯ + x_n = m} ∏ r^{x_i} / x_i! = (rn)^m / m!`. -/
private theorem sum_antidiagonalTuple_prod_pow_div (r : ℝ) (n m : ℕ) :
    ∑ x ∈ Nat.antidiagonalTuple n m, ∏ i, (r ^ x i / (x i)!) = (r * n) ^ m / m ! := by
  have hset : Nat.antidiagonalTuple n m = piAntidiag (univ : Finset (Fin n)) m := by
    ext x; simp [Nat.mem_antidiagonalTuple, mem_piAntidiag]
  have key := sum_pow_eq_sum_piAntidiag (univ : Finset (Fin n)) (fun _ => r) m
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at key
  rw [hset, eq_div_iff (by positivity), mul_comm r, key, sum_mul]
  refine sum_congr rfl fun k hk => ?_
  have hs : ∑ i, k i = m := (mem_piAntidiag.1 hk).1
  have hspec := Nat.multinomial_spec (univ : Finset (Fin n)) k
  rw [hs] at hspec
  have hpos : (0 : ℝ) < ∏ i, ((k i)! : ℝ) := prod_pos fun i _ => by positivity
  rw [prod_div_distrib, ← hspec]
  push_cast
  field_simp

/-- For Poisson(`r`) step weights, `W_p(k, n) = e^{-rn} (rn)^{n-k} / (n-k)!` when `k ≤ n`:
the sum of `n` independent Poisson(`r`) variables is Poisson(`rn`). -/
theorem walkWeight_poisson (r : ℝ≥0) {k n : ℕ} (hkn : k ≤ n) :
    walkWeight (fun j => (poissonMeasure r).real {j}) k n =
      Real.exp (-(r * n)) * (r * n) ^ (n - k) / (n - k)! := by
  rw [walkWeight, filter_true_of_mem fun x hx => by
    rw [Nat.mem_antidiagonalTuple] at hx; omega]
  simp_rw [poissonMeasure_real_singleton, mul_div_assoc, prod_mul_distrib, prod_const,
    card_univ, Fintype.card_fin, ← mul_sum, sum_antidiagonalTuple_prod_pow_div,
    ← Real.exp_nat_mul]
  ring_nf

/-- **Borel–Tanner law.** For Poisson(`r`) offspring and `k ≤ n` ancestors,
`n · P(T = n) = k e^{-rn} (rn)^{n-k} / (n-k)!` (Tanner 1961; Haight–Breuer 1960). -/
theorem natCast_mul_hittingWeight_poisson (r : ℝ≥0) {k n : ℕ} (hkn : k ≤ n) :
    (n : ℝ) * hittingWeight (fun j => (poissonMeasure r).real {j}) k n =
      k * (Real.exp (-(r * n)) * (r * n) ^ (n - k) / (n - k)!) := by
  rw [natCast_mul_hittingWeight, walkWeight_poisson r hkn]

/-- **Borel law.** For Poisson(`r`) offspring and one ancestor, the total progeny satisfies
`P(T = n) = e^{-rn} (rn)^{n-1} / n!` for `n ≥ 1` (Borel 1942). -/
theorem hittingWeight_poisson_one (r : ℝ≥0) {n : ℕ} (hn : 1 ≤ n) :
    hittingWeight (fun j => (poissonMeasure r).real {j}) 1 n =
      Real.exp (-(r * n)) * (r * n) ^ (n - 1) / n ! := by
  have h := natCast_mul_hittingWeight_poisson r hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hfac : (n ! : ℝ) = n * (n - 1)! := by
    exact_mod_cast (Nat.mul_factorial_pred (show n ≠ 0 by omega)).symm
  have hf : ((n - 1)! : ℝ) ≠ 0 := by positivity
  rw [hfac, eq_div_iff (mul_ne_zero hn0 hf)]
  rw [Nat.cast_one, one_mul, eq_div_iff hf] at h
  linear_combination h

/-- The mean total progeny `∑_n E Z_n` of the Galton–Watson process started from one individual.
By Tonelli this is `E ∑_n Z_n` for any process with the generation laws `law ν n`. -/
noncomputable def meanTotalProgeny : ℝ≥0∞ :=
  ∑' n, ∫⁻ z, (z : ℝ≥0∞) ∂(law ν n)

omit [IsFiniteMeasure ν] in
/-- The mean total progeny is `(1 - m)⁻¹` in `[0, ∞]`: it is `1 / (1 - m)` for `m < 1` and `∞`
for `m ≥ 1` (`m` the mean offspring number). -/
theorem meanTotalProgeny_eq [IsProbabilityMeasure ν] : meanTotalProgeny ν = (1 - mean ν)⁻¹ := by
  simp only [meanTotalProgeny, lintegral_law, ENNReal.tsum_geometric]

end MathlibExt.Probability.GaltonWatson
