/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Balanced signs on an infinite family of sequences (Erdős Problem 178)

Erdős Problem 178: let `A₁, A₂, …` be infinite sets of integers, `Aᵢ = {a_{i1} < a_{i2} < ⋯}`. Is
there `f : ℕ → {-1, 1}` with `max_{m, 1 ≤ i ≤ d} |∑_{j ≤ m} f(a_{ij})| ≪_d 1` for all `d ≥ 1`?

The answer is yes (Beck). The property is the proposition `boundedDiscrepancyInfiniteFamily`, and
`boundedDiscrepancyInfiniteFamily_holds` proves it.

Source: T. F. Bloom, Erdős Problems, Problem #178, https://www.erdosproblems.com/178 (status PROVED
(LEAN)). UnsolvedMath record UM-30006751 (`EP-178`), dataset ulamai/UnsolvedMath v1.8.0.

The sets are subsets of `ℕ` (the domain of `f`), given by strictly increasing enumerations `a i`;
indices start at `0`, so `1 ≤ i ≤ d` becomes `i < d`. `≪_d 1` is a bound `C` depending only on `d`,
uniform in `m`. Compared with the formal-conjectures statement `ErdosProblems/178.lean` (equivalent;
no code imported).

## Proof outline

The proof balances arbitrary integer weights `χ i n` with `|χ i n| ≤ 1`; for the theorem, `χ i` is
the indicator of the range of `a i`, and the sum of `f` over the first `m` terms of `a i` is the
prefix sum `∑ n < a i m, χ i n * f n`.

* Fix a horizon `M`. A level-`k` structure partitions `{0, …, M - 1}` into units, each with a
  relative sign pattern `g`, such that for every choice of orientations of the units, all prefix
  sums of the weights `χ 0, …, χ (k - 1)` are bounded by constants that depend neither on `k` nor
  on `M`. It also bounds, for every `N`, the number of points `n ≥ N` whose unit starts before `N`.
* Level `k + 1` is built from level `k` as follows. The charge of a unit is the sum of
  `χ k n * g n` over it. Among the units with a given nonzero charge, taken in the order of their
  least elements, consecutive ones are coupled and the second one is flipped, so that every couple
  has charge `0`. A prefix sum of `χ k` then only sees the units that cross the end of the prefix
  and, for each charge, at most one unit whose partner starts later or does not exist. This bounds
  it whatever the orientations of the new units are, and the bounds for `χ 0, …, χ (k - 1)` are
  inherited from level `k`.
* Level `M`, with every unit oriented by `+1`, gives signs for the horizon `M`. These sets of signs
  are closed and decreasing in `ℕ → ℤ`, and they lie in the compact set of `±1`-valued sequences,
  so their intersection is nonempty: it contains signs that work for every horizon.

The bound obtained here for the `i`-th sequence grows very quickly with `i`; the sharper bounds of
Beck are not pursued.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.BalancedSignsInfiniteFamilyErdosProblem178Wanted

/-- **Erdős Problem 178 (balancing infinite families of sequences).** The statement that for every
family $a_0, a_1, a_2, \ldots$ of strictly increasing sequences of natural numbers there is a
function $f : \mathbb{N} \to \mathbb{Z}$ taking only the values $1$ and $-1$ such that for every
$d \in \mathbb{N}$ there is a natural number $C$ with $\left|\sum_{j < m} f(a_i(j))\right| \le C$
for all $i < d$ and all $m \in \mathbb{N}$.

Here $a_i$ enumerates the infinite set $A_i = \{a_i(0) < a_i(1) < \cdots\} \subseteq \mathbb{N}$ in
increasing order, and the sum runs over the first $m$ elements of $A_i$. -/
def boundedDiscrepancyInfiniteFamily : Prop :=
  ∀ a : ℕ → ℕ → ℕ, (∀ i, StrictMono (a i)) →
    ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
      ∀ d : ℕ, ∃ C : ℕ, ∀ i < d, ∀ m : ℕ, |∑ j ∈ Finset.range m, f (a i j)| ≤ C

open Finset

/-! ### Coupling indices with equal charges -/

/-- The indices below `r` whose charge equals the charge of `r`. -/
private def same (q : ℕ → ℤ) (r : ℕ) : Finset ℕ := (range r).filter fun x => q x = q r

/-- `r` is the second member of a couple: its charge is nonzero and an odd number of earlier
indices have the same charge. -/
private def IsSecond (q : ℕ → ℤ) (r : ℕ) : Prop := q r ≠ 0 ∧ (same q r).card % 2 = 1

private instance instDecidablePredIsSecond (q : ℕ → ℤ) : DecidablePred (IsSecond q) := fun r => by
  unfold IsSecond; infer_instance

/-- The partner of a second member: the last earlier index with the same charge. -/
private def prev (q : ℕ → ℤ) (r : ℕ) : ℕ := (same q r).sup id

private lemma mem_same {q : ℕ → ℤ} {r x : ℕ} : x ∈ same q r ↔ x < r ∧ q x = q r := by
  simp [same]

private lemma prev_mem {q : ℕ → ℤ} {r : ℕ} (h : IsSecond q r) : prev q r ∈ same q r := by
  have hne : (same q r).Nonempty := by
    rw [← Finset.card_pos]
    have := h.2
    omega
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup _ hne id
  rw [prev, he]
  exact hi

private lemma le_prev {q : ℕ → ℤ} {r x : ℕ} (hx : x ∈ same q r) : x ≤ prev q r :=
  Finset.le_sup (f := id) hx

private lemma prev_lt {q : ℕ → ℤ} {r : ℕ} (h : IsSecond q r) : prev q r < r :=
  (mem_same.1 (prev_mem h)).1

private lemma charge_prev {q : ℕ → ℤ} {r : ℕ} (h : IsSecond q r) : q (prev q r) = q r :=
  (mem_same.1 (prev_mem h)).2

private lemma same_eq_insert {q : ℕ → ℤ} {p s : ℕ} (hps : p < s) (hq : q p = q s)
    (hgap : ∀ x, p < x → x < s → q x ≠ q s) : same q s = insert p (same q p) := by
  ext x
  simp only [mem_same, Finset.mem_insert]
  constructor
  · rintro ⟨hxs, hx⟩
    rcases lt_trichotomy x p with h | h | h
    · exact Or.inr ⟨h, hx.trans hq.symm⟩
    · exact Or.inl h
    · exact absurd hx (hgap x h hxs)
  · rintro (rfl | ⟨hxp, hx⟩)
    · exact ⟨hps, hq⟩
    · exact ⟨hxp.trans hps, hx.trans hq⟩

private lemma card_same_eq {q : ℕ → ℤ} {p s : ℕ} (hps : p < s) (hq : q p = q s)
    (hgap : ∀ x, p < x → x < s → q x ≠ q s) : (same q s).card = (same q p).card + 1 := by
  rw [same_eq_insert hps hq hgap, Finset.card_insert_of_notMem]
  simp [mem_same]

private lemma gap_prev (q : ℕ → ℤ) (r : ℕ) : ∀ x, prev q r < x → x < r → q x ≠ q r := by
  intro x h1 h2 h3
  exact absurd (le_prev (mem_same.2 ⟨h2, h3⟩)) (not_le.2 h1)

/-- The partner of a second member is not a second member. -/
private lemma not_isSecond_prev {q : ℕ → ℤ} {r : ℕ} (h : IsSecond q r) :
    ¬ IsSecond q (prev q r) := by
  intro h'
  have := card_same_eq (prev_lt h) (charge_prev h) (gap_prev q r)
  have h1 := h.2
  have h2 := h'.2
  omega

/-- Two second members with the same partner are equal. -/
private lemma eq_of_prev_eq {q : ℕ → ℤ} {s₁ s₂ : ℕ} (h₁ : IsSecond q s₁) (h₂ : IsSecond q s₂)
    (he : prev q s₁ = prev q s₂) : s₁ = s₂ := by
  have key : ∀ {a b : ℕ}, IsSecond q a → IsSecond q b → prev q a = prev q b → ¬ a < b := by
    intro a b ha hb hab hlt
    have hq : q a = q b := by rw [← charge_prev ha, hab, charge_prev hb]
    have h1 := le_prev (mem_same.2 ⟨hlt, hq⟩)
    have h2 := prev_lt ha
    omega
  rcases lt_trichotomy s₁ s₂ with hlt | heq | hgt
  · exact absurd hlt (key h₁ h₂ he)
  · exact heq
  · exact absurd hgt (key h₂ h₁ he.symm)

/-- An index with nonzero charge that is not a second member is the partner of the next index
with the same charge. -/
private lemma exists_isSecond_prev_eq {q : ℕ → ℤ} {p₁ p₂ : ℕ} (hlt : p₁ < p₂) (hq : q p₁ = q p₂)
    (h0 : q p₁ ≠ 0) (hns : ¬ IsSecond q p₁) : ∃ s ≤ p₂, IsSecond q s ∧ prev q s = p₁ := by
  set S := (Finset.Ioc p₁ p₂).filter fun x => q x = q p₁
  have hne : S.Nonempty := ⟨p₂, by simp [S, hlt, hq]⟩
  set s := S.min' hne
  have hsS : s ∈ S := S.min'_mem hne
  simp only [S, Finset.mem_filter, Finset.mem_Ioc] at hsS
  obtain ⟨⟨hs1, hs2⟩, hqs⟩ := hsS
  have hgap : ∀ x, p₁ < x → x < s → q x ≠ q s := by
    intro x h1 h2 h3
    have hx : x ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨h1, by omega⟩, h3.trans hqs⟩
    exact absurd (S.min'_le x hx) (not_le.2 h2)
  have hcard := card_same_eq hs1 hqs.symm hgap
  have hsec : IsSecond q s := by
    refine ⟨by rw [hqs]; exact h0, ?_⟩
    have : ¬ (same q p₁).card % 2 = 1 := fun h => hns ⟨h0, h⟩
    omega
  refine ⟨s, hs2, hsec, le_antisymm ?_ ?_⟩
  · have hm := prev_mem hsec
    rw [same_eq_insert hs1 hqs.symm hgap, Finset.mem_insert] at hm
    rcases hm with hm | hm
    · exact hm.le
    · exact (mem_same.1 hm).1.le
  · exact le_prev (by rw [same_eq_insert hs1 hqs.symm hgap]; exact Finset.mem_insert_self _ _)

/-- The representative of the couple containing `r`. -/
private def rho (q : ℕ → ℤ) (r : ℕ) : ℕ := if IsSecond q r then prev q r else r

/-- The relative sign of `r` in its couple: second members are flipped. -/
private def eps (q : ℕ → ℤ) (r : ℕ) : ℤ := if IsSecond q r then -1 else 1

private lemma rho_le (q : ℕ → ℤ) (r : ℕ) : rho q r ≤ r := by
  unfold rho
  split_ifs with h
  · exact (prev_lt h).le
  · exact le_rfl

private lemma eps_sign (q : ℕ → ℤ) (r : ℕ) : eps q r = 1 ∨ eps q r = -1 := by
  unfold eps
  split_ifs <;> simp

private lemma rho_eq_iff {q : ℕ → ℤ} {r p : ℕ} :
    rho q r = p ↔ (¬ IsSecond q r ∧ r = p) ∨ (IsSecond q r ∧ prev q r = p) := by
  unfold rho
  split_ifs with h <;> simp [h]

/-! ### Levels -/

/-- The bound on the tail of the units at level `k`. -/
private def bound : ℕ → ℕ
  | 0 => 0
  | k + 1 => bound k + (2 * bound k + 3) * (bound k + 1)

private lemma bound_mono : Monotone bound :=
  monotone_nat_of_le_succ fun k => by simp only [bound]; omega

/-- A level-`k` partition of `range M` into units, given by the least element `rep n` of the unit
of `n`, with relative signs `g`: whatever the orientations `σ` of the units, the prefix sums of
the first `k` weights are bounded. -/
private structure Good (χ : ℕ → ℕ → ℤ) (M k : ℕ) (rep : ℕ → ℕ) (g : ℕ → ℤ) : Prop where
  sign : ∀ n, g n = 1 ∨ g n = -1
  rep_le : ∀ n < M, rep n ≤ n
  rep_rep : ∀ n < M, rep (rep n) = rep n
  tail : ∀ N, ((range M).filter fun n => N ≤ n ∧ rep n < N).card ≤ bound k
  disc : ∀ σ : ℕ → ℤ, (∀ r, σ r = 1 ∨ σ r = -1) → ∀ i < k, ∀ N ≤ M,
    |∑ n ∈ range N, χ i n * (σ (rep n) * g n)| ≤ bound (i + 1)

private lemma Good.zero (χ : ℕ → ℕ → ℤ) (M : ℕ) : Good χ M 0 id fun _ => 1 where
  sign _ := Or.inl rfl
  rep_le _ _ := le_rfl
  rep_rep _ _ := rfl
  tail N := by simp [bound]
  disc _ _ i hi := absurd hi (Nat.not_lt_zero i)

private lemma Good.card_unit {χ : ℕ → ℕ → ℤ} {M k : ℕ} {rep : ℕ → ℕ} {g : ℕ → ℤ}
    (h : Good χ M k rep g) (r : ℕ) :
    ((range M).filter fun n => rep n = r).card ≤ bound k + 1 := by
  calc ((range M).filter fun n => rep n = r).card
      ≤ (insert r ((range M).filter fun n => r + 1 ≤ n ∧ rep n < r + 1)).card := by
        apply Finset.card_le_card
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert] at hn ⊢
        have := h.rep_le n hn.1
        rcases eq_or_ne n r with hnr | hnr
        · exact Or.inl hnr
        · exact Or.inr ⟨hn.1, by omega, by omega⟩
    _ ≤ _ := (Finset.card_insert_le _ _).trans (by have := h.tail (r + 1); omega)

/-- The charge of the unit with least element `r`. -/
private def charge (χ : ℕ → ℕ → ℤ) (M k : ℕ) (rep : ℕ → ℕ) (g : ℕ → ℤ) (r : ℕ) : ℤ :=
  ∑ n ∈ (range M).filter (fun n => rep n = r), χ k n * g n

private lemma abs_mul_le_one {a b : ℤ} (ha : |a| ≤ 1) (hb : b = 1 ∨ b = -1) : |a * b| ≤ 1 := by
  rcases hb with rfl | rfl <;> simpa using ha

private lemma Good.abs_charge_le {χ : ℕ → ℕ → ℤ} {M k : ℕ} {rep : ℕ → ℕ} {g : ℕ → ℤ}
    (h : Good χ M k rep g) (hχ : ∀ i n, |χ i n| ≤ 1) (r : ℕ) :
    |charge χ M k rep g r| ≤ bound k + 1 := by
  calc |charge χ M k rep g r| ≤ ∑ n ∈ (range M).filter (fun n => rep n = r), |χ k n * g n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ (range M).filter (fun n => rep n = r), (1 : ℤ) :=
        Finset.sum_le_sum fun n _ => abs_mul_le_one (hχ k n) (h.sign n)
    _ ≤ bound k + 1 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast h.card_unit r

private lemma Good.rep_eq_of_charge_ne_zero {χ : ℕ → ℕ → ℤ} {M k : ℕ} {rep : ℕ → ℕ}
    {g : ℕ → ℤ} (h : Good χ M k rep g) {r : ℕ} (hr : charge χ M k rep g r ≠ 0) : rep r = r := by
  obtain ⟨n, hn, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  rw [← hn.2, h.rep_rep n hn.1]

section Step

variable {χ : ℕ → ℕ → ℤ} {M k : ℕ} {rep : ℕ → ℕ} {g : ℕ → ℤ}

private lemma charge_eq_add (N : ℕ) (hN : N ≤ M) (r : ℕ) :
    charge χ M k rep g r = ∑ n ∈ (range N).filter (fun n => rep n = r), χ k n * g n
      + ∑ n ∈ (Ico N M).filter (fun n => rep n = r), χ k n * g n := by
  unfold charge
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_range_add_sum_Ico _ hN]

private lemma abs_sign_mul (a b c : ℤ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    |a * b * c| = |c| := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

private lemma Good.disc_new (h : Good χ M k rep g) (hχ : ∀ i n, |χ i n| ≤ 1)
    (σ : ℕ → ℤ) (hσ : ∀ r, σ r = 1 ∨ σ r = -1) (N : ℕ) (hN : N ≤ M) :
    |∑ n ∈ range N, χ k n * (σ (rho (charge χ M k rep g) (rep n)) *
      (eps (charge χ M k rep g) (rep n) * g n))| ≤ bound (k + 1) := by
  set q := charge χ M k rep g with hq
  have hqb : ∀ r, |q r| ≤ bound k + 1 := h.abs_charge_le hχ
  set P : ℕ → ℤ := fun r => ∑ n ∈ (range N).filter (fun n => rep n = r), χ k n * g n with hP
  set T : ℕ → ℤ := fun r => ∑ n ∈ (Ico N M).filter (fun n => rep n = r), χ k n * g n
  have hPT : ∀ r, P r = q r - T r := fun r => by
    rw [hq, charge_eq_add N hN r]
    ring
  -- group the sum by the units of level `k`
  have h1 : ∑ n ∈ range N, χ k n * (σ (rho q (rep n)) * (eps q (rep n) * g n)) =
      ∑ r ∈ range N, σ (rho q r) * eps q r * P r := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := range N) (t := range N) (g := rep)]
    · refine Finset.sum_congr rfl fun r _ => ?_
      simp only [hP]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [(Finset.mem_filter.1 hn).2]
      ring
    · intro n hn
      simp only [Finset.mem_range] at hn ⊢
      exact (h.rep_le n (by omega)).trans_lt hn
  have h2 : ∑ r ∈ range N, σ (rho q r) * eps q r * P r =
      ∑ r ∈ range N, σ (rho q r) * eps q r * q r -
        ∑ r ∈ range N, σ (rho q r) * eps q r * T r := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hPT]
    ring
  -- the units of level `k` that start below `N` and end after `N`
  have h3 : |∑ r ∈ range N, σ (rho q r) * eps q r * T r| ≤ bound k := by
    have hT1 : ∀ r, |T r| ≤ ((Ico N M).filter (fun n => rep n = r)).card := by
      intro r
      calc |T r| ≤ ∑ n ∈ (Ico N M).filter (fun n => rep n = r), |χ k n * g n| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ (Ico N M).filter (fun n => rep n = r), (1 : ℤ) :=
            Finset.sum_le_sum fun n _ => abs_mul_le_one (hχ k n) (h.sign n)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : ∑ r ∈ range N, ((Ico N M).filter (fun n => rep n = r)).card ≤ bound k := by
      have : ∑ r ∈ range N, ((Ico N M).filter (fun n => rep n = r)).card =
          ((Ico N M).filter (fun n => rep n < N)).card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := rep) (t := range N)]
        · refine Finset.sum_congr rfl fun r hr => ?_
          rw [Finset.filter_filter]
          simp only [Finset.mem_range] at hr
          refine congrArg Finset.card (Finset.filter_congr fun n _ => ?_)
          constructor
          · intro hn
            exact ⟨hn ▸ hr, hn⟩
          · exact fun h => h.2
        · intro n hn
          simp only [Finset.coe_filter, Finset.coe_range, Set.mem_Iio] at hn ⊢
          exact hn.2
      rw [this]
      refine le_trans (Finset.card_le_card ?_) (h.tail N)
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at hn ⊢
      exact ⟨hn.1.2, hn.1.1, hn.2⟩
    calc _ ≤ ∑ r ∈ range N, |σ (rho q r) * eps q r * T r| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ r ∈ range N, |T r| :=
          Finset.sum_congr rfl fun r _ => abs_sign_mul _ _ _ (hσ _) (eps_sign q r)
      _ ≤ ∑ r ∈ range N, (((Ico N M).filter (fun n => rep n = r)).card : ℤ) :=
          Finset.sum_le_sum fun r _ => hT1 r
      _ ≤ bound k := by exact_mod_cast hcard
  -- the couples cancel, except at most one unit for each charge
  have h4 : |∑ r ∈ range N, σ (rho q r) * eps q r * q r| ≤
      (2 * bound k + 3) * (bound k + 1) := by
    set I : ℕ → ℤ := fun p => ∑ r ∈ (range N).filter (fun r => rho q r = p), eps q r * q r
      with hI
    have hgroup : ∑ r ∈ range N, σ (rho q r) * eps q r * q r = ∑ p ∈ range N, σ p * I p := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := range N) (t := range N) (g := rho q)]
      · refine Finset.sum_congr rfl fun p _ => ?_
        simp only [hI]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [(Finset.mem_filter.1 hr).2]
        ring
      · intro r hr
        simp only [Finset.mem_range] at hr ⊢
        exact (rho_le q r).trans_lt hr
    let Bad : ℕ → Prop := fun p => q p ≠ 0 ∧ ¬ IsSecond q p ∧ ∀ s < N, IsSecond q s → prev q s ≠ p
    have hIp : ∀ p ∈ range N, |I p| ≤ if Bad p then (bound k + 1 : ℤ) else 0 := by
      intro p hp
      have hpN : p < N := Finset.mem_range.1 hp
      have hnn : (0 : ℤ) ≤ if Bad p then (bound k + 1 : ℤ) else 0 := by
        split_ifs <;> positivity
      by_cases hps : IsSecond q p
      · have : I p = 0 := by
          simp only [hI]
          apply Finset.sum_eq_zero
          intro r hr
          simp only [Finset.mem_filter] at hr
          exfalso
          rcases rho_eq_iff.1 hr.2 with ⟨hr1, rfl⟩ | ⟨hr1, hr2⟩
          · exact hr1 hps
          · exact not_isSecond_prev hr1 (hr2 ▸ hps)
        rw [this, abs_zero]
        exact hnn
      · by_cases hex : ∃ s < N, IsSecond q s ∧ prev q s = p
        · obtain ⟨s, hsN, hss, hsp⟩ := hex
          have hne : p ≠ s := fun h => hps (h ▸ hss)
          have hfib : (range N).filter (fun r => rho q r = p) = {p, s} := by
            ext r
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
              Finset.mem_singleton]
            constructor
            · rintro ⟨_, hrp⟩
              rcases rho_eq_iff.1 hrp with ⟨_, rfl⟩ | ⟨hr1, hr2⟩
              · exact Or.inl rfl
              · exact Or.inr (eq_of_prev_eq hr1 hss (hr2.trans hsp.symm))
            · rintro (rfl | rfl)
              · exact ⟨hpN, rho_eq_iff.2 (Or.inl ⟨hps, rfl⟩)⟩
              · exact ⟨hsN, rho_eq_iff.2 (Or.inr ⟨hss, hsp⟩)⟩
          have : I p = 0 := by
            simp only [hI]
            rw [hfib, Finset.sum_pair hne]
            simp only [eps, ite_eq_right hps, ite_eq_left hss]
            rw [← hsp, charge_prev hss]
            ring
          rw [this, abs_zero]
          exact hnn
        · push Not at hex
          have hfib : (range N).filter (fun r => rho q r = p) = {p} := by
            ext r
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
            constructor
            · rintro ⟨hr, hrp⟩
              rcases rho_eq_iff.1 hrp with ⟨_, h⟩ | ⟨hr1, hr2⟩
              · exact h
              · exact absurd hr2 (hex r hr hr1)
            · rintro rfl
              exact ⟨hpN, rho_eq_iff.2 (Or.inl ⟨hps, rfl⟩)⟩
          have hIq : I p = q p := by
            simp only [hI]
            rw [hfib, Finset.sum_singleton]
            simp [eps, hps]
          by_cases hq0 : q p = 0
          · rw [hIq, show |q p| = 0 by rw [hq0, abs_zero]]
            exact hnn
          · rw [ite_eq_left ⟨hq0, hps, hex⟩, hIq]
            exact hqb p
    have hBadcard : ((range N).filter Bad).card ≤ 2 * bound k + 3 := by
      have hmaps : Set.MapsTo q ((range N).filter Bad : Set ℕ)
          (Finset.Icc (-(bound k + 1 : ℤ)) (bound k + 1) : Set ℤ) := by
        intro p _
        simp only [Finset.coe_Icc, Set.mem_Icc]
        exact abs_le.1 (hqb p)
      have key : ∀ {p₁ p₂}, p₁ ∈ (range N).filter Bad → p₂ ∈ (range N).filter Bad →
          q p₁ = q p₂ → ¬ p₁ < p₂ := by
        intro p₁ p₂ h₁ h₂ he hlt
        simp only [Finset.mem_filter, Finset.mem_range] at h₁ h₂
        obtain ⟨s, hs, hss, hsp⟩ := exists_isSecond_prev_eq hlt he h₁.2.1 h₁.2.2.1
        exact h₁.2.2.2 s (by omega) hss hsp
      have hinj : Set.InjOn q ((range N).filter Bad : Set ℕ) := by
        intro p₁ h₁ p₂ h₂ he
        rw [Finset.mem_coe] at h₁ h₂
        rcases lt_trichotomy p₁ p₂ with hlt | heq | hgt
        · exact absurd hlt (key h₁ h₂ he)
        · exact heq
        · exact absurd hgt (key h₂ h₁ he.symm)
      calc _ ≤ (Finset.Icc (-(bound k + 1 : ℤ)) (bound k + 1)).card :=
            Finset.card_le_card_of_injOn q hmaps hinj
        _ = 2 * bound k + 3 := by rw [Int.card_Icc]; omega
    rw [hgroup]
    calc _ ≤ ∑ p ∈ range N, |σ p * I p| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ p ∈ range N, |I p| := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [abs_mul]
          rcases hσ p with h | h <;> simp [h]
      _ ≤ ∑ p ∈ range N, if Bad p then (bound k + 1 : ℤ) else 0 := Finset.sum_le_sum hIp
      _ = ((range N).filter Bad).card * (bound k + 1 : ℤ) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * bound k + 3 : ℕ) * (bound k + 1 : ℤ) := by
          gcongr
      _ = _ := by push_cast; ring
  rw [h1, h2]
  calc _ ≤ |∑ r ∈ range N, σ (rho q r) * eps q r * q r| +
        |∑ r ∈ range N, σ (rho q r) * eps q r * T r| := abs_sub _ _
    _ ≤ (2 * bound k + 3) * (bound k + 1) + bound k := add_le_add h4 h3
    _ = bound (k + 1) := by simp only [bound]; push_cast; ring

private lemma Good.step (h : Good χ M k rep g) (hχ : ∀ i n, |χ i n| ≤ 1) :
    Good χ M (k + 1) (fun n => rho (charge χ M k rep g) (rep n))
      (fun n => eps (charge χ M k rep g) (rep n) * g n) := by
  set q := charge χ M k rep g with hq
  have hqb : ∀ r, |q r| ≤ bound k + 1 := h.abs_charge_le hχ
  refine ⟨fun n => ?_, fun n hn => ?_, fun n hn => ?_, fun N => ?_, ?_⟩
  · rcases eps_sign q (rep n) with he | he <;> rcases h.sign n with hg | hg <;> simp [he, hg]
  · exact (rho_le q _).trans (h.rep_le n hn)
  · have hr := h.rep_rep n hn
    by_cases hs : IsSecond q (rep n)
    · have hp : rep (prev q (rep n)) = prev q (rep n) := by
        apply h.rep_eq_of_charge_ne_zero
        rw [← hq, charge_prev hs]
        exact hs.1
      simp only [rho, ite_eq_left hs, hp, ite_eq_right (not_isSecond_prev hs)]
    · simp only [rho, ite_eq_right hs, hr]
  · have hsub : ((range M).filter fun n => N ≤ n ∧ rho q (rep n) < N) ⊆
        ((range M).filter fun n => N ≤ n ∧ rep n < N) ∪
          ((range M).filter fun n => N ≤ rep n ∧ rho q (rep n) < N) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range] at hn ⊢
      by_cases h1 : rep n < N
      · exact Or.inl ⟨hn.1, hn.2.1, h1⟩
      · exact Or.inr ⟨hn.1, not_lt.1 h1, hn.2.2⟩
    set F := (range M).filter fun n => N ≤ rep n ∧ rho q (rep n) < N
    have key : ∀ s ∈ F.image rep, IsSecond q s ∧ prev q s < N ∧ N ≤ s := by
      intro s hs
      simp only [F, Finset.mem_image, Finset.mem_filter] at hs
      obtain ⟨n, ⟨_, h1, h2⟩, rfl⟩ := hs
      have hsec : IsSecond q (rep n) := by
        by_contra hns
        rw [show rho q (rep n) = rep n from ite_eq_right hns] at h2
        omega
      rw [show rho q (rep n) = prev q (rep n) from ite_eq_left hsec] at h2
      exact ⟨hsec, h2, h1⟩
    have himage : (F.image rep).card ≤ 2 * bound k + 3 := by
      have hmaps : Set.MapsTo q (F.image rep : Set ℕ)
          (Finset.Icc (-(bound k + 1 : ℤ)) (bound k + 1) : Set ℤ) := by
        intro s _
        simp only [Finset.coe_Icc, Set.mem_Icc]
        exact abs_le.1 (hqb s)
      have hinj : Set.InjOn q (F.image rep : Set ℕ) := by
        intro s₁ hs₁ s₂ hs₂ he
        rw [Finset.mem_coe] at hs₁ hs₂
        obtain ⟨-, h1p, h1N⟩ := key s₁ hs₁
        obtain ⟨-, h2p, h2N⟩ := key s₂ hs₂
        rcases lt_trichotomy s₁ s₂ with hlt | heq | hgt
        · have := le_prev (mem_same.2 ⟨hlt, he⟩)
          omega
        · exact heq
        · have := le_prev (mem_same.2 ⟨hgt, he.symm⟩)
          omega
      calc (F.image rep).card ≤ (Finset.Icc (-(bound k + 1 : ℤ)) (bound k + 1)).card :=
            Finset.card_le_card_of_injOn q hmaps hinj
        _ = 2 * bound k + 3 := by rw [Int.card_Icc]; omega
    have hFcard : F.card ≤ (bound k + 1) * (2 * bound k + 3) := by
      refine (Finset.card_le_mul_card_image F (bound k + 1) ?_).trans
        (Nat.mul_le_mul_left _ himage)
      intro s _
      refine (Finset.card_le_card ?_).trans (h.card_unit s)
      intro n hn
      simp only [F, Finset.mem_filter] at hn ⊢
      exact ⟨hn.1.1, hn.2⟩
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ bound k + (bound k + 1) * (2 * bound k + 3) := Nat.add_le_add (h.tail N) hFcard
      _ = bound (k + 1) := by simp only [bound]; ring
  · intro σ hσ i hi N hN
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · have hσ' : ∀ r, σ (rho q r) * eps q r = 1 ∨ σ (rho q r) * eps q r = -1 := by
        intro r
        rcases hσ (rho q r) with h1 | h1 <;> rcases eps_sign q r with h2 | h2 <;> simp [h1, h2]
      have := h.disc (fun r => σ (rho q r) * eps q r) hσ' i hi N hN
      convert this using 3 with n
      ring
    · exact h.disc_new hχ σ hσ N hN

end Step

private lemma exists_good (χ : ℕ → ℕ → ℤ) (hχ : ∀ i n, |χ i n| ≤ 1) (M : ℕ) :
    ∀ k, ∃ rep g, Good χ M k rep g
  | 0 => ⟨_, _, Good.zero χ M⟩
  | k + 1 => by
    obtain ⟨rep, g, h⟩ := exists_good χ hχ M k
    exact ⟨_, _, h.step hχ⟩

/-- Signs balancing the first `M` weight sequences on the first `M` prefixes. -/
private lemma exists_signs_fin (χ : ℕ → ℕ → ℤ) (hχ : ∀ i n, |χ i n| ≤ 1) (M : ℕ) :
    ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
      ∀ i < M, ∀ N ≤ M, |∑ n ∈ range N, χ i n * f n| ≤ bound (i + 1) := by
  obtain ⟨rep, g, h⟩ := exists_good χ hχ M M
  refine ⟨g, h.sign, fun i hi N hN => ?_⟩
  simpa using h.disc (fun _ => 1) (fun _ => Or.inl rfl) i hi N hN

/-- Signs balancing every weight sequence on every prefix, by compactness. -/
private lemma exists_signs (χ : ℕ → ℕ → ℤ) (hχ : ∀ i n, |χ i n| ≤ 1) :
    ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
      ∀ i N, |∑ n ∈ range N, χ i n * f n| ≤ bound (i + 1) := by
  set S : Set (ℕ → ℤ) := {f | ∀ n, f n = 1 ∨ f n = -1} with hS
  let K : ℕ → Set (ℕ → ℤ) := fun M => S ∩
    {f | ∀ i < M, ∀ N ≤ M, |∑ n ∈ range N, χ i n * f n| ≤ bound (i + 1)}
  have hSeq : S = Set.pi Set.univ fun _ => ({1, -1} : Set ℤ) := by
    ext f
    simp [hS, Set.mem_pi]
  have hScompact : IsCompact S := by
    rw [hSeq]
    exact isCompact_univ_pi fun _ => (Set.toFinite _).isCompact
  have hSclosed : IsClosed S := by
    rw [hSeq]
    exact isClosed_set_pi fun _ _ => isClosed_discrete _
  have hclosed : ∀ M, IsClosed (K M) := by
    intro M
    refine hSclosed.inter ?_
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_iInter fun N =>
      isClosed_iInter fun _ => ?_
    exact (isClosed_discrete {z : ℤ | |z| ≤ bound (i + 1)}).preimage
      (continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_apply n))
  obtain ⟨f, hf⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K
    (fun M f hf => ⟨hf.1, fun i hi N hN => hf.2 i (by omega) N (by omega)⟩)
    (fun M => by
      obtain ⟨f, hf⟩ := exists_signs_fin χ hχ M
      exact ⟨f, hf⟩)
    (hScompact.of_isClosed_subset (hclosed 0) Set.inter_subset_left) hclosed
  simp only [Set.mem_iInter] at hf
  exact ⟨f, (hf 0).1, fun i N => (hf (i + N + 1)).2 i (by omega) N (by omega)⟩

/-- The sum over the first `m` terms of a strictly increasing sequence is a prefix sum of the
indicator weights of its range. -/
private lemma sum_range_comp_eq {a : ℕ → ℕ} (ha : StrictMono a) (f : ℕ → ℤ) (m : ℕ) :
    ∑ j ∈ range m, f (a j) =
      ∑ n ∈ range (a m), (Set.range a).indicator (fun _ => (1 : ℤ)) n * f n := by
  induction m with
  | zero =>
    rw [Finset.sum_range_zero, eq_comm]
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Finset.mem_range] at hn
    have : n ∉ Set.range a := by
      rintro ⟨j, rfl⟩
      exact absurd hn (not_lt.2 (ha.monotone (Nat.zero_le j)))
    simp [this]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, ← Finset.sum_range_add_sum_Ico _ (ha.monotone m.le_succ)]
    congr 1
    rw [Finset.sum_eq_single_of_mem (a m) (by simp [ha m.lt_succ_self])]
    · simp
    · intro n hn hne
      have : n ∉ Set.range a := by
        rintro ⟨j, rfl⟩
        simp only [Finset.mem_Ico] at hn
        have h1 := ha.lt_iff_lt.1 (lt_of_le_of_ne hn.1 (Ne.symm hne))
        have h2 := ha.lt_iff_lt.1 hn.2
        omega
      simp [this]

/--
**Beck's theorem on balancing infinite families of sequences (Erdős Problem 178).** For every
family $a_0, a_1, a_2, \ldots$ of strictly increasing sequences of natural numbers there is a
function $f : \mathbb{N} \to \mathbb{Z}$ taking only the values $1$ and $-1$ such that for every
$d \in \mathbb{N}$ there is a natural number $C$ with $\left|\sum_{j < m} f(a_i(j))\right| \le C$
for all $i < d$ and all $m \in \mathbb{N}$.

Beck proved this; he later showed that the bound $C$ can be taken $\ll d^{4 + \varepsilon}$.

Source: T. F. Bloom, Erdős
Problems, Problem #178, https://www.erdosproblems.com/178 (status PROVED (LEAN)); resolution: J.
Beck, Balancing families of integer sequences, Combinatorica 1 (1981), 209-216,
erdosproblems.com/178: solved by Beck [Be81]; Beck (2017) improved the bound to d^{4+ε},
https://doi.org/10.1007/BF02579326.
-/
theorem boundedDiscrepancyInfiniteFamily_holds : boundedDiscrepancyInfiniteFamily := by
  intro a ha
  obtain ⟨f, hf, hb⟩ := exists_signs (fun i => (Set.range (a i)).indicator fun _ => 1)
    (fun i n => by
      by_cases hn : n ∈ Set.range (a i) <;> simp [hn])
  refine ⟨f, hf, fun d => ⟨bound d, fun i hi m => ?_⟩⟩
  rw [sum_range_comp_eq (ha i)]
  exact (hb i (a i m)).trans (by exact_mod_cast bound_mono (by omega : i + 1 ≤ d))

end MathlibExt.Combinatorics.BalancedSignsInfiniteFamilyErdosProblem178Wanted
