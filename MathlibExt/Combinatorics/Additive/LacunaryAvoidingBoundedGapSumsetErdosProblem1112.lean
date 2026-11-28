/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Find

/-!
# Bounded-gap triple sums and lacunary sequences (Erdős Problem 1112)

Bollobás, Hegyvári and Jin disproved the existence of a lacunarity threshold
for gaps in `[2, 3]` and triple sums. See *On a problem of Erdős and Graham*,
Discrete Math. 175 (1997), 253–257, Theorem 3,
https://doi.org/10.1016/S0012-365X(96)00122-7, and
https://www.erdosproblems.com/1112 for the problem and its context.

The proof below uses two facts. First, every triple sumset in question
contains an infinite arithmetic progression. If the double sumset contains
three consecutive integers then the triple sumset contains a whole tail.
Otherwise, any two runs of 3-gaps between successive 2-gaps have equal
length: runs of unequal lengths would give three consecutive double sums.
This gives a progression in the original sequence, unless it already has a
tail of 3-gaps. Second, one can prescribe arbitrarily large successive
ratios while making the lacunary sequence meet every infinite arithmetic
progression (use multiples of `i!` plus `i`).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.LacunaryAvoidingBoundedGapSumsetErdosProblem1112Wanted

open scoped Pointwise

/-- **Lacunary threshold for bounded-gap sumsets.** For natural numbers $d_1$, $d_2$ and $k$,
the threshold $r_k(d_1, d_2)$ of Erdős Problem 1112 exists when there is a natural number $r$
such that for every strictly increasing sequence $b_0 < b_1 < \cdots$ of positive integers with
$b_{i+1} \ge r b_i$ for all $i$, there is a sequence $a_0, a_1, \dots$ of positive integers with
$a_i + d_1 \le a_{i+1} \le a_i + d_2$ for all $i$ such that no $b_i$ lies in the $k$-fold sumset
of $A = \{a_0, a_1, \dots\}$, the set of all sums of $k$ elements of $A$ with repetition allowed
(for $k = 0$ this set is $\{0\}$). -/
def HasLacunaryThreshold (d₁ d₂ k : ℕ) : Prop :=
  ∃ r : ℕ, ∀ b : ℕ → ℕ, 0 < b 0 → StrictMono b → (∀ i, r * b i ≤ b (i + 1)) →
    ∃ a : ℕ → ℕ, 0 < a 0 ∧ (∀ i, a i + d₁ ≤ a (i + 1) ∧ a (i + 1) ≤ a i + d₂) ∧
      Disjoint (k • Set.range a) (Set.range b)

/-- **Statement of Erdős Problem 1112 for gaps in $[2, 3]$ and triple sums.** The threshold
$r_3(2, 3)$ exists: there is a natural number $r$ such that for every strictly increasing
sequence $b_0 < b_1 < \cdots$ of positive integers with $b_{i+1} \ge r b_i$ for all $i$, there is
a sequence $a_0, a_1, \dots$ of positive integers with $a_i + 2 \le a_{i+1} \le a_i + 3$ for all
$i$ such that no $b_i$ is a sum $x + y + z$ of three, not necessarily distinct, terms $x, y, z$
of the sequence $a$. -/
def lacunaryThresholdGapsTwoThreeThreeFold : Prop :=
  HasLacunaryThreshold 2 3 3

private theorem step_three_eq {a : ℕ → ℕ} {i : ℕ} (n : ℕ)
    (h : ∀ j, i ≤ j → j < i + n → a (j + 1) = a j + 3) :
    a (i + n) = a i + 3 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := h (i + n) (by omega) (by omega)
    have he := ih (fun j hj hj' ↦ h j hj (by omega))
    rw [← Nat.add_assoc]
    omega

private theorem exists_term_close_below {a : ℕ → ℕ}
    (ha : ∀ i, a i + 2 ≤ a (i + 1) ∧ a (i + 1) ≤ a i + 3)
    {t : ℕ} (ht : a 0 ≤ t) : ∃ i, a i ≤ t ∧ t ≤ a i + 2 := by
  have unbounded (i : ℕ) : i ≤ a i := by
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih => have := (ha i).1; omega
  have hex : ∃ j, t < a j := ⟨t + 1, by have := unbounded (t + 1); omega⟩
  have hfirst := Nat.find_spec hex
  obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by rintro hz; rw [hz] at hfirst; omega)
  have hprev := Nat.find_min hex (show i < Nat.find hex by omega)
  have hgap := (ha i).2
  rw [hi] at hfirst
  exact ⟨i, by omega, by omega⟩

private theorem exists_progression_in_threeFold (a : ℕ → ℕ)
    (ha : ∀ i, a i + 2 ≤ a (i + 1) ∧ a (i + 1) ≤ a i + 3) :
    ∃ m c : ℕ, 0 < m ∧ ∀ n : ℕ, c + m * n ∈ (3 : ℕ) • Set.range a := by
  have hthree : (3 : ℕ) • Set.range a =
      Set.range a + Set.range a + Set.range a := by
    rw [show (3 : ℕ) = 2 + 1 by decide, add_nsmul, two_nsmul, one_nsmul]
  have hsum (i j : ℕ) : a i + a j ∈ Set.range a + Set.range a :=
    Set.add_mem_add (Set.mem_range_self i) (Set.mem_range_self j)
  have of_progression (m c : ℕ) (hm : 0 < m)
      (h : ∀ n, c + m * n ∈ Set.range a) :
      ∃ m c : ℕ, 0 < m ∧ ∀ n : ℕ, c + m * n ∈ (3 : ℕ) • Set.range a := by
    have hc : c ∈ Set.range a := by simpa using h 0
    refine ⟨m, 3 * c, hm, fun n ↦ ?_⟩
    rw [hthree, show 3 * c + m * n = (c + m * n) + c + c by omega]
    exact Set.add_mem_add (Set.add_mem_add (h n) hc) hc
  by_cases hcon : ∃ s : ℕ, ∀ d ≤ 2, s + d ∈ Set.range a + Set.range a
  · -- Translating the three consecutive sums by terms of `a` covers a tail.
    obtain ⟨s, hs⟩ := hcon
    refine ⟨1, s + a 0, by decide, fun n ↦ ?_⟩
    obtain ⟨i, hi, hi'⟩ := exists_term_close_below ha (t := a 0 + n) (by omega)
    let d := a 0 + n - a i
    have hd : d ≤ 2 := by dsimp [d]; omega
    rw [hthree, show s + a 0 + 1 * n = (s + d) + a i by dsimp [d]; omega]
    exact Set.add_mem_add (hs d hd) (Set.mem_range_self i)
  by_cases hfreq : ∀ i, ∃ j, i ≤ j ∧ a (j + 1) = a j + 2
  · -- Record the run of 3-gaps after each 2-gap, up to the next 2-gap.
    let next (i : ℕ) := Nat.find (hfreq (i + 1))
    let len (i : ℕ) := next i - (i + 1)
    have hnext (i : ℕ) : i + 1 ≤ next i ∧ a (next i + 1) = a (next i) + 2 :=
      Nat.find_spec (hfreq (i + 1))
    have hindex (i : ℕ) : i + 1 + len i = next i := by
      dsimp [len]
      have := (hnext i).1
      omega
    have hrun (i : ℕ) (hi : a (i + 1) = a i + 2) (n : ℕ) (hn : n ≤ len i) :
        a (i + 1 + n) = a i + 2 + 3 * n := by
      rw [step_three_eq (a := a) (i := i + 1) n, hi]
      intro j hj hj'
      have hjnext : j < next i := by have := hindex i; omega
      have hnot := Nat.find_min (hfreq (i + 1)) hjnext
      have hgap := ha j
      omega
    have hend (i : ℕ) (hi : a (i + 1) = a i + 2) :
        a (next i + 1) = a i + 4 + 3 * len i := by
      have he := hrun i hi (len i) le_rfl
      rw [hindex i] at he
      have := (hnext i).2
      omega
    have not_shorter (i j : ℕ) (hi : a (i + 1) = a i + 2)
        (hj : a (j + 1) = a j + 2) : ¬ len i < len j := by
      intro hlt
      apply hcon
      -- The shorter run supplies its right endpoint; the longer one has
      -- one additional step of size 3, giving the missing middle sum.
      refine ⟨a (next i + 1) + a j, fun d hd ↦ ?_⟩
      have he := hend i hi
      have hm := hrun j hj (len i + 1) (by omega)
      rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl
      · simpa using hsum (next i + 1) j
      · convert hsum i (j + 1 + (len i + 1)) using 1; omega
      · convert hsum (next i + 1) (j + 1) using 1; omega
    obtain ⟨start, _, hstart⟩ := hfreq 0
    have hterm (n : ℕ) :
        ∃ i, a (i + 1) = a i + 2 ∧ a i = a start + (2 + 3 * len start) * n := by
      induction n with
      | zero => exact ⟨start, hstart, by simp⟩
      | succ n ih =>
        obtain ⟨i, hi, hval⟩ := ih
        have hlen : len i = len start :=
          le_antisymm (Nat.le_of_not_gt (not_shorter start i hstart hi))
            (Nat.le_of_not_gt (not_shorter i start hi hstart))
        have hr := hrun i hi (len i) le_rfl
        rw [hindex i, hlen, hval] at hr
        refine ⟨next i, (hnext i).2, ?_⟩
        rw [Nat.mul_succ]
        omega
    exact of_progression (2 + 3 * len start) (a start) (by omega) fun n ↦ by
      obtain ⟨i, _, hi⟩ := hterm n
      exact ⟨i, hi⟩
  · -- Beyond a suitable index all gaps are 3.
    push Not at hfreq
    obtain ⟨i, hi⟩ := hfreq
    refine of_progression 3 (a i) (by decide) fun n ↦ ⟨i + n, step_three_eq n ?_⟩
    intro j hj _
    have := hi j hj
    have := ha j
    omega

/-- A lacunary sequence whose prescribed residues make it hit every infinite
arithmetic progression in `ℕ`. -/
private def hittingSequence (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => (r i * hittingSequence r i + hittingSequence r i + 1) *
      (i + 1).factorial + (i + 1)

private theorem hittingSequence_growth (r : ℕ → ℕ) (i : ℕ) :
    hittingSequence r i < hittingSequence r (i + 1) ∧
      r i * hittingSequence r i ≤ hittingSequence r (i + 1) := by
  let M := r i * hittingSequence r i + hittingSequence r i + 1
  have hle : M ≤ hittingSequence r (i + 1) := by
    rw [hittingSequence]
    change M ≤ M * (i + 1).factorial + (i + 1)
    have := Nat.le_mul_of_pos_right M (Nat.factorial_pos (i + 1))
    omega
  dsimp [M] at hle
  omega

private theorem hittingSequence_hits (r : ℕ → ℕ) {m : ℕ} (hm : 0 < m) (c : ℕ) :
    ∃ i n : ℕ, hittingSequence r i = c + m * n := by
  let i := c + m * (c + 1)
  have hmi : m ≤ i := by dsimp [i]; rw [Nat.mul_succ]; omega
  obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  obtain ⟨q, hq⟩ := Nat.dvd_factorial hm hmi
  let B := r j * hittingSequence r j + hittingSequence r j + 1
  refine ⟨i, B * q + (c + 1), ?_⟩
  calc
    hittingSequence r i = B * i.factorial + i := by rw [hj, hittingSequence]
    _ = c + m * (B * q + (c + 1)) := by
      change B * i.factorial + (c + m * (c + 1)) = _
      rw [hq, Nat.mul_add m (B * q) (c + 1)]
      ac_rfl

/--
**Bollobás–Hegyvári–Jin theorem on Erdős Problem 1112.** There is no natural number $r$ such
that for every strictly increasing sequence $b_0 < b_1 < \cdots$ of positive integers with
$b_{i+1} \ge r b_i$ for all $i$, there is a sequence $a_0, a_1, \dots$ of positive integers with
$a_i + 2 \le a_{i+1} \le a_i + 3$ for all $i$ such that no $b_i$ is a sum of three, not
necessarily distinct, terms of the sequence $a$. In other words, the threshold $r_3(2, 3)$ of
Erdős Problem 1112 (gaps between $2$ and $3$, triple sums) does not exist.

Source: B. Bollobás, N. Hegyvári and G. Jin, *On a problem of Erdős and Graham*,
Discrete Math. 175 (1997), 253–257, Theorem 3,
https://doi.org/10.1016/S0012-365X(96)00122-7.
-/
theorem lacunaryThresholdGapsTwoThreeThreeFold_refuted :
    ¬ lacunaryThresholdGapsTwoThreeThreeFold := by
  rintro ⟨r, hr⟩
  let b := hittingSequence (fun _ ↦ r)
  have hg := hittingSequence_growth (fun _ ↦ r)
  obtain ⟨a, _, ha, hdisj⟩ := hr b (show 0 < (1 : ℕ) by decide)
    (strictMono_nat_of_lt_succ fun i ↦ (hg i).1) (fun i ↦ (hg i).2)
  obtain ⟨m, c, hm, hmem⟩ := exists_progression_in_threeFold a ha
  obtain ⟨i, n, hi⟩ := hittingSequence_hits (fun _ ↦ r) hm c
  have hbi : b i ∈ (3 : ℕ) • Set.range a := by
    change hittingSequence (fun _ ↦ r) i ∈ _
    rw [hi]
    exact hmem n
  exact Set.disjoint_left.mp hdisj hbi (Set.mem_range_self i)

end MathlibExt.Combinatorics.LacunaryAvoidingBoundedGapSumsetErdosProblem1112Wanted
