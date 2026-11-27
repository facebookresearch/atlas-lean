/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Intervals and residues of the anti-bonacci numbers

The positive mex construction generates anti-recurrence numbers in blocks. For the all-ones
form, `antiBonacci_mem_Icc_and_modEq` locates each block sum within its interval of length
`k ^ 2 + 1` and bounds its residue there.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Least positive integer missing from a finite set.** For a finite set $s$ of natural numbers,
this is the least positive integer not in $s$ (the source's $\mathrm{mex}$ over the positive
integers, used to build the anti-Tribonacci sequence). It always lies among $1, \dots, |s| + 1$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public def antiTribonacciMex (s : Finset ℕ) : ℕ :=
  ((List.range (s.card + 2)).find? fun m => decide (0 < m ∧ m ∉ s)).getD 0

private theorem antiTribonacciMex_spec (s : Finset ℕ) :
    0 < antiTribonacciMex s ∧ antiTribonacciMex s ∉ s ∧
      ∀ m, 0 < m → m ∉ s → antiTribonacciMex s ≤ m := by
  have hex : ∃ m ∈ List.range (s.card + 2), 0 < m ∧ m ∉ s := by
    by_contra h
    push Not at h
    have hsub : Finset.Icc 1 (s.card + 1) ⊆ s := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      exact h m (List.mem_range.mpr (by omega)) (by omega)
    have := Finset.card_le_card hsub
    simp at this
  obtain ⟨m0, hm0, hp0⟩ := hex
  have hsome : ((List.range (s.card + 2)).find? fun m => decide (0 < m ∧ m ∉ s)).isSome :=
    List.find?_isSome.mpr ⟨m0, hm0, by simpa using hp0⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsome
  have hval : antiTribonacciMex s = b := by unfold antiTribonacciMex; rw [hb]; rfl
  rw [List.find?_eq_some_iff_getElem] at hb
  obtain ⟨hpb, i, hi, hib, hmin⟩ := hb
  simp only [List.getElem_range] at hib
  subst hib
  simp only [decide_eq_true_eq] at hpb
  refine ⟨hval ▸ hpb.1, hval ▸ hpb.2, fun m hm hms => ?_⟩
  rw [hval]
  by_contra hlt
  push Not at hlt
  have := hmin m hlt
  simp [hm, hms] at this

/-- **The mex of a finite set is positive.** Write $\mathrm{mex}(s)$ for the least positive integer
not in a finite set $s$ of natural numbers. For every such $s$, $\mathrm{mex}(s) > 0$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem antiTribonacciMex_pos (s : Finset ℕ) : 0 < antiTribonacciMex s :=
  (antiTribonacciMex_spec s).1

/-- **The mex of a finite set lies outside the set.** Write $\mathrm{mex}(s)$ for the least positive
integer not in a finite set $s$ of natural numbers. For every such $s$, $\mathrm{mex}(s) \notin s$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem antiTribonacciMex_notMem (s : Finset ℕ) : antiTribonacciMex s ∉ s :=
  (antiTribonacciMex_spec s).2.1

/-- **The mex is at most every missing positive integer.** Write $\mathrm{mex}(s)$ for the least
positive integer not in a finite set $s$ of natural numbers. If $m$ is a positive integer with
$m \notin s$, then $\mathrm{mex}(s) \le m$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Section 4. -/
public theorem antiTribonacciMex_le_of_notMem (s : Finset ℕ) {m : ℕ} (hm : 0 < m)
    (hms : m ∉ s) : antiTribonacciMex s ≤ m :=
  (antiTribonacciMex_spec s).2.2 m hm hms

/-- **Block of successive mex values.** For a natural number $m$ and a finite set $s$ of natural
numbers, the mex block of length $m$ from $s$ is the list $(x_1, \dots, x_m)$ in which each $x_j$
is the least positive integer not in $s \cup \{x_1, \dots, x_{j-1}\}$.

Source: Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026),
Article A24, Section 2 (proof of Lemma 2, the mex rule). -/
def antiRecurrenceBlock : ℕ → Finset ℕ → List ℕ
  | 0, _ => []
  | m + 1, s => antiTribonacciMex s :: antiRecurrenceBlock m (insert (antiTribonacciMex s) s)

/-- **State of the anti-recurrence construction.** Let $a = (a_1, \dots, a_k)$ be a finite list of
natural numbers. The state at step $0$ is the pair of the empty list and the empty set. If the
state at step $n$ has set $S$, then the state at step $n + 1$ is the pair $(\beta, S')$, where
$\beta = (x_1, \dots, x_k)$ is the mex block of length $k$ from $S$ (each $x_j$ is the least
positive integer not in $S \cup \{x_1, \dots, x_{j-1}\}$) and
$S' = S \cup \{x_1, \dots, x_k\} \cup \{a_1 x_1 + \dots + a_k x_k\}$.

In the notation of the source, for $n \ge 1$ the block at step $n$ is
$(B_{(n-1)k+1}, \dots, B_{nk})$ and the set at step $n$ is
$\{B_1, \dots, B_{nk}\} \cup \{A_1, \dots, A_n\}$, where the $B_m$ are the non-anti-recurrence
numbers and the $A_m$ are the anti-recurrence numbers of $a$.

Source: Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026),
Article A24, Section 2 (definition of anti-recurrence sequences and Lemma 2). -/
def antiRecurrenceState (a : List ℕ) : ℕ → List ℕ × Finset ℕ
  | 0 => ([], ∅)
  | n + 1 =>
    let s := (antiRecurrenceState a n).2
    let blk := antiRecurrenceBlock a.length s
    (blk, insert (List.zipWith (· * ·) a blk).sum (s ∪ blk.toFinset))

/-- **Anti-recurrence numbers.** Let $a = (a_1, \dots, a_k)$ be a linear form with natural number
coefficients. The non-anti-recurrence numbers $B_1, B_2, \dots$ are produced in blocks of $k$ by
the mex rule, and each block $B_{(n-1)k+1}, \dots, B_{nk}$ generates the anti-recurrence number
$A_n = \sum_{j=1}^{k} a_j B_{(n-1)k+j}$. Here $B_m$ is the least positive integer that differs
from $B_1, \dots, B_{m-1}$ and from the anti-recurrence numbers of earlier blocks. By convention
$A_0 = 0$, following Hofstadter.

Source: Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026),
Article A24, Section 2 (definition of anti-recurrence sequences). -/
def antiRecurrence (a : List ℕ) (n : ℕ) : ℕ :=
  (List.zipWith (· * ·) a (antiRecurrenceState a n).1).sum

-- Once 1 through m have been used, the next block is consecutive from m + 1.
private theorem antiRecurrenceBlock_Icc (l m : ℕ) :
    antiRecurrenceBlock l (Finset.Icc 1 m) = List.range' (m + 1) l := by
  induction l generalizing m with
  | zero => rfl
  | succ l ih =>
    have hmex := antiTribonacciMex_spec (Finset.Icc 1 m)
    have hnot : m + 1 ∉ Finset.Icc 1 m := by simp
    have hle := hmex.2.2 (m + 1) (by omega) hnot
    have hn := hmex.2.1
    rw [Finset.mem_Icc] at hn
    have he : antiTribonacciMex (Finset.Icc 1 m) = m + 1 := by omega
    have hi : insert (m + 1) (Finset.Icc 1 m) = Finset.Icc 1 (m + 1) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [antiRecurrenceBlock, he, hi, ih, List.range'_succ]

private theorem antiRecurrence_one_eq_sum (a : List ℕ) :
    antiRecurrence a 1 = a.sum + ∑ j : Fin a.length, (j : ℕ) * a[j] := by
  have hb : (antiRecurrenceState a 1).1 = List.range' 1 a.length := by
    change antiRecurrenceBlock a.length ∅ = _
    have hempty : Finset.Icc 1 (0 : ℕ) = ∅ := by simp
    simpa only [hempty, Nat.zero_add] using antiRecurrenceBlock_Icc a.length 0
  have hz : List.zipWith (· * ·) a (List.range' 1 a.length) =
      List.ofFn (fun j : Fin a.length => a[j] * (1 + (j : ℕ))) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [List.getElem_zipWith, List.getElem_range']
  have hs : a.sum = ∑ j : Fin a.length, a[j] := by
    rw [← List.sum_ofFn]
    change a.sum = (List.ofFn a.get).sum
    rw [List.ofFn_get]
  rw [antiRecurrence, hb, hz, List.sum_ofFn, hs]
  simp only [Nat.mul_add, Nat.mul_one, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j _ => Nat.mul_comm _ _

/-- **Lower bound for the first anti-recurrence number.** Let $a = (a_1, \dots, a_k)$ be a linear
form with positive integer coefficients, of trace $\tau = a_1 + \dots + a_k$, and let $A_1$ be its
first anti-recurrence number. Then $\tau + (k - 1)k/2 \le A_1$, and the inequality is strict if
and only if $a_j > 1$ for some $j$ with $2 \le j \le k$.

This corrects the printed strictness condition ("$k > 2$ and not anti-bonacci"), which fails for
$a = (2, 1, 1)$: there $A_1 = 2 + 2 + 3 = 7 = \tau + 3$. The correction follows the paper's
proof, $A_1 = \tau + \sum_j (j - 1) a_j$. The paper's hypothesis $k > 1$ is not needed.

Source: Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026),
Article A24, Lemma 4 (`integers-2026-A24-lem-4`). -/
public theorem antiRecurrence_one_ge (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    a.sum + (a.length - 1) * a.length / 2 ≤ antiRecurrence a 1 ∧
      (a.sum + (a.length - 1) * a.length / 2 < antiRecurrence a 1 ↔
        ∃ j : Fin a.length, 1 ≤ (j : ℕ) ∧ 1 < a[j]) := by
  have htriangle : (a.length - 1) * a.length / 2 = ∑ j : Fin a.length, (j : ℕ) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => j), Finset.sum_range_id, Nat.mul_comm]
  rw [antiRecurrence_one_eq_sum, htriangle, Nat.add_le_add_iff_left, Nat.add_lt_add_iff_left]
  have hpos (j : Fin a.length) : 0 < a[j] := ha _ (List.getElem_mem j.isLt)
  have hle (j : Fin a.length) : (j : ℕ) ≤ (j : ℕ) * a[j] := by
    simpa using Nat.mul_le_mul_left (j : ℕ) (hpos j)
  refine ⟨Finset.sum_le_sum fun j _ => hle j, ?_⟩
  constructor
  · intro h
    by_contra! hnone
    have he (j : Fin a.length) : (j : ℕ) = (j : ℕ) * a[j] := by
      by_cases hj : 1 ≤ (j : ℕ)
      · have hj' := hnone j hj
        have ha' : a[j] = 1 := by have := hpos j; omega
        simp [ha']
      · have hj' : (j : ℕ) = 0 := by omega
        simp [hj']
    exact (ne_of_lt h) (Finset.sum_congr rfl fun j _ => he j)
  · rintro ⟨j, hj, haj⟩
    refine Finset.sum_lt_sum (fun i _ => hle i) ⟨j, Finset.mem_univ _, ?_⟩
    simpa using mul_lt_mul_of_pos_left haj (show 0 < (j : ℕ) from hj)

namespace antiBonacci_mem_Icc_and_modEq

-- All interval positions in the proof are zero-based.
private abbrev width (k : ℕ) := k * k + 1
-- The admissible omitted positions start at ⌊k²/2⌋ and have length k.
private def base (k : ℕ) := k / 2 * k + k % 2 * (k / 2)
private abbrev mid (k : ℕ) := (k - 1) / 2

private theorem parameters {k : ℕ} (hk : 1 < k) :
    k ≤ base k ∧ mid k * k < base k ∧ base k ≤ (mid k + 1) * k ∧
    base k + k ≤ k * k ∧ mid k < k ∧
    2 * (base k + mid k + 1) = k * (k + 1) := by
  rcases Nat.even_or_odd k with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · have hi : 1 ≤ i := by omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    simp only [base, mid, show (1 + j + (1 + j)) / 2 = 1 + j by omega,
      show (1 + j + (1 + j)) % 2 = 0 by omega,
      show (1 + j + (1 + j) - 1) / 2 = j by omega]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith
  · have hi : 1 ≤ i := by omega
    simp only [base, mid, show (2 * i + 1) / 2 = i by omega,
      show (2 * i + 1) % 2 = 1 by omega, show (2 * i + 1 - 1) / 2 = i by omega]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [Nat.mul_le_mul_right i hi]

-- The last `shift` entries of the r-th block move one place to skip position h.
private def shift (k r h : ℕ) := min k ((r + 1) * k - h)

private theorem shift_bounds {k r h : ℕ} (hk : 1 < k) (hr : r < k)
    (hlo : base k ≤ h) (hhi : h < base k + k) :
    r ≤ mid k + shift k r h ∧ mid k + shift k r h < r + k := by
  obtain ⟨_, h₁, h₂, _, hd, _⟩ := parameters hk
  unfold shift
  by_cases hrd : r ≤ mid k
  · have hmul := Nat.mul_le_mul_right (k - 1) hrd
    have hk' : k - 1 + 1 = k := by omega
    have hb : r * k + mid k + 1 ≤ h + r := by
      nlinarith [congrArg (r * ·) hk', congrArg (mid k * ·) hk']
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · have hmul := Nat.mul_le_mul_right (k - 1) (show mid k + 1 ≤ r by omega)
    have hk' : k - 1 + 1 = k := by omega
    have hb : h + r ≤ (r + 1) * k + mid k := by
      nlinarith [congrArg (r * ·) hk', congrArg (mid k * ·) hk']
    omega

-- Block t is block t % k of interval t / k. Its sum gives the omitted position of
-- interval t. The initial sum is the triangular number 1 + ⋯ + k.
private def hole (k : ℕ) (hk : 1 < k) (t : ℕ) : ℕ :=
  if _ht : t = 0 then base k + mid k
  else base k + mid k + shift k (t % k) (hole k hk (t / k)) - t % k
termination_by t
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero _ht) hk

private theorem hole_bounds {k : ℕ} (hk : 1 < k) (t : ℕ) :
    base k ≤ hole k hk t ∧ hole k hk t < base k + k := by
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    rw [hole]
    split
    · obtain ⟨_, _, _, _, hm, _⟩ := parameters hk
      omega
    · have hp := ih (t / k) (Nat.div_lt_self (by omega) hk)
      have := shift_bounds hk (Nat.mod_lt t (by omega)) hp.1 hp.2
      omega

private theorem hole_step {k : ℕ} (hk : 1 < k) (t : ℕ) :
    hole k hk t + t % k =
      base k + mid k + shift k (t % k) (hole k hk (t / k)) := by
  by_cases ht : t = 0
  · subst t
    obtain ⟨hb, _⟩ := parameters hk
    simp [hole, shift, Nat.sub_eq_zero_of_le (show k ≤ base k + mid k by omega)]
  · obtain ⟨hl, hu⟩ := hole_bounds hk (t / k)
    have := (shift_bounds hk (Nat.mod_lt t (by omega)) hl hu).1
    rw [hole.eq_def k hk t, dite_eq_right ht]
    omega

private def total (k : ℕ) (hk : 1 < k) (t : ℕ) :=
  width k * t + hole k hk t + 1

private def skip (h s : ℕ) := s + if h ≤ s then 1 else 0

-- Each interval supplies k² summands in increasing order around its omitted position.
private def entry (k : ℕ) (hk : 1 < k) (m : ℕ) :=
  width k * (m / (k * k)) + skip (hole k hk (m / (k * k))) (m % (k * k)) + 1

private theorem entry_at {k : ℕ} (hk : 1 < k) (q : ℕ) {s : ℕ} (hs : s < k * k) :
    entry k hk (k * k * q + s) = width k * q + skip (hole k hk q) s + 1 := by
  have hk₂ : 0 < k * k := by positivity
  simp [entry, Nat.mul_add_div hk₂, Nat.div_eq_of_lt hs, Nat.mod_eq_of_lt hs]

private theorem entry_mono {k : ℕ} (hk : 1 < k) : StrictMono (entry k hk) := by
  intro m n hmn
  have hk₂ : 0 < k * k := by positivity
  have hm := Nat.mod_lt m hk₂
  have hn := Nat.mod_lt n hk₂
  have hq : m / (k * k) ≤ n / (k * k) := Nat.div_le_div_right hmn.le
  by_cases he : m / (k * k) = n / (k * k)
  · have h := Nat.div_add_mod m (k * k)
    have h' := Nat.div_add_mod n (k * k)
    rw [he] at h
    simp only [entry, he, skip]
    split_ifs <;> omega
  · have h := Nat.mul_le_mul_left (width k)
        (show m / (k * k) + 1 ≤ n / (k * k) by omega)
    rw [Nat.mul_add, Nat.mul_one] at h
    simp only [entry, skip]
    split_ifs <;> unfold width at * <;> omega

private theorem total_mono {k : ℕ} (hk : 1 < k) : StrictMono (total k hk) := by
  apply strictMono_nat_of_lt_succ
  intro t
  obtain ⟨_, _, _, hb, _, _⟩ := parameters hk
  have hh := (hole_bounds hk t).2
  simp only [total, Nat.mul_succ]
  unfold width
  omega

private theorem entry_ne_total {k : ℕ} (hk : 1 < k) (m t : ℕ) :
    entry k hk m ≠ total k hk t := by
  have hm := Nat.mod_lt m (show 0 < k * k by positivity)
  have ht := (hole_bounds hk t).2
  obtain ⟨_, _, _, hb, _, _⟩ := parameters hk
  rcases lt_trichotomy (m / (k * k)) t with h | h | h
  · have h' := Nat.mul_le_mul_left (width k) (Nat.succ_le_of_lt h)
    simp only [Nat.mul_succ] at h'
    unfold entry total skip
    split <;> unfold width at * <;> omega
  · simp only [entry, h, total, skip]
    split <;> omega
  · have h' := Nat.mul_le_mul_left (width k) (Nat.succ_le_of_lt h)
    simp only [Nat.mul_succ] at h'
    unfold entry total skip
    split <;> unfold width at * <;> omega

private theorem covers {k : ℕ} (hk : 1 < k) {x : ℕ} (hx : 0 < x) :
    (∃ t, total k hk t = x) ∨ ∃ m, entry k hk m = x := by
  let q := (x - 1) / width k
  let s := (x - 1) % width k
  have hs : s < width k := Nat.mod_lt _ (by unfold width; omega)
  have hxs : width k * q + s = x - 1 := Nat.div_add_mod _ _
  obtain ⟨_, _, _, hb, _, _⟩ := parameters hk
  have hh := (hole_bounds hk q).2
  rcases lt_trichotomy s (hole k hk q) with h | h | h
  · right
    refine ⟨k * k * q + s, ?_⟩
    rw [entry_at hk q (by omega)]
    simp [skip, Nat.not_le.mpr h]
    omega
  · left
    exact ⟨q, by unfold total; omega⟩
  · right
    refine ⟨k * k * q + (s - 1), ?_⟩
    rw [entry_at hk q (by unfold width at hs; omega)]
    simp [skip, show hole k hk q ≤ s - 1 by omega]
    omega

private abbrev block (k : ℕ) (hk : 1 < k) (t : ℕ) :=
  (List.range' (k * t) k).map (entry k hk)

private theorem sum_range' (f : ℕ → ℕ) (m l : ℕ) :
    ((List.range' m l).map f).sum = ∑ j ∈ Finset.range l, f (m + j) := by
  induction l with
  | zero => simp
  | succ l ih => simp [List.range'_1_concat, Finset.sum_range_succ, ih]

private theorem count_shift (u h l : ℕ) :
    (∑ j ∈ Finset.range l, if h ≤ u + j then 1 else 0) = min l (u + l - h) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Finset.sum_range_succ, ih]
    split <;> omega

-- In a block starting at rank r * k, the omission adds one to each shifted summand.
private theorem block_sum {k : ℕ} (hk : 1 < k) (t : ℕ) :
    (block k hk t).sum = total k hk t := by
  let q := t / k
  let r := t % k
  have hqr : k * q + r = t := Nat.div_add_mod _ _
  have hr : r < k := Nat.mod_lt t (by omega)
  have he {j : ℕ} (hj : j < k) :
      entry k hk (k * t + j) =
        (width k * q + r * k + 1) + j + (if hole k hk q ≤ r * k + j then 1 else 0) := by
    have heq : k * t + j = k * k * q + (r * k + j) := by rw [← hqr]; ring
    have hs : r * k + j < k * k := by
      have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt hr)
      nlinarith
    rw [heq, entry_at hk q hs, skip]
    omega
  unfold block
  rw [sum_range', Finset.sum_congr rfl (fun j hj => he (Finset.mem_range.mp hj))]
  simp only [Finset.sum_add_distrib, count_shift]
  have hsum (c : ℕ) : (∑ j ∈ Finset.range k, (c + j)) = k * c + ∑ j ∈ Finset.range k, j := by
    exact (Finset.sum_add_distrib (s := Finset.range k) (f := fun _ : ℕ => c)
      (g := fun j : ℕ => j)).trans (by simp)
  rw [hsum]
  have hshift : min k (r * k + k - hole k hk q) = shift k r (hole k hk q) := by
    simp [shift, Nat.add_mul]
  rw [hshift]
  have hs := Finset.sum_range_id_mul_two k
  obtain ⟨_, _, _, _, _, htri⟩ := parameters hk
  have ht : (∑ i ∈ Finset.range k, i) + k = base k + mid k + 1 := by
    have heq : k - 1 + 1 = k := by omega
    nlinarith [congrArg (k * ·) heq]
  have hrec : hole k hk t + r = base k + mid k + shift k r (hole k hk q) := hole_step hk t
  unfold total
  have hprod : k * (width k * q + r * k + 1) + r = width k * t + k := by
    rw [← hqr]
    unfold width
    ring
  omega

private theorem zip_ones (l : List ℕ) :
    List.zipWith (· * ·) (List.replicate l.length 1) l = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.replicate_succ, ih]

-- Membership after t sums and m summands have been inserted.
private def used (k : ℕ) (hk : 1 < k) (t m x : ℕ) : Prop :=
  (∃ u < t, total k hk u = x) ∨ ∃ v < m, entry k hk v = x

private theorem next_mex {k : ℕ} (hk : 1 < k) {t m : ℕ} {s : Finset ℕ}
    (hs : ∀ x, x ∈ s ↔ used k hk t m x) (hm : entry k hk m ≤ total k hk t) :
    antiTribonacciMex s = entry k hk m := by
  apply le_antisymm
  · apply antiTribonacciMex_le_of_notMem _ (by unfold entry; omega)
    intro h
    rcases (hs _).mp h with ⟨u, _, hu⟩ | ⟨v, hv, he⟩
    · exact entry_ne_total hk m u hu.symm
    · exact (entry_mono hk hv).ne he
  · by_contra! h
    apply antiTribonacciMex_notMem s
    apply (hs _).mpr
    rcases covers hk (antiTribonacciMex_pos s) with ⟨u, hu⟩ | ⟨v, hv⟩
    · exact Or.inl ⟨u, (total_mono hk).lt_iff_lt.mp (by omega), hu⟩
    · exact Or.inr ⟨v, (entry_mono hk).lt_iff_lt.mp (by omega), hv⟩

private theorem mex_block {k : ℕ} (hk : 1 < k) (l : ℕ) {m t : ℕ} {s : Finset ℕ}
    (hs : ∀ x, x ∈ s ↔ used k hk t m x)
    (hm : ∀ v ∈ List.range' m l, entry k hk v ≤ total k hk t) :
    antiRecurrenceBlock l s = (List.range' m l).map (entry k hk) := by
  induction l generalizing m s with
  | zero => rfl
  | succ l ih =>
    rw [List.range'_succ] at hm ⊢
    have h := next_mex hk hs (hm m (by simp))
    simp only [antiRecurrenceBlock, h, List.map_cons, List.cons.injEq, true_and]
    apply ih (hm := fun v hv => hm v (List.mem_cons_of_mem _ hv))
    intro x
    rw [Finset.mem_insert, hs]
    unfold used
    constructor
    · rintro (rfl | h' | ⟨v, hv, he⟩)
      · exact Or.inr ⟨m, by omega, rfl⟩
      · exact Or.inl h'
      · exact Or.inr ⟨v, by omega, he⟩
    · rintro (h' | ⟨v, hv, he⟩)
      · exact Or.inr (Or.inl h')
      · rcases Nat.lt_or_eq_of_le (show v ≤ m by omega) with hv | rfl
        · exact Or.inr (Or.inr ⟨v, hv, he⟩)
        · exact Or.inl he.symm

private theorem next_block {k : ℕ} (hk : 1 < k) {s : Finset ℕ} {t : ℕ}
    (hs : ∀ x, x ∈ s ↔ used k hk t (k * t) x) :
    antiRecurrenceBlock k s = block k hk t := by
  apply mex_block hk k hs
  intro v hv
  rw [← block_sum hk t]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨v, hv, rfl⟩)

private theorem weighted_block {k : ℕ} (hk : 1 < k) (t : ℕ) :
    (List.zipWith (· * ·) (List.replicate k 1) (block k hk t)).sum = total k hk t := by
  have hl : (block k hk t).length = k := by simp [block]
  have hz := zip_ones (block k hk t)
  rw [hl] at hz
  rw [hz, block_sum]

private theorem state_spec {k : ℕ} (hk : 1 < k) (t : ℕ) (x : ℕ) :
    x ∈ (antiRecurrenceState (List.replicate k 1) t).2 ↔ used k hk t (k * t) x := by
  induction t generalizing x with
  | zero => simp [antiRecurrenceState, used]
  | succ t ih =>
    simp only [antiRecurrenceState, List.length_replicate, next_block hk ih, weighted_block,
      Finset.mem_insert, Finset.mem_union, List.mem_toFinset, ih, Nat.mul_succ]
    simp only [block, List.mem_map, List.mem_range'_1, used]
    constructor
    · rintro (rfl | (⟨u, hu, he⟩ | ⟨v, hv, he⟩) | ⟨v, ⟨_, hv⟩, he⟩)
      · exact Or.inl ⟨t, by omega, rfl⟩
      · exact Or.inl ⟨u, by omega, he⟩
      · exact Or.inr ⟨v, by omega, he⟩
      · exact Or.inr ⟨v, hv, he⟩
    · rintro (⟨u, hu, he⟩ | ⟨v, hv, he⟩)
      · rcases Nat.lt_or_eq_of_le (show u ≤ t by omega) with hu | rfl
        · exact Or.inr (Or.inl (Or.inl ⟨u, hu, he⟩))
        · exact Or.inl he.symm
      · by_cases hv' : v < k * t
        · exact Or.inr (Or.inl (Or.inr ⟨v, hv', he⟩))
        · exact Or.inr (Or.inr ⟨v, ⟨by omega, hv⟩, he⟩)

private theorem eq_total {k : ℕ} (hk : 1 < k) (t : ℕ) :
    antiRecurrence (List.replicate k 1) (t + 1) = total k hk t := by
  simp only [antiRecurrence, antiRecurrenceState, List.length_replicate,
    next_block hk (state_spec hk t), weighted_block]

end antiBonacci_mem_Icc_and_modEq

open antiBonacci_mem_Icc_and_modEq

/-- **Intervals and residues of the anti-$k$-bonacci numbers.** Let $k > 1$, let $A_n$ be the
anti-recurrence numbers of the linear form $(1, \dots, 1)$ of length $k$, and put
$i = \lfloor k/2 \rfloor$ and $\kappa = k^2 + 1$. Then for every $n \ge 1$, $A_n$ lies in the
interval $[\kappa(n - 1) + 1, \kappa n]$, and $A_n \equiv ik + c \pmod{\kappa}$ for some natural
number $c$ with $1 \le c \le k$ if $k$ is even and $i + 1 \le c \le i + k$ if $k$ is odd.

The paper attaches the condition $k > 2$ to $\kappa$; it is not needed, since $k = 2$ is the
anti-Fibonacci case (Zaslavsky's formula $A_n = 5n - 2 + PD_{n-1}$, with $PD$ the
period-doubling sequence).

Source: Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026),
Article A24, Lemma 3 (`integers-2026-A24-lem-3`). -/
public theorem antiBonacci_mem_Icc_and_modEq (k : ℕ) (hk : 1 < k) {n : ℕ} (hn : 1 ≤ n) :
    antiRecurrence (List.replicate k 1) n ∈
        Finset.Icc ((k ^ 2 + 1) * (n - 1) + 1) ((k ^ 2 + 1) * n) ∧
      ∃ c : ℕ, (if Even k then 1 ≤ c ∧ c ≤ k else k / 2 + 1 ≤ c ∧ c ≤ k / 2 + k) ∧
        antiRecurrence (List.replicate k 1) n ≡ k / 2 * k + c [MOD k ^ 2 + 1] := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [eq_total hk, Finset.mem_Icc]
  simp only [Nat.succ_sub_one, pow_two, Nat.mul_succ]
  obtain ⟨hlo, hhi⟩ := hole_bounds hk t
  obtain ⟨_, _, _, hb, _, _⟩ := parameters hk
  constructor
  · unfold total width
    omega
  · refine ⟨hole k hk t + 1 - k / 2 * k, ?_, ?_⟩
    · unfold base at hlo hhi
      split
      · rename_i he
        rw [Nat.even_iff.mp he] at hlo hhi
        omega
      · rename_i ho
        have : k % 2 = 1 := Nat.not_even_iff.mp ho
        rw [this] at hlo hhi
        omega
    · have hl : k / 2 * k ≤ hole k hk t := by unfold base at hlo; omega
      rw [Nat.add_sub_of_le (by omega : k / 2 * k ≤ hole k hk t + 1)]
      simp [Nat.ModEq, total, Nat.add_assoc]

end

end MetaMathlibExt
