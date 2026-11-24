/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.AntiBonacci
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.GetD

/-!
# Gaps between successive anti-recurrence numbers

`antiRecurrence_add_length_mul_sum_le` bounds the increase of the weighted block sum
and gives equality and strictness criteria in terms of the complement blocks.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Non-anti-recurrence numbers.** Let $a = (a_1, \dots, a_k)$ be a linear form with natural
number coefficients. Its non-anti-recurrence numbers $B_1, B_2, \dots$ are produced in blocks of
$k$ by the mex rule: for $n \ge 1$, each of $B_{(n-1)k+1}, \dots, B_{nk}$ in turn is the least
positive integer not among $B_1, \dots, B_{(n-1)k}$, the anti-recurrence numbers
$A_1, \dots, A_{n-1}$ and the earlier entries of its block, and then
$A_n = a_1 B_{(n-1)k+1} + \dots + a_k B_{nk}$. For $k = 2$ the subsequences $B^1_n = B_{2n-1}$
and $B^2_n = B_{2n}$ are the paper's $B^1$ and $B^2$.

By Lemma 2 of the source, for a positive form with $k > 1$ the numbers $B_m$ are the positive
integers that are not anti-recurrence numbers, listed in increasing order.

Source: Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026),
Article A24, Section 2 (definition of anti-recurrence sequences). -/
def antiRecurrenceComplement (a : List ℕ) (m : ℕ) : ℕ :=
  (antiRecurrenceState a ((m - 1) / a.length + 1)).1.getD ((m - 1) % a.length) 0

namespace AntiRecurrenceGaps

private theorem mex_mono {s t : Finset ℕ} (h : s ⊆ t) :
    antiTribonacciMex s ≤ antiTribonacciMex t :=
  antiTribonacciMex_le_of_notMem s (antiTribonacciMex_pos t)
    (fun hx => antiTribonacciMex_notMem t (h hx))

-- There is room for j unit steps before entry j and m - j after it, up to the next mex.
private theorem block_spacing (m : ℕ) (s t : Finset ℕ)
    (h : s ∪ (antiRecurrenceBlock m s).toFinset ⊆ t) :
    antiTribonacciMex s + m ≤ antiTribonacciMex t ∧
      ∀ j < m, antiTribonacciMex s + j ≤ (antiRecurrenceBlock m s).getD j 0 ∧
        (antiRecurrenceBlock m s).getD j 0 + (m - j) ≤ antiTribonacciMex t := by
  induction m generalizing s with
  | zero =>
    simpa using mex_mono (s := s) (t := t) (by simpa [antiRecurrenceBlock] using h)
  | succ m ih =>
    let u := insert (antiTribonacciMex s) s
    have hstep : antiTribonacciMex s < antiTribonacciMex u := by
      apply lt_of_le_of_ne (mex_mono (Finset.subset_insert _ _))
      intro he
      exact antiTribonacciMex_notMem u (he ▸ Finset.mem_insert_self _ _)
    have hu : u ∪ (antiRecurrenceBlock m u).toFinset ⊆ t := by
      simpa [u, antiRecurrenceBlock, Finset.insert_union, Finset.union_insert] using h
    obtain ⟨hcut, hentry⟩ := ih u hu
    refine ⟨by omega, ?_⟩
    intro j hj
    cases j with
    | zero =>
      change antiTribonacciMex s + 0 ≤ antiTribonacciMex s ∧
        antiTribonacciMex s + (m + 1 - 0) ≤ antiTribonacciMex t
      omega
    | succ j =>
      obtain ⟨hl, hr⟩ := hentry j (by omega)
      change antiTribonacciMex s + (j + 1) ≤ (antiRecurrenceBlock m u).getD j 0 ∧
        (antiRecurrenceBlock m u).getD j 0 + (m + 1 - (j + 1)) ≤ antiTribonacciMex t
      omega

private theorem block_length (m : ℕ) (s : Finset ℕ) : (antiRecurrenceBlock m s).length = m := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih => simp [antiRecurrenceBlock, ih]

private theorem complement_entry (a : List ℕ) (r j : ℕ) (hj : j < a.length) :
    antiRecurrenceComplement a (r * a.length + j + 1) =
      (antiRecurrenceState a (r + 1)).1.getD j 0 := by
  have hk : 0 < a.length := by omega
  unfold antiRecurrenceComplement
  rw [Nat.add_one_sub_one, Nat.mul_add_mod_of_lt hj, Nat.mul_comm r,
    Nat.mul_add_div hk, Nat.div_eq_of_lt hj, Nat.add_zero]

private theorem weighted_sum (a : List ℕ) (r : ℕ) :
    antiRecurrence a (r + 1) =
      ∑ j : Fin a.length, a[j] * antiRecurrenceComplement a (r * a.length + j + 1) := by
  have hlen : (antiRecurrenceState a (r + 1)).1.length = a.length := block_length _ _
  have hz : List.zipWith (· * ·) a (antiRecurrenceState a (r + 1)).1 =
      List.ofFn (fun j : Fin a.length =>
        a[j] * antiRecurrenceComplement a (r * a.length + j + 1)) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      simp only [List.length_ofFn] at hj
      simp only [List.getElem_zipWith, List.getElem_ofFn, complement_entry a r i hj,
        List.getD_eq_getElem _ _ (hlen.symm ▸ hj), Fin.getElem_fin]
  rw [antiRecurrence, hz, List.sum_ofFn]

private theorem entry_spacing (a : List ℕ) (r j : ℕ) (hj : j < a.length) :
    antiRecurrenceComplement a (r * a.length + j + 1) + a.length ≤
      antiRecurrenceComplement a ((r + 1) * a.length + j + 1) := by
  let s (i : ℕ) := (antiRecurrenceState a i).2
  have hsub (i : ℕ) : s i ∪ (antiRecurrenceBlock a.length (s i)).toFinset ⊆ s (i + 1) :=
    Finset.subset_insert _ _
  have hright := ((block_spacing _ _ _ (hsub r)).2 j hj).2
  have hleft := ((block_spacing _ _ _ (hsub (r + 1))).2 j hj).1
  rw [complement_entry _ _ _ hj, complement_entry _ _ _ hj]
  change (antiRecurrenceBlock a.length (s r)).getD j 0 + a.length ≤
    (antiRecurrenceBlock a.length (s (r + 1))).getD j 0
  omega

end AntiRecurrenceGaps

open AntiRecurrenceGaps in
/-- **Gaps between successive anti-recurrence numbers.** Let $a = (a_1, \dots, a_k)$ be a linear
form with positive integer coefficients and $k > 1$, let $\tau = a_1 + \dots + a_k$ be its trace,
and let $A_n$ and $B_m$ be the anti-recurrence and non-anti-recurrence numbers of $a$; for
$m \ge 1$, block $m$ consists of $B_{(m-1)k+1}, \dots, B_{mk}$, and it is an interval when
$B_{mk} = B_{(m-1)k+1} + k - 1$. Then for every $n \ge 1$ we have $A_{n+1} \ge A_n + k\tau$.
Equality holds if $B_{(n-1)k+1+j} = B_{(n-1)k+1} + j$ for every $j$ with $0 \le j < 2k$, that
is, if $B_{(n-1)k+1}, \dots, B_{(n+1)k}$ are consecutive integers. The inequality is strict if
exactly one of the blocks $n$ and $n + 1$ is an interval.

Source: Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026),
Article A24, Lemma 1 (`integers-2026-A24-lem-1`). -/
public theorem antiRecurrence_add_length_mul_sum_le (a : List ℕ) (ha : ∀ x ∈ a, 0 < x)
    (hk : 1 < a.length) {n : ℕ} (hn : 1 ≤ n) :
    antiRecurrence a n + a.length * a.sum ≤ antiRecurrence a (n + 1) ∧
      ((∀ j < 2 * a.length, antiRecurrenceComplement a ((n - 1) * a.length + j + 1) =
          antiRecurrenceComplement a ((n - 1) * a.length + 1) + j) →
        antiRecurrence a (n + 1) = antiRecurrence a n + a.length * a.sum) ∧
      (¬ (antiRecurrenceComplement a (n * a.length) =
            antiRecurrenceComplement a ((n - 1) * a.length + 1) + (a.length - 1) ↔
          antiRecurrenceComplement a ((n + 1) * a.length) =
            antiRecurrenceComplement a (n * a.length + 1) + (a.length - 1)) →
        antiRecurrence a n + a.length * a.sum < antiRecurrence a (n + 1)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_sub_one]
  let B (p j : ℕ) := antiRecurrenceComplement a (p * a.length + j + 1)
  have hsum (p : ℕ) : antiRecurrence a (p + 1) = ∑ j : Fin a.length, a[j] * B p j :=
    weighted_sum a p
  have htrace : (∑ j : Fin a.length, a[j]) = a.sum := by
    simp only [Fin.getElem_fin, ← List.sum_ofFn, List.ofFn_getElem]
  have hbase : antiRecurrence a (r + 1) + a.length * a.sum =
      ∑ j : Fin a.length, a[j] * (B r j + a.length) := by
    simp only [Nat.mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, htrace, ← hsum,
      Nat.mul_comm a.length a.sum]
  have hterm (j : Fin a.length) : a[j] * (B r j + a.length) ≤ a[j] * B (r + 1) j :=
    Nat.mul_le_mul_left _ (entry_spacing a r j j.isLt)
  have hle : antiRecurrence a (r + 1) + a.length * a.sum ≤ antiRecurrence a (r + 1 + 1) := by
    rw [hbase, hsum]
    exact Finset.sum_le_sum fun j _ => hterm j
  have heq : antiRecurrence a (r + 1) + a.length * a.sum = antiRecurrence a (r + 1 + 1) ↔
      ∀ j : Fin a.length, B r j + a.length = B (r + 1) j := by
    rw [hbase, hsum, Finset.sum_eq_sum_iff_of_le (fun j _ => hterm j)]
    simp [Nat.mul_right_inj (Nat.ne_of_gt (ha _ (List.getElem_mem ..)))]
  refine ⟨hle, ?_, ?_⟩
  · intro h
    apply Eq.symm
    apply heq.mpr
    intro j
    have hj := j.isLt
    dsimp [B]
    rw [Nat.succ_mul, Nat.add_assoc (r * a.length) a.length j.val,
      h (a.length + j.val) (by omega), h j.val (by omega)]
    omega
  · intro hdiff
    refine lt_of_le_of_ne hle fun h => hdiff ?_
    have hfirst : B r 0 + a.length = B (r + 1) 0 := heq.mp h ⟨0, by omega⟩
    have hlast : B r (a.length - 1) + a.length = B (r + 1) (a.length - 1) :=
      heq.mp h ⟨a.length - 1, by omega⟩
    have hend (p : ℕ) : antiRecurrenceComplement a ((p + 1) * a.length) = B p (a.length - 1) := by
      apply congrArg (antiRecurrenceComplement a)
      rw [Nat.succ_mul]
      omega
    rw [hend r, hend (r + 1)]
    change (B r (a.length - 1) = B r 0 + (a.length - 1) ↔
      B (r + 1) (a.length - 1) = B (r + 1) 0 + (a.length - 1))
    omega

end

end MetaMathlibExt
