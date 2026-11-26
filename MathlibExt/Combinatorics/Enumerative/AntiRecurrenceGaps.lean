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
import Mathlib.Tactic.Ring

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

namespace AntiRecurrenceGaps

variable {a : List ℕ}

private abbrev capacity (a : List ℕ) : ℕ := a.length * a.sum
private abbrev width (a : List ℕ) : ℕ := capacity a + 1

private theorem trace_eq (a : List ℕ) : (∑ j : Fin a.length, a[j]) = a.sum := by
  simp only [Fin.getElem_fin, ← List.sum_ofFn, List.ofFn_getElem]

private theorem length_le_trace (ha : ∀ x ∈ a, 0 < x) : a.length ≤ a.sum := by
  rw [← trace_eq]
  calc
    a.length = ∑ _j : Fin a.length, (1 : ℕ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun j _ => ha _ (List.getElem_mem j.isLt)

private theorem range_weighted_sum (a : List ℕ) (m : ℕ) (f : ℕ → ℕ) :
    (List.zipWith (· * ·) a ((List.range' m a.length).map f)).sum =
      ∑ j : Fin a.length, a[j] * f (m + j) := by
  have h : List.zipWith (· * ·) a ((List.range' m a.length).map f) =
      List.ofFn (fun j : Fin a.length => a[j] * f (m + j)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [List.getElem_zipWith, List.getElem_range']
  rw [h, List.sum_ofFn]

private theorem mex_eq {s : Finset ℕ} {x : ℕ} (hx : 0 < x) (hnot : x ∉ s)
    (hsmall : ∀ y, 0 < y → y < x → y ∈ s) : antiTribonacciMex s = x := by
  refine le_antisymm (antiTribonacciMex_le_of_notMem _ hx hnot) ?_
  by_contra! h
  exact antiTribonacciMex_notMem s (hsmall _ (antiTribonacciMex_pos s) h)

private theorem initial_block (l m : ℕ) :
    antiRecurrenceBlock l (Finset.Icc 1 m) = List.range' (m + 1) l := by
  induction l generalizing m with
  | zero => rfl
  | succ l ih =>
    have hm : antiTribonacciMex (Finset.Icc 1 m) = m + 1 := by
      apply mex_eq (by omega) (by simp)
      intro y hy h
      rw [Finset.mem_Icc]
      omega
    have hs : insert (m + 1) (Finset.Icc 1 m) = Finset.Icc 1 (m + 1) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [antiRecurrenceBlock, hm, hs, ih, List.range'_succ]

private def firstSum (a : List ℕ) : ℕ := ∑ j : Fin a.length, a[j] * ((j : ℕ) + 1)

private theorem firstSum_eq (a : List ℕ) : antiRecurrence a 1 = firstSum a := by
  have h : (antiRecurrenceState a 1).1 = List.range' 1 a.length := by
    change antiRecurrenceBlock a.length ∅ = _
    have he : Finset.Icc 1 (0 : ℕ) = ∅ := by simp
    simpa only [he, Nat.zero_add] using initial_block a.length 0
  unfold antiRecurrence firstSum
  rw [h, ← List.map_id (List.range' 1 a.length), range_weighted_sum]
  simp [Nat.add_comm]

private theorem firstSum_ge (ha : ∀ x ∈ a, 0 < x) (hk : 1 < a.length) :
    a.sum + (a.length - 1) ≤ firstSum a := by
  let j : Fin a.length := ⟨a.length - 1, by omega⟩
  have hj : 0 < a[j] := ha _ (List.getElem_mem j.isLt)
  have hle : a.length - 1 ≤ a[j] * (j : ℕ) := by
    simpa [j] using Nat.mul_le_mul_right (j : ℕ) hj
  have hs : a[j] * (j : ℕ) ≤ ∑ i : Fin a.length, a[i] * (i : ℕ) :=
    Finset.single_le_sum (f := fun i : Fin a.length => a[i] * (i : ℕ))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  simp only [firstSum, Nat.mul_add, Nat.mul_one, Finset.sum_add_distrib, trace_eq]
  omega

-- The hole shifts each subsequent entry of the block by one. The weighted correction is the
-- sum of the coefficients of those shifted entries.
private def correction (a : List ℕ) (u h : ℕ) : ℕ :=
  ∑ j : Fin a.length, a[j] * (if h ≤ u * a.length + j + 1 then 1 else 0)

private theorem correction_le (a : List ℕ) (u h : ℕ) : correction a u h ≤ a.sum := by
  rw [← trace_eq]
  apply Finset.sum_le_sum
  intro j _
  split <;> simp

private theorem correction_zero {h : ℕ} (hh : a.length < h) : correction a 0 h = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hj := j.isLt
  simp [Nat.not_le.mpr (show (j : ℕ) + 1 < h by omega)]

-- An offset is one-based within its interval. Block t belongs to interval t / τ, which is
-- already determined when t > 0. The increase over κ * t is the first sum, minus the block's
-- index in its interval, plus the correction from that earlier interval's hole.
private def hole (a : List ℕ) (hτ : 1 < a.sum) (t : ℕ) : ℕ :=
  if _ht : t = 0 then firstSum a
  else firstSum a + correction a (t % a.sum) (hole a hτ (t / a.sum)) - t % a.sum
termination_by t
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero _ht) hτ

private theorem next_hole_bounds (ha : ∀ x ∈ a, 0 < x) (hk : 1 < a.length)
    (hτ : 1 < a.sum) {u h : ℕ} (hu : u < a.sum) (hlo : a.length + 1 ≤ h)
    (hhi : h ≤ firstSum a + a.sum - 1) :
    a.length + 1 ≤ firstSum a + correction a u h - u ∧
      firstSum a + correction a u h - u ≤ firstSum a + a.sum - 1 := by
  have hbase := firstSum_ge ha hk
  refine ⟨?_, ?_⟩
  · by_cases hsafe : a.sum + a.length ≤ firstSum a ∨ u + 1 < a.sum
    · rcases hsafe with hsafe | hsafe <;> omega
    · -- At the lower boundary the last entry must be shifted in the last block.
      have he : firstSum a = a.sum + (a.length - 1) := by omega
      have hu' : u + 1 = a.sum := by omega
      have hcap : 2 * a.sum + a.length - 2 ≤ capacity a := by
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show 2 ≤ a.length by omega)
        have hmul := Nat.mul_le_mul_left d (show 1 ≤ a.sum by omega)
        simpa only [capacity, hd, Nat.add_mul, Nat.mul_one] using
          (show 2 * a.sum + (2 + d) - 2 ≤ (2 + d) * a.sum by rw [Nat.add_mul]; omega)
      let j : Fin a.length := ⟨a.length - 1, by omega⟩
      have hj : u * a.length + (j : ℕ) + 1 = capacity a := by
        have hh := congrArg (· * a.length) hu'
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm a.sum] at hh
        dsimp [j, capacity]
        omega
      have hshift : h ≤ u * a.length + (j : ℕ) + 1 := by omega
      have hterm : a[j] ≤ correction a u h := by
        have hs : a[j] * (if h ≤ u * a.length + j + 1 then 1 else 0) ≤ correction a u h := by
          unfold correction
          exact Finset.single_le_sum
            (f := fun i : Fin a.length => a[i] * (if h ≤ u * a.length + i + 1 then 1 else 0))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        simpa only [ite_eq_left hshift, Nat.mul_one] using hs
      have hp : 0 < a[j] := ha _ (List.getElem_mem j.isLt)
      omega
  · by_cases hu0 : u = 0
    · subst u
      rw [correction_zero (by omega : a.length < h)]
      omega
    · have := correction_le a u h
      omega

private theorem hole_bounds (ha : ∀ x ∈ a, 0 < x) (hk : 1 < a.length) (hτ : 1 < a.sum)
    (t : ℕ) : a.length + 1 ≤ hole a hτ t ∧ hole a hτ t ≤ firstSum a + a.sum - 1 := by
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    rw [hole]
    split
    · have := firstSum_ge ha hk
      omega
    · obtain ⟨hl, hr⟩ := ih (t / a.sum) (Nat.div_lt_self (by omega) hτ)
      exact next_hole_bounds ha hk hτ (Nat.mod_lt _ (by omega)) hl hr

private theorem hole_le_width {h : ℕ} (hb : firstSum a ≤ (a.length - 1) * a.sum + 2)
    (hh : h ≤ firstSum a + a.sum - 1) : h ≤ width a := by
  have hc : (a.length - 1) * a.sum + a.sum = capacity a := by
    by_cases hk : a.length = 0
    · have hn : a = [] := List.length_eq_zero_iff.mp hk
      simp [hn]
    · have he := congrArg (· * a.sum) (show a.length - 1 + 1 = a.length by omega)
      simpa only [Nat.add_mul, Nat.one_mul] using he
  unfold width
  omega

private theorem hole_step (ha : ∀ x ∈ a, 0 < x) (hk : 1 < a.length) (hτ : 1 < a.sum)
    (t : ℕ) : hole a hτ t + t % a.sum =
      firstSum a + correction a (t % a.sum) (hole a hτ (t / a.sum)) := by
  by_cases ht : t = 0
  · subst t
    have hl := (hole_bounds ha hk hτ 0).1
    simp only [Nat.zero_mod, Nat.zero_div, Nat.add_zero,
      correction_zero (by omega : a.length < hole a hτ 0)]
    rw [hole.eq_def]
    simp
  · have hu := Nat.mod_lt t (show 0 < a.sum by omega)
    have hf := firstSum_ge ha hk
    rw [hole.eq_def a hτ t, dite_eq_right ht]
    omega

private theorem capacity_pos (hk : 1 < a.length) (hτ : 1 < a.sum) : 0 < capacity a :=
  Nat.mul_pos (by omega) (by omega)

private def total (a : List ℕ) (hτ : 1 < a.sum) (t : ℕ) : ℕ := width a * t + hole a hτ t

-- Entry m has zero-based rank m among the complement numbers, and one-based offset
-- m % (kτ) + 1 before accounting for the hole.
private def entry (a : List ℕ) (hτ : 1 < a.sum) (m : ℕ) : ℕ :=
  let q := m / capacity a
  let s := m % capacity a + 1
  width a * q + s + if hole a hτ q ≤ s then 1 else 0

private theorem entry_at (hk : 1 < a.length) (hτ : 1 < a.sum) (q : ℕ) {s : ℕ}
    (hs : s < capacity a) : entry a hτ (capacity a * q + s) =
      width a * q + (s + 1) + if hole a hτ q ≤ s + 1 then 1 else 0 := by
  simp [entry, Nat.mul_add_div (capacity_pos hk hτ), Nat.div_eq_of_lt hs, Nat.mod_eq_of_lt hs]

private theorem entry_bounds (hk : 1 < a.length) (hτ : 1 < a.sum) (m : ℕ) :
    width a * (m / capacity a) < entry a hτ m ∧
      entry a hτ m ≤ width a * (m / capacity a) + width a := by
  have hs := Nat.mod_lt m (capacity_pos hk hτ)
  dsimp [entry, width]
  split <;> omega

private theorem entry_mono (hk : 1 < a.length) (hτ : 1 < a.sum) :
    StrictMono (entry a hτ) := by
  intro m n hmn
  have hq : m / capacity a ≤ n / capacity a := Nat.div_le_div_right hmn.le
  by_cases he : m / capacity a = n / capacity a
  · have hm := Nat.div_add_mod m (capacity a)
    have hn := Nat.div_add_mod n (capacity a)
    rw [he] at hm
    simp only [entry, he]
    split_ifs <;> omega
  · have h := Nat.mul_le_mul_left (width a)
      (show m / capacity a + 1 ≤ n / capacity a by omega)
    rw [Nat.mul_succ] at h
    have hm := (entry_bounds hk hτ m).2
    have hn := (entry_bounds hk hτ n).1
    omega

private theorem total_mono (ha : ∀ x ∈ a, 0 < x) (hk : 1 < a.length)
    (hb : firstSum a ≤ (a.length - 1) * a.sum + 2) (hτ : 1 < a.sum) :
    StrictMono (total a hτ) := by
  apply strictMono_nat_of_lt_succ
  intro t
  have hh := hole_le_width hb (hole_bounds ha hk hτ t).2
  have hh' := (hole_bounds ha hk hτ (t + 1)).1
  simp only [total, Nat.mul_succ]
  omega

private theorem entry_ne_total (ha : ∀ x ∈ a, 0 < x) (hk : 1 < a.length)
    (hb : firstSum a ≤ (a.length - 1) * a.sum + 2) (hτ : 1 < a.sum) (m t : ℕ) :
    entry a hτ m ≠ total a hτ t := by
  have he := entry_bounds hk hτ m
  obtain ⟨hl, hr⟩ := hole_bounds ha hk hτ t
  have hu := hole_le_width hb hr
  rcases lt_trichotomy (m / capacity a) t with h | h | h
  · have h' := Nat.mul_le_mul_left (width a) (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at h'
    unfold total
    omega
  · simp only [entry, h, total]
    split <;> omega
  · have h' := Nat.mul_le_mul_left (width a) (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at h'
    unfold total
    omega

private theorem covers (ha : ∀ x ∈ a, 0 < x) (hk : 1 < a.length)
    (hb : firstSum a ≤ (a.length - 1) * a.sum + 2) (hτ : 1 < a.sum) {x : ℕ}
    (hx : 0 < x) : (∃ t, total a hτ t = x) ∨ ∃ m, entry a hτ m = x := by
  let q := (x - 1) / width a
  let s := (x - 1) % width a
  have hs : s < capacity a + 1 := Nat.mod_lt _ (Nat.succ_pos _)
  have hxs : width a * q + s = x - 1 := Nat.div_add_mod _ _
  have hh : hole a hτ q ≤ capacity a + 1 := hole_le_width hb (hole_bounds ha hk hτ q).2
  rcases lt_trichotomy (s + 1) (hole a hτ q) with h | h | h
  · right
    have hs' : s < capacity a := by omega
    refine ⟨capacity a * q + s, ?_⟩
    rw [entry_at hk hτ q hs', ite_eq_right (not_le_of_gt h)]
    omega
  · left
    exact ⟨q, by unfold total; omega⟩
  · right
    have hc := capacity_pos hk hτ
    have hl := (hole_bounds ha hk hτ q).1
    have hs' : s - 1 < capacity a := by omega
    have he : s - 1 + 1 = s := by omega
    refine ⟨capacity a * q + (s - 1), ?_⟩
    rw [entry_at hk hτ q hs', he, ite_eq_left (by omega)]
    omega

-- Grouping the complement entries into blocks, the q-th interval supplies the blocks with
-- indices qτ, …, qτ + τ − 1. The weighted sum of block t is κt plus its prescribed offset.
private theorem block_sum (ha : ∀ x ∈ a, 0 < x) (hk : 1 < a.length) (hτ : 1 < a.sum)
    (t : ℕ) : (∑ j : Fin a.length, a[j] * entry a hτ (a.length * t + j)) = total a hτ t := by
  let q := t / a.sum
  let u := t % a.sum
  have hqu : a.sum * q + u = t := Nat.div_add_mod _ _
  have hu : u < a.sum := Nat.mod_lt _ (by omega)
  have hentry (j : Fin a.length) : entry a hτ (a.length * t + j) =
      (width a * q + u * a.length) + ((j : ℕ) + 1) +
        if hole a hτ q ≤ u * a.length + j + 1 then 1 else 0 := by
    have he : a.length * t + (j : ℕ) = capacity a * q + (u * a.length + j) := by
      rw [← hqu]
      unfold capacity
      ring
    have hs : u * a.length + (j : ℕ) < capacity a := by
      have hj := j.isLt
      have hm := Nat.mul_le_mul_right a.length (Nat.succ_le_of_lt hu)
      rw [Nat.succ_mul, Nat.mul_comm a.sum] at hm
      unfold capacity
      omega
    rw [he, entry_at hk hτ q hs, Nat.add_assoc (u * a.length) (j : ℕ) 1]
    ac_rfl
  rw [Finset.sum_congr rfl (fun j _ => congrArg (a[j] * ·) (hentry j))]
  have hsum (b : ℕ) :
      (∑ j : Fin a.length, a[j] * (b + ((j : ℕ) + 1) +
        if hole a hτ q ≤ u * a.length + j + 1 then 1 else 0)) =
        a.sum * b + firstSum a + correction a u (hole a hτ q) := by
    unfold firstSum correction
    simp only [Nat.mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, trace_eq]
  rw [hsum]
  have hscale : a.sum * (width a * q + u * a.length) + u = width a * t := by
    rw [← hqu]
    unfold width capacity
    ring
  have hstep := hole_step ha hk hτ t
  change hole a hτ t + u = firstSum a + correction a u (hole a hτ q) at hstep
  unfold total
  omega

-- The state after t sums and m entries have been inserted. During a block only m changes.
private def used (a : List ℕ) (hτ : 1 < a.sum) (t m x : ℕ) : Prop :=
  (∃ u < t, total a hτ u = x) ∨ ∃ v < m, entry a hτ v = x

private theorem next_mex (ha : ∀ x ∈ a, 0 < x) (hk : 1 < a.length)
    (hb : firstSum a ≤ (a.length - 1) * a.sum + 2) (hτ : 1 < a.sum) {t m : ℕ}
    {s : Finset ℕ} (hs : ∀ x, x ∈ s ↔ used a hτ t m x)
    (hm : entry a hτ m ≤ total a hτ t) : antiTribonacciMex s = entry a hτ m := by
  have hp := (entry_bounds hk hτ m).1
  apply mex_eq (by omega)
  · intro hx
    rcases (hs _).mp hx with ⟨u, _, hu⟩ | ⟨v, hv, he⟩
    · exact entry_ne_total ha hk hb hτ m u hu.symm
    · exact (entry_mono hk hτ hv).ne he
  · intro x hx hlt
    apply (hs _).mpr
    rcases covers ha hk hb hτ hx with ⟨u, hu⟩ | ⟨v, hv⟩
    · exact Or.inl ⟨u, (total_mono ha hk hb hτ).lt_iff_lt.mp (by omega), hu⟩
    · exact Or.inr ⟨v, (entry_mono hk hτ).lt_iff_lt.mp (by omega), hv⟩

private theorem mex_block (ha : ∀ x ∈ a, 0 < x) (hk : 1 < a.length)
    (hb : firstSum a ≤ (a.length - 1) * a.sum + 2) (hτ : 1 < a.sum) (l : ℕ) {m t : ℕ}
    {s : Finset ℕ} (hs : ∀ x, x ∈ s ↔ used a hτ t m x)
    (hm : ∀ v ∈ List.range' m l, entry a hτ v ≤ total a hτ t) :
    antiRecurrenceBlock l s = (List.range' m l).map (entry a hτ) := by
  induction l generalizing m s with
  | zero => rfl
  | succ l ih =>
    rw [List.range'_succ] at hm ⊢
    have hmex := next_mex ha hk hb hτ hs (hm m (by simp))
    simp only [antiRecurrenceBlock, hmex, List.map_cons, List.cons.injEq, true_and]
    apply ih (hm := fun v hv => hm v (List.mem_cons_of_mem _ hv))
    intro x
    rw [Finset.mem_insert, hs]
    unfold used
    constructor
    · rintro (rfl | h | ⟨v, hv, he⟩)
      · exact Or.inr ⟨m, by omega, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨v, by omega, he⟩
    · rintro (h | ⟨v, hv, he⟩)
      · exact Or.inr (Or.inl h)
      · rcases Nat.lt_or_eq_of_le (show v ≤ m by omega) with hv | rfl
        · exact Or.inr (Or.inr ⟨v, hv, he⟩)
        · exact Or.inl he.symm

private theorem next_block (ha : ∀ x ∈ a, 0 < x) (hk : 1 < a.length)
    (hb : firstSum a ≤ (a.length - 1) * a.sum + 2) (hτ : 1 < a.sum) {t : ℕ}
    {s : Finset ℕ} (hs : ∀ x, x ∈ s ↔ used a hτ t (a.length * t) x) :
    antiRecurrenceBlock a.length s = (List.range' (a.length * t) a.length).map (entry a hτ) := by
  apply mex_block ha hk hb hτ _ hs
  intro v hv
  obtain ⟨hl, hr⟩ := List.mem_range'_1.mp hv
  let j : Fin a.length := ⟨v - a.length * t, by omega⟩
  have he : a.length * t + (j : ℕ) = v := by dsimp [j]; omega
  rw [← block_sum ha hk hτ t, ← he]
  calc
    _ ≤ a[j] * entry a hτ (a.length * t + j) := by
      simpa using Nat.mul_le_mul_right (entry a hτ (a.length * t + j))
        (ha _ (List.getElem_mem j.isLt))
    _ ≤ _ := Finset.single_le_sum
      (f := fun i : Fin a.length => a[i] * entry a hτ (a.length * t + i))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

private theorem state_spec (ha : ∀ x ∈ a, 0 < x) (hk : 1 < a.length)
    (hb : firstSum a ≤ (a.length - 1) * a.sum + 2) (hτ : 1 < a.sum) (t x : ℕ) :
    x ∈ (antiRecurrenceState a t).2 ↔ used a hτ t (a.length * t) x := by
  induction t generalizing x with
  | zero => simp [antiRecurrenceState, used]
  | succ t ih =>
    simp only [antiRecurrenceState, next_block ha hk hb hτ ih, range_weighted_sum,
      block_sum ha hk hτ, Finset.mem_insert, Finset.mem_union, List.mem_toFinset, ih,
      Nat.mul_succ, List.mem_map, List.mem_range'_1, used]
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
      · by_cases hv' : v < a.length * t
        · exact Or.inr (Or.inl (Or.inr ⟨v, hv', he⟩))
        · exact Or.inr (Or.inr ⟨v, ⟨by omega, hv⟩, he⟩)

private theorem actual_block (ha : ∀ x ∈ a, 0 < x) (hk : 1 < a.length)
    (hb : firstSum a ≤ (a.length - 1) * a.sum + 2) (hτ : 1 < a.sum) (t : ℕ) :
    (antiRecurrenceState a (t + 1)).1 = (List.range' (a.length * t) a.length).map (entry a hτ) :=
  next_block ha hk hb hτ (state_spec ha hk hb hτ t)

private theorem complement_eq_entry (ha : ∀ x ∈ a, 0 < x) (hk : 1 < a.length)
    (hb : firstSum a ≤ (a.length - 1) * a.sum + 2) (hτ : 1 < a.sum) (m : ℕ) :
    antiRecurrenceComplement a (m + 1) = entry a hτ m := by
  have h := Nat.mod_lt m (show 0 < a.length by omega)
  have he := Nat.div_add_mod m a.length
  have hlen : m % a.length <
      ((List.range' (a.length * (m / a.length)) a.length).map (entry a hτ)).length := by simpa
  simp only [antiRecurrenceComplement, Nat.add_one_sub_one, actual_block ha hk hb hτ,
    List.getD_eq_getElem _ _ hlen, List.getElem_map, List.getElem_range', Nat.one_mul, he]

end AntiRecurrenceGaps

open AntiRecurrenceGaps in
/-- **Interval location of anti-recurrence numbers for bounded forms.** Let
$a = (a_1, \dots, a_k)$ be a linear form with positive integer coefficients and $k > 1$, of trace
$\tau = a_1 + \dots + a_k$, with anti-recurrence numbers $A_1, A_2, \dots$ and non-anti-recurrence
numbers $B_1, B_2, \dots$, and let $\kappa = k\tau + 1$. Suppose that $a$ is $A_1$-bounded, that
is, $A_1 \le (k - 1)\tau + 2$. Then for every $n \ge 1$, $A_n$ lies in the interval
$I_n = [\kappa(n - 1) + 1, \kappa n]$, and the first $k$ numbers of $I_n$ are non-anti-recurrence
numbers: $B_{(n-1)k\tau + j} = \kappa(n - 1) + j$ for $1 \le j \le k$.

Source: Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026),
Article A24, Lemma 5 (`integers-2026-A24-lem-5`). -/
public theorem antiRecurrence_mem_Icc_of_bounded (a : List ℕ) (ha : ∀ x ∈ a, 0 < x)
    (hk : 1 < a.length) (hb : antiRecurrence a 1 ≤ (a.length - 1) * a.sum + 2) {n : ℕ}
    (hn : 1 ≤ n) :
    antiRecurrence a n ∈
        Finset.Icc ((a.length * a.sum + 1) * (n - 1) + 1) ((a.length * a.sum + 1) * n) ∧
      ∀ j < a.length, antiRecurrenceComplement a ((n - 1) * a.length * a.sum + j + 1) =
        (a.length * a.sum + 1) * (n - 1) + j + 1 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hτ : 1 < a.sum := lt_of_lt_of_le hk (length_le_trace ha)
  have hb' : firstSum a ≤ (a.length - 1) * a.sum + 2 := firstSum_eq a ▸ hb
  have hA : antiRecurrence a (t + 1) = total a hτ t := by
    rw [antiRecurrence, actual_block ha hk hb' hτ, range_weighted_sum, block_sum ha hk hτ]
  obtain ⟨hlo, hhi⟩ := hole_bounds ha hk hτ t
  have hupper := hole_le_width hb' hhi
  simp only [Nat.succ_sub_one]
  constructor
  · rw [hA, Finset.mem_Icc]
    change width a * t + 1 ≤ width a * t + hole a hτ t ∧
      width a * t + hole a hτ t ≤ width a * (t + 1)
    rw [Nat.mul_succ]
    omega
  · intro j hj
    have hindex : t * a.length * a.sum + j = capacity a * t + j := by
      unfold capacity
      ring
    have hmul : a.length ≤ capacity a := by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left a.length (show 1 ≤ a.sum by omega)
    have hj' : j < capacity a := lt_of_lt_of_le hj hmul
    rw [complement_eq_entry ha hk hb' hτ, hindex, entry_at hk hτ t hj', ite_eq_right (by omega),
      Nat.add_zero, Nat.mul_comm (width a), Nat.add_assoc]

end

end MetaMathlibExt
