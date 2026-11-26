/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`SqueezeBench/Problems/Golomb/Def.lean` and `SqueezeBench/Problems/Golomb/README.md`
(leansolving/SqueezeBench, commit e2e19eef093a77882da57f348def029533ec2d5e).
Copyright the SqueezeBench contributors.
Authors: P. Manrique, H. Xia, S. Szeider.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
SqueezeBench ships no NOTICE file.

The adapted portions are `golombRulerLengths`, `optimalGolombLength`, and the
table of values in the statement of `optimalGolombLength_three_to_eleven`. The
definitions rename SqueezeBench's `RulerLengths` and `f`, use `Set.IsSidon` on
the coerced set, and inline the minimum mark count. The table was stated in
`WantedExt/Combinatorics/GolombRulersWanted.lean` and is proved here.
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.Additive.Sidon
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.IntervalCases

/-!
# Optimal Golomb rulers with 3 to 11 marks

We prove the exact optimal lengths using explicit rulers and a finite search.
The search translates the first mark to zero and reflects the ruler when needed
so that its middle mark lies in the first half. It places marks in increasing order,
using bit masks to exclude every gap that would repeat a difference. One search
per mark count covers all spans below the proposed optimum.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.GolombRulersWanted

open Finset

/-- **Golomb ruler lengths.** For a natural number $m$, the set of Golomb ruler lengths with $m$
marks consists of the natural numbers $L$ for which there is a finite Sidon set $S$ of natural
numbers with $S \subseteq \{0, 1, \dots, L\}$, exactly $m$ elements, and $L \in S$. A mark at
$0$ is not required.

For finite sets of integers the Sidon condition is equivalent to all positive pairwise
differences being distinct. -/
def golombRulerLengths (m : ℕ) : Set ℕ :=
  {L | ∃ S : Finset ℕ, S ⊆ range (L + 1) ∧ S.card = m ∧ (S : Set ℕ).IsSidon ∧ L ∈ S}

/-- **Optimal Golomb ruler length.** For $m \ge 1$, the optimal Golomb ruler length $G(m)$ is
the infimum in $\mathbb{N}$ of the set of Golomb ruler lengths with $m$ marks, that is, of the
natural numbers $L$ such that some $m$-element Sidon set of natural numbers contained in
$\{0, 1, \dots, L\}$ contains $L$; for $m = 0$ we set $G(0) = 0$.

For $m \ge 2$ this is OEIS A003022, the length of a shortest Golomb ruler with $m$ marks. -/
noncomputable def optimalGolombLength (m : ℕ) : ℕ :=
  if m < 1 then 0 else sInf (golombRulerLengths m)

/-! ### Ordered rulers and bounds on intervals of marks -/

/-- The first `n` entries list increasing marks with distinct positive differences. -/
private structure Ruler (n : ℕ) (a : ℕ → ℕ) : Prop where
  mono : ∀ ⦃i j⦄, i < j → j < n → a i < a j
  diff : ∀ ⦃i j u v⦄, i < j → j < n → u < v → v < n →
    a j - a i = a v - a u → i = u ∧ j = v

private theorem Ruler.le {n a} (h : Ruler n a) {i j : ℕ} (hij : i ≤ j) (hj : j < n) :
    a i ≤ a j :=
  hij.eq_or_lt.elim (fun e => e ▸ le_rfl) (fun e => (h.mono e hj).le)

private theorem Ruler.interval {n a} (h : Ruler n a) {i j : ℕ} (hij : i ≤ j) (hj : j < n) :
    Ruler (j + 1 - i) (fun k => a (i + k)) where
  mono _ _ hk hl := h.mono (by omega) (by omega)
  diff _ _ _ _ hk hl hu hv hd := by
    obtain ⟨e₁, e₂⟩ := h.diff (by omega) (by omega) (by omega) (by omega) hd
    exact ⟨by omega, by omega⟩

/-- Translation by the first mark, optionally followed by reflection in the endpoints. -/
private def normalizedMark (n : ℕ) (a : ℕ → ℕ) (reflect : Bool) (i : ℕ) : ℕ :=
  if reflect then a (n - 1) - a (n - 1 - i) else a i - a 0

private theorem Ruler.normalize {n a} (h : Ruler n a) (reflect : Bool) :
    Ruler n (normalizedMark n a reflect) := by
  cases reflect
  · have hnonneg (i : ℕ) (hi : i < n) := h.le (Nat.zero_le i) hi
    refine ⟨?_, ?_⟩
    · intro i j hij hj
      simp only [normalizedMark, Bool.false_eq_true, ↓reduceIte]
      have := h.mono hij hj
      have := hnonneg i (by omega)
      omega
    · intro i j u v hij hj huv hv e
      simp only [normalizedMark, Bool.false_eq_true, ↓reduceIte] at e
      have := hnonneg i (by omega)
      have := hnonneg u (by omega)
      exact h.diff hij hj huv hv (by omega)
  · have hb (i : ℕ) (hi : i < n) : a (n - 1 - i) ≤ a (n - 1) :=
      h.le (by omega) (by omega)
    refine ⟨?_, ?_⟩
    · intro i j hij hj
      simp only [normalizedMark, ↓reduceIte]
      have hs : a (n - 1 - j) < a (n - 1 - i) := h.mono (by omega) (by omega)
      have := hb i (by omega)
      omega
    · intro i j u v hij hj huv hv e
      simp only [normalizedMark, ↓reduceIte] at e
      have := hb j hj
      have := hb i (by omega)
      have := hb v hv
      have := hb u (by omega)
      have hd : a (n - 1 - i) - a (n - 1 - j) =
          a (n - 1 - u) - a (n - 1 - v) := by omega
      obtain ⟨e₁, e₂⟩ := h.diff (by omega) (by omega) (by omega) (by omega) hd
      exact ⟨by omega, by omega⟩

/-- One orientation places the lower middle mark in the first half of the ruler. -/
private theorem Ruler.orient {n a} (h : Ruler n a) (hn : 3 ≤ n) :
    ∃ b, Ruler n b ∧ b 0 = 0 ∧ b (n - 1) = a (n - 1) - a 0 ∧
      b ((n - 1) / 2) ≤ b (n - 1) / 2 := by
  let m := (n - 1) / 2
  have hm : a m ≤ a (n - 1 - m) := h.le (by dsimp [m]; omega) (by omega)
  have h₀ := h.le (i := 0) (j := m) (by omega) (by dsimp [m]; omega)
  by_cases hf : a m - a 0 ≤ (a (n - 1) - a 0) / 2
  · exact ⟨_, h.normalize false, by simp [normalizedMark], by simp [normalizedMark],
      by simpa [normalizedMark, m] using hf⟩
  · refine ⟨_, h.normalize true, by simp [normalizedMark], by simp [normalizedMark], ?_⟩
    simp only [normalizedMark, ↓reduceIte, Nat.sub_self]
    change a (n - 1) - a (n - 1 - m) ≤ (a (n - 1) - a 0) / 2
    omega

/-- A bound valid for the span of every ruler with the given number of marks. -/
private def LowerBound (n l : ℕ) : Prop :=
  ∀ a : ℕ → ℕ, Ruler n a → l ≤ a (n - 1) - a 0

private theorem LowerBound.span {n l N a i j} (hb : LowerBound n l) (h : Ruler N a)
    (hij : i ≤ j) (hj : j < N) (hn : n = j + 1 - i) : l ≤ a j - a i := by
  subst n
  have hs := hb _ (h.interval hij hj)
  simpa [show i + (j + 1 - i - 1) = j by omega] using hs

/-- Candidate lower bounds, checked successively in order of the number of marks. -/
private def bounds : List ℕ := [0, 0, 1, 3, 6, 11, 17, 25, 34, 44, 55, 72]

/-! ### Pruning by the sum of unused gaps -/

/-- The sum of the `k` smallest unblocked numbers starting at `i`. Bit zero
of `d` represents `i`. After `fuel` numbers, all remaining numbers are
optimistically taken to be `i + fuel`. -/
private def sumFree (d : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, k, i => Nat.mul k i
  | fuel + 1, k, i =>
    cond (Nat.beq k 0) 0
      (cond (Nat.beq (Nat.land d 1) 0)
        (Nat.add i (sumFree (Nat.shiftRight d 1) fuel (Nat.sub k 1) (Nat.succ i)))
        (sumFree (Nat.shiftRight d 1) fuel k (Nat.succ i)))

private theorem land_eq_zero_iff {d e : ℕ} :
    d &&& e = 0 ↔ ∀ k, d.testBit k = true → e.testBit k = false := by
  constructor
  · intro h k hd
    have := congrArg (fun n => Nat.testBit n k) h
    simpa [Nat.testBit_land, hd] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    cases hd : d.testBit k <;> simp [hd, h]

private theorem sumFree_le_sum (fuel d i : ℕ) (S : Finset ℕ)
    (hS : ∀ x ∈ S, i ≤ x ∧ d.testBit (x - i) = false) :
    sumFree d fuel S.card i ≤ ∑ x ∈ S, x := by
  induction fuel generalizing d i S with
  | zero =>
    simpa [sumFree, Nat.mul_comm] using
      (Finset.sum_le_sum (s := S) (f := fun _ => i) (g := id) fun x hx => (hS x hx).1)
  | succ fuel ih =>
    simp only [sumFree, Bool.cond_eq_ite, Nat.beq_eq]
    by_cases hcard : S.card = 0
    · simp [hcard]
    rw [ite_eq_right hcard]
    by_cases hbit : Nat.land d 1 = 0
    · rw [ite_eq_left hbit]
      obtain ⟨x, hx, hmin⟩ : ∃ x ∈ S, ∀ y ∈ S, y ≠ x → i < y := by
        by_cases hi : i ∈ S
        · exact ⟨i, hi, fun y hy hne => lt_of_le_of_ne (hS y hy).1 (Ne.symm hne)⟩
        · obtain ⟨x, hx⟩ := card_pos.mp (Nat.pos_of_ne_zero hcard)
          exact ⟨x, hx, fun y hy _ => lt_of_le_of_ne (hS y hy).1 (by
            intro e
            exact hi (e ▸ hy))⟩
      have hbound := ih (d >>> 1) (i + 1) (S.erase x) (by
        intro y hy
        obtain ⟨hne, hy⟩ := mem_erase.mp hy
        refine ⟨hmin y hy hne, ?_⟩
        rw [Nat.testBit_shiftRight, show 1 + (y - (i + 1)) = y - i by
          have := hmin y hy hne
          omega]
        exact (hS y hy).2)
      rw [card_erase_of_mem hx] at hbound
      have hsum := sum_erase_add (f := id) _ hx
      calc
        _ ≤ x + ∑ y ∈ S.erase x, y := Nat.add_le_add (hS x hx).1 hbound
        _ = _ := by simpa [Nat.add_comm] using hsum
    · rw [ite_eq_right hbit]
      apply ih
      intro y hy
      have hny : y ≠ i := by
        rintro rfl
        have hzero := (hS y hy).2
        rw [Nat.sub_self] at hzero
        apply hbit
        exact land_eq_zero_iff.mpr fun k hk => by
          have hne : k ≠ 0 := by rintro rfl; simp [hzero] at hk
          simpa using Nat.testBit_two_pow_of_ne (n := 0) (Ne.symm hne)
      have hlt := lt_of_le_of_ne (hS y hy).1 (Ne.symm hny)
      refine ⟨hlt, ?_⟩
      change (d >>> 1).testBit (y - (i + 1)) = false
      rw [Nat.testBit_shiftRight, show 1 + (y - (i + 1)) = y - i by omega]
      exact (hS y hy).2

private theorem Ruler.sum_gaps {n a} (h : Ruler n a) {i j : ℕ} (hij : i ≤ j) (hj : j < n) :
    ∑ k ∈ Ico i j, (a (k + 1) - a k) = a j - a i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show i + (k + 1) = i + k + 1 by omega, sum_Ico_succ_top (by omega),
      ih (by omega) (by omega)]
    have := h.le (show i ≤ i + k by omega) (by omega)
    have hs := h.mono (Nat.lt_succ_self (i + k)) (by omega)
    simp only [Nat.succ_eq_add_one] at hs
    omega

private theorem sumFree_le_span {n a i j d} (h : Ruler n a)
    (hij : i ≤ j) (hjn : j < n)
    (hd : ∀ t, d.testBit t = true → ∃ u v, u < v ∧ v < i ∧ t = a v - a u) :
    sumFree ((d >>> 1) % 256) 8 (j - i) 1 ≤ a j - a i := by
  let T := Ico i j
  let gap u := a (u + 1) - a u
  have hinj : (T : Set ℕ).InjOn gap := by
    intro u hu v hv he
    simp only [mem_coe, mem_Ico, T] at hu hv
    exact (h.diff (Nat.lt_succ_self u) (by omega) (Nat.lt_succ_self v) (by omega) he).1
  have hc : (T.image gap).card = j - i := by
    rw [card_image_of_injOn hinj, Nat.card_Ico]
  rw [← hc]
  refine (sumFree_le_sum _ _ _ _ ?_).trans_eq ?_
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
    obtain ⟨hiu, huj⟩ := mem_Ico.mp hu
    have hpos : 1 ≤ gap u := by
      have hs := h.mono (Nat.lt_succ_self u) (by omega)
      simp only [Nat.succ_eq_add_one] at hs
      dsimp [gap]
      omega
    refine ⟨hpos, ?_⟩
    change (((d >>> 1) % 2 ^ 8).testBit (gap u - 1)) = false
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, show 1 + (gap u - 1) = gap u by omega]
    cases hb : d.testBit (gap u)
    · simp
    obtain ⟨v, w, hvw, hw, he⟩ := hd _ hb
    have hwn : w < n := by omega
    have huv := (h.diff (Nat.lt_succ_self u) (by omega) hvw hwn he).1
    omega
  · rw [sum_image hinj, h.sum_gaps hij hjn]

/-! ### Searching all shorter spans together -/

/-- The byte indexed by the low eight difference bits bounds the span of the remaining gaps. -/
private def sumTable (k : ℕ) : ℕ :=
  (List.range 256).foldr (fun m t => Nat.lor (sumFree m 8 k 1) (Nat.shiftLeft t 8)) 0

private def gapBound (table d : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight table (Nat.mul 8 (Nat.mod (Nat.shiftRight d 1) 256))) 255

private theorem gapBound_eq {k : ℕ} (hk : k ≤ 10) (d : ℕ) :
    gapBound (sumTable k) d = sumFree ((d >>> 1) % 256) 8 k 1 := by
  have tables : ∀ k : Fin 11, ∀ m : Fin 256,
      Nat.land (Nat.shiftRight (sumTable k) (8 * m.val)) 255 = sumFree m 8 k 1 := by
    decide +kernel
  exact tables ⟨k, by omega⟩ ⟨_, Nat.mod_lt _ (by decide)⟩

/-- Each call tests the power of two for one available gap. Exhausting the fuel counts
as a possible completion, so a negative answer always covers every candidate. -/
private def anyBit (f : ℕ → Bool) (fuel : ℕ) : ℕ → Bool :=
  Nat.rec (fun _ => true) (fun _ rec m =>
    cond (Nat.beq m 0) false (
      let rest := Nat.land m (Nat.sub m 1)
      cond (f (Nat.xor m rest)) true (rec rest))) fuel

private theorem removed_bit {m j : ℕ} (hm : m.testBit j = true)
    (hr : (m &&& (m - 1)).testBit j = false) : m ^^^ (m &&& (m - 1)) = 2 ^ j := by
  induction m using Nat.binaryRec generalizing j with
  | zero => simp at hm
  | bit b m ih =>
    cases b
    · have hn : m ≠ 0 := by rintro rfl; simp at hm
      have he : Nat.bit false m - 1 = Nat.bit true (m - 1) := by
        simp only [Nat.bit_false, Nat.bit_true]; omega
      rw [he, Nat.land_bit] at hr ⊢
      cases j with
      | zero => simp at hm
      | succ j =>
        rw [Nat.testBit_bit_succ] at hm hr
        rw [Nat.xor_bit, ih hm hr]
        simp [pow_succ, Nat.mul_comm]
    · have he : Nat.bit true m - 1 = Nat.bit false m := by simp
      rw [he, Nat.land_bit] at hr ⊢
      cases j with
      | zero => rw [Nat.xor_bit]; simp
      | succ j =>
        rw [Nat.testBit_bit_succ] at hm hr
        simp [hm] at hr

private theorem anyBit_of {f : ℕ → Bool} {m j : ℕ} (fuel : ℕ)
    (hm : m.testBit j = true) (hf : f (2 ^ j) = true) : anyBit f fuel m = true := by
  induction fuel generalizing m with
  | zero => rfl
  | succ k ih =>
    have hn : m ≠ 0 := by rintro rfl; simp at hm
    change cond (Nat.beq m 0) false
      (cond (f (m ^^^ (m &&& (m - 1)))) true (anyBit f k (m &&& (m - 1)))) = true
    simp only [Bool.cond_eq_ite, Nat.beq_eq, ite_eq_right hn]
    split_ifs with h
    · rfl
    · apply ih
      cases hr : (m &&& (m - 1)).testBit j
      · exact False.elim (h ((removed_bit hm hr) ▸ hf))
      · rfl

/-- A cap for the next mark from the suffix and, in the first half, from the middle mark. -/
private def cap (n L i : ℕ) : ℕ :=
  let m := (n - 1) / 2
  let hi := L - bounds.getD (n - i) 0
  if i ≤ m then min hi (L / 2 - bounds.getD (m + 1 - i) 0) else hi

private theorem le_cap {n a L} (h : Ruler n a) (hL : a (n - 1) ≤ L)
    (hm : a ((n - 1) / 2) ≤ L / 2) (hb : ∀ j < n, LowerBound j (bounds.getD j 0))
    {i : ℕ} (hi : 0 < i) (hin : i < n) : a i ≤ cap n L i := by
  have hs := (hb (n - i) (by omega)).span h (i := i) (j := n - 1) (by omega)
    (by omega) (by omega)
  have hl := h.le (i := i) (j := n - 1) (by omega) (by omega)
  simp only [cap]
  split_ifs with hc
  · have hs' := (hb ((n - 1) / 2 + 1 - i) (by omega)).span h hc (by omega) rfl
    have hl' := h.le hc (by omega)
    exact le_min (by omega) (by omega)
  · omega

/-- Relative to the last mark, the masks record earlier marks (backwards), used
differences, and gaps excluded for every future mark (forwards). -/
private structure Masks (a : ℕ → ℕ) (n i r d c : ℕ) : Prop where
  mark : ∀ t, r.testBit t = true → ∃ j ≤ i, t = a i - a j
  diff : ∀ t, d.testBit t = true → ∃ u v, u < v ∧ v ≤ i ∧ t = a v - a u
  free : ∀ j, i < j → j < n → c.testBit (a j - a i) = false

private theorem Masks.extend {n a i r d c} (h : Ruler n a) (hi : i + 1 < n)
    (s : Masks a n i r d c) :
    let g := a (i + 1) - a i
    let p := r <<< g
    let ds := d ||| p
    Masks a n (i + 1) (p ||| 1) ds ((c >>> g) ||| ds) := by
  let g := a (i + 1) - a i
  have hinc : a i < a (i + 1) := h.mono (Nat.lt_succ_self i) hi
  have hp (t) (ht : (r <<< g).testBit t = true) : ∃ j ≤ i, t = a (i + 1) - a j := by
    rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨j, hj, he⟩ := s.mark _ ht.2
    have := h.le hj (by omega)
    dsimp [g] at *
    exact ⟨j, hj, by omega⟩
  have hd (t) (ht : (d ||| (r <<< g)).testBit t = true) :
      ∃ u v, u < v ∧ v ≤ i + 1 ∧ t = a v - a u := by
    rw [Nat.testBit_lor, Bool.or_eq_true] at ht
    rcases ht with ht | ht
    · obtain ⟨u, v, huv, hv, e⟩ := s.diff _ ht
      exact ⟨u, v, huv, by omega, e⟩
    · obtain ⟨j, hj, e⟩ := hp _ ht
      exact ⟨j, i + 1, by omega, le_rfl, e⟩
  refine ⟨?_, hd, ?_⟩
  · intro t ht
    rw [Nat.testBit_lor, Bool.or_eq_true] at ht
    rcases ht with ht | ht
    · obtain ⟨j, hj, e⟩ := hp _ ht
      exact ⟨j, by omega, e⟩
    · have ht' : t = 0 := by simpa [Nat.testBit_one_eq_true_iff_self_eq_zero] using ht
      exact ⟨i + 1, le_rfl, by simp [ht']⟩
  · intro j hj hjn
    have hj' := h.mono hj hjn
    rw [Nat.testBit_lor, Bool.or_eq_false_iff, Nat.testBit_shiftRight]
    refine ⟨?_, ?_⟩
    · rw [show a (i + 1) - a i + (a j - a (i + 1)) = a j - a i by omega]
      exact s.free j (by omega) hjn
    · cases he : (d ||| (r <<< g)).testBit (a j - a (i + 1))
      · rfl
      obtain ⟨u, v, huv, hv, eq⟩ := hd _ he
      have := (h.diff hj hjn huv (by omega) eq).2
      omega

/-- Try all feasible next gaps. The position and the gap are represented by their
powers of two, so multiplication and division shift the masks directly. -/
private def step (L limit table : ℕ) (next : ℕ → ℕ → ℕ → ℕ → Bool)
    (pos r d c : ℕ) : Bool :=
  let hi := Nat.min limit (Nat.sub L (gapBound table d))
  let m := Nat.sub (Nat.div (Nat.shiftLeft 2 hi) pos) 2
  let avail := Nat.xor m (Nat.land m c)
  anyBit (fun b =>
    let p := Nat.mul r b
    let ds := Nat.lor d p
    next (Nat.mul pos b) (Nat.lor p 1) ds (Nat.lor (Nat.div c b) ds)) 72 avail

private def search (n L : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (fun _ _ _ _ => true) (fun k next =>
    step L (cap n L (n - (k + 1))) (sumTable k) next) k

private theorem search_of_ruler {n a L} (h : Ruler n a) (hn : n ≤ 11)
    (hL : a (n - 1) ≤ L) (hm : a ((n - 1) / 2) ≤ L / 2)
    (hb : ∀ j < n, LowerBound j (bounds.getD j 0)) {k i r d c : ℕ}
    (hi : i + k + 1 = n) (s : Masks a n i r d c) :
    search n L k (2 ^ a i) r d c = true := by
  induction k generalizing i r d c with
  | zero => rfl
  | succ k ih =>
    let g := a (i + 1) - a i
    have hinc : a i < a (i + 1) := h.mono (Nat.lt_succ_self i) (by omega)
    have hg : 0 < g := by dsimp [g]; omega
    have hi' : n - (k + 1) = i + 1 := by omega
    have hc := le_cap h hL hm hb (i := i + 1) (by omega) (by omega)
    have hs := sumFree_le_span h (i := i + 1) (j := n - 1) (d := d) (by omega)
      (by omega) (fun t ht => by
        obtain ⟨u, v, huv, hv, e⟩ := s.diff t ht
        exact ⟨u, v, huv, by omega, e⟩)
    rw [show n - 1 - (i + 1) = k by omega, ← gapBound_eq (by omega)] at hs
    let high := min (cap n L (i + 1)) (L - gapBound (sumTable k) d)
    have hl := h.le (i := i + 1) (j := n - 1) (by omega) (by omega)
    have hfit : a (i + 1) ≤ high := le_min hc (by omega)
    change step L _ _ _ _ _ _ _ = true
    unfold step
    rw [hi']
    apply anyBit_of (j := g)
    · have hpow : Nat.shiftLeft 2 high / 2 ^ a i = 2 ^ (high + 1 - a i) := by
        change (2 <<< high) / 2 ^ a i = _
        rw [Nat.shiftLeft_eq, ← pow_succ']
        exact Nat.pow_div (by omega) (by decide)
      have hmask : (2 ^ (high + 1 - a i) - 2).testBit g = true := by
        have e : 2 ^ (high + 1 - a i) - 2 =
            (2 ^ (high - a i) - 1) <<< 1 := by
          rw [show high + 1 - a i = (high - a i) + 1 by omega, pow_succ, Nat.shiftLeft_eq]
          have := Nat.two_pow_pos (high - a i)
          omega
        rw [e, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
        simp [show 1 ≤ g by omega, show g - 1 < high - a i by dsimp [g]; omega]
      change ((Nat.shiftLeft 2 high / 2 ^ a i - 2) ^^^
        ((Nat.shiftLeft 2 high / 2 ^ a i - 2) &&& c)).testBit g = true
      rw [hpow, Nat.testBit_xor, Nat.testBit_land, hmask, s.free (i + 1) (by omega) (by omega)]
      rfl
    · have e : a i + g = a (i + 1) := by dsimp [g]; omega
      change search n L k (2 ^ a i * 2 ^ g) (r * 2 ^ g ||| 1) (d ||| r * 2 ^ g)
        (c / 2 ^ g ||| (d ||| r * 2 ^ g)) = true
      rw [← pow_add, e, ← Nat.shiftLeft_eq, ← Nat.shiftRight_eq_div_pow]
      exact ih (i := i + 1) (by omega) (s.extend h (by omega))

private def firstCap (n : ℕ) : ℕ := cap n (bounds.getD n 0 - 1) 1

private def start (n gap : ℕ) : Bool :=
  let p := Nat.shiftLeft 1 gap
  search n (bounds.getD n 0 - 1) (n - 2) p (Nat.lor p 1) p p

private theorem lower_of_checked {n : ℕ} (hn : 3 ≤ n) (hn' : n ≤ 11)
    (hb : ∀ j < n, LowerBound j (bounds.getD j 0))
    (hc : ∀ g, 1 ≤ g → g ≤ firstCap n → start n g = false) :
    LowerBound n (bounds.getD n 0) := by
  intro a ha
  by_contra! hs
  obtain ⟨b, h, h₀, he, hm⟩ := ha.orient hn
  let L := bounds.getD n 0 - 1
  have hL : b (n - 1) ≤ L := by dsimp [L]; omega
  have hm' : b ((n - 1) / 2) ≤ L / 2 := by omega
  have hg := h.mono (show 0 < 1 by decide) (show 1 < n by omega)
  have init : Masks b n 0 1 0 0 := by
    refine ⟨fun t ht => ⟨0, le_rfl, ?_⟩, by simp, by simp⟩
    simpa [Nat.testBit_one_eq_true_iff_self_eq_zero] using ht
  have ext := init.extend h (by omega)
  have fit := search_of_ruler h hn' hL hm' hb (k := n - 2) (i := 1) (by omega) ext
  have imposs := hc (b 1) (by omega) (le_cap h hL hm' hb (by decide) (by omega))
  change search n L (n - 2) (1 <<< b 1) ((1 <<< b 1) ||| 1) (1 <<< b 1)
    (1 <<< b 1) = false at imposs
  simp only [Nat.zero_add, Nat.zero_shiftRight, Nat.zero_or, h₀, Nat.sub_zero,
    Nat.one_shiftLeft] at fit imposs
  rw [imposs] at fit
  contradiction

private theorem ruler_of_sidon {S : Finset ℕ} {n : ℕ} (hcard : S.card = n) (hn : 0 < n)
    (hs : (S : Set ℕ).IsSidon) :
    ∃ a : ℕ → ℕ, Ruler n a ∧ ∀ i < n, a i ∈ S := by
  let e := S.orderEmbOfFin hcard
  let a (i : ℕ) := e ⟨i % n, Nat.mod_lt _ hn⟩
  have hmono (i j : ℕ) (hij : i < j) (hj : j < n) : a i < a j := by
    apply e.strictMono
    change i % n < j % n
    rw [Nat.mod_eq_of_lt (hij.trans hj), Nat.mod_eq_of_lt hj]
    exact hij
  have hm (i : ℕ) : a i ∈ S := S.orderEmbOfFin_mem hcard _
  refine ⟨a, ⟨fun i j => hmono i j, ?_⟩, fun i _ => hm i⟩
  intro i j u v hij hj huv hv hd
  have h₁ := hmono i j hij hj
  have h₂ := hmono u v huv hv
  have hinj {k l : ℕ} (hk : k < n) (hl : l < n) (he : a k = a l) : k = l := by
    rcases lt_trichotomy k l with hlt | rfl | hlt
    · exact False.elim ((hmono k l hlt hl).ne he)
    · rfl
    · exact False.elim ((hmono l k hlt hk).ne he.symm)
  rcases hs (a j) (hm j) (a u) (hm u) (a v) (hm v) (a i) (hm i) (by omega) with h | h
  · exact ⟨hinj (hij.trans hj) (huv.trans hv) h.2.symm, hinj hj hv h.1⟩
  · exact False.elim (h₁.ne h.1.symm)

private theorem le_of_mem_lengths {n l L : ℕ} (h : LowerBound n l) (hn : 0 < n)
    (hL : L ∈ golombRulerLengths n) : l ≤ L := by
  obtain ⟨S, hS, hc, hs, _⟩ := hL
  obtain ⟨a, ha, hm⟩ := ruler_of_sidon hc hn hs
  have hle := mem_range.mp (hS (hm (n - 1) (by omega)))
  exact (h _ ha).trans (by omega)

private theorem optimal_eq {n l : ℕ} (hn : 0 < n) (h : LowerBound n l)
    (hw : l ∈ golombRulerLengths n) : optimalGolombLength n = l := by
  rw [optimalGolombLength, ite_eq_right (by omega)]
  exact le_antisymm (Nat.sInf_le hw) (le_of_mem_lengths h hn (Nat.sInf_mem ⟨l, hw⟩))

/-- Convert a finite check of the Sidon condition into a witness for a length. -/
private theorem mem_lengths_of_finset {n L : ℕ} (S : Finset ℕ)
    (hS : ∀ x ∈ S, x < L + 1) (hc : S.card = n) (hL : L ∈ S)
    (hs : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) :
    L ∈ golombRulerLengths n :=
  ⟨S, (by intro x hx; exact mem_range.mpr (hS x hx)), hc, hs, hL⟩

/-! ### Verification of the bounds -/

/-- The first three lower bounds, requiring only that two distinct ordered marks differ by one
or more. -/
private theorem lower_small {n : ℕ} (hn : n < 3) : LowerBound n (bounds.getD n 0) := by
  interval_cases n
  · exact fun _ _ => Nat.zero_le _
  · exact fun _ _ => Nat.zero_le _
  · intro a h
    have hlt := h.mono (show 0 < 1 by decide) (show 1 < 2 by decide)
    change 1 ≤ a 1 - a 0
    omega

private theorem lower_all
    (checks : ∀ n, 3 ≤ n → n ≤ 11 →
      ∀ g, 1 ≤ g → g ≤ firstCap n → start n g = false)
    (n : ℕ) (hn : n ≤ 11) : LowerBound n (bounds.getD n 0) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hlo : n < 3
    · exact lower_small hlo
    · have hl := Nat.le_of_not_gt hlo
      exact lower_of_checked hl hn (fun j hj => ih j hj (by omega)) (checks n hl hn)

/-- Explicit rulers attaining the proposed bounds, indexed by their number of marks. -/
private def witnesses : List (List ℕ) :=
  [[], [], [], [0, 1, 3], [0, 1, 4, 6], [0, 1, 4, 9, 11], [0, 1, 4, 10, 12, 17],
    [0, 1, 4, 10, 18, 23, 25], [0, 1, 4, 9, 15, 22, 32, 34],
    [0, 1, 5, 12, 25, 27, 35, 41, 44], [0, 1, 6, 10, 23, 26, 34, 41, 53, 55],
    [0, 1, 4, 13, 28, 33, 47, 54, 64, 70, 72]]

private def WitnessOK (n : ℕ) : Prop :=
  let S := (witnesses.getD n []).toFinset
  let L := bounds.getD n 0
  (∀ x ∈ S, x < L + 1) ∧ S.card = n ∧ L ∈ S ∧
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

set_option maxHeartbeats 1000000 in
-- The kernel checks the Sidon condition over quadruples of marks in each finite witness.
set_option maxRecDepth 4096 in
private theorem witness_mem {n : ℕ} (hlo : 3 ≤ n) (hhi : n ≤ 11) :
    bounds.getD n 0 ∈ golombRulerLengths n := by
  have h : WitnessOK n := by
    interval_cases n <;> unfold WitnessOK <;> decide +kernel
  exact mem_lengths_of_finset _ h.1 h.2.1 h.2.2.1 h.2.2.2

private theorem values_of_checked
    (checks : ∀ n, 3 ≤ n → n ≤ 11 →
      ∀ g, 1 ≤ g → g ≤ firstCap n → start n g = false) :
    (List.range 9).map (fun i => optimalGolombLength (i + 3)) =
      [3, 6, 11, 17, 25, 34, 44, 55, 72] := by
  have h (i : ℕ) (hlo : 3 ≤ i) (hhi : i ≤ 11) : optimalGolombLength i = bounds.getD i 0 :=
    optimal_eq (by omega) (lower_all checks i hhi) (witness_mem hlo hhi)
  change [optimalGolombLength 3, optimalGolombLength 4, optimalGolombLength 5,
    optimalGolombLength 6, optimalGolombLength 7, optimalGolombLength 8,
    optimalGolombLength 9, optimalGolombLength 10, optimalGolombLength 11] = _
  rw [h 3 (by decide) (by decide), h 4 (by decide) (by decide), h 5 (by decide) (by decide),
    h 6 (by decide) (by decide), h 7 (by decide) (by decide), h 8 (by decide) (by decide),
    h 9 (by decide) (by decide), h 10 (by decide) (by decide), h 11 (by decide) (by decide)]
  rfl

set_option maxHeartbeats 16000000 in
-- Splitting by the first gap keeps each independent kernel reduction small.
private theorem checks (n : ℕ) (hlo : 3 ≤ n) (hhi : n ≤ 11)
    (g : ℕ) (hg : 1 ≤ g) (hc : g ≤ firstCap n) : start n g = false := by
  interval_cases n <;> norm_num [firstCap, cap, bounds, List.getD] at hc <;>
    interval_cases g <;> decide +kernel

/-- **Optimal Golomb rulers with 3 to 11 marks.** The optimal Golomb ruler lengths with
$m = 3, 4, \dots, 11$ marks are, in order, $3, 6, 11, 17, 25, 34, 44, 55, 72$.

Source: exhaustive searches; OEIS A003022; listed in leansolving/SqueezeBench
`SqueezeBench/Problems/Golomb/README.md`. -/
public theorem optimalGolombLength_three_to_eleven :
    (List.range 9).map (fun i => optimalGolombLength (i + 3)) =
      [3, 6, 11, 17, 25, 34, 44, 55, 72] := values_of_checked checks

end MathlibExt.Combinatorics.GolombRulersWanted
