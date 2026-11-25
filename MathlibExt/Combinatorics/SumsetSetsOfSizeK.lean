/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Equiv
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Data.Finsupp.Lex
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Sumsets of sets of size `k`

We describe the trivial elements of an iterated sumset, show that adjoining a new maximum
preserves nontrivial sums, and bound their number when the final gap is either not a multiple
of the preceding gap or a proper multiple of
the preceding one. We also compute the size of the sumset of an arithmetic progression with its
penultimate term removed. For a set of size `k` in a torsion-free abelian group, we show that
no sumset size lies between `hk - h + 2` and `hk - 1`, inclusive.
When the final two gaps agree, either the sequence is an arithmetic progression or the sumset
of the prefix has at least `h - 1` nontrivial elements.
-/

open scoped Pointwise

namespace MetaMathlibExt

@[expose] public section

/-- **Trivial elements of an $h$-fold sumset.** Let $G$ be an additive commutative monoid, let
$h, k \in \mathbb{N}$ and let $a \colon \mathbb{N} \to G$ list the set
$A = \{a_0, a_1, \dots, a_{k-1}\}$; write $n x$ for the $n$-fold sum $x + \dots + x$. The
trivial elements of the $h$-fold sumset $hA$ form the finite set that is empty when $k = 0$ and
otherwise consists of $h a_0$ together with the sums $(h - i) a_j + i a_{j+1}$ for all natural
numbers $i \le h$ and $j$ with $j + 1 < k$. An element of $hA$ that is not trivial is called
nontrivial.

These are the sums obtained by moving one summand at a time from each element to the next.
When $k \ge 1$ and $a_0 < a_1 < \dots < a_{k-1}$ in a linearly ordered additive group (the
paper's setting) they form an increasing list of $hk - h + 1$ distinct sums; for an arbitrary
$a$ they may coincide (for example $a = 0$ and $h = k = 2$ give a single element). The sum
$h a_0$ is listed separately so that for $k = 1$ the single sum $h a_0$ is trivial, as in the
paper's list.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, definition of trivial and nontrivial elements (arXiv:2505.07679v2,
Definition 1.8). -/
public def sumsetTrivialElements {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (h k : ℕ) (a : ℕ → G) : Finset G :=
  if k = 0 then ∅
  else insert (h • a 0) ((Finset.range (k - 1) ×ˢ Finset.range (h + 1)).image
    fun p => (h - p.2) • a p.1 + p.2 • a (p.1 + 1))

/-- **No trivial elements for $k = 0$.** Let $G$ be an additive commutative monoid, $h$ a natural
number and $a \colon \mathbb{N} \to G$. For $k = 0$, when $\{a_0, \dots, a_{k-1}\}$ is the empty
set, the set of trivial elements of its $h$-fold sumset is empty.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, definition of trivial elements (arXiv:2505.07679v2, Definition 1.8). -/
public theorem sumsetTrivialElements_zero {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (h : ℕ) (a : ℕ → G) : sumsetTrivialElements h 0 a = ∅ := by
  simp [sumsetTrivialElements]

/-- **Trivial elements of a one-element set.** Let $G$ be an additive commutative monoid, $h$ a
natural number and $a \colon \mathbb{N} \to G$. For $k = 1$, when $\{a_0, \dots, a_{k-1}\}$ is
the one-element set $\{a_0\}$, the set of trivial elements of its $h$-fold sumset is exactly
$\{h a_0\}$, where $h a_0 = a_0 + \dots + a_0$ is the $h$-fold sum of $a_0$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, definition of trivial elements (arXiv:2505.07679v2, Definition 1.8). -/
public theorem sumsetTrivialElements_one {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (h : ℕ) (a : ℕ → G) : sumsetTrivialElements h 1 a = {h • a 0} := by
  simp [sumsetTrivialElements]

/-- **Adjacent sums are trivial elements.** Let $G$ be an additive commutative monoid,
$a_0, a_1, \ldots$ a sequence in $G$, and $h, k, i, j$ natural numbers with $j + 1 < k$ and
$i \le h$. Then $(h - i)a_j + i a_{j+1}$ is a trivial element of the $h$-fold sumset of
$a_0, \ldots, a_{k-1}$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, definition of trivial elements (arXiv:2505.07679v2, Definition 1.8). -/
public theorem adjacent_sum_mem_sumsetTrivialElements {G : Type*} [AddCommMonoid G]
    [DecidableEq G] {h k i j : ℕ} (a : ℕ → G) (hj : j + 1 < k) (hi : i ≤ h) :
    (h - i) • a j + i • a (j + 1) ∈ sumsetTrivialElements h k a := by
  unfold sumsetTrivialElements
  simp only [show k ≠ 0 by omega, ↓reduceIte]
  refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(j, i), ?_, rfl⟩)
  simp only [Finset.mem_product, Finset.mem_range]
  omega

/-- **Characterization of the trivial elements.** Let $G$ be an additive commutative monoid,
$a_0, a_1, \ldots$ a sequence in $G$, and $h, k$ natural numbers. An element $x \in G$ is a
trivial element of the $h$-fold sumset of $a_0, \ldots, a_{k-1}$ if and only if either $k > 0$
and $x = h a_0$, or $x = (h - i)a_j + i a_{j+1}$ for some natural numbers $j$ and $i$ with
$j + 1 < k$ and $i \le h$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, definition of trivial elements (arXiv:2505.07679v2, Definition 1.8). -/
public theorem mem_sumsetTrivialElements_iff {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {h k : ℕ} (a : ℕ → G) (x : G) :
    x ∈ sumsetTrivialElements h k a ↔
      (0 < k ∧ x = h • a 0) ∨
        ∃ j i : ℕ, j + 1 < k ∧ i ≤ h ∧ x = (h - i) • a j + i • a (j + 1) := by
  unfold sumsetTrivialElements
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  simp only [show k ≠ 0 by omega, ↓reduceIte]
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_product, Finset.mem_range,
    Prod.exists]
  constructor
  · rintro (hx | ⟨j, i, ⟨hj, hi⟩, rfl⟩)
    · exact Or.inl ⟨hk, hx⟩
    · exact Or.inr ⟨j, i, by omega, by omega, rfl⟩
  · rintro (⟨-, hx⟩ | ⟨j, i, hj, hi, rfl⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨j, i, ⟨by omega, by omega⟩, rfl⟩

/-- **Dropping the largest element keeps nontrivial sums nontrivial.** Let $G$ be a linearly
ordered additive commutative group, let $h$ and $k > 1$ be natural numbers, and let
$a_0, a_1, \ldots$ be a sequence in $G$ with $a_0 < a_1 < \cdots < a_{k-1}$. Put
$A = \{a_0, \ldots, a_{k-1}\}$ and $B = \{a_0, \ldots, a_{k-2}\}$, and write $hX$ for the
$h$-fold sumset of a set $X$, the set of sums of $h$ elements of $X$. Then $hB \subseteq hA$,
and every element of $hB$ that is not a trivial element of the $h$-fold sumset of
$a_0, \ldots, a_{k-2}$ is not a trivial element of the $h$-fold sumset of $a_0, \ldots, a_{k-1}$.

The paper takes $h > 1$; the statement holds for every $h$ (for $h = 0$ there are no
nontrivial elements).

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Lemma 1 (`integers-2026-A31-lem-1`; arXiv:2505.07679v2, Lemma 3.2). -/
public theorem nsmul_sumset_erase_max_nontrivial
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (h k : ℕ) (hk : 1 < k) (a : ℕ → G) (ha : ∀ i, i + 1 < k → a i < a (i + 1)) :
    h • (Finset.range (k - 1)).image a ⊆ h • (Finset.range k).image a ∧
      ∀ c ∈ h • (Finset.range (k - 1)).image a,
        c ∉ sumsetTrivialElements h (k - 1) a → c ∉ sumsetTrivialElements h k a := by
  constructor
  · exact Finset.nsmul_subset_nsmul_left
      (Finset.image_subset_image (Finset.range_mono (Nat.sub_le k 1)))
  intro c hc hnontriv htriv
  apply hnontriv
  rw [mem_sumsetTrivialElements_iff] at htriv ⊢
  rcases htriv with ⟨_, hc₀⟩ | ⟨j, i, hj, hi, hci⟩
  · exact Or.inl ⟨by omega, hc₀⟩
  by_cases hold : j + 1 < k - 1
  · exact Or.inr ⟨j, i, hold, hi, hci⟩
  obtain rfl : k = j + 2 := by omega
  -- On the last adjacent pair, the only sum reachable from the shorter list is its maximum.
  have hmono : Monotone (fun n : Fin (j + 1) => a n) :=
    Fin.monotone_iff_le_succ.mpr fun n => (ha n (by omega)).le
  have hmax : c ≤ h • a j := by
    obtain ⟨f, rfl⟩ := Finset.mem_nsmul.mp hc
    simpa only [List.length_ofFn] using List.sum_le_length_nsmul _ (a j)
      (List.forall_mem_ofFn_iff.mpr fun t => by
        obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp (f t).property
        rw [← heq]
        exact hmono (Fin.le_last ⟨n, Finset.mem_range.mp hn⟩))
  have heq : c = h • a j := hmax.antisymm <| calc
    h • a j = (h - i) • a j + i • a j := by rw [← add_nsmul, Nat.sub_add_cancel hi]
    _ ≤ c := by
      rw [hci]
      exact add_le_add_right (nsmul_le_nsmul_right (ha j hj).le i) _
  cases j with
  | zero => exact Or.inl ⟨by omega, heq⟩
  | succ j => exact Or.inr ⟨j, h, by omega, le_rfl, by simpa using heq⟩

/-- **Many nontrivial sums when the last gap is not a multiple of the previous one.** Let $G$ be
a linearly ordered additive commutative group, let $h$ and $k \ge 4$ be natural numbers, and let
$a_0, a_1, \ldots$ be a sequence in $G$ with $0 = a_0 < a_1 < \cdots < a_{k-3}$. Suppose that
$a_{k-2} = a_{k-3} + b$ and $a_{k-1} = a_{k-3} + b + c$, where $b, c \in G$ satisfy $b > 0$,
$c > 0$ and $c \ne db$ for every integer $d \ge 1$. Then at least $h - 1$ elements of the
$h$-fold sumset $h\{a_0, \ldots, a_{k-1}\}$ (the set of sums of $h$ elements of
$\{a_0, \ldots, a_{k-1}\}$) are not trivial elements of the $h$-fold sumset of
$a_0, \ldots, a_{k-1}$.

The paper takes $h > 1$; the bound is vacuous for $h \le 1$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 1 (`integers-2026-A31-thm-1`; arXiv:2505.07679v2,
Theorem 3.3). -/
public theorem nontrivial_sumset_card_of_last_gap_ne_nsmul
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (h k : ℕ) (hk : 4 ≤ k) (a : ℕ → G) (ha0 : a 0 = 0)
    (ha : ∀ i, i + 1 ≤ k - 3 → a i < a (i + 1)) (b c : G) (hb : 0 < b) (hc : 0 < c)
    (hb' : a (k - 2) = a (k - 3) + b) (hc' : a (k - 1) = a (k - 3) + b + c)
    (hcb : ∀ d : ℕ, 1 ≤ d → c ≠ d • b) :
    h - 1 ≤ (h • (Finset.range k).image a \ sumsetTrivialElements h k a).card := by
  have hx : a (k - 3) = a (k - 2) - b := eq_sub_of_add_eq hb'.symm
  have hz : a (k - 1) = a (k - 2) + c := by rw [hc', ← hb']
  -- Every element up to the third-to-last one is at most that element.
  have hbound (j : ℕ) (hj : j ≤ k - 3) : a j ≤ a (k - 3) := by
    induction hj using Nat.decreasingInduction with
    | self => exact le_rfl
    | of_succ j hj ih => exact (ha j hj).le.trans ih
  -- The paper's witnesses `h a_{k-3} + e b + c` for `1 ≤ e ≤ h - 1`, with `e = h - (p + 1)`.
  let w (p : ℕ) := h • a (k - 2) - (p + 1) • b + c
  -- Each witness exceeds every trivial sum of the elements up to the third-to-last one.
  have habove (p : ℕ) (hp : p + 1 ≤ h) : h • a (k - 3) < w p := by
    rw [hx, nsmul_sub]
    exact (sub_le_sub_left (nsmul_le_nsmul_left hb.le hp) _).trans_lt
      (lt_add_of_pos_right _ hc)
  refine Finset.le_card_of_inj_on_range w
    (fun p hp => Finset.mem_sdiff.mpr ⟨?_, fun htriv => ?_⟩) ?_
  · -- The witness uses `p + 1` copies of `a (k - 3)`, `h - (p + 2)` of `a (k - 2)` and the last.
    have hmem (j : ℕ) (hj : j < k) : a j ∈ (Finset.range k).image a :=
      Finset.mem_image_of_mem a (Finset.mem_range.mpr hj)
    have hsum := Finset.add_mem_add (Finset.add_mem_add
      (Finset.nsmul_mem_nsmul (n := p + 1) (hmem (k - 3) (by omega)))
      (Finset.nsmul_mem_nsmul (n := h - (p + 2)) (hmem (k - 2) (by omega))))
      (hmem (k - 1) (by omega))
    have hval : (p + 1) • a (k - 3) + (h - (p + 2)) • a (k - 2) + a (k - 1) =
        (p + 1 + (h - (p + 2)) + 1) • a (k - 2) - (p + 1) • b + c := by
      rw [hx, hz]
      simp only [add_nsmul, one_nsmul, nsmul_sub]
      abel
    rwa [hval, ← add_nsmul, ← succ_nsmul, show p + 1 + (h - (p + 2)) + 1 = h by omega] at hsum
  · rcases (mem_sumsetTrivialElements_iff _ _).mp htriv with ⟨_, heq⟩ | ⟨j, i, hj, hi, heq⟩
    · apply (habove p (by omega)).not_ge
      rw [heq, ha0, nsmul_zero]
      exact nsmul_nonneg (ha0 ▸ hbound 0 (Nat.zero_le _)) h
    by_cases hlow : j + 1 ≤ k - 3
    · apply (habove p (by omega)).not_ge
      calc w p = (h - i) • a j + i • a (j + 1) := heq
        _ ≤ (h - i) • a (k - 3) + i • a (k - 3) :=
          add_le_add (nsmul_le_nsmul_right (hbound j (by omega)) _)
            (nsmul_le_nsmul_right (hbound _ hlow) _)
        _ = h • a (k - 3) := by rw [← add_nsmul, Nat.sub_add_cancel hi]
    rcases (show j = k - 3 ∨ j = k - 2 by omega) with rfl | rfl
    · -- On the previous pair the sum is `h a_{k-2} - (h - i) b`, so `c = (p + 1) b - (h - i) b`
      -- is either a positive multiple of `b` or not positive.
      rw [show k - 3 + 1 = k - 2 by omega, hx, nsmul_sub, sub_add_eq_add_sub, ← add_nsmul,
        Nat.sub_add_cancel hi] at heq
      have hc2 : c = (p + 1) • b - (h - i) • b := by
        calc c = w p - h • a (k - 2) + (p + 1) • b := by simp only [w]; abel
          _ = (p + 1) • b - (h - i) • b := by rw [heq]; abel
      rcases lt_or_ge (h - i) (p + 1) with hlt | hge
      · exact hcb (p + 1 - (h - i)) (by omega)
          (by rw [hc2, sub_nsmul _ hlt.le, sub_eq_add_neg])
      · exact hc.not_ge (hc2 ▸ sub_nonpos.mpr (nsmul_le_nsmul_left hb.le hge))
    · -- On the last pair the sum is `h a_{k-2} + i c`, so `c - (p + 1) b = i c`.
      rw [show k - 2 + 1 = k - 1 by omega, hz, nsmul_add, ← add_assoc, ← add_nsmul,
        Nat.sub_add_cancel hi] at heq
      have hc2 : c - (p + 1) • b = i • c := by
        calc c - (p + 1) • b = w p - h • a (k - 2) := by simp only [w]; abel
          _ = i • c := by rw [heq]; abel
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact hcb (p + 1) (by omega) (by rwa [zero_nsmul, sub_eq_zero] at hc2)
      · exact (sub_lt_self c (nsmul_pos hb (by omega))).not_ge
          (hc2 ▸ le_self_nsmul hc.le (by omega))
  · intro p _ q _ hpq
    exact Nat.succ.inj ((nsmul_left_strictMono hb).injective
      (sub_right_injective (add_right_cancel hpq)))

namespace nontrivial_sumset_card_of_last_gap_eq_nsmul

-- Replace one copy of the penultimate element by its predecessor in a last-pair sum.
private theorem sub_gap_mem {G : Type*} [AddCommGroup G] [DecidableEq G] {A : Finset G}
    {y b c : G} (hx : y - b ∈ A) (hy : y ∈ A) (hz : y + c ∈ A) (m e : ℕ) :
    (m + e + 1) • y + e • c - b ∈ (m + e + 1) • A := by
  have hsum : (m + e + 1) • y + e • c - b = m • y + e • (y + c) + (y - b) := by
    rw [succ_nsmul, add_nsmul, nsmul_add]
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [hsum, succ_nsmul A, add_nsmul A]
  exact Finset.add_mem_add
    (Finset.add_mem_add (Finset.nsmul_mem_nsmul hy) (Finset.nsmul_mem_nsmul hz)) hx

end nontrivial_sumset_card_of_last_gap_eq_nsmul

/-- **Many nontrivial sums when the last gap is a proper multiple of the previous one.** Let $G$
be a linearly ordered additive commutative group, let $h$ and $k \ge 4$ be natural numbers, and
let $a_0, a_1, \ldots$ be a sequence in $G$ with $0 = a_0 < a_1 < \cdots < a_{k-3}$. Suppose
that $a_{k-2} = a_{k-3} + b$ and $a_{k-1} = a_{k-3} + b + db$, where $b \in G$ satisfies
$b > 0$ and $d > 1$ is an integer. Then at least $h - 1$ elements of the $h$-fold sumset
$h\{a_0, \ldots, a_{k-1}\}$ (the set of sums of $h$ elements of $\{a_0, \ldots, a_{k-1}\}$)
are not trivial elements of the $h$-fold sumset of $a_0, \ldots, a_{k-1}$.

The paper's last gap $c$ is written as $db$ (its positivity follows). The paper takes $h > 1$;
the bound is vacuous for $h \le 1$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 2 (`integers-2026-A31-thm-2`; arXiv:2505.07679v2,
Theorem 3.4). -/
public theorem nontrivial_sumset_card_of_last_gap_eq_nsmul
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (h k : ℕ) (hk : 4 ≤ k) (a : ℕ → G) (ha0 : a 0 = 0)
    (ha : ∀ i, i + 1 ≤ k - 3 → a i < a (i + 1)) (b : G) (hb : 0 < b) (d : ℕ) (hd : 1 < d)
    (hb' : a (k - 2) = a (k - 3) + b) (hc' : a (k - 1) = a (k - 3) + b + d • b) :
    h - 1 ≤ (h • (Finset.range k).image a \ sumsetTrivialElements h k a).card := by
  let y := a (k - 2)
  let c := d • b
  have hlast : a (k - 1) = y + c := by simpa only [y, hb'] using hc'
  have hbc : b < c := by
    calc b = (1 : ℕ) • b := (one_nsmul b).symm
         _ < c := nsmul_left_strictMono hb hd
  -- All elements before the last pair are bounded by its lower endpoint.
  have hbound (j : ℕ) (hj : j ≤ k - 2) : a j ≤ y := by
    induction hj using Nat.decreasingInduction with
    | self => exact le_rfl
    | of_succ j hj ih =>
      by_cases h : j + 1 ≤ k - 3
      · exact (ha j h).le.trans ih
      · rw [show j = k - 3 by omega]
        change a (k - 3) ≤ a (k - 2)
        rw [hb']
        exact le_add_of_nonneg_right hb.le
  let lastSum (i : ℕ) := h • y + i • c
  have hmono : StrictMono lastSum := (nsmul_left_strictMono (hb.trans hbc)).const_add _
  have hstep (i : ℕ) : lastSum (i + 1) = lastSum i + c := by
    simp [lastSum, succ_nsmul, add_assoc]
  -- Each witness lies strictly inside its own interval between consecutive last-pair sums.
  refine Finset.le_card_of_inj_on_range (fun i => lastSum (i + 1) - b) ?_ ?_
  · intro i hi
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · have hmem (j : ℕ) (hj : j < k) : a j ∈ (Finset.range k).image a :=
        Finset.mem_image_of_mem a (Finset.mem_range.mpr hj)
      have hx : y - b = a (k - 3) := by simp [y, hb']
      have hcount : h - (i + 2) + (i + 1) + 1 = h := by omega
      simpa only [hcount, lastSum] using
        nontrivial_sumset_card_of_last_gap_eq_nsmul.sub_gap_mem
          (hx ▸ hmem (k - 3) (by omega)) (hmem (k - 2) (by omega))
          (hlast ▸ hmem (k - 1) (by omega)) (h - (i + 2)) (i + 1)
    · have hlo : lastSum i < lastSum (i + 1) - b := by
        rw [lt_sub_iff_add_lt, hstep]
        exact add_lt_add_right hbc _
      have habove : h • y < lastSum (i + 1) - b := by
        simpa [lastSum] using (hmono.monotone (Nat.zero_le i)).trans_lt hlo
      intro htriv
      rcases (mem_sumsetTrivialElements_iff _ _).mp htriv with ⟨_, heq⟩ | ⟨j, r, hj, hr, heq⟩
      · apply habove.not_ge
        rw [heq, ha0, nsmul_zero]
        exact nsmul_nonneg (ha0 ▸ hbound 0 (by omega)) _
      by_cases hprev : j + 1 ≤ k - 2
      · apply habove.not_ge
        calc
          _ = _ := heq
          _ ≤ (h - r) • y + r • y := add_le_add
            (nsmul_le_nsmul_right (hbound j (by omega)) _)
            (nsmul_le_nsmul_right (hbound _ hprev) _)
          _ = _ := by rw [← add_nsmul, Nat.sub_add_cancel hr]
      have hpair : lastSum (i + 1) - b = lastSum r := by
        rw [heq, show j + 1 = k - 1 by omega, show j = k - 2 by omega, hlast]
        change (h - r) • y + r • (y + c) = _
        rw [nsmul_add, ← add_assoc, ← add_nsmul, Nat.sub_add_cancel hr]
      rcases le_or_gt r i with hri | hri
      · exact hlo.not_ge (hpair.trans_le (hmono.monotone hri))
      · exact (sub_lt_self _ hb).not_ge (hpair ▸ hmono.monotone hri)
  · intro i _ j _ heq
    exact Nat.succ.inj (hmono.injective (sub_left_inj.mp heq))

namespace arithProg_or_nontrivial_sumset_card_of_last_gaps_eq

-- Adding h - 2 terms from an adjacent pair to a double sum strictly between two of its
-- consecutive trivial sums gives h - 1 distinct nontrivial sums.
private theorem card_of_intermediate_sum
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (h n : ℕ) (a : ℕ → G) (ha : ∀ i, i + 1 < n → a i < a (i + 1))
    {j r : ℕ} (hj : j + 1 < n) (hr : r ≤ 1) {δ : G}
    (hδ : 0 < δ) (hlt : δ < a (j + 1) - a j)
    (hsum : 2 • a j + r • (a (j + 1) - a j) + δ ∈ 2 • (Finset.range n).image a) :
    h - 1 ≤ (h • (Finset.range n).image a \ sumsetTrivialElements h n a).card := by
  let gap (l : ℕ) := a (l + 1) - a l
  let row (l i : ℕ) := h • a l + i • gap l
  have hmono (l : ℕ) (hl : l + 1 < n) : StrictMono (row l) :=
    (nsmul_left_strictMono (sub_pos.mpr (ha l hl))).const_add _
  have hstart (l : ℕ) : row l 0 = h • a l := by simp [row]
  have hend (l : ℕ) : row l h = h • a (l + 1) := by simp [row, gap, nsmul_sub]
  have hle {u v : ℕ} (huv : u ≤ v) (hv : v < n) : a u ≤ a v := by
    induction huv with
    | refl => exact le_rfl
    | step h ih => exact (ih (by omega)).trans (ha _ hv).le
  let w (p : ℕ) := row j (p + r) + δ
  refine Finset.le_card_of_inj_on_range w (fun p hp => Finset.mem_sdiff.mpr ⟨?_, ?_⟩) ?_
  · have hmem (i : ℕ) (hi : i < n) := Finset.mem_image_of_mem a (Finset.mem_range.mpr hi)
    have hs := Finset.add_mem_add (Finset.add_mem_add
      (Finset.nsmul_mem_nsmul (n := h - (p + 2)) (hmem j (by omega)))
      (Finset.nsmul_mem_nsmul (n := p) (hmem (j + 1) hj))) hsum
    have hcount : h - (p + 2) + p + 2 = h := by omega
    rw [← add_nsmul, ← add_nsmul, hcount] at hs
    convert hs using 1
    change h • a j + (p + r) • gap j + δ = _
    conv_lhs => rw [← hcount, add_nsmul, add_nsmul, add_nsmul]
    simp only [gap, nsmul_sub]
    abel
  · have hlo : row j (p + r) < w p := lt_add_of_pos_right _ hδ
    have hhi : w p < row j (p + r + 1) := by
      simpa only [w, row, succ_nsmul, ← add_assoc] using
        (add_lt_add_right hlt (row j (p + r)))
    have hfirst : h • a j < w p :=
      (hstart j ▸ (hmono j hj).monotone (Nat.zero_le (p + r))).trans_lt hlo
    have hlast : w p < h • a (j + 1) := by
      rw [← hend]
      exact hhi.trans_le ((hmono j hj).monotone (by omega))
    intro htriv
    rcases (mem_sumsetTrivialElements_iff _ _).mp htriv with ⟨_, he⟩ | ⟨l, t, hl, ht, he⟩
    · exact hfirst.not_ge (he.trans_le (nsmul_le_nsmul_right (hle (Nat.zero_le j) (by omega)) h))
    have hw : w p = row l t := by
      rw [he]
      simp only [row, gap, nsmul_sub, sub_nsmul _ ht]
      abel
    rcases lt_trichotomy l j with hlj | rfl | hjl
    · apply hfirst.not_ge
      calc w p = row l t := hw
        _ ≤ row l h := (hmono l hl).monotone ht
        _ = h • a (l + 1) := hend l
        _ ≤ h • a j := nsmul_le_nsmul_right (hle hlj (by omega)) h
    · rcases le_or_gt t (p + r) with ht' | ht'
      · exact hlo.not_ge (hw.trans_le ((hmono l hj).monotone ht'))
      · exact hhi.not_ge (hw ▸ (hmono l hj).monotone ht')
    · apply hlast.not_ge
      calc h • a (j + 1) ≤ h • a l := nsmul_le_nsmul_right (hle hjl (by omega)) h
        _ = row l 0 := (hstart l).symm
        _ ≤ w p := hw ▸ (hmono l hl).monotone (Nat.zero_le t)
  · intro p _ q _ he
    exact Nat.add_right_cancel ((hmono j hj).injective (add_right_cancel he))

end arithProg_or_nontrivial_sumset_card_of_last_gaps_eq

/-- **Equal last two gaps: an arithmetic progression or many nontrivial sums.** Let $G$ be a
linearly ordered additive commutative group, let $h$ and $k \ge 4$ be natural numbers, and let
$a_0, a_1, \ldots$ be a sequence in $G$ with $0 = a_0 < a_1 < \cdots < a_{k-1}$ and
$a_{k-1} - a_{k-2} = a_{k-2} - a_{k-3}$. Then either $a_i = i a_1$ for every $i < k$, or at
least $h - 1$ elements of the $h$-fold sumset $hB$ of $B = \{a_0, \ldots, a_{k-2}\}$ (the set
of sums of $h$ elements of $B$) are not trivial elements of the $h$-fold sumset of
$a_0, \ldots, a_{k-2}$.

The gap hypothesis is the paper's $b_{k-2} = b_{k-3}$, where $b_j = a_{j+1} - a_j$ for
$j \ge 1$. The paper takes $h > 1$; the second alternative is vacuous for $h \le 1$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 3 (`integers-2026-A31-thm-3`; arXiv:2505.07679v2,
Theorem 3.5). -/
public theorem arithProg_or_nontrivial_sumset_card_of_last_gaps_eq
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (h k : ℕ) (hk : 4 ≤ k) (a : ℕ → G) (ha0 : a 0 = 0)
    (ha : ∀ i, i + 1 < k → a i < a (i + 1))
    (hgap : a (k - 1) - a (k - 2) = a (k - 2) - a (k - 3)) :
    (∀ i < k, a i = i • a 1) ∨
      h - 1 ≤ (h • (Finset.range (k - 1)).image a \
        sumsetTrivialElements h (k - 1) a).card := by
  let gap (i : ℕ) := a (i + 1) - a i
  by_cases hall : ∀ j, j + 2 < k - 1 → gap (j + 1) = gap j
  · left
    -- Equal successive gaps throughout the prefix extend across the final pair by hypothesis.
    have hstep (j : ℕ) (hj : j + 2 < k) : gap (j + 1) = gap j := by
      by_cases h : j + 2 < k - 1
      · exact hall j h
      simpa only [gap, show k - 1 = j + 2 by omega, show k - 2 = j + 1 by omega,
        show k - 3 = j by omega] using hgap
    have hconst (i : ℕ) (hi : i + 1 < k) : gap i = a 1 := by
      induction i with
      | zero => simp [gap, ha0]
      | succ i ih => exact (hstep i hi).trans (ih (by omega))
    intro i hi
    induction i with
    | zero => simpa using ha0
    | succ i ih =>
      rw [succ_nsmul, ← ih (by omega), ← hconst i hi]
      simp [gap]
  · right
    push Not at hall
    obtain ⟨j, hj, hne⟩ := hall
    have hpos (i : ℕ) (hi : i + 1 < k) : 0 < gap i := sub_pos.mpr (ha i hi)
    have hmem (i : ℕ) (hi : i < k - 1) := Finset.mem_image_of_mem a (Finset.mem_range.mpr hi)
    -- The sum of the outer terms of the triple falls inside the wider gap's row of double sums.
    have hsum : a j + a (j + 2) ∈ 2 • (Finset.range (k - 1)).image a := by
      rw [two_nsmul]
      exact Finset.add_mem_add (hmem j (by omega)) (hmem _ hj)
    rcases hne.lt_or_gt with hlt | hgt
    · apply arithProg_or_nontrivial_sumset_card_of_last_gaps_eq.card_of_intermediate_sum
        h (k - 1) a (fun i hi => ha i (by omega)) (j := j) (r := 1) (by omega) le_rfl
        (hpos (j + 1) (by omega)) hlt
      convert hsum using 1
      simp only [one_nsmul, two_nsmul, gap]
      abel
    · apply arithProg_or_nontrivial_sumset_card_of_last_gaps_eq.card_of_intermediate_sum
        h (k - 1) a (fun i hi => ha i (by omega)) (j := j + 1) (r := 0) hj (by decide)
        (sub_pos.mpr hgt) (sub_lt_self _ (hpos j (by omega)))
      convert hsum using 1
      simp only [zero_nsmul, add_zero, two_nsmul, gap]
      abel

namespace card_nsmul_arithProg_skip_penultimate

/-- `k` together with the natural numbers less than `k - 1`. -/
private def coefficients (k : ℕ) : Finset ℕ := insert k (Finset.range (k - 1))

private theorem coefficients_add {m k : ℕ} (hm : 3 ≤ m) (hk : 3 ≤ k) :
    coefficients m + coefficients k = coefficients (m + k) := by
  ext x
  simp only [coefficients, Finset.mem_add, Finset.mem_insert, Finset.mem_range]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    omega
  · intro hx
    by_cases hlow : x < k - 1
    · exact ⟨0, Or.inr (by omega), x, Or.inr hlow, Nat.zero_add x⟩
    -- The gap in the second summand is filled by adding 1 to k - 2.
    by_cases hgap : x = k - 1
    · exact ⟨1, Or.inr (by omega), k - 2, Or.inr (by omega), by omega⟩
    exact ⟨x - k, by omega, k, Or.inl rfl, by omega⟩

private theorem nsmul_coefficients {k h : ℕ} (hk : 3 ≤ k) (hh : 1 ≤ h) :
    h • coefficients k = coefficients (h * k) := by
  induction h, hh using Nat.le_induction with
  | base => rw [one_nsmul, one_mul]
  | succ h hh ih =>
    have hle : k ≤ h * k := by simpa using Nat.mul_le_mul_right k hh
    rw [succ_nsmul, ih, Nat.succ_mul, coefficients_add (hk.trans hle) hk]

end card_nsmul_arithProg_skip_penultimate

open card_nsmul_arithProg_skip_penultimate

/-- **Sumset of an arithmetic progression with its second-to-last term removed.** Let $G$ be a
linearly ordered additive commutative group, let $a \in G$ with $a > 0$, and let $k \ge 3$ and
$h \ge 1$ be natural numbers. The set $A = \{0, a, 2a, \ldots, (k - 2)a, ka\}$, obtained from
$\{0, a, 2a, \ldots, ka\}$ by removing $(k - 1)a$, has $|hA| = hk$, where $hA$ is the $h$-fold
sumset of $A$, the set of sums of $h$ elements of $A$.

The paper leaves $h$ unquantified; $h \ge 1$ is needed, since $|0A| = 1$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 5 (`integers-2026-A31-thm-5`). -/
public theorem card_nsmul_arithProg_skip_penultimate
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (a : G) (ha : 0 < a) (k h : ℕ) (hk : 3 ≤ k) (hh : 1 ≤ h) :
    (h • insert (k • a) ((Finset.range (k - 1)).image fun i => i • a)).card = h * k := by
  have himage : (coefficients k).image (multiplesHom G a) =
      insert (k • a) ((Finset.range (k - 1)).image fun i => i • a) := by
    rw [coefficients, Finset.image_insert]
    rfl
  have hinj : Function.Injective (multiplesHom G a) := (nsmul_left_strictMono ha).injective
  rw [← himage, ← Finset.image_nsmul, nsmul_coefficients hk hh,
    Finset.card_image_of_injective _ hinj, coefficients,
    Finset.card_insert_of_notMem (by simp only [Finset.mem_range]; omega), Finset.card_range]
  exact Nat.sub_add_cancel (Nat.mul_pos hh (by omega))

namespace card_nsmul_notMem_Icc_of_isAddTorsionFree

variable {G : Type*} [AddCommGroup G] [DecidableEq G] {A : Finset G} {l u : G}

-- If all double sums lie in the two endpoint translates, every further sum
-- either uses the lower endpoint or consists of upper endpoints and one element of A.
private theorem cover_succ (hu : u ∈ A)
    (hc : A + A ⊆ ({l} + A) ∪ ({u} + A)) (n : ℕ) :
    (n + 1) • A ⊆ ({l} + n • A) ∪ ({n • u} + A) := by
  induction n with
  | zero =>
    intro x hx
    apply Finset.mem_union_right
    simpa [Finset.mem_add] using hx
  | succ n ih =>
    intro x hx
    rw [succ_nsmul A (n + 1)] at hx
    obtain ⟨s, hs, a, ha, rfl⟩ := Finset.mem_add.mp hx
    rcases Finset.mem_union.mp (ih hs) with hs | hs
    · obtain ⟨b, hb, rfl⟩ : ∃ b ∈ n • A, l + b = s := by simpa [Finset.mem_add] using hs
      apply Finset.mem_union_left
      rw [add_assoc, succ_nsmul A n]
      exact Finset.add_mem_add (Finset.mem_singleton_self _) (Finset.add_mem_add hb ha)
    · obtain ⟨b, hb, rfl⟩ : ∃ b ∈ A, n • u + b = s := by simpa [Finset.mem_add] using hs
      rcases Finset.mem_union.mp (hc (Finset.add_mem_add hb ha)) with hh | hh
      · obtain ⟨c, hc, he⟩ : ∃ c ∈ A, l + c = b + a := by simpa [Finset.mem_add] using hh
        apply Finset.mem_union_left
        rw [add_assoc, ← he, add_left_comm, succ_nsmul A n]
        exact Finset.add_mem_add (Finset.mem_singleton_self _) <|
          Finset.add_mem_add (Finset.nsmul_mem_nsmul hu) hc
      · obtain ⟨c, hc, he⟩ : ∃ c ∈ A, u + c = b + a := by simpa [Finset.mem_add] using hh
        apply Finset.mem_union_right
        rw [add_assoc, ← he, ← add_assoc, ← succ_nsmul]
        exact Finset.add_mem_add (Finset.mem_singleton_self _) hc

private theorem card_le_of_cover (hl : l ∈ A) (hu : u ∈ A)
    (hc : A + A ⊆ ({l} + A) ∪ ({u} + A)) (h : ℕ) :
    (h • A).card ≤ h * (A.card - 1) + 1 := by
  induction h with
  | zero => simp
  | succ n ih =>
    have hinter : (({l} + n • A) ∩ ({n • u} + A)).Nonempty := by
      refine ⟨l + n • u, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · exact Finset.add_mem_add (Finset.mem_singleton_self _) (Finset.nsmul_mem_nsmul hu)
      · rw [add_comm l (n • u)]
        exact Finset.add_mem_add (Finset.mem_singleton_self _) hl
    have he := Finset.card_union_add_card_inter ({l} + n • A) ({n • u} + A)
    simp only [Finset.card_singleton_add] at he
    have hb := Finset.card_le_card (cover_succ hu hc n)
    have hp := Finset.card_pos.mpr hinter
    rw [Nat.succ_mul]
    omega

section Ordered

variable [LinearOrder G] [IsOrderedAddMonoid G]

-- A double sum below l + u outside the lower translate supplies a full extra
-- block of |A| elements at every step. Order duality handles the upper half.
private theorem card_ge_of_extra (hl : l ∈ A) (hu : u ∈ A)
    (hmin : ∀ a ∈ A, l ≤ a) (hmax : ∀ a ∈ A, a ≤ u)
    {x : G} (hx : x ∈ A + A) (hxlt : x < l + u) (hxout : x ∉ {l} + A) (h : ℕ) :
    h * A.card ≤ (h • A).card := by
  let B := insert x ({l} + A.erase u)
  have hB : B ⊆ A + A := by
    refine Finset.insert_subset hx ?_
    exact Finset.add_subset_add (Finset.singleton_subset_iff.mpr hl) (Finset.erase_subset ..)
  have hBlt (b : G) (hb : b ∈ B) : b < l + u := by
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hxlt
    obtain ⟨a, ha, rfl⟩ : ∃ a ∈ A.erase u, l + a = b := by simpa [Finset.mem_add] using hb
    exact add_lt_add_right ((hmax a (Finset.mem_of_mem_erase ha)).lt_of_ne
      (Finset.ne_of_mem_erase ha)) _
  have hBc : B.card = A.card := by
    have hnot : x ∉ {l} + A.erase u := fun hh =>
      hxout (Finset.add_subset_add_left (Finset.erase_subset ..) hh)
    simp [B, Finset.card_insert_of_notMem hnot, Finset.card_singleton_add,
      Finset.card_erase_add_one hu]
  obtain _ | h := h
  · simp
  induction h with
  | zero => simp
  | succ n ih =>
    -- The first translate lies strictly below u + (n + 1) • l, the minimum of the second.
    let S := {n • l} + B
    let T := {u} + (n + 1) • A
    have hST : S ∪ T ⊆ (n + 2) • A := by
      apply Finset.union_subset
      · rw [add_nsmul, two_nsmul]
        exact Finset.add_subset_add (Finset.singleton_subset_iff.mpr
          (Finset.nsmul_mem_nsmul hl)) hB
      · rw [succ_nsmul, add_comm]
        exact Finset.add_subset_add_right (Finset.singleton_subset_iff.mpr hu)
    have hdis : Disjoint S T := by
      apply Finset.disjoint_left.mpr
      intro y hS hT
      obtain ⟨b, hb, rfl⟩ : ∃ b ∈ B, n • l + b = y := by simpa [S, Finset.mem_add] using hS
      obtain ⟨a, ha, he⟩ : ∃ a ∈ (n + 1) • A, u + a = n • l + b := by
        simpa [T, Finset.mem_add] using hT
      have hlow : (n + 1) • l ≤ a := by
        obtain ⟨f, rfl⟩ := Finset.mem_nsmul.mp ha
        simpa only [List.length_ofFn] using List.length_nsmul_le_sum _ l
          (List.forall_mem_ofFn_iff.mpr fun i => hmin _ (f i).property)
      have hlt := add_lt_add_right (hBlt b hb) (n • l)
      rw [← he, ← add_assoc, ← succ_nsmul, add_comm _ u] at hlt
      exact hlt.not_ge (add_le_add_right hlow u)
    have hb := Finset.card_le_card hST
    rw [Finset.card_union_of_disjoint hdis] at hb
    simp only [S, T, Finset.card_singleton_add, hBc] at hb
    rw [Nat.succ_mul]
    change _ ≤ ((n + 2) • A).card
    omega

private theorem ordered_gap (h : ℕ) (hA : A.Nonempty) :
    (h • A).card ∉ Set.Icc (h * A.card - h + 2) (h * A.card - 1) := by
  let l := A.min' hA
  let u := A.max' hA
  have hl : l ∈ A := A.min'_mem _
  have hu : u ∈ A := A.max'_mem _
  by_cases hc : A + A ⊆ ({l} + A) ∪ ({u} + A)
  · have hb := card_le_of_cover hl hu hc h
    rw [Nat.mul_sub, Nat.mul_one] at hb
    rintro ⟨hlo, _⟩
    omega
  obtain ⟨x, hx, hout⟩ := Finset.not_subset.mp hc
  have hnot := not_or.mp (Finset.mem_union.not.mp hout)
  have hne : x ≠ l + u := fun he =>
    hnot.1 (he ▸ Finset.add_mem_add (Finset.mem_singleton_self _) hu)
  have hb : h * A.card ≤ (h • A).card := by
    rcases hne.lt_or_gt with hlt | hgt
    · exact card_ge_of_extra hl hu (fun _ => A.min'_le _) (fun _ => A.le_max' _) hx hlt hnot.1 h
    · exact card_ge_of_extra (G := Gᵒᵈ) hu hl (fun _ => A.le_max' _) (fun _ => A.min'_le _)
        hx (by change u + l < x; rwa [add_comm u l]) hnot.2 h
  rintro ⟨hlo, hhi⟩
  omega

end Ordered
end card_nsmul_notMem_Icc_of_isAddTorsionFree

/-- **A gap in the possible sumset sizes.** Let $G$ be a torsion-free additive commutative
group and let $h$ and $k \ge 4$ be natural numbers. For every $k$-element set $A \subseteq G$,
the $h$-fold sumset $hA$ (the set of sums of $h$ elements of $A$) does not satisfy
$hk - h + 2 \le |hA| \le hk - 1$.

Equivalently, writing $R_G(h, k)$ for the set of sizes $|hA|$ of $k$-element sets
$A \subseteq G$, $R_G(h, k) \cap [hk - h + 2, hk - 1] = \emptyset$. The interval is empty for
$h \le 1$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 4 (`integers-2026-A31-thm-4`; arXiv:2505.07679v2,
Theorem 3.6). -/
public theorem card_nsmul_notMem_Icc_of_isAddTorsionFree
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G] [DecidableEq G]
    (h k : ℕ) (hk : 4 ≤ k) (A : Finset G) (hA : A.card = k) :
    (h • A).card ∉ Set.Icc (h * k - h + 2) (h * k - 1) := by
  classical
  let : HasUniqueDiv G := IsAddTorsionFree.hasUniqueDiv
  -- Only the subgroup spanned by A needs an order. A finite integral basis gives it one.
  let M := Submodule.span ℤ (A : Set G)
  obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := M)
  let e := b.repr.toAddEquiv.trans (toLexAddEquiv (Fin r →₀ ℤ))
  let : LinearOrder M := LinearOrder.lift' e e.injective
  let : IsOrderedAddMonoid M :=
    { add_le_add_left := fun a b hab c => by
        change e (a + c) ≤ e (b + c)
        change e a ≤ e b at hab
        simpa only [map_add] using add_le_add_left hab (e c) }
  let B : Finset M := A.subtype (· ∈ M)
  have hmap : B.image M.subtype = A := by
    change B.image (Function.Embedding.subtype _) = A
    rw [← Finset.map_eq_image]
    exact Finset.subtype_map_of_mem fun _ ha => Submodule.subset_span ha
  have hinj : Function.Injective M.subtype := Subtype.val_injective
  have hcard : B.card = k := by
    rwa [← hmap, Finset.card_image_of_injective _ hinj] at hA
  have hn : B.Nonempty := Finset.card_pos.mp (by omega)
  have he := card_nsmul_notMem_Icc_of_isAddTorsionFree.ordered_gap h hn
  rw [hcard] at he
  rwa [← hmap, ← Finset.image_nsmul, Finset.card_image_of_injective _ hinj]

end

end MetaMathlibExt
