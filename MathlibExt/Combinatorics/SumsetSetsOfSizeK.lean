/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Order.Fin.Basic

/-!
# Sumsets of sets of size `k`

We describe the trivial elements of an iterated sumset, show that adjoining a new maximum
preserves nontrivial sums, and bound their number when the final gap is a proper multiple of
the preceding one. We also compute the size of the sumset of an arithmetic progression with its
penultimate term removed.
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

end

end MetaMathlibExt
