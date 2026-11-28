/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Batteries.Data.List.Lemmas
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring

/-!
# Chu blocks and run sums

The two families of runs have prefixes of sum two, and their repeated segments are cyclic
shifts of one another.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Sets given by consecutive differences.** For an integer $a$ and natural numbers
$g_1, \dots, g_r$, the set $(a \mid g_1, \dots, g_r)$ is the finite set of integers
$\{a, a + g_1, a + g_1 + g_2, \dots, a + g_1 + \dots + g_r\}$; for $r = 0$ it is $\{a\}$.

When every $g_i$ is positive, the differences between consecutive elements of this set, listed
from the smallest element to the largest, are $g_1, \dots, g_r$; a zero gap repeats a partial
sum, which the set records once.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 1 (Spohn's notation). -/
public def setOfConsecutiveDifferences : ℤ → List ℕ → Finset ℤ
  | a, [] => {a}
  | a, g :: l => insert a (setOfConsecutiveDifferences (a + g) l)

/-- **Prepending a gap.** For an integer $a$ and natural numbers $g_1, \dots, g_r$ ($r \ge 0$),
write $(a \mid g_1, \dots, g_r)$ for the set of partial sums
$\{a, a + g_1, \dots, a + g_1 + \dots + g_r\}$. Then for every natural number $g$,
$(a \mid g, g_1, \dots, g_r) = \{a\} \cup (a + g \mid g_1, \dots, g_r)$.

When $g > 0$, the new element $a$ is smaller than every element of $(a + g \mid g_1, \dots, g_r)$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 1 (Spohn's notation). -/
public theorem setOfConsecutiveDifferences_cons (a : ℤ) (g : ℕ) (l : List ℕ) :
    setOfConsecutiveDifferences a (g :: l) = insert a (setOfConsecutiveDifferences (a + g) l) :=
  rfl

/-- **An example of difference notation.** The set with least element $0$ and consecutive
differences $1, 5, 1, 1, 9, 7$ is $(0 \mid 1, 5, 1, 1, 9, 7) = \{0, 1, 6, 7, 8, 17, 24\}$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 1 (Spohn's notation). -/
public theorem setOfConsecutiveDifferences_example :
    setOfConsecutiveDifferences 0 [1, 5, 1, 1, 9, 7] = {0, 1, 6, 7, 8, 17, 24} := by
  decide

/-- **Chu difference block.** For a natural number $k$, the difference block $M^k$ is the list of
natural numbers $1, 4, \ldots, 4, 3$ of length $k + 2$: a $1$, then $k$ copies of $4$, then a $3$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 1 (definition of `M^k`). -/
public def chuBlock (k : ℕ) : List ℕ :=
  1 :: List.replicate k 4 ++ [3]

/-- **The Chu difference blocks $M^1$ and $M^2$.** The Chu difference block $M^1$ is the list
$1, 4, 3$, and the Chu difference block $M^2$ is the list $1, 4, 4, 3$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 1 (definition of `M^k`). -/
public theorem chuBlock_one_two : chuBlock 1 = [1, 4, 3] ∧ chuBlock 2 = [1, 4, 4, 3] :=
  ⟨rfl, rfl⟩

/-- **Kumar–Mohan–Pandey sets.** For natural numbers $k$, $l$, $t$, let $M^n$ be the block
$1, 4, \dots, 4, 3$ with $n$ fours, and let $D$ be the sequence made of $t$ copies of the block
$1, 1, 2, M^k, \dots, M^k$ (with $l$ copies of $M^k$) followed by $1, 1, 2, 1$. The set
$A_{k,l,t}$ is $(0 \mid D)$, the set of partial sums of $D$ starting from $0$.

Each block $1, 1, 2, M^k, \dots, M^k$ has sum $4(kl + l + 1)$, matching the bounds
$t(kl + l + 1)$ in Lemmas 1-7 of the paper.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 3 (the set of Lemmas 1-7 and
Theorems 6-7). -/
public def chuFamilyKLT (k l t : ℕ) : Finset ℤ :=
  setOfConsecutiveDifferences 0
    ((List.replicate t ([1, 1, 2] ++ (List.replicate l (chuBlock k)).flatten)).flatten ++
      [1, 1, 2, 1])

/-- **The Kumar–Mohan–Pandey set $A_{1,1,1}$.** For $k = l = t = 1$, the Kumar–Mohan–Pandey set
$A_{1,1,1}$, the set of partial sums starting from $0$ of the sequence
$1, 1, 2, 1, 4, 3, 1, 1, 2, 1$, is $\{0, 1, 2, 4, 5, 9, 12, 13, 14, 16, 17\}$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Section 3 (the set of Lemmas 1-7 and
Theorems 6-7). -/
public theorem chuFamilyKLT_one_one_one :
    chuFamilyKLT 1 1 1 = {0, 1, 2, 4, 5, 9, 12, 13, 14, 16, 17} := by
  decide

private theorem self_mem_setOfConsecutiveDifferences (a : ℤ) (l : List ℕ) :
    a ∈ setOfConsecutiveDifferences a l := by
  cases l <;> simp [setOfConsecutiveDifferences]

private theorem setOfConsecutiveDifferences_append (a : ℤ) (p q : List ℕ) :
    setOfConsecutiveDifferences a (p ++ q) =
      setOfConsecutiveDifferences a p ∪ setOfConsecutiveDifferences (a + (p.sum : ℤ)) q := by
  induction p generalizing a with
  | nil => simp [setOfConsecutiveDifferences, self_mem_setOfConsecutiveDifferences]
  | cons g p ih =>
      simp [setOfConsecutiveDifferences_cons, ih, Finset.insert_union, add_assoc]

-- A repeated block covers consecutive intervals of grid indices, with no gap at a join.
private theorem mem_repeated_grid {b : List ℕ} {m : ℕ} (hs : b.sum = 4 * m)
    (hb : ∀ (a : ℤ) (i : ℕ), i < m →
      a + 4 * (i : ℤ) + 1 ∈ setOfConsecutiveDifferences a b)
    (n : ℕ) (a : ℤ) (i : ℕ) (hi : i < n * m) :
    a + 4 * (i : ℤ) + 1 ∈ setOfConsecutiveDifferences a (List.replicate n b).flatten := by
  induction n generalizing a i with
  | zero => simp at hi
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, setOfConsecutiveDifferences_append,
        Finset.mem_union]
      by_cases h : i < m
      · exact Or.inl (hb a i h)
      · have hsub : i - m < n * m := by rw [Nat.succ_mul] at hi; omega
        have ha : a + 4 * (i : ℤ) + 1 = a + (b.sum : ℤ) + 4 * ((i - m : ℕ) : ℤ) + 1 := by
          simp only [hs, Int.natCast_mul]
          omega
        rw [ha]
        exact Or.inr (ih (a + (b.sum : ℤ)) (i - m) hsub)

private theorem chuBlock_sum (k : ℕ) : (chuBlock k).sum = 4 * (k + 1) := by
  simp [chuBlock, List.sum_append]
  omega

private theorem mem_chuBlock_grid (k : ℕ) (a : ℤ) (i : ℕ) (hi : i < k + 1) :
    a + 4 * (i : ℤ) + 1 ∈ setOfConsecutiveDifferences a (chuBlock k) := by
  have hsplit : List.replicate k 4 = List.replicate i 4 ++ List.replicate (k - i) 4 := by
    rw [← List.replicate_add, Nat.add_sub_of_le (by omega)]
  change a + 4 * (i : ℤ) + 1 ∈
    setOfConsecutiveDifferences a (1 :: (List.replicate k 4 ++ [3]))
  rw [setOfConsecutiveDifferences_cons, Finset.mem_insert, hsplit, List.append_assoc,
    setOfConsecutiveDifferences_append, Finset.mem_union]
  refine Or.inr (Or.inr ?_)
  have ha : a + 4 * (i : ℤ) + 1 = a + 1 + ((List.replicate i 4).sum : ℤ) := by
    rw [List.sum_replicate]
    change a + 4 * (i : ℤ) + 1 = a + 1 + ((i * 4 : ℕ) : ℤ)
    omega
  rw [ha]
  cases k - i <;> simp [List.replicate_succ, setOfConsecutiveDifferences]

-- Keep the original named hypotheses even though the block argument also covers zero parameters.
set_option linter.unusedVariables false in
/-- **Elements of the Kumar–Mohan–Pandey sets (Lemma 4).** Let $k$, $l$, $t$ be positive
integers, let $A = A_{k,l,t}$ be the Kumar–Mohan–Pandey set, and put $T = t(kl + l + 1)$. Then
$1 + 4i \in A$ for every integer $i$ with $0 \le i \le 1 + T$, and $2 + 4T \in A$ and
$4 + 4T \in A$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Lemma 4 (`integers-2024-A32-lem-4`). -/
public theorem chuFamilyKLT_mem {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t) :
    (∀ i : ℕ, i ≤ 1 + t * (k * l + l + 1) → 1 + 4 * (i : ℤ) ∈ chuFamilyKLT k l t) ∧
      2 + 4 * ((t * (k * l + l + 1) : ℕ) : ℤ) ∈ chuFamilyKLT k l t ∧
      4 + 4 * ((t * (k * l + l + 1) : ℕ) : ℤ) ∈ chuFamilyKLT k l t := by
  let b := [1, 1, 2] ++ (List.replicate l (chuBlock k)).flatten
  let m := k * l + l + 1
  let T := t * m
  have hm : m = l * (k + 1) + 1 := by simp [m, Nat.mul_add, Nat.mul_comm]
  have hs : b.sum = 4 * m := by
    rw [hm, Nat.mul_add, Nat.mul_one]
    simp [b, List.sum_flatten, chuBlock_sum, Nat.mul_left_comm, Nat.add_comm]
    omega
  -- The header supplies index 0, and the Chu blocks supply the remaining indices.
  have hb (a : ℤ) (i : ℕ) (hi : i < m) :
      a + 4 * (i : ℤ) + 1 ∈ setOfConsecutiveDifferences a b := by
    cases i with
    | zero => simp [b, setOfConsecutiveDifferences]
    | succ i =>
        rw [hm] at hi
        change _ ∈ setOfConsecutiveDifferences a ([1, 1, 2] ++
          (List.replicate l (chuBlock k)).flatten)
        rw [setOfConsecutiveDifferences_append, Finset.mem_union]
        right
        have ha : a + 4 * ((i + 1 : ℕ) : ℤ) + 1 = a + 4 + 4 * (i : ℤ) + 1 := by
          simp only [Int.natCast_add]
          omega
        rw [ha]
        exact mem_repeated_grid (chuBlock_sum k) (mem_chuBlock_grid k) l
          (a + 4) i (by omega)
  have hsum : (List.replicate t b).flatten.sum = 4 * T := by
    simp [List.sum_flatten, hs, T, Nat.mul_left_comm]
  -- The fixed tail starts at 4T, after the t repeated blocks.
  have hfamily : chuFamilyKLT k l t =
      setOfConsecutiveDifferences 0 (List.replicate t b).flatten ∪
        setOfConsecutiveDifferences (4 * (T : ℤ)) [1, 1, 2, 1] := by
    change setOfConsecutiveDifferences 0
      ((List.replicate t b).flatten ++ [1, 1, 2, 1]) = _
    rw [setOfConsecutiveDifferences_append]
    simp [hsum]
  change (∀ i : ℕ, i ≤ 1 + T → 1 + 4 * (i : ℤ) ∈ chuFamilyKLT k l t) ∧
    2 + 4 * (T : ℤ) ∈ chuFamilyKLT k l t ∧ 4 + 4 * (T : ℤ) ∈ chuFamilyKLT k l t
  simp only [hfamily, Finset.mem_union]
  refine ⟨?_, Or.inr ?_, Or.inr ?_⟩
  · intro i hi
    by_cases hit : i < T
    · left
      simpa only [zero_add, add_comm] using mem_repeated_grid hs hb t 0 i hit
    · right
      have h : i = T ∨ i = T + 1 := by omega
      rcases h with rfl | rfl <;>
        simp only [setOfConsecutiveDifferences, Finset.mem_insert,
          Finset.mem_singleton, Int.natCast_add] <;> omega
  · simp only [setOfConsecutiveDifferences, Finset.mem_insert, Finset.mem_singleton]
    omega
  · simp only [setOfConsecutiveDifferences, Finset.mem_insert, Finset.mem_singleton]
    omega

open scoped Pointwise in
/-- **Differences in the Kumar–Mohan–Pandey sets (Lemma 1).** Let $k$, $l$, $t$ be positive
integers, let $A = A_{k,l,t}$ be the Kumar–Mohan–Pandey set, and put $T = t(kl + l + 1)$. Then
the difference set $A - A$ contains $4i$ and $1 + 4i$ for every integer $i$ with
$1 \le i \le 1 + T$, and contains $3 + 4i$ for every integer $i$ with $0 \le i \le T$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Lemma 1 (`integers-2024-A32-lem-1`). -/
public theorem chuFamilyKLT_mem_sub {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t) :
    (∀ i : ℕ, 1 ≤ i → i ≤ 1 + t * (k * l + l + 1) →
        4 * (i : ℤ) ∈ chuFamilyKLT k l t - chuFamilyKLT k l t ∧
          1 + 4 * (i : ℤ) ∈ chuFamilyKLT k l t - chuFamilyKLT k l t) ∧
      ∀ i : ℕ, i ≤ t * (k * l + l + 1) →
        3 + 4 * (i : ℤ) ∈ chuFamilyKLT k l t - chuFamilyKLT k l t := by
  let A := chuFamilyKLT k l t
  let T := t * (k * l + l + 1)
  change (∀ i : ℕ, 1 ≤ i → i ≤ 1 + T →
      4 * (i : ℤ) ∈ A - A ∧ 1 + 4 * (i : ℤ) ∈ A - A) ∧
    ∀ i : ℕ, i ≤ T → 3 + 4 * (i : ℤ) ∈ A - A
  obtain ⟨hgrid, -, hlast⟩ := chuFamilyKLT_mem hk hl ht
  change 4 + 4 * (T : ℤ) ∈ A at hlast
  have hzero : (0 : ℤ) ∈ A := by
    cases t <;> simp [A, chuFamilyKLT, List.replicate_succ, List.flatten_cons,
      List.append_assoc, setOfConsecutiveDifferences_cons]
  have hone : (1 : ℤ) ∈ A := by
    simpa using hgrid 0 (Nat.zero_le _)
  have sub_mem {a b c : ℤ} (ha : a ∈ A) (hb : b ∈ A) (h : a - b = c) : c ∈ A - A :=
    h ▸ Finset.sub_mem_sub ha hb
  constructor
  · intro i _ hi
    exact ⟨sub_mem (hgrid i hi) hone (by omega), sub_mem (hgrid i hi) hzero (by omega)⟩
  · intro i hi
    -- Subtract the grid point with reflected index `T - i` from the tail point.
    exact sub_mem hlast (hgrid (T - i) (by change T - i ≤ 1 + T; omega)) (by omega)

open scoped Pointwise in
/-- **Elements of the sumset of the Chu family set.** Let $k$, $l$, $t$ be positive integers, let
$A \subseteq \mathbb{Z}$ be the Chu family set with parameters $k$, $l$, $t$, and let
$T = t(kl + l + 1)$. Then $1 + 4i$ and $2 + 4i$ lie in $A + A$ for every integer $i$ with
$0 \le i \le 2 + 2T$, and $3 + 4i$ lies in $A + A$ for every integer $i$ with $0 \le i \le 1 + 2T$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Lemma 5 (`integers-2024-A32-lem-5`). -/
public theorem chuFamilyKLT_mem_add {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t) :
    (∀ i : ℕ, i ≤ 2 + 2 * (t * (k * l + l + 1)) →
        1 + 4 * (i : ℤ) ∈ chuFamilyKLT k l t + chuFamilyKLT k l t ∧
          2 + 4 * (i : ℤ) ∈ chuFamilyKLT k l t + chuFamilyKLT k l t) ∧
      ∀ i : ℕ, i ≤ 1 + 2 * (t * (k * l + l + 1)) →
        3 + 4 * (i : ℤ) ∈ chuFamilyKLT k l t + chuFamilyKLT k l t := by
  let A := chuFamilyKLT k l t
  let T := t * (k * l + l + 1)
  change (∀ i : ℕ, i ≤ 2 + 2 * T →
      1 + 4 * (i : ℤ) ∈ A + A ∧ 2 + 4 * (i : ℤ) ∈ A + A) ∧
    ∀ i : ℕ, i ≤ 1 + 2 * T → 3 + 4 * (i : ℤ) ∈ A + A
  have ⟨hgrid, hlast₂, hlast₄⟩ := chuFamilyKLT_mem hk hl ht
  have hpoint (i : ℕ) (hi : i ≤ 1 + T) : 1 + 4 * (i : ℤ) ∈ A := hgrid i hi
  change 2 + 4 * (T : ℤ) ∈ A at hlast₂
  change 4 + 4 * (T : ℤ) ∈ A at hlast₄
  have ⟨hzero, htwo⟩ : (0 : ℤ) ∈ A ∧ (2 : ℤ) ∈ A := by
    change (0 : ℤ) ∈ chuFamilyKLT k l t ∧ (2 : ℤ) ∈ chuFamilyKLT k l t
    cases t <;> simp [chuFamilyKLT, List.replicate_succ, List.flatten_cons,
      List.append_assoc, setOfConsecutiveDifferences_cons]
  have add_mem {a b c : ℤ} (ha : a ∈ A) (hb : b ∈ A) (h : a + b = c) : c ∈ A + A :=
    h ▸ Finset.add_mem_add ha hb
  constructor
  · intro i hi
    by_cases h : i ≤ 1 + T
    · exact ⟨add_mem hzero (hpoint i h) (by omega),
        add_mem (hpoint 0 (by omega)) (hpoint i h) (by omega)⟩
    · -- Pair with the last block, subtracting its grid index from the other summand.
      have hrest := hpoint (i - (1 + T)) (by omega)
      exact ⟨add_mem hlast₄ hrest (by omega),
        add_mem (hpoint (1 + T) le_rfl) hrest (by omega)⟩
  · intro i hi
    by_cases h : i ≤ 1 + T
    · exact add_mem htwo (hpoint i h) (by omega)
    · exact add_mem hlast₂ (hpoint (i - T) (by omega)) (by omega)

-- Keep the original named hypotheses although the prefix argument does not need them.
set_option linter.unusedVariables false in
/-- **Block starting points of the Chu family set.** Let $k$, $l$, $t$ be positive integers and
let $A \subseteq \mathbb{Z}$ be the Chu family set with parameters $k$, $l$, $t$. Then
$4 + (4k + 4)i + (4kl + 4l + 4)j \in A$ for all integers $i$, $j$ with $0 \le i \le l$ and
$0 \le j \le t - 1$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Lemma 6 (`integers-2024-A32-lem-6`). -/
public theorem chuFamilyKLT_mem_block_starts {k l t : ℕ} (hk : 0 < k) (hl : 0 < l)
    (ht : 0 < t) (i j : ℕ) (hi : i ≤ l) (hj : j < t) :
    4 + (4 * k + 4) * (i : ℤ) + (4 * k * l + 4 * l + 4) * (j : ℤ) ∈
      chuFamilyKLT k l t := by
  let block := [1, 1, 2] ++ (List.replicate l (chuBlock k)).flatten
  let before := (List.replicate j block).flatten ++ [1, 1, 2] ++
    (List.replicate i (chuBlock k)).flatten
  let after := (List.replicate (l - i) (chuBlock k)).flatten ++
    (List.replicate (t - (j + 1)) block).flatten ++ [1, 1, 2, 1]
  have hOuter : (List.replicate t block).flatten =
      (List.replicate j block).flatten ++ block ++
        (List.replicate (t - (j + 1)) block).flatten := by
    conv_lhs => rw [show t = j + (1 + (t - (j + 1))) by omega]
    simp only [List.replicate_add, List.replicate_one, List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.append_assoc]
  have hInner : (List.replicate l (chuBlock k)).flatten =
      (List.replicate i (chuBlock k)).flatten ++ (List.replicate (l - i) (chuBlock k)).flatten := by
    conv_lhs => rw [show l = i + (l - i) by omega]
    rw [List.replicate_add i (l - i), List.flatten_append]
  have hblock : block = [1, 1, 2] ++ (List.replicate i (chuBlock k)).flatten ++
      (List.replicate (l - i) (chuBlock k)).flatten := by
    dsimp only [block]
    rw [hInner, List.append_assoc]
  have hgaps : chuFamilyKLT k l t = setOfConsecutiveDifferences 0 (before ++ after) := by
    change setOfConsecutiveDifferences 0 ((List.replicate t block).flatten ++ [1, 1, 2, 1]) = _
    rw [hOuter]
    -- Split only the current block, leaving the complete blocks unchanged.
    refine (congrArg (fun current => setOfConsecutiveDifferences 0
      ((List.replicate j block).flatten ++ current ++
        (List.replicate (t - (j + 1)) block).flatten ++ [1, 1, 2, 1])) hblock).trans ?_
    simp only [before, after, List.append_assoc]
  have hsum : 0 + (before.sum : ℤ) =
      4 + (4 * k + 4) * (i : ℤ) + (4 * k * l + 4 * l + 4) * (j : ℤ) := by
    simp [before, block, chuBlock_sum, List.sum_flatten, Int.mul_add, Int.add_mul,
      mul_left_comm, mul_comm]
    omega
  rw [hgaps, ← hsum, setOfConsecutiveDifferences_append, Finset.mem_union]
  right
  cases after <;> simp [setOfConsecutiveDifferences]

-- With natural gaps, every element lies between the start and the start plus the total gap.
private theorem mem_setOfConsecutiveDifferences_bounds {a x : ℤ} {l : List ℕ}
    (hx : x ∈ setOfConsecutiveDifferences a l) : a ≤ x ∧ x ≤ a + (l.sum : ℤ) := by
  induction l generalizing a with
  | nil =>
      rw [setOfConsecutiveDifferences, Finset.mem_singleton] at hx
      simp [hx]
  | cons g l ih =>
      rw [setOfConsecutiveDifferences_cons, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · simp only [List.sum_cons, Nat.cast_add]
        omega
      · have := ih hx
        simp only [List.sum_cons, Nat.cast_add]
        omega

private theorem mem_setOfConsecutiveDifferences_replicate {g n : ℕ} {a x : ℤ}
    (hx : x ∈ setOfConsecutiveDifferences a (List.replicate n g)) :
    ∃ i ≤ n, x = a + ((i * g : ℕ) : ℤ) := by
  induction n generalizing a with
  | zero => exact ⟨0, le_rfl, by simpa [setOfConsecutiveDifferences] using hx⟩
  | succ n ih =>
      rw [List.replicate_succ, setOfConsecutiveDifferences_cons, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact ⟨0, Nat.zero_le _, by simp⟩
      · obtain ⟨i, hi, rfl⟩ := ih hx
        exact ⟨i + 1, by omega, by push_cast; ring⟩

-- An element of a repeated block lies in one copy of the block or is the final endpoint.
private theorem mem_setOfConsecutiveDifferences_replicate_flatten {b : List ℕ} {n : ℕ}
    {a x : ℤ} (hx : x ∈ setOfConsecutiveDifferences a (List.replicate n b).flatten) :
    x = a + ((n * b.sum : ℕ) : ℤ) ∨
      ∃ j < n, x ∈ setOfConsecutiveDifferences (a + ((j * b.sum : ℕ) : ℤ)) b := by
  induction n generalizing a with
  | zero => left; simpa [setOfConsecutiveDifferences] using hx
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, setOfConsecutiveDifferences_append,
        Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact Or.inr ⟨0, by omega, by simpa using hx⟩
      · rcases ih hx with rfl | ⟨j, hj, hx⟩
        · left; push_cast; ring
        · refine Or.inr ⟨j + 1, by omega, ?_⟩
          convert hx using 2
          push_cast; ring

private theorem mem_setOfConsecutiveDifferences_chuBlock {k : ℕ} {p x : ℤ}
    (hx : x ∈ setOfConsecutiveDifferences p (chuBlock k)) :
    x = p ∨ (∃ i ≤ k, x = p + 1 + 4 * (i : ℤ)) ∨ x = p + 4 * ((k + 1 : ℕ) : ℤ) := by
  change x ∈ setOfConsecutiveDifferences p (1 :: (List.replicate k 4 ++ [3])) at hx
  rw [setOfConsecutiveDifferences_cons, Finset.mem_insert, setOfConsecutiveDifferences_append,
    Finset.mem_union] at hx
  rcases hx with rfl | hx | hx
  · exact Or.inl rfl
  · obtain ⟨i, hi, rfl⟩ := mem_setOfConsecutiveDifferences_replicate hx
    exact Or.inr (Or.inl ⟨i, hi, by push_cast; ring⟩)
  · simp only [setOfConsecutiveDifferences, Finset.mem_insert, Finset.mem_singleton,
      List.sum_replicate_nat] at hx
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl ⟨k, le_rfl, by push_cast; ring⟩)
    · right; right; push_cast; ring

private theorem chuFamilyKLT_block_sum (k l : ℕ) :
    ([1, 1, 2] ++ (List.replicate l (chuBlock k)).flatten).sum = 4 * (k * l + l + 1) := by
  simp [List.sum_flatten, chuBlock_sum]
  ring

-- Every element is `1 + 4n`, or `2 + 4mj`, `4mj` or `4(tm + 1)`, or a block start.
private theorem chuFamilyKLT_mem_cases {k l t m : ℕ} (hm : m = k * l + l + 1) {x : ℤ}
    (hx : x ∈ chuFamilyKLT k l t) :
    (∃ n : ℕ, x = 1 + 4 * (n : ℤ)) ∨ (∃ j ≤ t, x = 2 + 4 * ((m * j : ℕ) : ℤ)) ∨
      (∃ j ≤ t, x = 4 * ((m * j : ℕ) : ℤ)) ∨ x = 4 * ((t * m + 1 : ℕ) : ℤ) ∨
      ∃ i ≤ l, ∃ j < t, x = 4 * ((1 + (k + 1) * i + m * j : ℕ) : ℤ) := by
  have hb := chuFamilyKLT_block_sum k l
  rw [← hm] at hb
  unfold chuFamilyKLT at hx
  rw [setOfConsecutiveDifferences_append, Finset.mem_union] at hx
  rcases hx with hx | hx
  · rcases mem_setOfConsecutiveDifferences_replicate_flatten hx with rfl | ⟨j, hj, hx⟩
    · refine Or.inr (Or.inr (Or.inl ⟨t, le_rfl, ?_⟩))
      rw [hb]; push_cast; ring
    rw [hb, setOfConsecutiveDifferences_append, Finset.mem_union,
      show ([1, 1, 2] : List ℕ).sum = 4 from rfl] at hx
    rcases hx with hx | hx
    · simp only [setOfConsecutiveDifferences, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl ⟨j, hj.le, by push_cast; ring⟩))
      · exact Or.inl ⟨m * j, by push_cast; ring⟩
      · exact Or.inr (Or.inl ⟨j, hj.le, by push_cast; ring⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨0, Nat.zero_le _, j, hj, by push_cast; ring⟩)))
    rcases mem_setOfConsecutiveDifferences_replicate_flatten hx with rfl | ⟨i, hi, hx⟩
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨l, le_rfl, j, hj, ?_⟩)))
      rw [chuBlock_sum]; push_cast; ring
    rw [chuBlock_sum] at hx
    rcases mem_setOfConsecutiveDifferences_chuBlock hx with rfl | ⟨i', -, rfl⟩ | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi.le, j, hj, by push_cast; ring⟩)))
    · exact Or.inl ⟨m * j + 1 + (k + 1) * i + i', by push_cast; ring⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i + 1, hi, j, hj, by push_cast; ring⟩)))
  · have hs : (List.replicate t
        ([1, 1, 2] ++ (List.replicate l (chuBlock k)).flatten)).flatten.sum = 4 * (t * m) := by
      rw [List.sum_flatten, List.map_replicate, hb, List.sum_replicate_nat]
      ring
    simp only [hs, setOfConsecutiveDifferences, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨t, le_rfl, by push_cast; ring⟩))
    · exact Or.inl ⟨t * m, by push_cast; ring⟩
    · exact Or.inr (Or.inl ⟨t, le_rfl, by push_cast; ring⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by push_cast; ring))))
    · exact Or.inl ⟨t * m + 1, by push_cast; ring⟩

private theorem chuFamilyKLT_mem_bounds {k l t : ℕ} {x : ℤ} (hx : x ∈ chuFamilyKLT k l t) :
    0 ≤ x ∧ x ≤ 4 * ((t * (k * l + l + 1) : ℕ) : ℤ) + 5 := by
  have h := mem_setOfConsecutiveDifferences_bounds hx
  have hs : ((List.replicate t ([1, 1, 2] ++ (List.replicate l (chuBlock k)).flatten)).flatten ++
      [1, 1, 2, 1]).sum = 4 * (t * (k * l + l + 1)) + 5 := by
    rw [List.sum_append, List.sum_flatten, List.map_replicate, chuFamilyKLT_block_sum,
      List.sum_replicate_nat, show ([1, 1, 2, 1] : List ℕ).sum = 5 from rfl]
    ring
  rw [hs] at h
  push_cast at h ⊢
  omega

-- The numbers `ms + (k + 1)i` with `s < t` and `i ≤ l`, and `tm`, are pairwise distinct.
private theorem card_insert_image_mul_add {k l t m : ℕ} (hm : m = (k + 1) * l + 1) :
    (insert (t * m) ((Finset.range t ×ˢ Finset.range (l + 1)).image
      fun p => m * p.1 + (k + 1) * p.2)).card = t * (l + 1) + 1 := by
  have hlt (i : ℕ) (hi : i ≤ l) : (k + 1) * i < m := by
    have := Nat.mul_le_mul_left (k + 1) hi
    omega
  rw [Finset.card_insert_of_notMem, Finset.card_image_of_injOn, Finset.card_product,
    Finset.card_range, Finset.card_range]
  · rintro ⟨s, i⟩ hp ⟨s', i'⟩ hp' h
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp hp' h
    have hs : s = s' := by
      have e := congrArg (· / m) h
      simp only [Nat.mul_add_div (by omega : 0 < m), Nat.div_eq_of_lt (hlt i (by omega)),
        Nat.div_eq_of_lt (hlt i' (by omega)), add_zero] at e
      exact e
    subst hs
    rw [Prod.mk.injEq]
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by omega : 0 < k + 1) (by omega)⟩
  · simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range, not_exists, not_and,
      Prod.forall]
    rintro s i ⟨hs, hi⟩ h
    have h1 := hlt i (by omega)
    have h2 := Nat.mul_le_mul_left m (Nat.succ_le_of_lt hs)
    rw [Nat.mul_succ, Nat.mul_comm m t] at h2
    omega

open scoped Pointwise in
/-- **Size of the difference set of the Chu family set.** Let $k$, $l$, $t$ be positive integers
and let $A \subseteq \mathbb{Z}$ be the Chu family set with parameters $k$, $l$, $t$. Then
$|A - A| = 11 + 6klt + 8lt + 8t$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Theorem 6 (`integers-2024-A32-thm-6`). -/
public theorem chuFamilyKLT_card_sub {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t) :
    (chuFamilyKLT k l t - chuFamilyKLT k l t).card = 11 + 6 * k * l * t + 8 * l * t + 8 * t := by
  obtain ⟨m, hm⟩ : ∃ m, m = k * l + l + 1 := ⟨_, rfl⟩
  set A := chuFamilyKLT k l t
  obtain ⟨hgrid, hlast₂, hlast₄⟩ := chuFamilyKLT_mem hk hl ht
  rw [← hm] at hgrid hlast₂ hlast₄
  have hzero : (0 : ℤ) ∈ A := self_mem_setOfConsecutiveDifferences 0 _
  have hstart (i j : ℕ) (hi : i ≤ l) (hj : j < t) :
      4 * ((1 + (k + 1) * i + m * j : ℕ) : ℤ) ∈ A := by
    convert chuFamilyKLT_mem_block_starts hk hl ht i j hi hj using 1
    subst hm; push_cast; ring
  have hbound (x : ℤ) (hx : x ∈ A) : 0 ≤ x ∧ x ≤ 4 * ((t * m : ℕ) : ℤ) + 5 := by
    rw [hm]; exact chuFamilyKLT_mem_bounds hx
  -- The positive differences `2 + 4v` are those with `v ∈ V`.
  set V : Finset ℕ := insert (t * m)
    ((Finset.range t ×ˢ Finset.range (l + 1)).image fun p => m * p.1 + (k + 1) * p.2) with hV
  have hVgen (s i : ℕ) (hs : s < t) (hi : i ≤ l) : m * s + (k + 1) * i ∈ V :=
    Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(s, i), Finset.mem_product.2
      ⟨Finset.mem_range.2 hs, Finset.mem_range.2 (Nat.lt_succ_of_le hi)⟩, rfl⟩)
  have hVmul (s : ℕ) (hs : s ≤ t) : m * s ∈ V := by
    rcases hs.lt_or_eq with hs | rfl
    · simpa using hVgen s 0 hs (Nat.zero_le _)
    · rw [Nat.mul_comm]; exact Finset.mem_insert_self _ _
  have hVcases (v : ℕ) (hv : v ∈ V) :
      v = t * m ∨ ∃ s < t, ∃ i ≤ l, v = m * s + (k + 1) * i := by
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact Or.inl rfl
    obtain ⟨⟨s, i⟩, hp, rfl⟩ := Finset.mem_image.1 hv
    simp only [Finset.mem_product, Finset.mem_range] at hp
    exact Or.inr ⟨s, hp.1, i, by omega, rfl⟩
  -- Differences `≡ 2 (mod 4)` subtract an element `≡ 0` from one `≡ 2`, or the reverse.
  have key (j : ℕ) (hj : j ≤ t) (b : ℤ)
      (hb : (∃ j ≤ t, b = 4 * ((m * j : ℕ) : ℤ)) ∨ b = 4 * ((t * m + 1 : ℕ) : ℤ) ∨
        ∃ i ≤ l, ∃ j < t, b = 4 * ((1 + (k + 1) * i + m * j : ℕ) : ℤ)) :
      ∃ v ∈ V, 2 + 4 * ((m * j : ℕ) : ℤ) - b = 2 + 4 * (v : ℤ) ∨
        b - (2 + 4 * ((m * j : ℕ) : ℤ)) = 2 + 4 * (v : ℤ) := by
    rcases hb with ⟨j', hj', rfl⟩ | rfl | ⟨i, hi, j', hj', rfl⟩
    · rcases le_or_gt j' j with h | h
      · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h
        exact ⟨m * s, hVmul s (by omega), Or.inl (by push_cast; ring)⟩
      · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_lt h
        refine ⟨m * s + (k + 1) * l, hVgen s l (by omega) le_rfl, Or.inr ?_⟩
        subst hm; push_cast; ring
    · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hj
      exact ⟨m * s, hVmul s (by omega), Or.inr (by push_cast; ring)⟩
    · rcases lt_or_ge j' j with h | h
      · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_lt h
        obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_le hi
        refine ⟨m * s + (k + 1) * i', hVgen s i' (by omega) (by omega), Or.inl ?_⟩
        subst hm; push_cast; ring
      · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h
        exact ⟨m * s + (k + 1) * i, hVgen s i (by omega) hi, Or.inr (by push_cast; ring)⟩
  have hres (x : ℤ) (hx : (∃ j ≤ t, x = 4 * ((m * j : ℕ) : ℤ)) ∨
      x = 4 * ((t * m + 1 : ℕ) : ℤ) ∨
        ∃ i ≤ l, ∃ j < t, x = 4 * ((1 + (k + 1) * i + m * j : ℕ) : ℤ)) : x % 4 = 0 := by
    rcases hx with ⟨_, _, rfl⟩ | rfl | ⟨_, _, _, _, rfl⟩ <;> omega
  have hsub (a b : ℤ) (ha : a ∈ A) (hb : b ∈ A) (h : (a - b) % 4 = 2) :
      ∃ v ∈ V, a - b = 2 + 4 * (v : ℤ) ∨ a - b = -2 - 4 * (v : ℤ) := by
    rcases chuFamilyKLT_mem_cases hm ha with ⟨n, rfl⟩ | ⟨j, hj, rfl⟩ | ha0 <;>
      rcases chuFamilyKLT_mem_cases hm hb with ⟨n', rfl⟩ | ⟨j', hj', rfl⟩ | hb0
    · omega
    · omega
    · have := hres b hb0; omega
    · omega
    · omega
    · obtain ⟨v, hv, h | h⟩ := key j hj b hb0
      exacts [⟨v, hv, Or.inl h⟩, ⟨v, hv, Or.inr (by omega)⟩]
    · have := hres a ha0; omega
    · obtain ⟨v, hv, h | h⟩ := key j' hj' a ha0
      exacts [⟨v, hv, Or.inr (by omega)⟩, ⟨v, hv, Or.inl h⟩]
    · have := hres a ha0; have := hres b hb0; omega
  -- The differences in the other residue classes fill `[-(4tm + 5), 4tm + 5]`.
  set I := Finset.Icc (-((t * m : ℕ) : ℤ) - 1) ((t * m : ℕ) + 1) with hI
  have hmemI (j : ℤ) : j ∈ I ↔ -((t * m : ℕ) : ℤ) - 1 ≤ j ∧ j ≤ (t * m : ℕ) + 1 := by
    rw [hI, Finset.mem_Icc]
  have hone (j : ℤ) (hj : j ∈ I) : ∃ a ∈ A, ∃ b ∈ A, a - b = 1 + 4 * j := by
    rw [hmemI] at hj
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
    · exact ⟨_, hgrid n (by omega), 0, hzero, by ring⟩
    · exact ⟨_, hgrid (t * m + 1 - n) (by omega), _, hlast₄, by omega⟩
  have htwo (v : ℕ) (hv : v ∈ V) : ∃ a ∈ A, ∃ b ∈ A, a - b = 2 + 4 * (v : ℤ) := by
    rcases hVcases v hv with rfl | ⟨s, hs, i, hi, rfl⟩
    · exact ⟨_, hlast₂, 0, hzero, by ring⟩
    · obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_le hi
      obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_lt hs
      refine ⟨_, hlast₂, _, hstart i' s' (by omega) (by omega), ?_⟩
      subst hm; push_cast; ring
  -- So `A - A` is the disjoint union of the classes `0`, `1` and `3 (mod 4)` of
  -- `[-(4tm + 5), 4tm + 5]` and the numbers `±(2 + 4v)` with `v ∈ V`.
  have hD : A - A = I.image (4 * ·) ∪ I.image (1 + 4 * ·) ∪ I.image (-1 + 4 * ·) ∪
      V.image (fun v : ℕ => 2 + 4 * (v : ℤ)) ∪ V.image (fun v : ℕ => -2 - 4 * (v : ℤ)) := by
    ext d
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_sub]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      have := hbound a ha
      have := hbound b hb
      have h4 : (a - b) % 4 = 0 ∨ (a - b) % 4 = 1 ∨ (a - b) % 4 = 2 ∨ (a - b) % 4 = 3 := by
        omega
      rcases h4 with h4 | h4 | h4 | h4
      · exact Or.inl (Or.inl (Or.inl (Or.inl
          ⟨(a - b) / 4, (hmemI _).2 ⟨by omega, by omega⟩, by omega⟩)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr
          ⟨(a - b - 1) / 4, (hmemI _).2 ⟨by omega, by omega⟩, by omega⟩)))
      · obtain ⟨v, hv, h | h⟩ := hsub a b ha hb h4
        · exact Or.inl (Or.inr ⟨v, hv, h.symm⟩)
        · exact Or.inr ⟨v, hv, h.symm⟩
      · exact Or.inl (Or.inl (Or.inr
          ⟨(a - b + 1) / 4, (hmemI _).2 ⟨by omega, by omega⟩, by omega⟩))
    · rintro ((((⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨v, hv, rfl⟩) | ⟨v, hv, rfl⟩)
      · rw [hmemI] at hj
        obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
        · exact ⟨_, hgrid n (by omega), _, hgrid 0 (by omega), by push_cast; ring⟩
        · exact ⟨_, hgrid 0 (by omega), _, hgrid n (by omega), by push_cast; ring⟩
      · exact hone j hj
      · obtain ⟨a, ha, b, hb, h⟩ := hone (-j) ((hmemI _).2 (by rw [hmemI] at hj; omega))
        exact ⟨b, hb, a, ha, by omega⟩
      · exact htwo v hv
      · obtain ⟨a, ha, b, hb, h⟩ := htwo v hv
        exact ⟨b, hb, a, ha, by omega⟩
  have hIcard : I.card = 2 * (t * m) + 3 := by
    rw [hI, Int.card_Icc]; omega
  have hVcard : V.card = t * (l + 1) + 1 := card_insert_image_mul_add (by rw [hm]; ring)
  rw [hD, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
    Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
    Finset.card_image_of_injective _ (fun a b h => by simpa using h),
    Finset.card_image_of_injective _ (fun a b h => by simpa using h),
    Finset.card_image_of_injective _ (fun a b h => by simpa using h),
    Finset.card_image_of_injective _ (fun a b h => by simpa using h),
    Finset.card_image_of_injective _ (fun a b h => by simpa using h), hIcard, hVcard]
  · subst hm; ring
  all_goals
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_union, Finset.mem_image] at hx hy
    obtain ⟨w, -, rfl⟩ := hy
    rcases hx with (((⟨a, -, h⟩ | ⟨a, -, h⟩) | ⟨a, -, h⟩) | ⟨a, -, h⟩) <;> omega

/-- **Two families of runs with the same sums (Proposition 1).** Let $k$, $l$, $t$ be natural
numbers, let $M^k$ be the block $1, 4, \dots, 4, 3$ with $k$ fours, and let $B$ be the
concatenation of $l$ copies of $M^k$. For $j \ge 1$ let $R_1(j)$ be the sequence $1, 1$ followed
by $j$ copies of $2, B, 1, 1$, and let $R_3(j)$ be the sequence $2$ followed by $j$ copies of
$B, 1, 1, 2$. Then the sums of the entries of $R_1(j)$ for $1 \le j \le t$ form the same set as
the sums of the entries of $R_3(j)$ for $1 \le j \le t$.

In the paper, $R_1$ and $R_3$ are runs of consecutive differences of the set of Lemma 2, so
they give the same positive differences of that set. The paper's hypothesis $k, l, t \ge 1$ is
not needed.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Proposition 1
(`integers-2024-A32-prop-1`). -/
public theorem chuFamilyKLT_run_sums_R1_eq_R3 (k l t : ℕ) :
    (Finset.Icc 1 t).image (fun j =>
        ([1, 1] ++ (List.replicate j
          (2 :: (List.replicate l (chuBlock k)).flatten ++ [1, 1])).flatten).sum) =
      (Finset.Icc 1 t).image (fun j =>
        (2 :: (List.replicate j
          ((List.replicate l (chuBlock k)).flatten ++ [1, 1, 2])).flatten).sum) := by
  apply Finset.image_congr
  intro j _
  simp [List.sum_flatten, Nat.add_left_comm]
  omega

open scoped Pointwise

-- The image of a set of quotients in one residue class modulo four.
private def chuResidue (r : ℤ) (s : Finset ℤ) : Finset ℤ :=
  s.image fun q => 4 * q + r

private theorem mem_chuResidue {r x : ℤ} {s : Finset ℤ} :
    x ∈ chuResidue r s ↔ ∃ q ∈ s, 4 * q + r = x :=
  Finset.mem_image

private def chuBalancedZero (p : ℤ) : Finset ℤ := {0, 1, p, 2 * p}

private def chuBalancedTwo (p : ℤ) : Finset ℤ := {0, 2 * p}

private def chuBalancedResidues (p : ℤ) : Finset ℤ :=
  chuResidue 0 (chuBalancedZero p) ∪ chuResidue 1 (Finset.Icc 0 (2 * p)) ∪
    chuResidue 2 (chuBalancedTwo p)

private theorem mem_replicate_four {a x : ℤ} (k : ℕ) :
    x ∈ setOfConsecutiveDifferences a (List.replicate k 4) ↔
      ∃ i : ℤ, 0 ≤ i ∧ i ≤ k ∧ x = a + 4 * i := by
  induction k generalizing a with
  | zero =>
    simp only [List.replicate_zero, setOfConsecutiveDifferences, Finset.mem_singleton,
      Int.natCast_zero]
    exact ⟨fun h => ⟨0, by omega⟩, fun ⟨i, hi, hki, hx⟩ => by omega⟩
  | succ k ih =>
    simp only [List.replicate_succ, setOfConsecutiveDifferences_cons, Finset.mem_insert, ih,
      Int.natCast_succ]
    constructor
    · rintro (h | ⟨i, hi, hki, hx⟩)
      · exact ⟨0, by omega⟩
      · exact ⟨i + 1, by omega⟩
    · rintro ⟨i, hi, hki, hx⟩
      by_cases h : i = 0
      · left; omega
      · exact Or.inr ⟨i - 1, by omega⟩

private theorem mem_chuBlock {a x : ℤ} (k : ℕ) :
    x ∈ setOfConsecutiveDifferences a (chuBlock k) ↔
      x = a ∨ (∃ i : ℤ, 0 ≤ i ∧ i ≤ k ∧ x = a + 4 * i + 1) ∨
        x = a + 4 * ((k : ℤ) + 1) := by
  change x ∈ setOfConsecutiveDifferences a (1 :: (List.replicate k 4 ++ [3])) ↔ _
  rw [setOfConsecutiveDifferences_cons, Finset.mem_insert, setOfConsecutiveDifferences_append,
    Finset.mem_union, mem_replicate_four, List.sum_replicate, nsmul_eq_mul, Int.natCast_mul]
  simp only [Nat.cast_id, setOfConsecutiveDifferences, Finset.mem_insert, Finset.mem_singleton]
  apply or_congr_right
  constructor
  · rintro (⟨i, hi, hki, hx⟩ | h | h)
    · exact Or.inl ⟨i, by omega⟩
    · exact Or.inl ⟨k, by omega⟩
    · right; omega
  · rintro (⟨i, hi, hki, hx⟩ | h)
    · exact Or.inl ⟨i, by omega⟩
    · exact Or.inr (Or.inr (by omega))

private theorem chuBalanced_eq (k : ℕ) :
    setOfConsecutiveDifferences 0 ([1, 1, 2] ++ chuBlock k ++ chuBlock (k + 1) ++ [1, 1]) =
      chuBalancedResidues ((k : ℤ) + 2) := by
  ext x
  rw [setOfConsecutiveDifferences_append, setOfConsecutiveDifferences_append,
    setOfConsecutiveDifferences_append]
  have h₁ : (([1, 1, 2].sum : ℕ) : ℤ) = 4 := rfl
  have h₂ : ((([1, 1, 2] ++ chuBlock k).sum : ℕ) : ℤ) = 4 * ((k : ℤ) + 2) := by
    simp only [List.sum_append, chuBlock_sum, Int.natCast_add, Int.natCast_mul, h₁]
    omega
  have h₃ : ((([1, 1, 2] ++ chuBlock k ++ chuBlock (k + 1)).sum : ℕ) : ℤ) =
      4 * (2 * ((k : ℤ) + 2)) := by
    simp only [List.sum_append, Int.natCast_add, chuBlock_sum, Int.natCast_mul]
    omega
  simp only [h₁, h₂, h₃, zero_add, Finset.mem_union, mem_chuBlock, Int.natCast_add,
    setOfConsecutiveDifferences, Finset.mem_insert, Finset.mem_singleton,
    chuBalancedResidues, mem_chuResidue, chuBalancedZero, chuBalancedTwo, Finset.mem_Icc]
  -- The header, two Chu blocks, and tail give the three residue classes of A.
  constructor
  · rintro ((((h | h | h | h) | (h | ⟨i, hi, hki, hx⟩ | h)) |
      (h | ⟨i, hi, hki, hx⟩ | h)) | (h | h | h))
    · exact Or.inl (Or.inl ⟨0, by omega⟩)
    · exact Or.inl (Or.inr ⟨0, by omega⟩)
    · exact Or.inr ⟨0, by omega⟩
    · exact Or.inl (Or.inl ⟨1, by omega⟩)
    · exact Or.inl (Or.inl ⟨1, by omega⟩)
    · exact Or.inl (Or.inr ⟨i + 1, by omega⟩)
    · exact Or.inl (Or.inl ⟨(k : ℤ) + 2, by omega⟩)
    · exact Or.inl (Or.inl ⟨(k : ℤ) + 2, by omega⟩)
    · exact Or.inl (Or.inr ⟨(k : ℤ) + 2 + i, by omega⟩)
    · exact Or.inl (Or.inl ⟨2 * ((k : ℤ) + 2), by omega⟩)
    · exact Or.inl (Or.inl ⟨2 * ((k : ℤ) + 2), by omega⟩)
    · exact Or.inl (Or.inr ⟨2 * ((k : ℤ) + 2), by omega⟩)
    · exact Or.inr ⟨2 * ((k : ℤ) + 2), by omega⟩
  · rintro ((⟨i, hi, hx⟩ | ⟨i, ⟨hi, hki⟩, hx⟩) | ⟨i, hi, hx⟩)
    · omega
    · -- The grid at residue one joins at k + 2, with endpoints in the header and tail.
      by_cases h₀ : i = 0
      · omega
      by_cases hlast : i = 2 * ((k : ℤ) + 2)
      · omega
      by_cases hmid : i < (k : ℤ) + 2
      · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl ⟨i - 1, by omega⟩))))
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨i - ((k : ℤ) + 2), by omega⟩)))
    · omega

private theorem chuResidue_add (r t : ℤ) (s u : Finset ℤ) :
    chuResidue r s + chuResidue t u = chuResidue (r + t) (s + u) := by
  unfold chuResidue
  change Finset.image₂ (· + ·) _ _ = (Finset.image₂ (· + ·) s u).image _
  symm
  exact Finset.image_image₂_distrib (fun a b => by omega)

private theorem chuResidue_sub (r t : ℤ) (s u : Finset ℤ) :
    chuResidue r s - chuResidue t u = chuResidue (r - t) (s - u) := by
  unfold chuResidue
  change Finset.image₂ (· - ·) _ _ = (Finset.image₂ (· - ·) s u).image _
  symm
  exact Finset.image_image₂_distrib (fun a b => by omega)

private theorem chuResidue_shift (r d : ℤ) (s : Finset ℤ) :
    chuResidue (r + 4 * d) s = chuResidue r (s.image (· + d)) := by
  simp only [chuResidue, Finset.image_image, Function.comp_def]
  congr 1
  funext q
  omega

private theorem chuResidue_union (r : ℤ) (s t : Finset ℤ) :
    chuResidue r (s ∪ t) = chuResidue r s ∪ chuResidue r t :=
  Finset.image_union _ _

private theorem card_chuResidue (r : ℤ) (s : Finset ℤ) : (chuResidue r s).card = s.card :=
  Finset.card_image_of_injective _ (fun _ _ h => by omega)

private theorem disjoint_chuResidue {r t : ℤ} (h : r % 4 ≠ t % 4) (s u : Finset ℤ) :
    Disjoint (chuResidue r s) (chuResidue t u) := by
  refine Finset.disjoint_left.mpr fun x hx hy => ?_
  obtain ⟨a, _, ha⟩ := mem_chuResidue.mp hx
  obtain ⟨b, _, hb⟩ := mem_chuResidue.mp hy
  exact h (by omega)

-- Only the endpoints of the sparse set are needed to fill the interval.
private theorem chu_add_interval {m : ℤ} {s : Finset ℤ} (hs : s ⊆ Finset.Icc 0 m)
    (h₀ : 0 ∈ s) (hm : m ∈ s) : s + Finset.Icc 0 m = Finset.Icc 0 (2 * m) := by
  ext x
  simp only [Finset.mem_add, Finset.mem_Icc]
  constructor
  · rintro ⟨a, ha, b, ⟨hb₀, hb₁⟩, rfl⟩
    have ⟨ha₀, ha₁⟩ := Finset.mem_Icc.mp (hs ha)
    omega
  · rintro ⟨hx₀, hx₁⟩
    by_cases hx : x ≤ m
    · exact ⟨0, h₀, x, ⟨hx₀, hx⟩, zero_add _⟩
    · exact ⟨m, hm, x - m, by omega, by omega⟩

private theorem chu_sub_interval {m : ℤ} {s : Finset ℤ} (hs : s ⊆ Finset.Icc 0 m)
    (h₀ : 0 ∈ s) (hm : m ∈ s) :
    Finset.Icc 0 m - s = Finset.Icc (-m) m ∧ s - Finset.Icc 0 m = Finset.Icc (-m) m := by
  have h : Finset.Icc 0 m - s = Finset.Icc (-m) m := by
    ext x
    simp only [Finset.mem_sub, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ⟨ha₀, ha₁⟩, b, hb, rfl⟩
      have ⟨hb₀, hb₁⟩ := Finset.mem_Icc.mp (hs hb)
      omega
    · rintro ⟨hx₀, hx₁⟩
      by_cases hx : 0 ≤ x
      · exact ⟨x, ⟨hx, hx₁⟩, 0, h₀, sub_zero _⟩
      · exact ⟨x + m, by omega, m, hm, by omega⟩
  refine ⟨h, ?_⟩
  ext x
  have hx : x ∈ s - Finset.Icc 0 m ↔ -x ∈ Finset.Icc 0 m - s := by
    simp only [Finset.mem_sub]
    constructor <;> rintro ⟨a, ha, b, hb, he⟩ <;> exact ⟨b, hb, a, ha, by omega⟩
  rw [hx, h]
  simp only [Finset.mem_Icc]
  omega

private theorem chu_add_subset {m : ℤ} {s t : Finset ℤ}
    (hs : s ⊆ Finset.Icc 0 m) (ht : t ⊆ Finset.Icc 0 m) :
    s + t ⊆ Finset.Icc 0 (2 * m) := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
  have ⟨ha₀, ha₁⟩ := Finset.mem_Icc.mp (hs ha)
  have ⟨hb₀, hb₁⟩ := Finset.mem_Icc.mp (ht hb)
  exact Finset.mem_Icc.mpr (by omega)

private theorem chu_sub_subset {m : ℤ} {s t : Finset ℤ}
    (hs : s ⊆ Finset.Icc 0 m) (ht : t ⊆ Finset.Icc 0 m) :
    s - t ⊆ Finset.Icc (-m) m := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
  have ⟨ha₀, ha₁⟩ := Finset.mem_Icc.mp (hs ha)
  have ⟨hb₀, hb₁⟩ := Finset.mem_Icc.mp (ht hb)
  exact Finset.mem_Icc.mpr (by omega)

private theorem chuBalanced_endpoints (p : ℤ) (hp : 1 ≤ p) :
    chuBalancedZero p ⊆ Finset.Icc 0 (2 * p) ∧
      chuBalancedTwo p ⊆ Finset.Icc 0 (2 * p) := by
  constructor <;> intro x hx <;>
    simp only [chuBalancedZero, chuBalancedTwo, Finset.mem_insert, Finset.mem_singleton] at hx <;>
    exact Finset.mem_Icc.mpr (by omega)

-- Only 0+0 and 2+2 contribute to residue zero; 2+2 carries one into the quotient.
private theorem chuBalanced_add_zero (p : ℤ) :
    chuBalancedZero p + chuBalancedZero p ∪ (chuBalancedTwo p + chuBalancedTwo p).image (· + 1) =
      {0, 1, 2, p, p + 1, 2 * p, 2 * p + 1, 3 * p, 4 * p, 4 * p + 1} := by
  change Finset.image₂ (· + ·) (chuBalancedZero p) (chuBalancedZero p) ∪
    (Finset.image₂ (· + ·) (chuBalancedTwo p) (chuBalancedTwo p)).image (· + 1) = _
  ext x
  simp only [chuBalancedZero, chuBalancedTwo, Finset.image₂_insert_left,
    Finset.image₂_singleton_left, Finset.image_insert, Finset.image_singleton,
    Finset.image_union, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  omega

private theorem chuBalanced_add_eq (p : ℤ) (hp : 1 ≤ p) :
    chuBalancedResidues p + chuBalancedResidues p =
      chuResidue 0 {0, 1, 2, p, p + 1, 2 * p, 2 * p + 1, 3 * p, 4 * p, 4 * p + 1} ∪
        chuResidue 1 (Finset.Icc 0 (4 * p)) ∪ chuResidue 2 (Finset.Icc 0 (4 * p)) ∪
        chuResidue 3 (Finset.Icc 0 (4 * p)) := by
  let I := Finset.Icc (0 : ℤ) (2 * p)
  obtain ⟨hZ, hT⟩ := chuBalanced_endpoints p hp
  have hZI : chuBalancedZero p + I = Finset.Icc 0 (2 * (2 * p)) :=
    chu_add_interval hZ (by simp [chuBalancedZero]) (by simp [chuBalancedZero])
  have hTI : chuBalancedTwo p + I = Finset.Icc 0 (2 * (2 * p)) :=
    chu_add_interval hT (by simp [chuBalancedTwo]) (by simp [chuBalancedTwo])
  have hII : I + I = Finset.Icc 0 (2 * (2 * p)) :=
    chu_add_interval (Finset.Subset.refl _) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
      (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hZT := chu_add_subset hZ hT
  have hTZ := chu_add_subset hT hZ
  have hIZ : I + chuBalancedZero p = _ := (add_comm _ _).trans hZI
  have hIT : I + chuBalancedTwo p = _ := (add_comm _ _).trans hTI
  change (chuResidue 0 (chuBalancedZero p) ∪ chuResidue 1 I ∪ chuResidue 2 (chuBalancedTwo p)) +
    (chuResidue 0 (chuBalancedZero p) ∪ chuResidue 1 I ∪ chuResidue 2 (chuBalancedTwo p)) = _
  rw [← chuBalanced_add_zero p, chuResidue_union]
  simp only [Finset.union_add, Finset.add_union, chuResidue_add, hZI, hIZ, hII, hIT, hTI,
    Int.reduceAdd]
  rw [show (4 : ℤ) = 0 + 4 * 1 by decide, chuResidue_shift, show 2 * (2 * p) = 4 * p by omega]
  ext x
  simp only [Finset.mem_union]
  have h₁ (hx : x ∈ chuResidue 2 (chuBalancedZero p + chuBalancedTwo p)) :
      x ∈ chuResidue 2 (Finset.Icc 0 (4 * p)) := by
    apply Finset.image_subset_image _ hx
    simpa only [show 2 * (2 * p) = 4 * p by omega] using hZT
  have h₂ (hx : x ∈ chuResidue 2 (chuBalancedTwo p + chuBalancedZero p)) :
      x ∈ chuResidue 2 (Finset.Icc 0 (4 * p)) := by
    apply Finset.image_subset_image _ hx
    simpa only [show 2 * (2 * p) = 4 * p by omega] using hTZ
  simp only [or_assoc, or_left_comm, or_comm]
  grind only

private def chuBalancedSubTwo (p : ℤ) : Finset ℤ := {0, p - 1, p, 2 * p - 1, 2 * p}

-- Negation in residue two sends quotient q to -q-1.
private theorem chuBalanced_sub_two (p : ℤ) :
    (chuBalancedZero p - chuBalancedTwo p).image (· + (-1)) ∪
      (chuBalancedTwo p - chuBalancedZero p) =
      chuBalancedSubTwo p ∪ (chuBalancedSubTwo p).image (fun q => -q - 1) := by
  change (Finset.image₂ (· - ·) (chuBalancedZero p) (chuBalancedTwo p)).image _ ∪
    Finset.image₂ (· - ·) (chuBalancedTwo p) (chuBalancedZero p) = _
  ext x
  simp only [chuBalancedZero, chuBalancedTwo, chuBalancedSubTwo, Finset.image₂_insert_left,
    Finset.image₂_singleton_left, Finset.image_insert, Finset.image_singleton,
    Finset.image_union, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  omega

private theorem chuBalanced_sub_eq (p : ℤ) (hp : 1 ≤ p) :
    chuBalancedResidues p - chuBalancedResidues p =
      chuResidue 0 (Finset.Icc (-(2 * p)) (2 * p)) ∪
        chuResidue 1 (Finset.Icc (-(2 * p)) (2 * p)) ∪
        chuResidue 2 (chuBalancedSubTwo p ∪ (chuBalancedSubTwo p).image (fun q => -q - 1)) ∪
        chuResidue (-1) (Finset.Icc (-(2 * p)) (2 * p)) := by
  let I := Finset.Icc (0 : ℤ) (2 * p)
  let J := Finset.Icc (-(2 * p)) (2 * p)
  obtain ⟨hZ, hT⟩ := chuBalanced_endpoints p hp
  obtain ⟨hIZ, hZI⟩ : I - chuBalancedZero p = J ∧ chuBalancedZero p - I = J :=
    chu_sub_interval hZ (by simp [chuBalancedZero]) (by simp [chuBalancedZero])
  obtain ⟨hIT, hTI⟩ : I - chuBalancedTwo p = J ∧ chuBalancedTwo p - I = J :=
    chu_sub_interval hT (by simp [chuBalancedTwo]) (by simp [chuBalancedTwo])
  have hII : I - I = J := (chu_sub_interval (Finset.Subset.refl _)
    (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)).1
  have hZZ := chu_sub_subset hZ hZ
  have hTT := chu_sub_subset hT hT
  change (chuResidue 0 (chuBalancedZero p) ∪ chuResidue 1 I ∪ chuResidue 2 (chuBalancedTwo p)) -
    (chuResidue 0 (chuBalancedZero p) ∪ chuResidue 1 I ∪ chuResidue 2 (chuBalancedTwo p)) = _
  rw [← chuBalanced_sub_two p, chuResidue_union,
    ← chuResidue_shift 2 (-1), show (2 : ℤ) + 4 * (-1) = -2 by decide]
  simp only [Finset.union_sub, Finset.sub_union, chuResidue_sub, hZI, hIZ, hII, hIT, hTI,
    Int.reduceSub]
  ext x
  simp only [Finset.mem_union]
  have h₁ (hx : x ∈ chuResidue 0 (chuBalancedZero p - chuBalancedZero p)) : x ∈ chuResidue 0 J :=
    Finset.image_subset_image hZZ hx
  have h₂ (hx : x ∈ chuResidue 0 (chuBalancedTwo p - chuBalancedTwo p)) : x ∈ chuResidue 0 J :=
    Finset.image_subset_image hTT hx
  simp only [or_assoc, or_left_comm, or_comm]
  grind only

-- Four distinct residues make the union a disjoint sum of cardinalities.
private theorem card_chuResidue_union_four {r₀ r₁ r₂ r₃ : ℤ} (s₀ s₁ s₂ s₃ : Finset ℤ)
    (h₀₁ : r₀ % 4 ≠ r₁ % 4) (h₀₂ : r₀ % 4 ≠ r₂ % 4) (h₁₂ : r₁ % 4 ≠ r₂ % 4)
    (h₀₃ : r₀ % 4 ≠ r₃ % 4) (h₁₃ : r₁ % 4 ≠ r₃ % 4) (h₂₃ : r₂ % 4 ≠ r₃ % 4) :
    (chuResidue r₀ s₀ ∪ chuResidue r₁ s₁ ∪ chuResidue r₂ s₂ ∪ chuResidue r₃ s₃).card =
      s₀.card + s₁.card + s₂.card + s₃.card := by
  have hd₀₁ := disjoint_chuResidue h₀₁ s₀ s₁
  have hd₂ : Disjoint (chuResidue r₀ s₀ ∪ chuResidue r₁ s₁) (chuResidue r₂ s₂) :=
    Finset.disjoint_union_left.mpr ⟨disjoint_chuResidue h₀₂ _ _, disjoint_chuResidue h₁₂ _ _⟩
  have hd₃ : Disjoint (chuResidue r₀ s₀ ∪ chuResidue r₁ s₁ ∪ chuResidue r₂ s₂)
      (chuResidue r₃ s₃) := by
    simp only [Finset.disjoint_union_left]
    exact ⟨⟨disjoint_chuResidue h₀₃ _ _, disjoint_chuResidue h₁₃ _ _⟩, disjoint_chuResidue h₂₃ _ _⟩
  rw [Finset.card_union_of_disjoint hd₃, Finset.card_union_of_disjoint hd₂,
    Finset.card_union_of_disjoint hd₀₁]
  simp only [card_chuResidue]

private theorem chuBalanced_card_add (p : ℤ) (hp : 3 ≤ p) :
    (chuBalancedResidues p + chuBalancedResidues p).card = 3 * (4 * p + 1).toNat + 10 := by
  rw [chuBalanced_add_eq p (by omega),
    card_chuResidue_union_four _ _ _ _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
  have h : ({0, 1, 2, p, p + 1, 2 * p, 2 * p + 1, 3 * p, 4 * p, 4 * p + 1} : Finset ℤ).card =
      10 := by
    repeat' rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega)]
    simp
  rw [h]
  simp only [Int.card_Icc, sub_zero]
  omega

private theorem chuBalanced_card_sub (p : ℤ) (hp : 3 ≤ p) :
    (chuBalancedResidues p - chuBalancedResidues p).card = 3 * (4 * p + 1).toNat + 10 := by
  rw [chuBalanced_sub_eq p (by omega),
    card_chuResidue_union_four _ _ _ _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
  have hdis : Disjoint (chuBalancedSubTwo p) ((chuBalancedSubTwo p).image (fun q => -q - 1)) := by
    refine Finset.disjoint_left.mpr fun x hx hy => ?_
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    simp only [chuBalancedSubTwo, Finset.mem_insert, Finset.mem_singleton] at hx hq
    omega
  have h : (chuBalancedSubTwo p).card = 5 := by
    unfold chuBalancedSubTwo
    repeat' rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega)]
    simp
  rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injective _ (fun _ _ he => by omega),
    h]
  simp only [Int.card_Icc]
  omega

/-- **A balanced family of Chu et al.** Let $k$ be a positive integer and let
$A = (0 \mid 1, 1, 2, M^k, M^{k+1}, 1, 1) \subseteq \mathbb{Z}$ be the set of partial sums,
starting at $0$, of the difference sequence formed by $1, 1, 2$, the Chu difference blocks $M^k$
and $M^{k+1}$, and $1, 1$. Then $A$ is balanced: $|A + A| = |A - A|$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Theorem 1 (`integers-2024-A32-thm-1`). -/
public theorem chu_family_balanced {k : ℕ} (hk : 0 < k) :
    let A := setOfConsecutiveDifferences 0 ([1, 1, 2] ++ chuBlock k ++ chuBlock (k + 1) ++ [1, 1])
    (A + A).card = (A - A).card := by
  dsimp only
  rw [chuBalanced_eq, chuBalanced_card_add _ (by omega), chuBalanced_card_sub _ (by omega)]

end

end MetaMathlibExt
