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

private theorem setOfConsecutiveDifferences_append (a : ℤ) (p q : List ℕ) :
    setOfConsecutiveDifferences a (p ++ q) =
      setOfConsecutiveDifferences a p ∪ setOfConsecutiveDifferences (a + (p.sum : ℤ)) q := by
  induction p generalizing a with
  | nil =>
      have ha : a ∈ setOfConsecutiveDifferences a q := by
        cases q <;> simp [setOfConsecutiveDifferences]
      simp [setOfConsecutiveDifferences, ha]
  | cons g p ih =>
      simp [setOfConsecutiveDifferences_cons, ih, Finset.insert_union, Int.natCast_add, add_assoc]

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

end

end MetaMathlibExt
