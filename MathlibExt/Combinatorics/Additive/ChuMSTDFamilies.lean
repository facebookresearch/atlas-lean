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
