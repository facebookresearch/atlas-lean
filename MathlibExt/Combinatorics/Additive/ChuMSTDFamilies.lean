/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Interval.Finset.Nat
import Batteries.Data.List.Lemmas
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

private theorem mem_setOfConsecutiveDifferences_at_prefix (a : ℤ) (ds es : List ℕ) :
    a + (ds.sum : ℤ) ∈ setOfConsecutiveDifferences a (ds ++ es) := by
  induction ds generalizing a with
  | nil => cases es <;> simp [setOfConsecutiveDifferences]
  | cons d ds ih =>
    rw [List.cons_append, setOfConsecutiveDifferences_cons]
    apply Finset.mem_insert_of_mem
    simpa [List.sum_cons, Int.natCast_add, add_assoc] using ih (a + d)

/-- **Block starting points of the Chu family set.** Let $k$, $l$, $t$ be positive integers and
let $A \subseteq \mathbb{Z}$ be the Chu family set with parameters $k$, $l$, $t$. Then
$4 + (4k + 4)i + (4kl + 4l + 4)j \in A$ for all integers $i$, $j$ with $0 \le i \le l$ and
$0 \le j \le t - 1$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Lemma 6 (`integers-2024-A32-lem-6`). -/
public theorem chuFamilyKLT_mem_block_starts {k l t : ℕ} (_hk : 0 < k) (_hl : 0 < l)
    (_ht : 0 < t) (i j : ℕ) (hi : i ≤ l) (hj : j < t) :
    4 + (4 * k + 4) * (i : ℤ) + (4 * k * l + 4 * l + 4) * (j : ℤ) ∈ chuFamilyKLT k l t := by
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
    simp [before, block, chuBlock, List.sum_flatten]
    ring
  rw [hgaps, ← hsum]
  exact mem_setOfConsecutiveDifferences_at_prefix 0 before after

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
