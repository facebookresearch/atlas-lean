/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.List.Rotate
public import Mathlib.Data.Finset.Card

/-!
# Cyclic-pattern-avoiding stacks

Statements from Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15.

Permutations of `[n]` are lists `π` with `π ~ [1, …, n]` (`List.range' 1 n`, which is also the
identity `id_n`). A stack is a list whose head is its top. A restricted stack-sorting map
(Berlow's `s_T`) reads the input from left to right; before pushing the next entry `x` it pops the
minimum number of entries from the top so that the stack with `x` on top, read from top to
bottom, is not "bad"; popped entries go to the output in order of removal, and at the end the
stack is emptied from top to bottom onto the output. West's map `s` forbids the pattern `21`, the
cyclic map `s_[σ]` forbids every rotation of `σ` as a pattern, and the consecutive cyclic map
`s^[σ]` forbids every rotation of `σ` as a consecutive pattern. `SC_[σ] = s ∘ s_[σ]`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Two sequences have the same relative order (`st(s) = st(p)`): same length, and
`s_i < s_j ↔ p_i < p_j` for all positions.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 2. -/
def SameRelativeOrder (s p : List ℕ) : Prop :=
  s.length = p.length ∧
    ∀ i < p.length, ∀ j < p.length, (s.getD i 0 < s.getD j 0 ↔ p.getD i 0 < p.getD j 0)

instance : DecidableRel SameRelativeOrder := fun s p => by
  unfold SameRelativeOrder; infer_instance

/-- `w` contains the pattern `p`: some subsequence of `w` has the relative order of `p`.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 2. -/
def ContainsPatternSeq (w p : List ℕ) : Prop :=
  ∃ s ∈ w.sublists, SameRelativeOrder s p

instance : DecidableRel ContainsPatternSeq := fun w p => by
  unfold ContainsPatternSeq; infer_instance

/-- `w` contains `p` as a consecutive pattern: some block of `|p|` adjacent entries of `w` has the
relative order of `p`.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 1 (after Defant and Zheng). -/
def ContainsConsecutivePatternSeq (w p : List ℕ) : Prop :=
  ∃ t ∈ w.tails, SameRelativeOrder (t.take p.length) p

instance : DecidableRel ContainsConsecutivePatternSeq := fun w p => by
  unfold ContainsConsecutivePatternSeq; infer_instance

/-- One pass of a restricted stack: input `π`, current stack `st` (head = top). Before pushing
`x`, pop the least number `k` of top entries such that `x :: st.drop k` is not `bad`.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 1 (Berlow's map `s_T`). -/
def restrictedStackSortAux (bad : List ℕ → Prop) [DecidablePred bad] :
    List ℕ → List ℕ → List ℕ
  | [], st => st
  | x :: xs, st =>
      let k := ((List.range (st.length + 1)).find? fun k => !decide (bad (x :: st.drop k))).getD
        st.length
      st.take k ++ restrictedStackSortAux bad xs (x :: st.drop k)

/-- West's deterministic stack-sorting map `s`: the stack, read from top to bottom, avoids `21`.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 1. -/
def westStackSort (π : List ℕ) : List ℕ :=
  restrictedStackSortAux (fun st => ContainsPatternSeq st [2, 1]) π []

/-- The cyclic-pattern-avoiding stack-sorting map `s_[σ]`: the stack, read from top to bottom,
avoids every rotation of `σ`.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 1. -/
def cyclicStackSort (σ π : List ℕ) : List ℕ :=
  restrictedStackSortAux (fun st => ∃ p ∈ σ.cyclicPermutations, ContainsPatternSeq st p) π []

/-- The consecutive-cyclic-pattern-avoiding stack-sorting map `s^[σ]`: the stack, read from top to
bottom, avoids every rotation of `σ` as a consecutive pattern.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 1. -/
def consecutiveCyclicStackSort (σ π : List ℕ) : List ℕ :=
  restrictedStackSortAux
    (fun st => ∃ p ∈ σ.cyclicPermutations, ContainsConsecutivePatternSeq st p) π []

/-- The cyclic avoidance machine `SC_[σ] = s ∘ s_[σ]`.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 1. -/
def cyclicSortingMachine (σ π : List ℕ) : List ℕ :=
  westStackSort (cyclicStackSort σ π)

/-- The paper's examples: `s(3124) = 1234`, `s_[123](3124) = 2143`, `s^[123](3124) = 4213`,
`SC_[123](3124) = 1234`, `SC_[123](1324) = 3124`, and `SC_[123](231) = 123`.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 1, Figures 1-3. -/
theorem stackSort_examples :
    westStackSort [3, 1, 2, 4] = [1, 2, 3, 4] ∧ cyclicStackSort [1, 2, 3] [3, 1, 2, 4] = [2, 1, 4, 3] ∧
      consecutiveCyclicStackSort [1, 2, 3] [3, 1, 2, 4] = [4, 2, 1, 3] ∧
      cyclicSortingMachine [1, 2, 3] [3, 1, 2, 4] = [1, 2, 3, 4] ∧
      cyclicSortingMachine [1, 2, 3] [1, 3, 2, 4] = [3, 1, 2, 4] ∧
      cyclicSortingMachine [1, 2, 3] [2, 3, 1] = [1, 2, 3] := by
  decide

/-- The standardization `st(s)`: each entry is replaced by its rank (the `i`th smallest entry
becomes `i`); intended for sequences of distinct numbers.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 2. -/
def standardizeSeq (s : List ℕ) : List ℕ :=
  s.map fun x => (s.filter (· ≤ x)).length

/-- The minima of the maximal blocks of adjacent consecutive integers `a, a + 1, …, a + k`, given
the previous entry.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 2. -/
def consecutiveRunHeads : Option ℕ → List ℕ → List ℕ
  | _, [] => []
  | none, x :: xs => x :: consecutiveRunHeads (some x) xs
  | some y, x :: xs => (if x = y + 1 then [] else [x]) ++ consecutiveRunHeads (some x) xs

/-- The reduction `red(s)`: replace every maximal block of adjacent consecutive integers
`a, a + 1, …, a + k` by its minimum `a`, then standardize.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 2. -/
def reductionSeq (s : List ℕ) : List ℕ :=
  standardizeSeq (consecutiveRunHeads none s)

/-- The paper's examples `st(315) = 213` and `red(16783425) = 15324`.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 2. -/
theorem standardizeSeq_reductionSeq_examples :
    standardizeSeq [3, 1, 5] = [2, 1, 3] ∧
      reductionSeq [1, 6, 7, 8, 3, 4, 2, 5] = [1, 5, 3, 2, 4] := by
  decide

/-- The push order of the superimpose operation, on the reversed sequences `a = rev σ₁`,
`b = rev σ₂`: push the head of `b`, then the next two entries of `a` (or one if one is left),
and repeat; once one sequence is exhausted, push the rest of the other.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 3.2. -/
def superimposePush : List ℕ → List ℕ → List ℕ
  | a, [] => a
  | a, y :: b => if a = [] then y :: b else y :: (a.take 2 ++ superimposePush (a.drop 2) b)

/-- The superimpose operation `si(σ₁, σ₂)`: the stack built by `superimposePush`, read from top to
bottom.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 3.2. -/
def superimpose (σ₁ σ₂ : List ℕ) : List ℕ :=
  (superimposePush σ₁.reverse σ₂.reverse).reverse

/-- The paper's examples `si((1,…,5), (6,…,10)) = 6,7,1,8,2,3,9,4,5,10` and
`si((1,2), (3,4,5,6)) = 3,4,5,1,2,6`.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 3.2 and Example 1. -/
theorem superimpose_examples :
    superimpose [1, 2, 3, 4, 5] [6, 7, 8, 9, 10] = [6, 7, 1, 8, 2, 3, 9, 4, 5, 10] ∧
      superimpose [1, 2] [3, 4, 5, 6] = [3, 4, 5, 1, 2, 6] := by
  decide

/-- The permutation `ξ_n`: the entries of `[n]` of parity different from `n`, increasing, followed
by those of the parity of `n`, increasing (`ξ_n = 1,3,…,n-1,2,4,…,n` for even `n` and
`2,4,…,n-1,1,3,…,n` for odd `n`).

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 1. -/
def xiPermutation (n : ℕ) : List ℕ :=
  (List.range' 1 n).filter (fun i => i % 2 ≠ n % 2) ++
    (List.range' 1 n).filter (fun i => i % 2 = n % 2)

/-- `ξ_6 = 135246` and `ξ_7 = 2461357`.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 1. -/
theorem xiPermutation_six_seven :
    xiPermutation 6 = [1, 3, 5, 2, 4, 6] ∧ xiPermutation 7 = [2, 4, 6, 1, 3, 5, 7] := by
  decide

/-- A sequence `s` is good if every entry `s_i` is the minimum or the maximum of
`s_i, s_{i+1}, …`.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 3.4. -/
def IsGoodSeq (s : List ℕ) : Prop :=
  ∀ i < s.length, (∀ y ∈ s.drop i, s.getD i 0 ≤ y) ∨ (∀ y ∈ s.drop i, y ≤ s.getD i 0)

instance : DecidablePred IsGoodSeq := fun s => by
  unfold IsGoodSeq; infer_instance

/-- `Sort_n(f)`: the permutations of `[n]` that `f` maps to the identity `id_n`.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 2. -/
def sortedPermutations (f : List ℕ → List ℕ) (n : ℕ) : Finset (List ℕ) :=
  (List.range' 1 n).permutations.toFinset.filter fun π => f π = List.range' 1 n

/-- `51432` is good, and among the six permutations of `[3]` exactly `312` and `321` are sorted by
`s^[321]` (the paper's `Sort_3(s^[321]) = {312, 321}`).

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Sections 2 and 3.4. -/
theorem isGoodSeq_consecutiveCyclicStackSort_examples :
    IsGoodSeq [5, 1, 4, 3, 2] ∧
      ([[1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]].filter fun π =>
        consecutiveCyclicStackSort [3, 2, 1] π = [1, 2, 3]) = [[3, 1, 2], [3, 2, 1]] := by
  decide

/-- For every permutation `π` of `[n]`, `n ≥ 3`, `SC_[123]^{n-2}(π) = id_n`, and the bound is
tight: `SC_[123]^{n-3}(ξ_n) ≠ id_n`.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Theorem 1 (`integers-2026-A15-thm-1`). -/
public theorem_wanted cyclicSortingMachine_123_iterate_sorts {n : ℕ} (hn : 3 ≤ n) :
    (∀ π : List ℕ, π.Perm (List.range' 1 n) →
      (cyclicSortingMachine [1, 2, 3])^[n - 2] π = List.range' 1 n) ∧
    (cyclicSortingMachine [1, 2, 3])^[n - 3] (xiPermutation n) ≠ List.range' 1 n

/-- For `n ≥ 4` and `m ≥ ⌈(n - 1 - ⌈(2n-1)/3⌉)/2⌉`,
`SC_[321]^m(id_n) = SC_[321]^{m + ⌈(2n-1)/3⌉}(id_n)`. With natural division,
`⌈(2n-1)/3⌉ = (2n+1)/3` and `⌈(n - 1 - c)/2⌉ = (n - c)/2`.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Theorem 2 (`integers-2026-A15-thm-2`). -/
public theorem_wanted cyclicSortingMachine_321_identity_orbit_period {n m : ℕ} (hn : 4 ≤ n)
    (hm : (n - (2 * n + 1) / 3) / 2 ≤ m) :
    (cyclicSortingMachine [3, 2, 1])^[m] (List.range' 1 n) =
      (cyclicSortingMachine [3, 2, 1])^[m + (2 * n + 1) / 3] (List.range' 1 n)

/-- For `n ≥ 4`, `|Sort_n(s^[123])| = 0`.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Theorem 3 (`integers-2026-A15-thm-3`). -/
public theorem_wanted sortedPermutations_consecutiveCyclicStackSort_123 {n : ℕ} (hn : 4 ≤ n) :
    (sortedPermutations (consecutiveCyclicStackSort [1, 2, 3]) n).card = 0

/-- For `n ≥ 2`, `|Sort_n(s^[321])| = 2^{n-2}`.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Theorem 4 (`integers-2026-A15-thm-4`). -/
public theorem_wanted card_sortedPermutations_consecutiveCyclicStackSort_321 {n : ℕ}
    (hn : 2 ≤ n) :
    (sortedPermutations (consecutiveCyclicStackSort [3, 2, 1]) n).card = 2 ^ (n - 2)

/-- For every permutation `π` of `[n]`, `red(SC_[123](red(π))) = red(SC_[123](π))`. The lemma's
second sentence (blocks `a, a+1, …, a+k` of `π` enter and leave the stack together) is a remark on
the stack dynamics and is not stated.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Lemma 1 (`integers-2026-A15-lem-1`). -/
public theorem_wanted reductionSeq_cyclicSortingMachine_123_reductionSeq {n : ℕ} {π : List ℕ}
    (hπ : π.Perm (List.range' 1 n)) :
    reductionSeq (cyclicSortingMachine [1, 2, 3] (reductionSeq π)) =
      reductionSeq (cyclicSortingMachine [1, 2, 3] π)

/-- For every permutation `π` of `[n]` and every `k`, `SC_[123]^k(π) = id_n` if and only if
`SC_[123]^k(red(π)) = id_{|red(π)|}`.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Corollary 1 (`integers-2026-A15-cor-1`). -/
public theorem_wanted cyclicSortingMachine_123_iterate_eq_id_iff_reductionSeq {n k : ℕ}
    {π : List ℕ} (hπ : π.Perm (List.range' 1 n)) :
    (cyclicSortingMachine [1, 2, 3])^[k] π = List.range' 1 n ↔
      (cyclicSortingMachine [1, 2, 3])^[k] (reductionSeq π) =
        List.range' 1 (reductionSeq π).length

/-- For every permutation `π` of `[n]` with `n ≥ 2`, `|red(SC_[123](π))| < |π|`.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Lemma 2 (`integers-2026-A15-lem-2`). -/
public theorem_wanted length_reductionSeq_cyclicSortingMachine_123_lt {n : ℕ} (hn : 2 ≤ n)
    {π : List ℕ} (hπ : π.Perm (List.range' 1 n)) :
    (reductionSeq (cyclicSortingMachine [1, 2, 3] π)).length < n

/-- For `n ≥ 4` and `1 ≤ m < ⌈(2n-1)/3⌉ = (2n+1)/3`,
`SC_[321](si((1,…,m), (m+1,…,n))) = si((1,…,m+1), (m+2,…,n))`.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Lemma 3 (`integers-2026-A15-lem-3`). -/
public theorem_wanted cyclicSortingMachine_321_superimpose {n m : ℕ} (hn : 4 ≤ n) (hm : 1 ≤ m)
    (hmn : m < (2 * n + 1) / 3) :
    cyclicSortingMachine [3, 2, 1] (superimpose (List.range' 1 m) (List.range' (m + 1) (n - m))) =
      superimpose (List.range' 1 (m + 1)) (List.range' (m + 2) (n - m - 1))

/-- For `n ≥ 2`, every `π ∈ Sort_n(s^[321])` has `π_1 = n` and `π_2 ⋯ π_n` good.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Lemma 4 (`integers-2026-A15-lem-4`). -/
public theorem_wanted head_tail_of_mem_sortedPermutations_consecutiveCyclicStackSort_321
    {n : ℕ} (hn : 2 ≤ n) {π : List ℕ}
    (hπ : π ∈ sortedPermutations (consecutiveCyclicStackSort [3, 2, 1]) n) :
    π.head? = some n ∧ IsGoodSeq π.tail

/-- For `n ≥ 2` and every permutation `π` of `[n]`, `π ∈ Sort_n(s^[321])` if and only if
`π_1 = n` and `π_2 ⋯ π_n` is good.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Corollary 2 (`integers-2026-A15-cor-2`). -/
public theorem_wanted mem_sortedPermutations_consecutiveCyclicStackSort_321_iff {n : ℕ}
    (hn : 2 ≤ n) {π : List ℕ} (hπ : π.Perm (List.range' 1 n)) :
    π ∈ sortedPermutations (consecutiveCyclicStackSort [3, 2, 1]) n ↔
      π.head? = some n ∧ IsGoodSeq π.tail

end

end MetaMathlibExt
