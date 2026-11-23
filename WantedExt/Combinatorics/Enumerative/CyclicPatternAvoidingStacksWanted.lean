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

/-- **Sequences with the same relative order.** Two finite sequences $s = s_1 \cdots s_\ell$ and
$p = p_1 \cdots p_m$ of natural numbers have the same relative order if $\ell = m$ and, for all
$1 \le i, j \le m$, $s_i < s_j$ holds if and only if $p_i < p_j$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 2. -/
def SameRelativeOrder (s p : List ℕ) : Prop :=
  s.length = p.length ∧
    ∀ i < p.length, ∀ j < p.length, (s.getD i 0 < s.getD j 0 ↔ p.getD i 0 < p.getD j 0)

instance : DecidableRel SameRelativeOrder := fun s p => by
  unfold SameRelativeOrder; infer_instance

/-- **Classical pattern containment in a sequence.** A sequence $w$ of natural numbers contains
the pattern $p = p_1 \cdots p_k$ if some subsequence $u_1 \cdots u_k$ of $w$ (whose entries need
not be adjacent in $w$) has the same relative order as $p$: for all $a, b \in \{1, \dots, k\}$,
$u_a < u_b$ if and only if $p_a < p_b$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 2. -/
def ContainsPatternSeq (w p : List ℕ) : Prop :=
  ∃ s ∈ w.sublists, SameRelativeOrder s p

instance : DecidableRel ContainsPatternSeq := fun w p => by
  unfold ContainsPatternSeq; infer_instance

/-- **Consecutive pattern containment.** A sequence $w$ of natural numbers contains a sequence
$p = p_1 \cdots p_k$ as a consecutive pattern if some $k$ adjacent entries
$w_{i+1}, \dots, w_{i+k}$ of $w$ have the same relative order as $p$: for all
$a, b \in \{1, \dots, k\}$, $w_{i+a} < w_{i+b}$ if and only if $p_a < p_b$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 1 (after Defant and Zheng). -/
def ContainsConsecutivePatternSeq (w p : List ℕ) : Prop :=
  ∃ t ∈ w.tails, SameRelativeOrder (t.take p.length) p

instance : DecidableRel ContainsConsecutivePatternSeq := fun w p => by
  unfold ContainsConsecutivePatternSeq; infer_instance

/-- **Restricted stack-sorting from a given stack.** Fix a property of finite sequences of natural
numbers, called bad. Given an input sequence $\pi$ and a stack (listed from top to bottom), read
$\pi$ from left to right. Before pushing the next entry $x$, pop the least number $k$ of entries
from the top of the stack such that the remaining stack with $x$ pushed on top, read from top to
bottom, is not bad (if there is no such $k$, the whole stack is popped and $x$ is pushed anyway);
popped entries are appended to the output in the order they are removed. When the input is
exhausted, the remaining stack is appended to the output from top to bottom. The map returns this
output.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 1 (Berlow's map `s_T`). -/
def restrictedStackSortAux (bad : List ℕ → Prop) [DecidablePred bad] :
    List ℕ → List ℕ → List ℕ
  | [], st => st
  | x :: xs, st =>
      let k := ((List.range (st.length + 1)).find? fun k => !decide (bad (x :: st.drop k))).getD
        st.length
      st.take k ++ restrictedStackSortAux bad xs (x :: st.drop k)

/-- **West's stack-sorting map.** For a finite sequence $\pi$ of natural numbers, $s(\pi)$ is
computed with a stack that starts empty. The entries of $\pi$ are read from left to right; before
the next entry $x$ is pushed, the fewest entries are popped from the top of the stack so that the
stack with $x$ on top, read from top to bottom, avoids the pattern $21$, and the popped entries
are appended to the output in the order in which they are popped. After the last entry has been
pushed, the stack is emptied from top to bottom onto the output.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 1. -/
def westStackSort (π : List ℕ) : List ℕ :=
  restrictedStackSortAux (fun st => ContainsPatternSeq st [2, 1]) π []

/-- **Cyclic-pattern-avoiding stack-sorting map.** For a finite sequence $\sigma$ of natural
numbers, the map $s_{[\sigma]}$ sends a finite sequence $\pi$ of natural numbers to the output of
the following procedure. Read $\pi$ from left to right, starting with an empty stack. Before
pushing the next entry $x$, pop the fewest entries from the top of the stack such that the stack
with $x$ pushed on top, read from top to bottom, contains no rotation of $\sigma$ as a pattern (if
even the stack holding only $x$ contains one, the whole stack is popped and $x$ is pushed anyway);
popped entries are appended to the output in the order they are removed. Once $\pi$ is exhausted,
the remaining stack is appended to the output from top to bottom. Here a sequence $w$ contains
$p = p_1 \cdots p_m$ as a pattern when some subsequence $w_1' \cdots w_m'$ of $w$ satisfies
$w_i' < w_j' \iff p_i < p_j$ for all $1 \le i, j \le m$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 1. -/
def cyclicStackSort (σ π : List ℕ) : List ℕ :=
  restrictedStackSortAux (fun st => ∃ p ∈ σ.cyclicPermutations, ContainsPatternSeq st p) π []

/-- **Consecutive-cyclic-pattern-avoiding stack-sorting map.** For a sequence $\sigma$, the map
$s^{[\sigma]}$ sends a sequence $\pi$ of natural numbers to the output of the following stack
procedure. Read $\pi$ from left to right, starting with an empty stack. Before pushing the next
entry $x$, pop the fewest entries from the top of the stack, sending them to the output in the
order they are removed, so that the stack with $x$ on top, read from top to bottom, contains no
rotation of $\sigma$ as a consecutive pattern (a block of adjacent entries with the same length
and relative order as the rotation); if no number of pops achieves this, pop the whole stack.
Then push $x$. When the input is exhausted, pop the stack from top to bottom onto the output.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 1. -/
def consecutiveCyclicStackSort (σ π : List ℕ) : List ℕ :=
  restrictedStackSortAux
    (fun st => ∃ p ∈ σ.cyclicPermutations, ContainsConsecutivePatternSeq st p) π []

/-- **Cyclic avoidance machine.** For a sequence $\sigma$, the cyclic avoidance machine
$SC_{[\sigma]} = s \circ s_{[\sigma]}$ sends a sequence $\pi$ of natural numbers to
$s(s_{[\sigma]}(\pi))$: it first applies the cyclic-pattern-avoiding stack-sorting map
$s_{[\sigma]}$, whose stack, read from top to bottom, avoids every rotation of $\sigma$ as a
pattern, and then West's stack-sorting map $s$, whose stack, read from top to bottom, avoids the
pattern $21$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 1. -/
def cyclicSortingMachine (σ π : List ℕ) : List ℕ :=
  westStackSort (cyclicStackSort σ π)

/-- **Stack-sorting examples.** Let $s$ be West's stack-sorting map, $s_{[123]}$ the
cyclic-pattern-avoiding stack-sorting map for $123$, $s^{[123]}$ the
consecutive-cyclic-pattern-avoiding stack-sorting map for $123$, and
$SC_{[123]} = s \circ s_{[123]}$ the cyclic sorting machine for $123$. Then $s(3124) = 1234$,
$s_{[123]}(3124) = 2143$, $s^{[123]}(3124) = 4213$, $SC_{[123]}(3124) = 1234$,
$SC_{[123]}(1324) = 3124$ and $SC_{[123]}(231) = 123$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 1, Figures 1-3. -/
theorem stackSort_examples :
    westStackSort [3, 1, 2, 4] = [1, 2, 3, 4] ∧ cyclicStackSort [1, 2, 3] [3, 1, 2, 4] = [2, 1, 4, 3] ∧
      consecutiveCyclicStackSort [1, 2, 3] [3, 1, 2, 4] = [4, 2, 1, 3] ∧
      cyclicSortingMachine [1, 2, 3] [3, 1, 2, 4] = [1, 2, 3, 4] ∧
      cyclicSortingMachine [1, 2, 3] [1, 3, 2, 4] = [3, 1, 2, 4] ∧
      cyclicSortingMachine [1, 2, 3] [2, 3, 1] = [1, 2, 3] := by
  decide

/-- **Standardization.** The standardization $\mathrm{st}(s)$ of a finite sequence
$s = s_1 s_2 \cdots s_k$ of natural numbers is obtained by replacing each entry $s_i$ by the number
of indices $j$ with $s_j \le s_i$. When the entries of $s$ are distinct, this number is the rank
of $s_i$: the $r$th smallest entry becomes $r$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 2. -/
def standardizeSeq (s : List ℕ) : List ℕ :=
  s.map fun x => (s.filter (· ≤ x)).length

/-- **Heads of runs of consecutive integers.** Given an optional previous entry $y$ and a sequence
$s_1 s_2 \cdots s_\ell$ of natural numbers, this lists, in order, the entries $s_i$ with
$s_i \ne s_{i-1} + 1$, where $s_0 = y$; if there is no previous entry, $s_1$ is always listed.
With no previous entry, these are the minima $a$ of the maximal blocks $a, a + 1, \dots, a + k$
of adjacent consecutive integers of the sequence.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 2. -/
def consecutiveRunHeads : Option ℕ → List ℕ → List ℕ
  | _, [] => []
  | none, x :: xs => x :: consecutiveRunHeads (some x) xs
  | some y, x :: xs => (if x = y + 1 then [] else [x]) ++ consecutiveRunHeads (some x) xs

/-- **Reduction of a sequence.** The reduction $\operatorname{red}(s)$ of a finite sequence $s$ of
natural numbers is obtained in two steps. First, every maximal block of adjacent entries of the
form $a, a + 1, \ldots, a + k$ is replaced by its first entry $a$. Then the resulting sequence is
standardized: each of its entries $x$ is replaced by the number of its entries that are at most
$x$, which for distinct entries is the rank of $x$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 2. -/
def reductionSeq (s : List ℕ) : List ℕ :=
  standardizeSeq (consecutiveRunHeads none s)

/-- **Standardization and reduction examples.** The standardization of $315$ is
$\mathrm{st}(315) = 213$, and the reduction of $16783425$ is $\mathrm{red}(16783425) = 15324$.
Here $\mathrm{st}$ replaces each entry by its rank, and $\mathrm{red}$ replaces each maximal block
of adjacent consecutive integers $a, a + 1, \dots, a + k$ by its minimum $a$ and then
standardizes.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 2. -/
theorem standardizeSeq_reductionSeq_examples :
    standardizeSeq [3, 1, 5] = [2, 1, 3] ∧
      reductionSeq [1, 6, 7, 8, 3, 4, 2, 5] = [1, 5, 3, 2, 4] := by
  decide

/-- **Push order of the superimpose operation.** For finite sequences $a$ and $b$ of natural
numbers, $\mathrm{push}(a, b)$ is the sequence obtained by taking the first entry of $b$, then the
next two entries of $a$ (only one if just one is left), and repeating; once one of the two
sequences is exhausted, the remaining entries of the other follow in order.

For finite sequences $\sigma_1$ and $\sigma_2$ with reversals $\mathrm{rev}\,\sigma_1$ and
$\mathrm{rev}\,\sigma_2$, the sequence $\mathrm{push}(\mathrm{rev}\,\sigma_1,
\mathrm{rev}\,\sigma_2)$ is the order in which the superimpose operation
$\mathrm{si}(\sigma_1, \sigma_2)$ pushes the entries of $\sigma_1$ and $\sigma_2$ onto its stack.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 3.2. -/
def superimposePush : List ℕ → List ℕ → List ℕ
  | a, [] => a
  | a, y :: b => if a = [] then y :: b else y :: (a.take 2 ++ superimposePush (a.drop 2) b)

/-- **Superimpose operation.** For finite sequences $\sigma_1$ and $\sigma_2$ of natural numbers,
let $p = \mathrm{push}(\mathrm{rev}\,\sigma_1, \mathrm{rev}\,\sigma_2)$ be the push order of the
superimpose operation on the reversed sequences. Then $\mathrm{si}(\sigma_1, \sigma_2)$ is the
reversal of $p$: the stack obtained by pushing the entries of $p$ in order onto an empty stack,
read from top to bottom.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 3.2. -/
def superimpose (σ₁ σ₂ : List ℕ) : List ℕ :=
  (superimposePush σ₁.reverse σ₂.reverse).reverse

/-- **Superimpose examples.** For the superimpose operation $\mathrm{si}$,
$\mathrm{si}((1, 2, 3, 4, 5), (6, 7, 8, 9, 10)) = (6, 7, 1, 8, 2, 3, 9, 4, 5, 10)$ and
$\mathrm{si}((1, 2), (3, 4, 5, 6)) = (3, 4, 5, 1, 2, 6)$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 3.2 and Example 1. -/
theorem superimpose_examples :
    superimpose [1, 2, 3, 4, 5] [6, 7, 8, 9, 10] = [6, 7, 1, 8, 2, 3, 9, 4, 5, 10] ∧
      superimpose [1, 2] [3, 4, 5, 6] = [3, 4, 5, 1, 2, 6] := by
  decide

/-- **The permutation $\xi_n$.** For a natural number $n$, $\xi_n$ is the sequence listing the
elements of $\{1, \dots, n\}$ whose parity differs from that of $n$ in increasing order, followed
by the elements with the same parity as $n$ in increasing order. Thus
$\xi_n = 1, 3, \dots, n-1, 2, 4, \dots, n$ for even $n$, and
$\xi_n = 2, 4, \dots, n-1, 1, 3, \dots, n$ for odd $n$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 1. -/
def xiPermutation (n : ℕ) : List ℕ :=
  (List.range' 1 n).filter (fun i => i % 2 ≠ n % 2) ++
    (List.range' 1 n).filter (fun i => i % 2 = n % 2)

/-- **The parity-split permutations for six and seven.** For $n \in \mathbb{N}$, let $\xi_n$ list
the elements of $[n] = \{1, \dots, n\}$ whose parity differs from that of $n$ in increasing order,
followed by the elements with the parity of $n$ in increasing order. Then $\xi_6 = 135246$ and
$\xi_7 = 2461357$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 1. -/
theorem xiPermutation_six_seven :
    xiPermutation 6 = [1, 3, 5, 2, 4, 6] ∧ xiPermutation 7 = [2, 4, 6, 1, 3, 5, 7] := by
  decide

/-- **Good sequences of suffix extrema.** A finite sequence $s = s_1 s_2 \cdots s_\ell$ of natural
numbers is good if every entry $s_i$ is the minimum or the maximum of
$s_i, s_{i+1}, \ldots, s_\ell$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 3.4. -/
def IsGoodSeq (s : List ℕ) : Prop :=
  ∀ i < s.length, (∀ y ∈ s.drop i, s.getD i 0 ≤ y) ∨ (∀ y ∈ s.drop i, y ≤ s.getD i 0)

instance : DecidablePred IsGoodSeq := fun s => by
  unfold IsGoodSeq; infer_instance

/-- **Permutations sorted by a map.** For a map $f$ from finite sequences of natural numbers to
finite sequences of natural numbers and for $n \in \mathbb{N}$, $\mathrm{Sort}_n(f)$ is the finite
set of permutations $\pi$ of $[n] = \{1, \dots, n\}$, written as sequences, such that $f(\pi)$ is
the identity permutation $\mathrm{id}_n = 12 \cdots n$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Section 2. -/
def sortedPermutations (f : List ℕ → List ℕ) (n : ℕ) : Finset (List ℕ) :=
  (List.range' 1 n).permutations.toFinset.filter fun π => f π = List.range' 1 n

/-- **Small cases of good sequences and of sorting by the consecutive $321$-cyclic stack.** The
sequence $51432$ is good (each entry is the minimum or the maximum of itself and all entries after
it), and among the six permutations of $\{1, 2, 3\}$ exactly $312$ and $321$ are sent to $123$ by
the consecutive-cyclic-pattern-avoiding stack-sorting map $s^{[321]}$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Sections 2 and 3.4. -/
theorem isGoodSeq_consecutiveCyclicStackSort_examples :
    IsGoodSeq [5, 1, 4, 3, 2] ∧
      ([[1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]].filter fun π =>
        consecutiveCyclicStackSort [3, 2, 1] π = [1, 2, 3]) = [[3, 1, 2], [3, 2, 1]] := by
  decide

/-- **$n - 2$ passes of $SC_{[123]}$ sort every permutation, and $n - 3$ do not.** Let $n \ge 3$
and let $SC_{[123]}^k$ be the $k$-fold iterate of the cyclic avoidance machine $SC_{[123]}$.
For every permutation $\pi$ of $[n] = \{1, \dots, n\}$, $SC_{[123]}^{n-2}(\pi) = 12 \cdots n$, and
the bound is tight: $SC_{[123]}^{n-3}(\xi_n) \ne 12 \cdots n$, where $\xi_n$ lists the elements of
$[n]$ of parity different from $n$ in increasing order, followed by those of the parity of $n$
in increasing order.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Theorem 1 (`integers-2026-A15-thm-1`). -/
public theorem_wanted cyclicSortingMachine_123_iterate_sorts {n : ℕ} (hn : 3 ≤ n) :
    (∀ π : List ℕ, π.Perm (List.range' 1 n) →
      (cyclicSortingMachine [1, 2, 3])^[n - 2] π = List.range' 1 n) ∧
    (cyclicSortingMachine [1, 2, 3])^[n - 3] (xiPermutation n) ≠ List.range' 1 n

/-- **Eventual periodicity of the identity under $SC_{[321]}$.** Let $n \ge 4$, let
$c = \lceil (2n-1)/3 \rceil$, and let $SC_{[321]}^k$ be the $k$-fold iterate of the cyclic
avoidance machine $SC_{[321]}$. For every natural number $m \ge \lceil (n-1-c)/2 \rceil$,
$SC_{[321]}^m(12 \cdots n) = SC_{[321]}^{m+c}(12 \cdots n)$.

Equivalently, $c = \lfloor (2n+1)/3 \rfloor$ and
$\lceil (n-1-c)/2 \rceil = \lfloor (n-c)/2 \rfloor$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Theorem 2 (`integers-2026-A15-thm-2`). -/
public theorem_wanted cyclicSortingMachine_321_identity_orbit_period {n m : ℕ} (hn : 4 ≤ n)
    (hm : (n - (2 * n + 1) / 3) / 2 ≤ m) :
    (cyclicSortingMachine [3, 2, 1])^[m] (List.range' 1 n) =
      (cyclicSortingMachine [3, 2, 1])^[m + (2 * n + 1) / 3] (List.range' 1 n)

/-- **No permutation of length at least four is sorted by the consecutive cyclic $123$-stack.**
Let $s^{[123]}$ be the consecutive-cyclic-pattern-avoiding stack-sorting map for $123$. For every
$n \ge 4$, no permutation of $[n] = \{1, \dots, n\}$ is mapped by $s^{[123]}$ to the identity
$12 \cdots n$; that is, the set $\mathrm{Sort}_n(s^{[123]})$ of permutations of $[n]$ that
$s^{[123]}$ maps to the identity has $0$ elements.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Theorem 3 (`integers-2026-A15-thm-3`). -/
public theorem_wanted sortedPermutations_consecutiveCyclicStackSort_123 {n : ℕ} (hn : 4 ≤ n) :
    (sortedPermutations (consecutiveCyclicStackSort [1, 2, 3]) n).card = 0

/-- **Permutations sorted by the consecutive $321$-cyclic stack.** Let $n \ge 2$, let
$s^{[321]}$ be the stack-sorting map whose stack, read from top to bottom, avoids every rotation
of $321$ as a consecutive pattern, and let $\mathrm{Sort}_n(s^{[321]})$ be the set of permutations
of $[n] = \{1, \dots, n\}$ that $s^{[321]}$ maps to the identity $12 \cdots n$. Then
$|\mathrm{Sort}_n(s^{[321]})| = 2^{n-2}$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Theorem 4 (`integers-2026-A15-thm-4`). -/
public theorem_wanted card_sortedPermutations_consecutiveCyclicStackSort_321 {n : ℕ}
    (hn : 2 ≤ n) :
    (sortedPermutations (consecutiveCyclicStackSort [3, 2, 1]) n).card = 2 ^ (n - 2)

/-- **Reducing before the $123$ cyclic sorting machine does not change the reduced output.** For
every permutation $\pi$ of $[n] = \{1, \ldots, n\}$, applying the cyclic sorting machine
$\mathrm{SC}_{[123]}$ to the reduction $\operatorname{red}(\pi)$ and reducing the result gives the
reduction of $\mathrm{SC}_{[123]}(\pi)$:
$\operatorname{red}(\mathrm{SC}_{[123]}(\operatorname{red}(\pi))) =
\operatorname{red}(\mathrm{SC}_{[123]}(\pi))$.

Only this identity is stated; the lemma's further assertion that blocks $a, a+1, \ldots, a+k$ of
$\pi$ enter and leave the stack together is not part of the statement.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Lemma 1 (`integers-2026-A15-lem-1`). -/
public theorem_wanted reductionSeq_cyclicSortingMachine_123_reductionSeq {n : ℕ} {π : List ℕ}
    (hπ : π.Perm (List.range' 1 n)) :
    reductionSeq (cyclicSortingMachine [1, 2, 3] (reductionSeq π)) =
      reductionSeq (cyclicSortingMachine [1, 2, 3] π)

/-- **Reduction and iterates of $SC_{[123]}$.** Let $\pi$ be a permutation of
$[n] = \{1, \dots, n\}$, written as a sequence, let $\mathrm{red}(\pi)$ be its reduction, of
length $\ell$, and let $SC_{[123]}^k$ be the $k$-fold iterate of the cyclic avoidance machine
$SC_{[123]}$. For every $k \ge 0$, $SC_{[123]}^k(\pi) = 12 \cdots n$ if and only if
$SC_{[123]}^k(\mathrm{red}(\pi)) = 12 \cdots \ell$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Corollary 1 (`integers-2026-A15-cor-1`). -/
public theorem_wanted cyclicSortingMachine_123_iterate_eq_id_iff_reductionSeq {n k : ℕ}
    {π : List ℕ} (hπ : π.Perm (List.range' 1 n)) :
    (cyclicSortingMachine [1, 2, 3])^[k] π = List.range' 1 n ↔
      (cyclicSortingMachine [1, 2, 3])^[k] (reductionSeq π) =
        List.range' 1 (reductionSeq π).length

/-- **After one pass of the $123$ cyclic sorting machine, the reduction is shorter.** For every
$n \ge 2$ and every permutation $\pi$ of $[n] = \{1, \ldots, n\}$, the reduction
$\operatorname{red}(\mathrm{SC}_{[123]}(\pi))$ of the image of $\pi$ under the cyclic sorting
machine $\mathrm{SC}_{[123]}$ has fewer than $n$ entries.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Lemma 2 (`integers-2026-A15-lem-2`). -/
public theorem_wanted length_reductionSeq_cyclicSortingMachine_123_lt {n : ℕ} (hn : 2 ≤ n)
    {π : List ℕ} (hπ : π.Perm (List.range' 1 n)) :
    (reductionSeq (cyclicSortingMachine [1, 2, 3] π)).length < n

/-- **One pass of $SC_{[321]}$ on superimposed increasing runs.** Let $n \ge 4$ and
$1 \le m < \lceil (2n-1)/3 \rceil = \lfloor (2n+1)/3 \rfloor$. Then the cyclic avoidance machine
$SC_{[321]}$ maps the superimposition $\mathrm{si}((1, \dots, m), (m+1, \dots, n))$ to
$\mathrm{si}((1, \dots, m+1), (m+2, \dots, n))$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Lemma 3 (`integers-2026-A15-lem-3`). -/
public theorem_wanted cyclicSortingMachine_321_superimpose {n m : ℕ} (hn : 4 ≤ n) (hm : 1 ≤ m)
    (hmn : m < (2 * n + 1) / 3) :
    cyclicSortingMachine [3, 2, 1] (superimpose (List.range' 1 m) (List.range' (m + 1) (n - m))) =
      superimpose (List.range' 1 (m + 1)) (List.range' (m + 2) (n - m - 1))

/-- **First entry and tail of permutations sorted by the consecutive $321$-cyclic stack.** Let
$n \ge 2$ and let $\mathrm{Sort}_n(s^{[321]})$ be the set of permutations of
$[n] = \{1, \ldots, n\}$ that the consecutive-cyclic-pattern-avoiding stack-sorting map
$s^{[321]}$ sends to the identity $12 \cdots n$. Every $\pi = \pi_1 \pi_2 \cdots \pi_n$ in
$\mathrm{Sort}_n(s^{[321]})$ has $\pi_1 = n$, and $\pi_2 \cdots \pi_n$ is good: each of its entries
is the minimum or the maximum of itself and all entries after it.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Lemma 4 (`integers-2026-A15-lem-4`). -/
public theorem_wanted head_tail_of_mem_sortedPermutations_consecutiveCyclicStackSort_321
    {n : ℕ} (hn : 2 ≤ n) {π : List ℕ}
    (hπ : π ∈ sortedPermutations (consecutiveCyclicStackSort [3, 2, 1]) n) :
    π.head? = some n ∧ IsGoodSeq π.tail

/-- **Characterization of the permutations sorted by the consecutive $321$-cyclic stack.** Let
$n \ge 2$ and let $\pi = \pi_1 \pi_2 \cdots \pi_n$ be a permutation of $[n] = \{1, \ldots, n\}$.
The consecutive-cyclic-pattern-avoiding stack-sorting map $s^{[321]}$ sends $\pi$ to the identity
$12 \cdots n$ (that is, $\pi \in \mathrm{Sort}_n(s^{[321]})$) if and only if $\pi_1 = n$ and
$\pi_2 \cdots \pi_n$ is good: each of its entries is the minimum or the maximum of itself and all
entries after it.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Corollary 2 (`integers-2026-A15-cor-2`). -/
public theorem_wanted mem_sortedPermutations_consecutiveCyclicStackSort_321_iff {n : ℕ}
    (hn : 2 ≤ n) {π : List ℕ} (hπ : π.Perm (List.range' 1 n)) :
    π ∈ sortedPermutations (consecutiveCyclicStackSort [3, 2, 1]) n ↔
      π.head? = some n ∧ IsGoodSeq π.tail

end

end MetaMathlibExt
