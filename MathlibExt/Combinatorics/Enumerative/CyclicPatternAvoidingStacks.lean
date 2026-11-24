/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Rotate
public import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Sublists

/-!
# Cyclic-pattern-avoiding stacks

After any given number of passes of the cyclic sorting machine for `123`, a permutation reaches
the identity exactly when its reduction does. The definitions are from
Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
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
    westStackSort [3, 1, 2, 4] = [1, 2, 3, 4] ∧
      cyclicStackSort [1, 2, 3] [3, 1, 2, 4] = [2, 1, 4, 3] ∧
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

end

namespace cyclicSortingMachine_123_iterate_eq_id_iff_reductionSeq

-- Split the value a into a and a + 1, shifting larger values up to make room.
private def liftEntry (a : ℕ) (hi : Bool) (x : ℕ) : ℕ :=
  if x < a then x else if x = a then a + hi.toNat else x + 1

private theorem liftEntry_mono (a : ℕ) (hi : Bool) : StrictMono (liftEntry a hi) := by
  intro x y h
  cases hi <;> simp only [liftEntry, Bool.toNat_false, Bool.toNat_true] <;> split_ifs <;> omega

private def block (a : ℕ) (down : Bool) (x : ℕ) : List ℕ :=
  if x = a then [liftEntry a down x, liftEntry a (!down) x] else [liftEntry a down x]

private def expand (a : ℕ) (down : Bool) (s : List ℕ) := s.flatMap (block a down)

private theorem liftEntry_ne {x a : ℕ} (hx : x ≠ a) (b c : Bool) :
    liftEntry a b x = liftEntry a c x := by simp [liftEntry, hx]

-- In the cyclic stack the two entries appear in descending order. In West’s stack
-- they appear in ascending order. The same simulation applies with either orientation.
private def bad (down : Bool) (w : List ℕ) : Prop :=
  if down then ∃ p ∈ [1, 2, 3].cyclicPermutations, ContainsPatternSeq w p
  else ContainsPatternSeq w [2, 1]

private instance badDecidable (d : Bool) : DecidablePred (bad d) := fun w => by
  unfold bad
  infer_instance

private def forbidden (down : Bool) (w : List ℕ) : Prop :=
  if down then ∃ p ∈ [1, 2, 3].cyclicPermutations, SameRelativeOrder w p
  else SameRelativeOrder w [2, 1]

private theorem bad_iff (d : Bool) (w : List ℕ) :
    bad d w ↔ ∃ s : List ℕ, s.Sublist w ∧ forbidden d s := by
  cases d <;> simp [bad, forbidden, ContainsPatternSeq, List.mem_sublists]
  aesop

private theorem relativeOrder_map (f : ℕ → ℕ) (hf : StrictMono f) (s p : List ℕ) :
    SameRelativeOrder (s.map f) p ↔ SameRelativeOrder s p := by
  unfold SameRelativeOrder
  simp only [List.length_map]
  by_cases h : s.length = p.length
  · simp only [h, true_and]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    apply forall_congr'
    intro j
    apply forall_congr'
    intro hj
    have his : i < s.length := h.symm ▸ hi
    have hjs : j < s.length := h.symm ▸ hj
    simp [List.getD_eq_getElem?_getD, his, hjs, hf.lt_iff_lt]
  · simp [h]

private theorem bad_map (d : Bool) (f : ℕ → ℕ) (hf : StrictMono f) (s : List ℕ) :
    bad d (s.map f) ↔ bad d s := by
  have h (w : List ℕ) : forbidden d (w.map f) ↔ forbidden d w := by
    cases d <;> simp [forbidden, relativeOrder_map f hf]
  simp only [bad_iff, List.sublist_map_iff]
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, hw⟩
    exact ⟨t, ht, (h t).mp hw⟩
  · rintro ⟨t, ht, hw⟩
    exact ⟨_, ⟨t, ht, rfl⟩, (h t).mpr hw⟩

private theorem bad_mono {w v : List ℕ} (h : w.Sublist v) (d : Bool) : bad d w → bad d v := by
  simp only [bad_iff]
  rintro ⟨t, ht, hbad⟩
  exact ⟨t, ht.trans h, hbad⟩

private theorem rotations_123 :
    ([1, 2, 3] : List ℕ).cyclicPermutations = [[1, 2, 3], [2, 3, 1], [3, 1, 2]] := by decide

-- The descent in a rotation of 123 has the third value strictly between its endpoints,
-- so it cannot be (a + 1, a). The pattern 21 cannot contain the ascending pair (a, a + 1).
private theorem incompatible (d : Bool) (a : ℕ) (u v : List ℕ) :
    ¬forbidden d (u ++ liftEntry a d a :: liftEntry a (!d) a :: v) := by
  intro h
  rcases u with _ | ⟨b, _ | ⟨b', u⟩⟩ <;> rcases v with _ | ⟨c, _ | ⟨c', v⟩⟩ <;>
    cases d <;> simp [forbidden, rotations_123, SameRelativeOrder, liftEntry,
      Nat.forall_lt_succ_right] at h <;> omega

private theorem bad_pair (a : ℕ) (d : Bool) (u v : List ℕ) :
    bad d (u ++ liftEntry a d a :: liftEntry a (!d) a :: v) ↔
      bad d (u ++ liftEntry a d a :: v) ∨ bad d (u ++ liftEntry a (!d) a :: v) := by
  constructor
  · intro h
    obtain ⟨s, hs, hf⟩ := (bad_iff ..).mp h
    obtain ⟨p, r, rfl, hp, hr⟩ := List.sublist_append_iff.mp hs
    cases hr with
    | cons _ hr =>
      exact Or.inr ((bad_iff ..).mpr ⟨_, hp.append hr, hf⟩)
    | cons_cons _ hr =>
      cases hr with
      | cons _ hr =>
        exact Or.inl ((bad_iff ..).mpr ⟨_, hp.append (hr.cons_cons _), hf⟩)
      | cons_cons _ hr => exact (incompatible d a p _ hf).elim
  · rintro (h | h)
    · exact bad_mono ((List.Sublist.refl u).append (((List.Sublist.refl v).cons _).cons_cons _)) d h
    · exact bad_mono ((List.Sublist.refl u).append ((List.Sublist.refl _).cons _)) d h

-- During a push or pop the stack can contain either member of the pair or both.
private inductive Piece (a : ℕ) (d : Bool) : ℕ → List ℕ → Prop
  | one (x : ℕ) (b : Bool) : Piece a d x [liftEntry a b x]
  | two : Piece a d a [liftEntry a d a, liftEntry a (!d) a]

private inductive Represents (a : ℕ) (d : Bool) : List ℕ → List ℕ → Prop
  | nil : Represents a d [] []
  | cons {x s p t} : Piece a d x p → Represents a d s t → Represents a d (x :: s) (p ++ t)

private theorem represents_map {a d s t} (h : Represents a d s t) (ha : a ∉ s) (b : Bool) :
    t = s.map (liftEntry a b) := by
  induction h with
  | nil => rfl
  | @cons x s p t hp _ ih =>
    simp only [List.mem_cons, not_or] at ha
    cases hp with
    | one x c => simp [ih ha.2, liftEntry_ne (Ne.symm ha.1) c b]
    | two => exact (ha.1 rfl).elim

private theorem represents_append {a d u v t} (h : Represents a d (u ++ v) t) :
    ∃ p q, t = p ++ q ∧ Represents a d u p ∧ Represents a d v q := by
  induction u generalizing t with
  | nil => exact ⟨[], t, rfl, .nil, h⟩
  | cons x u ih =>
    cases h with
    | cons hp hr =>
      obtain ⟨p, q, rfl, h₁, h₂⟩ := ih hr
      exact ⟨_, _, (List.append_assoc ..).symm, .cons hp h₁, h₂⟩

private theorem bad_represents {a d s t} (h : Represents a d s t) (hn : s.Nodup) :
    bad d t ↔ bad d s := by
  by_cases ha : a ∈ s
  · obtain ⟨u, v, rfl⟩ := List.append_of_mem ha
    obtain ⟨p, q, rfl, hp, hq⟩ := represents_append h
    have hu : a ∉ u := fun m => (List.nodup_append.mp hn).2.2 a m a (by simp) rfl
    have hv := (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
    cases hq with
    | @cons _ _ b r hb hr =>
      have equiv (c : Bool) :
          bad d (p ++ liftEntry a c a :: r) ↔ bad d (u ++ a :: v) := by
        rw [represents_map hp hu c, represents_map hr hv c]
        simpa using bad_map d _ (liftEntry_mono a c) (u ++ a :: v)
      cases hb with
      | one _ c => exact equiv c
      | two => simp only [List.cons_append, List.nil_append, bad_pair, equiv, or_self]
  · rw [represents_map h ha false, bad_map d _ (liftEntry_mono ..)]

private theorem piece_block (a : ℕ) (d : Bool) (x : ℕ) : Piece a d x (block a d x) := by
  by_cases h : x = a
  · subst x
    simpa [block] using Piece.two (a := a) (d := d)
  · simpa [block, h] using Piece.one (a := a) (d := d) x d

private theorem represents_expand (a : ℕ) (d : Bool) (s : List ℕ) :
    Represents a d s (expand a d s) := by
  induction s with
  | nil => exact .nil
  | cons x s ih => exact .cons (piece_block a d x) ih

private def popCount (d : Bool) (x : ℕ) (st : List ℕ) : ℕ :=
  ((List.range (st.length + 1)).find? fun k => !decide (bad d (x :: st.drop k))).getD st.length

private theorem popCount_cons (d : Bool) (x y : ℕ) (st : List ℕ) :
    popCount d x (y :: st) =
      if bad d (x :: y :: st) then (popCount d x st) + 1 else 0 := by
  unfold popCount
  rw [List.length_cons, List.range_succ_eq_map, List.find?_cons, List.find?_map]
  simp only [List.drop_zero, List.drop_succ_cons, Function.comp_def]
  split_ifs <;> simp_all

private abbrev run (d : Bool) := restrictedStackSortAux (bad d)

private theorem run_pop {d x y xs st} (hb : bad d (x :: y :: st)) :
    run d (x :: xs) (y :: st) = y :: run d (x :: xs) st := by
  change (y :: st).take (popCount d x (y :: st)) ++
    run d xs (x :: (y :: st).drop (popCount d x (y :: st))) =
    y :: (st.take (popCount d x st) ++ run d xs (x :: st.drop (popCount d x st)))
  simp [popCount_cons, hb]

private theorem run_push {d x xs st} (hg : ¬bad d (x :: st)) :
    run d (x :: xs) st = run d xs (x :: st) := by
  have hz : popCount d x st = 0 := by
    cases st with
    | nil => simp [popCount, List.range_succ_eq_map, hg]
    | cons y st => simp [popCount_cons, hg]
  change st.take (popCount d x st) ++ run d xs (x :: st.drop (popCount d x st)) = _
  simp [hz]

private theorem bad_singleton (d : Bool) (x : ℕ) : ¬bad d [x] := by
  rw [bad_iff]
  rintro ⟨s, hs, hf⟩
  have := hs.length_le
  cases d <;> simp [forbidden, rotations_123, SameRelativeOrder] at hf <;> simp at this <;> omega

private theorem push_block {a d x st} (rest : List ℕ) (hn : (x :: st).Nodup)
    (hg : ¬bad d (x :: st)) :
    run d (block a (!d) x ++ rest) (expand a d st) =
      run d rest (block a d x ++ expand a d st) := by
  have rep := represents_expand a d st
  have h₁ := (bad_represents (rep.cons (Piece.one x (!d))) hn).not.mpr hg
  by_cases hx : x = a
  · subst x
    have h₂ := (bad_represents (rep.cons Piece.two) hn).not.mpr hg
    simp only [block, ite_true, Bool.not_not, List.cons_append, List.nil_append]
    simp only [List.cons_append, List.nil_append] at h₁ h₂
    rw [run_push h₁, run_push h₂]
  · simp only [block, hx, ite_false, List.cons_append, List.nil_append]
    simp only [List.cons_append, List.nil_append] at h₁
    rw [run_push h₁, liftEntry_ne hx (!d) d]

private theorem pop_block {a d x y st} (rest : List ℕ) (hn : (x :: y :: st).Nodup)
    (hb : bad d (x :: y :: st)) :
    run d (block a (!d) x ++ rest) (block a d y ++ expand a d st) =
      block a d y ++ run d (block a (!d) x ++ rest) (expand a d st) := by
  obtain ⟨t, ht⟩ : ∃ t, block a (!d) x ++ rest = liftEntry a (!d) x :: t := by
    by_cases hx : x = a <;> simp [block, hx]
  rw [ht]
  have rep := represents_expand a d st
  have h₁ := (bad_represents ((rep.cons (piece_block a d y)).cons (Piece.one x (!d))) hn).mpr hb
  by_cases hy : y = a
  · subst y
    have h₂ := (bad_represents ((rep.cons (Piece.one a (!d))).cons (Piece.one x (!d))) hn).mpr hb
    simp only [block, ite_true, List.cons_append, List.nil_append] at h₁ ⊢
    simp only [List.cons_append, List.nil_append] at h₂
    rw [run_pop h₁, run_pop h₂]
  · simp only [block, hy, ite_false, List.cons_append, List.nil_append] at h₁ ⊢
    rw [run_pop h₁]

-- Simulate each push and pop with a whole block. A push reverses its input order.
private theorem run_expand (a : ℕ) (d : Bool) (s st : List ℕ) (hn : (s ++ st).Nodup) :
    run d (expand a (!d) s) (expand a d st) = expand a d (run d s st) := by
  cases s with
  | nil => rfl
  | cons x xs =>
    have hxt : (x :: st).Nodup := hn.sublist ((List.sublist_append_right xs st).cons_cons x)
    change run d (block a (!d) x ++ expand a (!d) xs) _ = _
    by_cases hb : bad d (x :: st)
    · cases st with
      | nil => exact (bad_singleton d x hb).elim
      | cons y st =>
        change run d _ (block a d y ++ expand a d st) = _
        rw [pop_block _ hxt hb, run_pop hb]
        apply congrArg (block a d y ++ ·)
        exact run_expand a d (x :: xs) st (hn.sublist
          ((List.Sublist.refl (x :: xs)).append (List.sublist_cons_self ..)))
    · rw [push_block _ hxt hb, run_push hb]
      exact run_expand a d xs (x :: st) (List.perm_middle.nodup_iff.mpr hn)
termination_by 2 * s.length + st.length
decreasing_by
  all_goals subst_vars; simp
  omega

private theorem run_perm (d : Bool) (s st : List ℕ) : (run d s st).Perm (s ++ st) := by
  induction s generalizing st with
  | nil => rfl
  | cons x xs ih =>
    let k := popCount d x st
    change (st.take k ++ run d xs (x :: st.drop k)).Perm _
    apply ((ih _).append_left _).trans
    apply (List.perm_append_comm_assoc ..).trans
    apply (List.perm_middle.append_left xs).trans
    simp

private abbrev machine := cyclicSortingMachine [1, 2, 3]

private theorem machine_perm (s : List ℕ) : (machine s).Perm s := by
  change (run false (run true s []) []).Perm s
  exact (run_perm false (run true s []) []).trans (by simpa using run_perm true s [])

private theorem machine_expand (a : ℕ) (s : List ℕ) (hn : s.Nodup) :
    machine (expand a false s) = expand a false (machine s) := by
  have h₁ := run_expand a true s [] (by simpa)
  have h₂ := run_expand a false (run true s []) [] (by
    simpa using (run_perm true s []).nodup_iff.mpr (by simpa))
  change run false (run true (expand a false s) []) [] = _
  change run true (expand a false s) [] = _ at h₁
  rw [h₁]
  exact h₂

private theorem iterate_expand (a k : ℕ) (s : List ℕ) (hn : s.Nodup) :
    machine^[k] (expand a false s) = expand a false (machine^[k] s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply, machine_expand a s hn]
    exact ih _ ((machine_perm s).nodup_iff.mpr hn)

-- Expansion preserves run boundaries, so it leaves the standardized run heads unchanged.
private theorem adjacent_lift (a x y : ℕ) :
    liftEntry a false x = liftEntry a true y + 1 ↔ x = y + 1 := by
  simp only [liftEntry, Bool.toNat_false, Bool.toNat_true]
  split_ifs <;> omega

private theorem heads_expand (a : ℕ) (s : List ℕ) (prev : Option ℕ) :
    consecutiveRunHeads (prev.map (liftEntry a true)) (expand a false s) =
      (consecutiveRunHeads prev s).map (liftEntry a false) := by
  induction s generalizing prev with
  | nil => cases prev <;> rfl
  | cons x xs ih =>
    change consecutiveRunHeads _ (block a false x ++ expand a false xs) = _
    have tail := ih (some x)
    simp only [Option.map_some] at tail
    by_cases hx : x = a
    · subst x
      have adjacent : liftEntry a true a = liftEntry a false a + 1 := by simp [liftEntry]
      rw [adjacent] at tail
      cases prev with
      | none => simp [block, consecutiveRunHeads, adjacent, tail]
      | some y =>
        simp only [Option.map_some, block, ite_true, Bool.not_false, List.cons_append,
          List.nil_append, consecutiveRunHeads, adjacent, adjacent_lift, tail, List.map_append]
        split <;> rfl
    · have he := liftEntry_ne hx false true
      rw [← he] at tail
      cases prev with
      | none => simp [block, hx, consecutiveRunHeads, tail]
      | some y =>
        simp only [block, hx, ite_false, List.cons_append, List.nil_append, Option.map_some,
          consecutiveRunHeads, adjacent_lift, tail, List.map_append]
        split <;> rfl

private theorem standardize_map (f : ℕ → ℕ) (hf : StrictMono f) (s : List ℕ) :
    standardizeSeq (s.map f) = standardizeSeq s := by
  simp [standardizeSeq, List.map_map, List.filter_map, hf.le_iff_le, Function.comp_def]

private theorem reduction_expand (a : ℕ) (s : List ℕ) :
    reductionSeq (expand a false s) = reductionSeq s := by
  unfold reductionSeq
  rw [show none = (none : Option ℕ).map (liftEntry a true) by rfl, heads_expand]
  exact standardize_map _ (liftEntry_mono ..) _

private def lower (a x : ℕ) : ℕ := if x ≤ a then x else x - 1

-- Delete the second member of the pair and close the gap in the remaining labels.
private def contract (a : ℕ) (s : List ℕ) : List ℕ := (s.filter (· ≠ a + 1)).map (lower a)

private theorem contract_append (a : ℕ) (s t : List ℕ) :
    contract a (s ++ t) = contract a s ++ contract a t := by simp [contract]

private theorem contract_expand (a : ℕ) (s : List ℕ) : contract a (expand a false s) = s := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    change contract a (block a false x ++ expand a false xs) = _
    rw [contract_append, ih]
    rcases lt_trichotomy x a with h | rfl | h
    · simp [block, liftEntry, lower, contract, h, ne_of_lt h, show x ≠ a + 1 by omega, h.le]
    · simp [block, liftEntry, lower, contract]
    · simp [block, liftEntry, lower, contract, h.ne', h.not_gt,
        show ¬ x + 1 ≤ a by omega]

private theorem expand_contract_away {a : ℕ} (s : List ℕ) (ha : a ∉ s) (hs : a + 1 ∉ s) :
    expand a false (contract a s) = s := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at ha hs
    have he : contract a (x :: xs) = lower a x :: contract a xs := by simp [contract, Ne.symm hs.1]
    rw [he]
    change block a false (lower a x) ++ expand a false (contract a xs) = _
    rw [ih ha.2 hs.2]
    rcases lt_or_gt_of_ne (Ne.symm ha.1) with h | h
    · simp [lower, h.le, block, h.ne, liftEntry, h]
    · have hx : a < x - 1 := by omega
      simp [lower, h.not_ge, block, hx.ne', liftEntry, hx.not_gt, show x - 1 + 1 = x by omega]

private theorem expand_contract_pair (a : ℕ) (u v : List ℕ)
    (hn : (u ++ a :: (a + 1) :: v).Nodup) :
    expand a false (contract a (u ++ a :: (a + 1) :: v)) = u ++ a :: (a + 1) :: v := by
  obtain ⟨_, ht, hd⟩ := List.nodup_append.mp hn
  have h₁ : a ∉ u := fun h => hd a h a (by simp) rfl
  have h₂ : a + 1 ∉ u := fun h => hd _ h _ (by simp) rfl
  have h₃ : a ∉ v := fun h => ht.notMem (by simp [h])
  have h₄ := ht.of_cons.notMem
  rw [contract_append]
  have he : contract a (a :: (a + 1) :: v) = a :: contract a v := by simp [contract, lower]
  rw [he]
  change (contract a u ++ a :: contract a v).flatMap _ = _
  rw [List.flatMap_append, List.flatMap_cons]
  change expand a false (contract a u) ++ (block a false a ++ expand a false (contract a v)) = _
  rw [expand_contract_away _ h₁ h₂, expand_contract_away _ h₃ h₄]
  simp [block, liftEntry]

private theorem expand_range_above {a b : ℕ} (hb : a < b) (n : ℕ) :
    expand a false (List.range' b n) = List.range' (b + 1) n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [List.range'_succ]
    change block a false b ++ expand a false (List.range' (b + 1) n) = _
    simp [block, liftEntry, hb.ne', hb.not_gt, ih (by omega : a < b + 1)]

private theorem expand_range {a b n : ℕ} (hb : b ≤ a) (ha : a < b + n) :
    expand a false (List.range' b n) = List.range' b (n + 1) := by
  induction n generalizing b with
  | zero => omega
  | succ n ih =>
    rw [List.range'_succ, List.range'_succ (s := b) (n := n + 1)]
    change block a false b ++ expand a false (List.range' (b + 1) n) = _
    rcases hb.eq_or_lt with rfl | h
    · simp [block, liftEntry, expand_range_above (Nat.lt_succ_self _), List.range'_succ]
    · have ht := ih (b := b + 1) (by omega) (by omega)
      simp [block, h.ne, liftEntry, h, ht]

private theorem standardize_perm {n : ℕ} {s : List ℕ} (hp : s.Perm (List.range' 1 n)) :
    standardizeSeq s = s := by
  refine (List.map_congr_left (l := s) (g := id) ?_).trans (List.map_id s)
  intro x hx
  have hm := List.mem_range'_1.mp (hp.mem_iff.mp hx)
  have split : List.range' 1 n = List.range' 1 x ++ List.range' (1 + x) (n - x) := by
    rw [List.range'_append_1]
    congr 1
    omega
  let p (y : ℕ) : Bool := decide (y ≤ x)
  change (s.filter p).length = x
  rw [(hp.filter p).length_eq, split, List.filter_append]
  have hl : (List.range' 1 x).filter p = List.range' 1 x := List.filter_eq_self.mpr (by
    intro y hy
    have := List.mem_range'_1.mp hy
    simp [p]; omega)
  have hr : (List.range' (1 + x) (n - x)).filter p = [] := List.filter_eq_nil_iff.mpr (by
    intro y hy
    have := List.mem_range'_1.mp hy
    simp [p]; omega)
  simp [hl, hr]

private theorem heads_of_no_pair (x : ℕ) (s : List ℕ)
    (h : ∀ u a v, x :: s ≠ u ++ a :: (a + 1) :: v) :
    consecutiveRunHeads (some x) s = s := by
  induction s generalizing x with
  | nil => rfl
  | cons y ys ih =>
    have hxy : y ≠ x + 1 := fun he => h [] x ys (by simp [he])
    have ht := ih y (fun u a v he => h (x :: u) a v (congrArg (x :: ·) he))
    simp [consecutiveRunHeads, hxy, ht]

end cyclicSortingMachine_123_iterate_eq_id_iff_reductionSeq

open cyclicSortingMachine_123_iterate_eq_id_iff_reductionSeq in
/-- **Reduction and iterates of $SC_{[123]}$.** Let $\pi$ be a permutation of
$[n] = \{1, \dots, n\}$, written as a sequence, let $\mathrm{red}(\pi)$ be its reduction, of
length $\ell$, and let $SC_{[123]}^k$ be the $k$-fold iterate of the cyclic avoidance machine
$SC_{[123]}$. For every $k \ge 0$, $SC_{[123]}^k(\pi) = 12 \cdots n$ if and only if
$SC_{[123]}^k(\mathrm{red}(\pi)) = 12 \cdots \ell$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Corollary 1 (`integers-2026-A15-cor-1`). -/
public theorem cyclicSortingMachine_123_iterate_eq_id_iff_reductionSeq {n k : ℕ}
    {π : List ℕ} (hπ : π.Perm (List.range' 1 n)) :
    (cyclicSortingMachine [1, 2, 3])^[k] π = List.range' 1 n ↔
      (cyclicSortingMachine [1, 2, 3])^[k] (reductionSeq π) =
        List.range' 1 (reductionSeq π).length := by
  change machine^[k] π = _ ↔ machine^[k] (reductionSeq π) = _
  by_cases h : ∃ u a v, π = u ++ a :: (a + 1) :: v
  · obtain ⟨u, a, v, rfl⟩ := h
    have ha := List.mem_range'_1.mp (hπ.mem_iff.mp (by simp : a ∈ u ++ a :: (a + 1) :: v))
    have ha' := List.mem_range'_1.mp
      (hπ.mem_iff.mp (by simp : a + 1 ∈ u ++ a :: (a + 1) :: v))
    cases n with
    | zero => omega
    | succ n =>
      let t := contract a (u ++ a :: (a + 1) :: v)
      have hr := expand_range (b := 1) (a := a) (n := n) ha.1 (by omega)
      have he : expand a false t = _ := expand_contract_pair a u v
        (hπ.nodup_iff.mpr (List.nodup_range' 1))
      have ht : t.Perm (List.range' 1 n) := by
        have hc := (hπ.filter (fun x => decide (x ≠ a + 1))).map (lower a)
        change t.Perm (contract a (List.range' 1 (n + 1))) at hc
        rwa [← hr, contract_expand] at hc
      have hinj : Function.Injective (expand a false) :=
        Function.LeftInverse.injective (contract_expand a)
      rw [← he, iterate_expand _ _ _ (ht.nodup_iff.mpr (List.nodup_range' 1)),
        ← hr, hinj.eq_iff, reduction_expand]
      exact cyclicSortingMachine_123_iterate_eq_id_iff_reductionSeq (k := k) ht
  · simp only [not_exists] at h
    have hs : consecutiveRunHeads none π = π := by
      cases π with
      | nil => rfl
      | cons x xs => simp [consecutiveRunHeads, heads_of_no_pair x xs h]
    have hr : reductionSeq π = π := by rw [reductionSeq, hs, standardize_perm hπ]
    rw [hr, hπ.length_eq, List.length_range']
termination_by n

end MetaMathlibExt
