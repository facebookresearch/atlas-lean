/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.ConsecutiveCyclicStackCount
public import MathlibExt.Combinatorics.Enumerative.CyclicPatternAvoidingStacks
public import MathlibExt.Combinatorics.Enumerative.CyclicSortingMachineReductionLength
public import MathlibExt.Combinatorics.Enumerative.CyclicSortingMachineSuperimpose

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

end MetaMathlibExt
