/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Odd-indexed Fibonacci numbers via pattern-avoiding permutations

Statements from Juan B. Gil, Felix H. Xu, and William
Y. Zhu, "Odd-Indexed Fibonacci Numbers via
Pattern-Avoiding Permutations", *INTEGERS* 25 (2025),
Article A79 (<https://math.colgate.edu/~integers/vol25.html>).

Pattern containment is classical: `HasPattern σ π` says
some subsequence of `σ` is order-isomorphic to `π`
(patterns are given as `0`-based value functions, so
`pat321 = ![2, 1, 0]`, etc.). Stated here are the counts
`|Sₙ(321, 4123)| = |Sₙ(321, 3412)| = |Sₙ(231, 3124)| =
F_{2n-1}` (Propositions 1, 7, 10), the position-of-`1`
refinements for the first and third classes
(Propositions 2, 11, counts only: the bivariate
generating-function clauses reach the extraction in
garbled form and are not stated), and the first clause of
Proposition 8 (positions `1` and `2` of the entry `1` in
the `(321, 3412)` class). All were verified by brute force
for `n ≤ 7`.

Not stated (see the source audit table): the `(321, 2143)`
family (Propositions 4, 5, 6), whose classical-pattern
counts `1, 2, 5, 13, 33, 80, 185` disagree with the
extracted `F_{2n-1}` claim, so the pattern `2143` as
extracted cannot be the classical pattern intended;
Proposition 8's clause for positions `≥ 3`, whose
extracted form `|Sₙ^{k→1}| = |S_{n-1}|` is numerically
false (the values are `F_{2n-2k+1}`); and the bijection
statements (Corollary 1, Propositions 3, 6, 9, 12), which
need the paper's classes of noncrossing/nonnesting
partitions, Dyck paths, block fountains, and directed
column-convex polyominoes.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

/-- Classical pattern containment: `σ` contains the
pattern `π` if some strictly increasing choice of
positions gives entries order-isomorphic to `π`. -/
def HasPattern {n k : ℕ} (σ : Equiv.Perm (Fin n))
    (π : Fin k → Fin k) : Prop :=
  ∃ e : Fin k → Fin n, (∀ i j : Fin k, i < j → e i < e j) ∧
    ∀ i j : Fin k, σ (e i) < σ (e j) ↔ π i < π j


/-- The pattern `321` (0-based). -/
def pat321 : Fin 3 → Fin 3 := ![2, 1, 0]

/-- The pattern `231` (0-based). -/
def pat231 : Fin 3 → Fin 3 := ![1, 2, 0]

/-- The pattern `4123` (0-based). -/
def pat4123 : Fin 4 → Fin 4 := ![3, 0, 1, 2]

/-- The pattern `3412` (0-based). -/
def pat3412 : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- The pattern `3124` (0-based). -/
def pat3124 : Fin 4 → Fin 4 := ![2, 0, 1, 3]

/-- **Proposition 1**: `|Sₙ(321, 4123)| = F_{2n-1}`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 1. -/
theorem_wanted card_avoid_321_4123 (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat4123} =
      Nat.fib (2 * n - 1)

/-- **Proposition 7**: `|Sₙ(321, 3412)| = F_{2n-1}`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 7. -/
theorem_wanted card_avoid_321_3412 (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat3412} =
      Nat.fib (2 * n - 1)

/-- **Proposition 10**: `|Sₙ(231, 3124)| = F_{2n-1}`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 10. -/
theorem_wanted card_avoid_231_3124 (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124} =
      Nat.fib (2 * n - 1)

/-- **Proposition 2** (count): for `1 ≤ k < n`, the number
of `(321, 4123)`-avoiding permutations of `[n]` with
`σ(k) = 1` is `k * |S_{n-k}(321, 4123)|` (positions and
values 1-based in the paper; here the position is
`j : Fin n` with `σ j = 0`, so `k = j + 1`).

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 2. -/
theorem_wanted card_avoid_321_4123_pos_zero (n : ℕ)
    (hn : 1 ≤ n) (j : Fin n) (hj : j.val + 1 < n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat4123 ∧
        σ j = ⟨0, hn⟩} =
      (j.val + 1) * Nat.card
        {σ : Equiv.Perm (Fin (n - j.val - 1)) //
          ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat4123}

/-- **Proposition 11** (count): for `1 ≤ k < n`, the
number of `(231, 3124)`-avoiding permutations of `[n]`
with `σ(k) = 1` is `k * |S_{n-k}(231, 3124)|`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 11. -/
theorem_wanted card_avoid_231_3124_pos_zero (n : ℕ)
    (hn : 1 ≤ n) (j : Fin n) (hj : j.val + 1 < n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124 ∧
        σ j = ⟨0, hn⟩} =
      (j.val + 1) * Nat.card
        {σ : Equiv.Perm (Fin (n - j.val - 1)) //
          ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124}

/-- **Proposition 8**, first clause: for `n > 1`, the
numbers of `(321, 3412)`-avoiding permutations of `[n]`
with `σ(1) = 1` and with `σ(2) = 1` (1-based) both equal
`F_{2n-3}`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 8. -/
theorem_wanted card_avoid_321_3412_pos_zero_le (n : ℕ)
    (hn : 2 ≤ n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat3412 ∧
        σ ⟨0, by omega⟩ = ⟨0, by omega⟩} =
      Nat.fib (2 * n - 3) ∧
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat3412 ∧
        σ ⟨1, hn⟩ = ⟨0, by omega⟩} =
      Nat.fib (2 * n - 3)

end MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted
