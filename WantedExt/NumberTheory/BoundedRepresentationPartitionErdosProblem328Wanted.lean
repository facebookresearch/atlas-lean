/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Splitting sets with bounded representation counts (Erdős Problem 328)

Erdős Problem 328 (Erdős and Newman): suppose `A ⊆ ℕ` and `C > 0` satisfy `1_A ∗ 1_A(n) ≤ C` for all
`n`. Can `A` be partitioned into `t = t(C)` sets `A_i` with `1_{A_i} ∗ 1_{A_i}(n) < C` for all `i`
and `n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.NumberTheory.BoundedRepresentationPartitionErdosProblem328Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #328, https://www.erdosproblems.com/328 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006825 (`EP-328`), dataset ulamai/UnsolvedMath v1.8.0.

`1_A ∗ 1_A(n)` counts ordered pairs. `C` ranges over integers `C ≥ 3`: for non-integer `C` the
single part `A` already works, and for `C = 1, 2` the claim fails for trivial reasons (a singleton,
resp. an infinite Sidon set), which would make the refutation vacuous; the cases `C = 3, 4` are the
ones Erdős settled. formal-conjectures `ErdosProblems/328.lean` quantifies over all `C > 0`, so its
refutation is witnessed by `C = 1` (no code imported).
-/

open Classical in
/-- `1_A ∗ 1_A (n)`: the number of ordered pairs `(a, b) ∈ A × A` with `a + b = n`, counted by
the first entry `a ∈ [0, n]`. -/
noncomputable def sumRepCount (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun a => a ∈ A ∧ n - a ∈ A).card

/-- Erdős Problem 328 (Erdős-Newman) for integers `C ≥ 3`: there is `t = t(C)` such that every
`A ⊆ ℕ` with `1_A ∗ 1_A ≤ C` is a disjoint union of `t` sets `A_i` with
`1_{A_i} ∗ 1_{A_i} < C`. -/
def boundedRepresentationPartition : Prop :=
  ∀ C : ℕ, 3 ≤ C → ∃ t : ℕ, ∀ A : Set ℕ, (∀ n, sumRepCount A n ≤ C) →
    ∃ P : Fin t → Set ℕ, (⋃ i, P i) = A ∧ Pairwise (fun i j => Disjoint (P i) (P j)) ∧
      ∀ i n, sumRepCount (P i) n < C

/--
Resolved false: Erdős showed that for `C = 3, 4` (and infinitely many other `C`) no uniform `t(C)`
exists, and Nešetřil and Rödl showed the answer is no for every `C`, even when `t` may depend on
`A`. erdosproblems.com/328 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems,
Problem #328, https://www.erdosproblems.com/328 (status DISPROVED (LEAN)); resolution: J. Nešetřil
and V. Rödl, Two proofs in combinatorial number theory, Proc. Amer. Math. Soc. (1985), 185-188; P.
Erdős, Some applications of Ramsey's theorem to additive number theory, European J. Combin. (1980),
43-46, erdosproblems.com/328: Nešetřil and Rödl showed the answer is no for all C (even if t may
depend on A); Erdős had shown no for C = 3, 4 and infinitely many other C,
https://www.erdosproblems.com/328.
-/
public theorem_wanted boundedRepresentationPartition_refuted : ¬ boundedRepresentationPartition

end MathlibExt.NumberTheory.BoundedRepresentationPartitionErdosProblem328Wanted
