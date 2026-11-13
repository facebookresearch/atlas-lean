/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Schnirelmann density of sums with an exact basis (exact-basis variant of Erdős Problem 35)

Erdős Problem 35: let `B ⊆ ℕ` be an additive basis of order `k` with `0 ∈ B`. Is it true that for
every `A ⊆ ℕ`, `d_s(A + B) ≥ α + α (1 - α) / k`, where `α = d_s(A)` is the Schnirelmann density?
This module records Plünnecke's exact-basis variant, in which every `n ∈ ℕ` is a sum of exactly `k`
elements of `B`; with erdosproblems.com's asymptotic notion of basis the claim is false.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.Schnirelmann

@[expose] public section

namespace MathlibExt.NumberTheory.SchnirelmannBasisSumErdosProblem35Wanted

/-!
Source of the variant: H. Plünnecke, Eine zahlentheoretische Anwendung der Graphentheorie, J. Reine
Angew. Math. (1970), 171-183, with Ruzsa's observation, as recorded for Erdős Problem 35 at T. F.
Bloom, Erdős Problems, Problem #35, https://www.erdosproblems.com/35 (status PROVED (LEAN)).
UnsolvedMath record UM-30006692 (`EP-35`), dataset ulamai/UnsolvedMath v1.8.0.

This is the exact-basis variant of Erdős Problem 35, not the problem with erdosproblems.com's
definition. Basis of order `k` is taken in the sense of Plünnecke's theorem: `0 ∈ B` and every
`n ∈ ℕ` is a sum of exactly `k` elements of `B` (equivalently, of at most `k` positive elements).
This is not the definition on erdosproblems.com's definitions page, where `B` is an additive basis
of order `k` when all sufficiently large integers are sums of at most `k` elements of `B`; with that
definition the claim is false for every `k ≥ 1`: `B = {0} ∪ [M, ∞)` and `A = [1, L] ∪ [M + 1, ∞)`
with `0 < L < M` give `A + B = A`, so `d_s(A + B) = d_s(A) = L/M`, below the claimed
`α + α (1 - α) / k`. `d_s` is Mathlib's `schnirelmannDensity`. Compared with the formal-conjectures
statement `ErdosProblems/35.lean` (equivalent; `Set.IsAddBasisOfOrder` there, `∀ n, n ∈ k • B`, is
the same exact notion, and the entry links a Lean proof of that statement; no code imported).
-/

open scoped Pointwise

open Classical in
/-- The exact-basis variant of Erdős Problem 35, with "additive basis of order `k`" in the sense of
Plünnecke's theorem (not erdosproblems.com's asymptotic one, under which the claim is false): if
`0 ∈ B` and every `n ∈ ℕ` is a sum of exactly `k` elements of `B`, then
`d_s(A + B) ≥ α + α (1 - α) / k` for every `A ⊆ ℕ`, where `α = d_s(A)` is the Schnirelmann
density. -/
def schnirelmannExactBasisSumBound : Prop :=
  ∀ (B : Set ℕ) (k : ℕ), 0 ∈ B → (∀ n : ℕ, ∃ x : Fin k → ℕ, (∀ i, x i ∈ B) ∧ n = ∑ i, x i) →
    ∀ A : Set ℕ, schnirelmannDensity A +
        schnirelmannDensity A * (1 - schnirelmannDensity A) / k ≤ schnirelmannDensity (A + B)

/--
Resolved true for the exact-basis variant only (bases in the sense of Plünnecke's theorem): if
`0 ∈ B` and every `n ∈ ℕ` is a sum of exactly `k` elements of `B`, Plünnecke proved
`d_s(A + B) ≥ d_s(A)^{1 - 1/k}` for every `A` with `d_s(A) > 0`, and `α^{1 - 1/k} ≥ α + α (1 - α)/k`
on `[0, 1]` (Ruzsa's observation; Erdős had the bound with `2k`). The statement uses that definition
because the resolution does: with erdosproblems.com's asymptotic definition (all large integers are
sums of at most `k` elements of `B`) the claim is false, e.g. `B = {0} ∪ [M, ∞)` and
`A = [1, L] ∪ [M + 1, ∞)` with `0 < L < M` give `d_s(A + B) = d_s(A) = L/M`. Source of the variant:
H. Plünnecke, Eine zahlentheoretische Anwendung der Graphentheorie, J. Reine Angew. Math. (1970),
171-183; related problem: T. F. Bloom, Erdős Problems, Problem #35, https://www.erdosproblems.com/35
(status PROVED (LEAN)), where Ruzsa observed that the claim follows from Plünnecke's inequality
d_s(A + B) ≥ d_s(A)^{1 - 1/k}, since α^{1 - 1/k} ≥ α + α(1 - α)/k for α ∈ [0, 1],
https://www.erdosproblems.com/35.
-/
public theorem_wanted schnirelmannExactBasisSumBound_holds : schnirelmannExactBasisSumBound

end MathlibExt.NumberTheory.SchnirelmannBasisSumErdosProblem35Wanted
