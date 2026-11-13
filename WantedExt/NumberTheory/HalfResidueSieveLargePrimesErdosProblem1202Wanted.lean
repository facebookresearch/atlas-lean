/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sieving half the residues modulo large primes (Erdős Problem 1202)

Erdős Problem 1202: let `ε, η > 0`. Is there `k` such that, given any `k` primes `p₁ < ⋯ < p_k <
n^{1-ε}`, each with a set `Aᵢ` of `(pᵢ - 1)/2` residue classes modulo `pᵢ`, the number of `m ≤ n`
with `m ∉ Aᵢ (mod pᵢ)` for all `i` is at most `ε n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.NumberTheory.HalfResidueSieveLargePrimesErdosProblem1202Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1202, https://www.erdosproblems.com/1202 (status
SOLVED). UnsolvedMath record UM-30007243 (`EP-1202`), dataset ulamai/UnsolvedMath v1.8.0.

The source's statement (on erdosproblems.com and in the record alike) introduces `η` but never uses
it; the target keeps the stated bound `ε n`, so the same `ε` bounds the primes and the survivors.
The presumably intended two-parameter question (at most `η n` survivors, for all `ε, η > 0`) implies
this one by taking `η = ε`, so this refutation refutes it as well; B. Green's version (Problem 44:
`k = 1000`, primes below `N^{9/10}`, at most `N/10` survivors) has `ε = η = 1/10`. `m` ranges over
`1 ≤ m ≤ n`. Compared with the formal-conjectures statement `ErdosProblems/1202.lean` (equivalent;
no code imported).
-/

/-- Erdős Problem 1202 (as stated, with the same `ε` in the prime range and in the conclusion):
for every `ε > 0` there is `k` such that for every `n`, all primes `p₁ < ⋯ < p_k < n^{1-ε}` and
all sets `Aᵢ` of `(pᵢ - 1)/2` residue classes modulo `pᵢ`, at most `ε n` integers `m ∈ [1, n]`
avoid every `Aᵢ` modulo `pᵢ`. -/
def halfResidueSieveLeavesFew : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ (n : ℕ) (p : Fin k → ℕ) (A : (i : Fin k) → Finset (ZMod (p i))),
    (∀ i, (p i).Prime) → StrictMono p → (∀ i, (p i : ℝ) < (n : ℝ) ^ (1 - ε)) →
      (∀ i, (A i).card = (p i - 1) / 2) →
        (((Finset.Icc 1 n).filter fun m => ∀ i, (m : ZMod (p i)) ∉ A i).card : ℝ) ≤ ε * n

/--
Resolved false: erdosproblems.com/1202 accepts the construction of Price (with GPT-5.4 Pro): for
every `c > 0` and `m > (n log n)^{1/2}` there are `k ≫_c m²/(n log n)` primes in `(m, 2m]`, with the
`Aᵢ` intervals of residues, leaving at least `(1/2 - c) n` integers of `[1, n]`. With `2m < n^{1-ε}`
and `ε < 1/2` this exceeds any fixed `k` for large `n` (keeping only `k` of the primes leaves more
survivors), while the survivors exceed `ε n` when `ε < 1/2 - c`. Source: T. F. Bloom, Erdős
Problems, Problem #1202, https://www.erdosproblems.com/1202 (status SOLVED); resolution: L. Price
(with GPT-5.4 Pro), construction posted on Overleaf and recorded on erdosproblems.com/1202; the
problem is Problem 44 of B. Green, 100 open problems, erdosproblems.com/1202: for every c > 0 and m
> (n log n)^{1/2} there are k ≫_c m²/(n log n) primes m < p₁ < ⋯ < p_k ≤ 2m with intervals Aᵢ of (pᵢ
- 1)/2 residues leaving at least (1/2 - c) n survivors in [1, n],
https://www.overleaf.com/read/qyhdmrchqnvb.
-/
public theorem_wanted halfResidueSieveLeavesFew_refuted : ¬ halfResidueSieveLeavesFew

end MathlibExt.NumberTheory.HalfResidueSieveLargePrimesErdosProblem1202Wanted
