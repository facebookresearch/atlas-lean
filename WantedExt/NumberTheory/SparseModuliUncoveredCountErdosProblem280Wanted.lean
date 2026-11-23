/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Uncovered counts for sparse moduli (Erdős Problem 280)

Erdős Problem 280: let `n₁ < n₂ < ⋯` with classes `a_k (mod n_k)` and, for some `ε > 0`, `n_k > (1 +
ε) k log k` for all `k`. Then `#{m < n_k : m ≢ a_i (mod n_i), 1 ≤ i ≤ k} ≠ o(k)`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Functor

@[expose] public section

namespace MathlibExt.NumberTheory.SparseModuliUncoveredCountErdosProblem280Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #280, https://www.erdosproblems.com/280 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006803 (`EP-280`), dataset ulamai/UnsolvedMath v1.8.0.

The moduli are `n k`, `k ≥ 1` (`n 0` only enters strict monotonicity); `m` ranges over `0 ≤ m <
n_k`, which changes the count by at most one. Compared with the formal-conjectures statement
`ErdosProblems/280.lean` (equivalent; no code imported).
-/

open Filter Asymptotics

open Classical in
/-- The number of `m < n k` lying in none of the classes `a i (mod n i)`, `1 ≤ i ≤ k`. -/
noncomputable def uncoveredBelow (n : ℕ → ℕ) (a : ℕ → ℤ) (k : ℕ) : ℕ :=
  ((Finset.range (n k)).filter fun m => ∀ i ∈ Finset.Icc 1 k, ¬ (m : ℤ) ≡ a i [ZMOD n i]).card

/-- Erdős Problem 280: if `n₁ < n₂ < ⋯` and, for some `ε > 0`, `n_k > (1 + ε) k log k` for all
`k ≥ 1`, then for any residues `a_k` the count `#{m < n_k : m ≢ a_i (mod n_i), 1 ≤ i ≤ k}` is
not `o(k)`. -/
def uncoveredCountNotLittleO : Prop :=
  ∀ (n : ℕ → ℕ) (a : ℕ → ℤ), StrictMono n → ∀ ε : ℝ, 0 < ε →
    (∀ k : ℕ, 1 ≤ k → (1 + ε) * k * Real.log k < n k) →
      ¬ (fun k : ℕ => (uncoveredBelow n a k : ℝ)) =o[atTop] fun k : ℕ => (k : ℝ)

/--
Resolved false: Cambie observed that `n_k = 2^k`, `a_k = 2^{k-1} + 1` satisfies the growth condition
(with `ε = 1`) while the only uncovered `m < 2^k` is `m = 1`, so the count is `1 = o(k)`.
erdosproblems.com/280 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem
#280, https://www.erdosproblems.com/280 (status DISPROVED (LEAN)); resolution: S. Cambie,
counterexample recorded on erdosproblems.com/280, n_k = 2^k and a_k = 2^{k-1} + 1 leave only m = 1
uncovered below n_k, so the count is 1 = o(k), https://www.erdosproblems.com/280.
-/
public theorem_wanted uncoveredCountNotLittleO_refuted : ¬ uncoveredCountNotLittleO

end MathlibExt.NumberTheory.SparseModuliUncoveredCountErdosProblem280Wanted
