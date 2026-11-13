/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Almost covering systems with moduli in a short range (Erdős Problem 27)

Erdős Problem 27: an `ε`-almost covering system is a set of congruences `a_i (mod n_i)` with
distinct moduli `n₁ < ⋯ < n_k` whose uncovered integers have density at most `ε`. Is there `C > 1`
such that for every `ε > 0` and `N ≥ 1` there is an `ε`-almost covering system with `N ≤ n₁ < ⋯ <
n_k ≤ C N`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Functor
public import Mathlib.Data.Int.ModEq

@[expose] public section

namespace MathlibExt.NumberTheory.AlmostCoveringShortRangeErdosProblem27Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #27, https://www.erdosproblems.com/27 (status
DISPROVED). UnsolvedMath record UM-30006688 (`EP-27`), dataset ulamai/UnsolvedMath v1.8.0.

A system is a finite set `S` of distinct moduli with one residue `a n` for each `n ∈ S`. The
uncovered set is periodic modulo `∏_{n ∈ S} n`, so its density is its proportion in one period. No
formal-conjectures statement exists for 27.
-/

open Classical in
/-- The density of the integers satisfying none of the congruences `x ≡ a n (mod n)`, `n ∈ S`.
The uncovered set is periodic modulo `∏_{n ∈ S} n`, so its density is its proportion in
`[0, ∏_{n ∈ S} n)`. -/
noncomputable def uncoveredDensity (S : Finset ℕ) (a : ℕ → ℤ) : ℝ :=
  (((Finset.range (∏ n ∈ S, n)).filter fun x => ∀ n ∈ S, ¬ (x : ℤ) ≡ a n [ZMOD n]).card : ℝ) /
    ((∏ n ∈ S, n : ℕ) : ℝ)

/-- Erdős Problem 27: there is `C > 1` such that for every `ε > 0` and `N ≥ 1` there is an
`ε`-almost covering system (one congruence `a n (mod n)` for each modulus `n` in a set `S` of
distinct moduli, uncovered density at most `ε`) with all moduli in `[N, C N]`. -/
def almostCoveringInShortRange : Prop :=
  ∃ C : ℝ, 1 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, 1 ≤ N →
    ∃ (S : Finset ℕ) (a : ℕ → ℤ), (∀ n ∈ S, N ≤ n ∧ (n : ℝ) ≤ C * N) ∧
      uncoveredDensity S a ≤ ε

/--
Resolved false: Filaseta, Ford, Konyagin, Pomerance and Yu proved (Theorem B, Conjecture 2 of their
paper) that for each `K > 1` there is `d_K > 0` such that for all large `N` any classes modulo
distinct `n ∈ (N, K N]` leave density at least `d_K` uncovered; since `[N, C N] ⊆ (N - 1, 2 C (N -
1)]` for `N ≥ 2` and dropping moduli only enlarges the uncovered set, every `C > 1` fails with `ε =
d_{2C} / 2`. erdosproblems.com/27 lists the problem as disproved. Source: T. F. Bloom, Erdős
Problems, Problem #27, https://www.erdosproblems.com/27 (status DISPROVED); resolution: M. Filaseta,
K. Ford, S. Konyagin, C. Pomerance and G. Yu, Sieving by large integers and covering systems of
congruences, J. Amer. Math. Soc. (2007), 495-517, arXiv:math/0507374, Theorem B, which proves the
Erdős-Graham Conjecture 2: for each K > 1 there is d_K > 0 such that for all large N, residue
classes r(n) (mod n) for distinct n ∈ (N, KN] leave uncovered a set of density at least d_K,
https://arxiv.org/abs/math/0507374.
-/
public theorem_wanted almostCoveringInShortRange_refuted : ¬ almostCoveringInShortRange

end MathlibExt.NumberTheory.AlmostCoveringShortRangeErdosProblem27Wanted
