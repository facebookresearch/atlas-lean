/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 857: weak sunflower conjecture for k ≥ 4

See https://www.erdosproblems.com/857 and P. Erdős and E. Szemerédi,
"Combinatorial properties of systems of sets,"
Journal of Combinatorial Theory, Series A 24(3) (1978), 308–313.
UnsolvedMath record id 2345 / EP-857. Proved by Bucić, He and Lee,
arXiv:2610.26686 (2026), Theorem 1; this repository records no Lean proof.
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem857WeakSunflowerWanted

/-- `F` contains a `k`-sunflower: `k` members whose pairwise intersections are all equal (the same
definition as in `SunflowerFreeFamilyExponentialBound`). -/
def ContainsKSunflower {n : ℕ} (k : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  ∃ (T : Finset (Finset (Fin n))), T ⊆ F ∧ T.card = k ∧
    ∀ ⦃a⦄, a ∈ T → ∀ ⦃b⦄, b ∈ T → a ≠ b → ∀ ⦃c⦄, c ∈ T → ∀ ⦃d⦄, d ∈ T → c ≠ d → a ∩ b = c ∩ d

/-- `F` contains no `k`-sunflower. -/
def IsKSunflowerFree {n : ℕ} (k : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  ¬ ContainsKSunflower (n := n) k F

/-- The Erdős–Szemerédi weak sunflower conjecture for `k ≥ 4`: every fixed
`k ≥ 4` admits a base `c < 2`, depending only on `k`, such that every
`k`-sunflower-free family of arbitrary subsets of an `n`-element universe has
at most `c ^ n` members for all sufficiently large `n`. The bound is eventual
because for `2 ^ n < k` the full powerset is `k`-sunflower-free. The case
`k = 3` was proved by Naslund–Sawin and is omitted. -/
def conjecture : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    ∃ c : ℝ, 0 < c ∧ c < 2 ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ F : Finset (Finset (Fin n)),
          IsKSunflowerFree k F →
            (F.card : ℝ) ≤ c ^ n

/--
Resolved true: Proved: Bucić, He and Lee (arXiv:2610.26686, 2026, Theorem 1) show that for every
k >= 3 and n >= 1 a family of subsets of [n] with no k-sunflower has at most 3(2 - 1/(16k^3))^n
members, which gives the formalized bound c^n with c < 2 for each k >= 4 and all large n.
erdosproblems.com/857 (checked 2026-10-22) records this bound as known. The paper states that
the proof of its vector-sunflower bound (Theorem 2) was found by ChatGPT 6 Astra Pro and
verified by the authors. Source: Matija Bucić, Fankang He and Hyunwoo Lee, Proof of the
Erdős-Szemerédi sunflower conjecture, arXiv:2610.26686 (2026), https://arxiv.org/abs/2610.26686;
T. F. Bloom, Erdős Problem #857, erdosproblems.com, https://www.erdosproblems.com/857. Moved
from `OpenConjectures/Combinatorics/ErdosProblem857WeakSunflower`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosProblem857WeakSunflowerWanted
