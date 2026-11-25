/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tomaszewski's conjecture on randomly signed sums (O'Donnell, Problem 2)

R. O'Donnell, Open Problems in Analysis of Boolean Functions, Problem 2 (Tomaszewski's Conjecture):
let `a ∈ ℝⁿ` have `‖a‖₂ = 1`. Then `Pr_{x ∼ {-1,1}ⁿ}[|⟨a, x⟩| ≤ 1] ≥ 1/2`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace MathlibExt.Combinatorics.TomaszewskiRandomSignedSumAMR127Problem0002Wanted

/-!
Source: R. O'Donnell, Open Problems in Analysis of Boolean Functions (2012), arXiv:1204.6447,
Problem 2 (Tomaszewski's Conjecture). UnsolvedMath record UM-00800433 (`AMR-127-0002`), dataset
ulamai/UnsolvedMath v1.8.0.

The uniform probability on `{-1, 1}ⁿ` is counting measure divided by `2ⁿ`, so the target says that
at least half of the `2ⁿ` sign vectors satisfy `|⟨a, x⟩| ≤ 1` (non-strict, as in the source and in
Keller–Klein; the bound is attained by `a = (1/√2, 1/√2)`). For `n = 0` the hypothesis `∑ aᵢ² = 1`
fails, so the statement is about `n ≥ 1`.
-/

/-- **Tomaszewski's conjecture.** The statement that for every natural number $n$ and every
vector $a = (a_1, \dots, a_n) \in \mathbb{R}^n$ with $a_1^2 + \dots + a_n^2 = 1$, at least half of
the $2^n$ sign vectors $x \in \{-1, 1\}^n$ satisfy $|a_1 x_1 + \dots + a_n x_n| \le 1$.

Source: O'Donnell, Open Problems in Analysis of Boolean Functions, Problem 2. A sign vector is a
map `x : Fin n → Bool`, with `true` read as `1` and `false` as `-1`. -/
def tomaszewskiConjecture : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ), ∑ i, a i ^ 2 = 1 →
    (2 : ℝ) ^ n ≤ 2 * ((Finset.univ.filter fun x : Fin n → Bool =>
      |∑ i, a i * (if x i then (1 : ℝ) else -1)| ≤ 1).card : ℝ)

/-- **Tomaszewski's conjecture holds.** For every natural number $n$ and every vector
$a = (a_1, \dots, a_n) \in \mathbb{R}^n$ with $a_1^2 + \dots + a_n^2 = 1$, at least half of the
$2^n$ sign vectors $x \in \{-1, 1\}^n$ satisfy $|a_1 x_1 + \dots + a_n x_n| \le 1$; equivalently,
for a uniformly random sign vector $x$ this inequality holds with probability at least $1/2$.

Source: R. O'Donnell, Open Problems in Analysis of Boolean Functions (2012), arXiv:1204.6447,
Problem 2 (Tomaszewski's Conjecture); resolution: N. Keller and O. Klein, Proof of Tomaszewski's
conjecture on randomly signed sums, Adv. Math. 407 (2022), 108558, arXiv:2006.16834, main theorem
(Section 1): for X = ∑ aᵢxᵢ with ∑ aᵢ² = 1 and independent uniform xᵢ ∈ {-1, 1}, Pr[|X| ≤ 1] ≥ 1/2,
https://arxiv.org/abs/2006.16834.
-/
public theorem_wanted tomaszewskiConjecture_holds : tomaszewskiConjecture

end MathlibExt.Combinatorics.TomaszewskiRandomSignedSumAMR127Problem0002Wanted
