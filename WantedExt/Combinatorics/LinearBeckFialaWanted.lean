/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linear Beck-Fiala systems

`AIM-COMBINATORICS-0044` (AIM Hereditary discrepancy and
factorization norms, item 1.7): for a `t`-sparse matrix (rows and
columns) in which every pair of rows intersects in at most one
element, the discrepancy bound improves from `O(√(t log t))` to
`O(√t)`, with one absolute constant.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.LinearBeckFialaWanted

open scoped BigOperators

/-- Linear Beck–Fiala systems
(AIM-COMBINATORICS-0044__20000919; AIM Hereditary discrepancy, item 1.7):
for a `t`-sparse matrix in which every pair of rows intersect in at most
one element, the discrepancy bound improves from `O(√(t log t))` to
`O(√t)`: one absolute constant `C` bounds every row sum by `C * √t`. -/
def conjecture : Prop :=
  ∃ C : ℝ, 0 < C ∧
  ∀ (n m t : ℕ), 0 < t →
    ∀ incidence : Fin n → Finset (Fin m),
      (∀ i, (incidence i).card ≤ t) →
      (∀ j, (Finset.univ.filter (fun i => j ∈ incidence i)).card ≤ t) →
      (∀ i₁ i₂, i₁ ≠ i₂ → ((incidence i₁ ∩ incidence i₂).card) ≤ 1) →
      ∃ ε : Fin m → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
        ∀ i, |∑ j ∈ incidence i, ε j| ≤ C * Real.sqrt t

/--
Resolved true: Resolved. Guo, Fang and Lu prove that every 0/1 matrix with at most t nonzero
entries in each column has discrepancy less than 3 sqrt(2 pi t) (Vector balancing via
directional total variation, arXiv:2609.11189, Corollary 1.2 of their Komlós bound, Theorem 1.1;
Karingula and Lovett give an elementary proof of the Komlós bound with constant 36,
arXiv:2609.20979). Linear systems with t-sparse rows and columns are a special case, so the
source's O(sqrt t) holds. The statement was restated from the constant 4 to one absolute
constant, as the source asks for O(sqrt t). Source: Shengtao Guo, Ethan X. Fang and Junwei Lu,
Vector balancing via directional total variation, arXiv:2609.11189 (2026),
https://arxiv.org/abs/2609.11189. Moved from `OpenConjectures/Combinatorics/LinearBeckFiala`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.LinearBeckFialaWanted
