/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Orders of abelian subgroups of finite p-groups (Kourovka Notebook Problem 20.76)

Kourovka Notebook, Problem 20.76 (L. Pyber), marked solved in the 21st issue: let `G` be a finite
`p`-group and assume that all abelian normal subgroups of `G` have order at most `p^k`. Is it true
that every abelian subgroup of `G` has order at most `p^(2k)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.AbelianNormalOrderPGroupKourovka20Problem76Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.76 (L. Pyber). UnsolvedMath record
UM-00701734 (`KOU-20.76`), dataset ulamai/UnsolvedMath v1.8.0.

Stated for all primes `p` and all `k`; abelian subgroups are written by pairwise commutation.
-/

/-- Kourovka 20.76 (L. Pyber): for every prime `p` and every `k`, if all abelian normal
subgroups of a finite `p`-group `G` have order at most `p^k`, then every abelian subgroup of `G`
has order at most `p^(2k)`. -/
def abelianSubgroupOrderLeSquareNormal : Prop :=
  ∀ (p k : ℕ) (G : Type) [Group G] [Finite G], p.Prime → IsPGroup p G →
    (∀ A : Subgroup G, A.Normal → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → Nat.card A ≤ p ^ k) →
    ∀ B : Subgroup G, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → Nat.card B ≤ p ^ (2 * k)

/--
Resolved false: Muliarchyk (Theorem 1.1) constructs a finite `2`-group of order `2^(144e+1)`, `e =
256363762`, whose abelian normal subgroups have order at most `2^(42e)` while it has an elementary
abelian subgroup of order `2^(85e) > 2^(84e)`; the 21st issue of the Kourovka Notebook marks 20.76
solved ("No, it is not"). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.76 (L. Pyber);
resolution: K. Muliarchyk, Abelian subgroups of finite 2-groups: counterexamples to Problems 20.75
and 20.76, preprint (2026), Kourovka Notebook site, Theorem 1.1: for e = 256363762 an explicitly
specified finite 2-group of order 2^(144e+1) whose abelian normal subgroups have order at most
2^(42e), with an elementary abelian subgroup of order 2^(85e) (p = 2, k = 42e); Kourovka Notebook
(21st issue), Problem 20.76: No, it is not,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka_20_75-20_76_solution.pdf.
-/
public theorem_wanted abelianSubgroupOrderLeSquareNormal_refuted :
    ¬ abelianSubgroupOrderLeSquareNormal

end MathlibExt.GroupTheory.AbelianNormalOrderPGroupKourovka20Problem76Wanted
