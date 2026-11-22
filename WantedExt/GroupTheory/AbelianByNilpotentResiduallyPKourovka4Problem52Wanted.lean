/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Virtually residually-p abelian-by-nilpotent groups (Kourovka Notebook Problem 4.52)

Kourovka Notebook, Archive of Solved Problems, Problem 4.52 (V. N. Remeslennikov): let `G` be a
finitely generated torsion-free group that is an extension of an abelian group by a nilpotent group.
Then is `G` almost a residually finite `p`-group for almost all primes `p`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Nilpotent
public import WantedExt.GroupTheory.KourovkaNotebookShared

@[expose] public section

namespace MathlibExt.GroupTheory.AbelianByNilpotentResiduallyPKourovka4Problem52Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.52 (V. N.
Remeslennikov). UnsolvedMath record UM-00700259 (`KOU-4.52`), dataset ulamai/UnsolvedMath v1.8.0.

An extension of an abelian group by a nilpotent group has a normal abelian subgroup `A` with `G / A`
nilpotent. "Almost" means a subgroup of finite index, and "almost all primes" all but finitely many.
A residually finite `p`-group has, for each non-trivial element, a normal subgroup of `p`-power
index avoiding it. Torsion-free is written `∀ g, g ≠ 1 → ¬ IsOfFinOrder g`.
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared (IsResiduallyFiniteP)

/-- Kourovka 4.52 (V. N. Remeslennikov): every finitely generated torsion-free group `G` that is an
extension of an abelian group by a nilpotent group (a normal abelian subgroup `A` with `G / A`
nilpotent) is almost (virtually) a residually finite `p`-group for almost all primes `p`: only
finitely many primes `p` admit no residually finite `p`-subgroup of finite index. -/
def abelianByNilpotentVirtuallyResiduallyP : Prop :=
  ∀ (G : Type) [Group G], Group.FG G → (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) →
    (∃ (A : Subgroup G) (_ : A.Normal), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      Group.IsNilpotent (G ⧸ A)) →
    {p : ℕ | p.Prime ∧
      ¬ ∃ H : Subgroup G, H.FiniteIndex ∧ IsResiduallyFiniteP p H}.Finite

/--
Resolved true: Noskov and Segal prove that a finitely generated torsion-free abelian-by-nilpotent
group has, for all but finitely many primes `p`, a subgroup of finite index that is residually a
finite `p`-group; the Kourovka Archive answers 4.52 "Yes, it is" (DOI of Segal:
10.1016/0021-8693(74)90147-1). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 4.52 (V. N. Remeslennikov); resolution: G. A. Noskov, Almost approximability of
finitely generated AB-groups without torsion with finite p-groups, Algebra and Logic 13 (1974),
388-393; D. Segal, A residual property of finitely generated abelian-by-nilpotent groups, J. Algebra
32 (1974), 389-399, Kourovka Archive of Solved Problems, Problem 4.52: Yes, it is,
https://doi.org/10.1007/BF01462950.
-/
public theorem_wanted abelianByNilpotentVirtuallyResiduallyP_holds :
    abelianByNilpotentVirtuallyResiduallyP

end MathlibExt.GroupTheory.AbelianByNilpotentResiduallyPKourovka4Problem52Wanted
