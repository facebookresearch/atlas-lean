/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Maximal subgroups of infinite index in SLₙ(ℤ) (Kourovka Notebook Problem 2.55)

Kourovka Notebook, Archive of Solved Problems, Problem 2.55 (V. P. Platonov): (b) does `SLₙ(ℤ)`, `n
≥ 2`, have maximal subgroups of infinite index?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Order.Atoms

@[expose] public section

namespace MathlibExt.GroupTheory.InfiniteIndexMaximalSubgroupSLZKourovka2Problem55Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.55 (V. P.
Platonov). UnsolvedMath record UM-00700127 (`KOU-2.55`), dataset ulamai/UnsolvedMath v1.8.0.

Maximal subgroups are coatoms of the subgroup lattice; infinite index is `Subgroup.index = 0`. The
Notebook records only part (b) of Problem 2.55.
-/

/-- Kourovka 2.55(b) (V. P. Platonov): for every `n ≥ 2`, `SLₙ(ℤ)` has a maximal subgroup of
infinite index (`Subgroup.index` is `0` exactly for infinite index). -/
def specialLinearIntegersHasInfiniteIndexMaximalSubgroup : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ M : Subgroup (Matrix.SpecialLinearGroup (Fin n) ℤ), IsCoatom M ∧ M.index = 0

/--
Resolved true: the Kourovka Archive answers 2.55(b) "Yes, it does", citing Margulis and Soifer
(1977); their theorem (as stated in the Introduction of arXiv:2609.25125) says that a finitely
generated linear group is either virtually solvable or has a maximal subgroup of infinite index, and
`SLₙ(ℤ)`, `n ≥ 2`, is finitely generated and not virtually solvable. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.55 (V. P. Platonov); resolution: G.
A. Margulis and G. A. Soifer, Soviet Math. Dokl. 18 (1977), 847-851, Kourovka Archive, Problem 2.55:
Yes, it does (Margulis-Soifer); the Margulis-Soifer theorem as stated in the Introduction of
arXiv:2609.25125: a finitely generated linear group is either virtually solvable or contains a
maximal subgroup of infinite index, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted specialLinearIntegersHasInfiniteIndexMaximalSubgroup_holds :
    specialLinearIntegersHasInfiniteIndexMaximalSubgroup

end MathlibExt.GroupTheory.InfiniteIndexMaximalSubgroupSLZKourovka2Problem55Wanted
