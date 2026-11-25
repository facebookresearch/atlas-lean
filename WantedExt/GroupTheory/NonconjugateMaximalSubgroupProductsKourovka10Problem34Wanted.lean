/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Groups that are products of non-conjugate maximal subgroups (Kourovka Notebook Problem 10.34)

Kourovka Notebook, Problem 10.34 (V. S. Monakhov), marked solved: does there exist a non-soluble
finite group which coincides with the product of any two of its non-conjugate maximal subgroups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.NonconjugateMaximalSubgroupProductsKourovka10Problem34Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 10.34 (V. S. Monakhov). UnsolvedMath record
UM-00700649 (`KOU-10.34`), dataset ulamai/UnsolvedMath v1.8.0.

Maximal subgroups are coatoms of the subgroup lattice; `N` is conjugate to `M` if `N = g M g⁻¹` for
some `g`; the product is the set product `MN`. The condition is not vacuous: a finite group is not
the union of the conjugates of a proper subgroup, so a non-cyclic finite group has non-conjugate
maximal subgroups.
-/

open scoped Pointwise

/-- **Non-soluble products of non-conjugate maximal subgroups (Kourovka 10.34, Monakhov).** The
statement that there is a finite group $G$ that is not soluble such that $G = MN$ for every two
maximal subgroups $M$ and $N$ of $G$ that are not conjugate in $G$. Here $MN$ is the set of
products $mn$ with $m \in M$ and $n \in N$. -/
def nonsolubleProductOfNonconjugateMaximals : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G), ¬ Group.IsSolvable G ∧
    ∀ M N : Subgroup G, IsCoatom M → IsCoatom N →
      (∀ g : G, N ≠ M.map (MulAut.conj g).toMonoidHom) → (M : Set G) * (N : Set G) = Set.univ

/--
**Finite groups that are the product of every two non-conjugate maximal subgroups are soluble.**
There is no finite group $G$ that is not soluble such that $G = MN$ for every two maximal
subgroups $M$ and $N$ of $G$ that are not conjugate in $G$; here $MN$ is the set of products $mn$
with $m \in M$ and $n \in N$. This answers Kourovka Problem 10.34 in the negative.

Sater (arXiv:2608.02970) and Li and Yang (arXiv:2608.19478) prove that a finite group with this
property is soluble (the almost simple case is due to Tikhonenko and Tyutyanov, 2010). The
Kourovka Notebook (21st issue) marks 10.34 solved, "No, there are no such groups".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 10.34 (V. S. Monakhov); resolution: R.
Sater, Finite groups that are the product of every pair of non-conjugate maximal subgroups are
soluble, arXiv:2608.02970 (2026); J. Li and Y. Yang, Products of nonconjugate maximal subgroups,
arXiv:2608.19478 (2026), main theorems: a finite group with MN = G for all non-conjugate maximal
subgroups M, N is soluble; the Kourovka Notebook (21st issue) marks 10.34 solved,
https://arxiv.org/abs/2608.19478.
-/
public theorem_wanted nonsolubleProductOfNonconjugateMaximals_refuted :
    ¬ nonsolubleProductOfNonconjugateMaximals

end MathlibExt.GroupTheory.NonconjugateMaximalSubgroupProductsKourovka10Problem34Wanted
