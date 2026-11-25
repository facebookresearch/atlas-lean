/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# σ-nilpotent supplements to maximal subgroups of Sylow subgroups (Kourovka Notebook Problem 19.88)

Kourovka Notebook, Archive of Solved Problems, Problem 19.88 (A. N. Skiba): suppose that for every
Sylow subgroup `P` of a finite group `G` and every maximal subgroup `V` of `P` there is a
`σ`-nilpotent subgroup `T` such that `V T = G`. Is it true that then `G` is `σ`-nilpotent?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.KourovkaNotebookShared

@[expose] public section

namespace MathlibExt.GroupTheory.SylowMaximalSigmaNilpotentSupplementKourovka19Problem88Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.88 (A. N.
Skiba). UnsolvedMath record UM-00701636 (`KOU-19.88`), dataset ulamai/UnsolvedMath v1.8.0.

A partition `σ` of the primes is a family `σ : I → Set ℕ` of nonempty, pairwise disjoint sets of
primes covering all primes; a positive integer (a finite group) is `σ`-primary when its prime
divisors (those of its order) lie in one block `σᵢ`. A finite group is `σ`-nilpotent when it is a
direct product of `σ`-primary groups (an internal direct product of finitely many normal `σ`-primary
subgroups). Maximal subgroups of `P` are the subgroups covered by `P` (`V ⋖ P`); `V T = G` means
every element is `v t`. Every partition `σ` is quantified. The `σ`-definitions are the shared ones
in `WantedExt/GroupTheory/KourovkaNotebookShared.lean`.
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared

/-- **Kourovka Problem 19.88 (statement).** The statement that for every partition $\sigma$ of the
set of all primes and every finite group $G$: if for every prime $p$, every Sylow $p$-subgroup $P$
of $G$ and every maximal subgroup $V$ of $P$ there is a $\sigma$-nilpotent subgroup $T$ of $G$ with
$VT = G$, that is, every element of $G$ is a product $vt$ with $v \in V$ and $t \in T$, then $G$ is
$\sigma$-nilpotent. Here a partition of the primes is a family of nonempty, pairwise disjoint sets
of primes whose union is the set of all primes, and a group is $\sigma$-nilpotent when it is the
internal direct product of finitely many normal subgroups, each of whose order has all its prime
divisors in a single block of $\sigma$. -/
def sylowMaximalSigmaNilpotentSupplement : Prop :=
  ∀ (I : Type) (σ : I → Set ℕ), IsPrimePartition σ → ∀ (G : Type) [Group G] [Finite G],
    (∀ p : ℕ, p.Prime → ∀ (P : Sylow p G) (V : Subgroup G), V ⋖ (P : Subgroup G) →
      ∃ T : Subgroup G, IsSigmaNilpotent σ T ∧ ∀ g : G, ∃ v ∈ V, ∃ t ∈ T, v * t = g) →
    IsSigmaNilpotent σ G

/--
**σ-nilpotent supplements to the maximal subgroups of Sylow subgroups (Kourovka 19.88).** Let
$\sigma$ be a partition of the set of all primes and let $G$ be a finite group. If for every prime
$p$, every Sylow $p$-subgroup $P$ of $G$ and every maximal subgroup $V$ of $P$ there is a
$\sigma$-nilpotent subgroup $T$ of $G$ with $VT = G$, that is, every element of $G$ is a product
$vt$ with $v \in V$ and $t \in T$, then $G$ is $\sigma$-nilpotent. Here a partition of the primes is
a family of nonempty, pairwise disjoint sets of primes whose union is the set of all primes, and a
group is $\sigma$-nilpotent when it is the internal direct product of finitely many normal
subgroups, each of whose order has all its prime divisors in a single block of $\sigma$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.88 (A. N.
Skiba); resolution: A.-M. Liu, W. Guo, I. N. Safonova and A. N. Skiba, G-covering subgroup systems
for some classes of σ-soluble groups, J. Algebra 585 (2021), 280-293; another solution using CFSG by
S. F. Kamornikov and V. N. Tyutyanov, Trudy Inst. Mat. Mekh. UrO RAN 27 (2021), no. 1, 98-102,
abstract: a set of subgroups of G containing a supplement to each maximal subgroup of every Sylow
subgroup of G is a G-covering subgroup system for the classes of σ-soluble and of σ-nilpotent
groups, which answers 19.87 and 19.88; Kourovka Archive, Problem 19.88: Yes, it is true,
https://doi.org/10.1016/j.jalgebra.2021.06.010.
-/
public theorem_wanted sylowMaximalSigmaNilpotentSupplement_holds :
    sylowMaximalSigmaNilpotentSupplement

end MathlibExt.GroupTheory.SylowMaximalSigmaNilpotentSupplementKourovka19Problem88Wanted
