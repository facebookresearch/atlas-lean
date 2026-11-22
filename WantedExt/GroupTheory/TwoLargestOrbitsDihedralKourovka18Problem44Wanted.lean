/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Two largest orbits and the dihedral group of order eight (Kourovka Notebook Problem 18.44)

Kourovka Notebook, Problem 18.44 (T. M. Keller), marked solved in the 21st issue: let `G` be a
finite non-abelian group and `V` a finite faithful irreducible `G`-module. Suppose that `M = |G/G'|`
is the largest orbit size of `G` on `V`, and among orbits of `G` on `V` there are exactly two orbits
of size `M`. Does this imply that `G` is dihedral of order `8` and `|V| = 9`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

@[expose] public section

namespace MathlibExt.GroupTheory.TwoLargestOrbitsDihedralKourovka18Problem44Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.44 (T. M. Keller). UnsolvedMath record
UM-00701473 (`KOU-18.44`), dataset ulamai/UnsolvedMath v1.8.0.

A finite `G`-module is a finite abelian group with a `DistribMulAction` of `G`; it is irreducible
when it is nonzero and has no `G`-invariant subgroups other than `0` and `V` (a finite irreducible
module is elementary abelian, so these are its subspaces over `𝔽ₚ`). `|G/G'|` is the order of
`Abelianization G`; the largest orbit size is `M` when every orbit has size at most `M` and some has
size `M`, the latter implied by the two orbits of size `M`.
-/

/-- Kourovka 18.44 (T. M. Keller): let `G` be a finite non-abelian group and `V` a finite faithful
irreducible `G`-module (a nonzero finite abelian group on which `G` acts faithfully by automorphisms
with no invariant subgroups other than `0` and `V`). If `M = |G / G'|` is the largest orbit size of
`G` on `V` and exactly two orbits have size `M`, then `G` is dihedral of order `8` and `|V| = 9`. -/
def twoLargestOrbitsImpliesDihedralEight : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Finite V]
    [DistribMulAction G V], (∃ a b : G, a * b ≠ b * a) → FaithfulSMul G V → Nontrivial V →
    (∀ W : AddSubgroup V, (∀ g : G, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∀ v : V, Nat.card (MulAction.orbit G v) ≤ Nat.card (Abelianization G)) →
    {O : MulAction.orbitRel.Quotient G V |
      Nat.card O.orbit = Nat.card (Abelianization G)}.ncard = 2 →
    Nonempty (G ≃* DihedralGroup 4) ∧ Nat.card V = 9

/--
Resolved true: Jones-Keller (2020), Theorem 3.1, accepted in the Kourovka Notebook (21st issue) as
answering 18.44: under these hypotheses `G` is dihedral of order `8` and `V = V(2, 3)`, so `|V| =
9`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.44 (T. M. Keller); resolution: N. A.
Jones and T. M. Keller, Orbit sizes and the dihedral group of order eight, Ann. Mat. Pura Appl. 199
(2020), 2323-2340, Theorem 3.1: G finite nonabelian, V finite faithful irreducible G-module, M =
|G/G'| the largest orbit size with exactly two orbits of size M; then G is dihedral of order 8 and V
= V(2, 3), https://doi.org/10.1007/s10231-020-00970-x.
-/
public theorem_wanted twoLargestOrbitsImpliesDihedralEight_holds :
    twoLargestOrbitsImpliesDihedralEight

end MathlibExt.GroupTheory.TwoLargestOrbitsDihedralKourovka18Problem44Wanted
