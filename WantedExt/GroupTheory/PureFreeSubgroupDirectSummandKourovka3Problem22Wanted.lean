/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Locally pure-free abelian groups and summands isomorphic to ℤ (Kourovka Notebook Problem 3.22)

Kourovka Notebook, Archive of Solved Problems, Problem 3.22 (V. I. Kuz'minov): let `ξ` be a
projective system (over a directed set) of finitely generated free abelian groups. If all the
projections are epimorphisms and all the groups are non-zero, does it follow that `lim ξ ≠ 0`?
Equivalently, suppose every finite set of elements of an abelian group `A` is contained in a pure
finitely-generated free subgroup of `A`. Then does it follow that `A` has a direct summand
isomorphic to the infinite cyclic group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import WantedExt.GroupTheory.PureSubgroupShared

@[expose] public section

namespace MathlibExt.GroupTheory.PureFreeSubgroupDirectSummandKourovka3Problem22Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.22 (V. I.
Kuz'minov). UnsolvedMath record UM-00700176 (`KOU-3.22`), dataset ulamai/UnsolvedMath v1.8.0.

The second (abelian group) form, which the problem gives as equivalent, is stated. `A` is required
to be non-zero, matching the non-zero groups of the first form (the zero group satisfies the
hypothesis and has no summand `ℤ`). Pure: `nA ∩ B = nB` (shared `IsPureSubgroup`); a direct summand
is a member `C` of a complementary pair `C, D` of subgroups.
-/

open MathlibExt.GroupTheory.PureSubgroupShared

/-- Kourovka 3.22 (V. I. Kuz'minov), second form: every non-zero abelian group `A` in which every
finite subset lies in a pure finitely generated free subgroup has a direct summand isomorphic to
`ℤ`. -/
def locallyPureFreeHasIntSummand : Prop :=
  ∀ (A : Type) [AddCommGroup A], Nontrivial A →
    (∀ S : Finset A, ∃ B : AddSubgroup A, (S : Set A) ⊆ B ∧ IsPureSubgroup B ∧ B.FG ∧
      Module.Free ℤ B) →
    ∃ C D : AddSubgroup A, IsCompl C D ∧ Nonempty (C ≃+ ℤ)

/--
Resolved false: the Kourovka Archive marks 3.22 solved, recording Palyutin's counterexample under CH
(Siberian Math. J. 19 (1978)) and Corson's ZFC example `A = ℤ^(ℵ₁) / N`, `N` the elements of
countable support: every finite subset of `A` lies in a pure finitely generated free subgroup, yet
`A` has no direct summand isomorphic to `ℤ`. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 3.22 (V. I. Kuz'minov); resolution: S. Corson, letter of 26
August 2024 (Kourovka Archive); E. A. Palyutin, Siberian Math. J. 19 (1978), 1415-1417 (under the
continuum hypothesis), Kourovka Archive, Problem 3.22 (marked solved): not always; in ZFC, A =
ℤ^(ℵ₁)/N with N the elements of countable support has every countable subgroup free, so each finite
subset lies in a pure finitely generated free subgroup, but A has no direct summand isomorphic to ℤ,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted locallyPureFreeHasIntSummand_refuted : ¬ locallyPureFreeHasIntSummand

end MathlibExt.GroupTheory.PureFreeSubgroupDirectSummandKourovka3Problem22Wanted
