/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linear groups without identities contain free subgroups (Kourovka Notebook Problem 1.88)

Kourovka Notebook, Archive of Solved Problems, Problem 1.88 (A. L. Shmel'kin): is it true that if a
matrix group over a field of characteristic `0` does not satisfy any non-trivial identity relation,
then it contains a non-abelian free subgroup?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.LinearGroupWithoutLawFreeSubgroupKourovka1Problem88Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.88 (A. L.
Shmel'kin). UnsolvedMath record UM-00700077 (`KOU-1.88`), dataset ulamai/UnsolvedMath v1.8.0.

A matrix group is a subgroup `G ≤ GLₙ(K)`; fields are taken in `Type`. "Does not satisfy any
non-trivial identity" means that every word `w ≠ 1` in `x₀, x₁, …` takes a value `≠ 1` on some
elements of `G`. A non-abelian free subgroup is an injective homomorphism from the free group of
rank `2`. Finitely generated linear groups over arbitrary fields are covered by
`TitsAlternativeWanted`; here `G` is arbitrary and the characteristic is `0`.
-/

/-- Kourovka 1.88 (A. L. Shmel'kin): if a group `G ≤ GLₙ(K)` of matrices over a field `K` of
characteristic `0` satisfies no nontrivial identity (every word `w ≠ 1` in `x₀, x₁, …` takes a
value `≠ 1` on some elements of `G`), then `G` contains a non-abelian free subgroup. -/
def charZeroLinearGroupWithoutLawHasFreeSubgroup : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (G : Subgroup (GL (Fin n) K)),
    (∀ w : FreeGroup ℕ, w ≠ 1 → ∃ f : ℕ → G, FreeGroup.lift f w ≠ 1) →
    ∃ f : FreeGroup (Fin 2) →* G, Function.Injective f

/--
Resolved true: the Kourovka Archive answers "Yes, it is", citing Tits (1972): in characteristic `0`
every subgroup of `GLₙ(K)` contains a non-abelian free subgroup or has a solvable subgroup of finite
index, and a group with a solvable subgroup of finite index satisfies a non-trivial identity.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.88 (A. L.
Shmel'kin); resolution: J. Tits, Free subgroups in linear groups, J. Algebra 20 (1972), 250-270, the
Tits alternative in characteristic 0 (a subgroup of GL_n(K), char K = 0, contains a non-abelian free
subgroup or has a solvable subgroup of finite index); Kourovka Archive, Problem 1.88.
-/
public theorem_wanted charZeroLinearGroupWithoutLawHasFreeSubgroup_holds :
    charZeroLinearGroupWithoutLawHasFreeSubgroup

end MathlibExt.GroupTheory.LinearGroupWithoutLawFreeSubgroupKourovka1Problem88Wanted
