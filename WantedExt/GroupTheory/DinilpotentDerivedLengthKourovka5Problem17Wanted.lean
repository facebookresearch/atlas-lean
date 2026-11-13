/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Derived length of products of two nilpotent groups (Kourovka Notebook Problem 5.17)

Kourovka Notebook, Archive of Solved Problems, Problem 5.17 (O. H. Kegel): if the finite group G =
AB is the product of subgroups A and B nilpotent of classes α and β, then G is soluble; is G^(α+β) =
1?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.DinilpotentDerivedLengthKourovka5Problem17Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.17 (O. H.
Kegel). UnsolvedMath record UM-00700301 (`KOU-5.17`), dataset ulamai/UnsolvedMath v1.8.0.

Nilpotent of class at most `α`: `A.lowerCentralSeries α = ⊥` (the lower central series of `A` starts
with `A` at index `0`). Classes "at most" and "exactly" give equivalent targets: a counterexample
with classes at most `α`, `β` is one with the exact classes `α' ≤ α`, `β' ≤ β`, since `G^(α'+β') ≥
G^(α+β)`. `G^(k)` is `derivedSeries G k`; Ito's theorem is the case `α = β = 1`.
-/

open scoped Pointwise

/-- Kourovka 5.17 (O. H. Kegel): if a finite group `G = AB` is the product of subgroups `A` and `B`
nilpotent of classes at most `α` and `β` (`γ_(α+1)(A) = γ_(β+1)(B) = 1`), then
`G^(α + β) = 1`. -/
def dinilpotentDerivedLengthBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A B : Subgroup G) (α β : ℕ),
    (A : Set G) * (B : Set G) = Set.univ → A.lowerCentralSeries α = ⊥ →
      B.lowerCentralSeries β = ⊥ → derivedSeries G (α + β) = ⊥

/--
Resolved false: the Kourovka Archive answers 5.17 "Not always", citing Cossey and Stonehewer, On the
derived length of finite dinilpotent groups (Bull. London Math. Soc. 30 (1998), 247-250): some
finite `G = AB` with `A`, `B` nilpotent of classes `α`, `β` has `G^(α + β) ≠ 1`. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.17 (O. H. Kegel);
resolution: J. Cossey and S. E. Stonehewer, On the derived length of finite dinilpotent groups,
Bull. London Math. Soc. 30 (1998), 247-250, Kourovka Archive, Problem 5.17: Not always
(Cossey-Stonehewer), https://doi.org/10.1112/S0024609397004050.
-/
public theorem_wanted dinilpotentDerivedLengthBound_refuted : ¬ dinilpotentDerivedLengthBound

end MathlibExt.GroupTheory.DinilpotentDerivedLengthKourovka5Problem17Wanted
