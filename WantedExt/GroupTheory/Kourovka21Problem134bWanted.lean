/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.SetTheory.Cardinal.NatCard
import Batteries.Util.ProofWanted

namespace MathlibExt.GroupTheory.Kourovka21Problem134bWanted

universe u

/-- Two finite groups have the same power-equation type when `x ^ n = 1` has the same
number of solutions in both groups for every positive `n`. -/
def SamePowerEquationType (G H : Type*) [Group G] [Group H] : Prop :=
  ∀ n : ℕ, 0 < n →
    Nat.card {x : G // x ^ n = 1} = Nat.card {x : H // x ^ n = 1}

/-- A group is almost simple when it is isomorphic to a subgroup between the inner and
full automorphism groups of a nonabelian finite simple group. -/
def IsAlmostSimple (G : Type u) [Group G] : Prop :=
  ∃ (S : Type u) (groupStructure : Group S) (finiteS : Finite S)
      (simpleS : IsSimpleGroup S),
    letI := groupStructure
    letI := finiteS
    letI := simpleS
    ¬IsMulCommutative S ∧
      ∃ A : Subgroup (MulAut S),
        MonoidHom.range (MulAut.conj : S →* MulAut S) ≤ A ∧
          Nonempty (G ≃* A)

/-- A finite group having the same power-equation type as an almost simple group is
isomorphic to that group. -/
def conjecture : Prop :=
  ∀ (G H : Type*) [Group G] [Finite G] [Group H] [Finite H],
    IsAlmostSimple G → SamePowerEquationType G H → Nonempty (G ≃* H)

/--
Resolved false: Kourovka Notebook v46 records that J. G. Thompson had already given a negative
answer to part (b), so power-equation type does not characterize every almost simple group up to
isomorphism. Source: Yu Li and Wujie Shi, A Note on Thompson Problem, arXiv:2303.09460v1 (2023);
published in Ricerche di Matematica 74(1) (2025), 559-563, https://arxiv.org/abs/2303.09460v1;
The Kourovka Notebook: Unsolved Problems in Group Theory, 21st edition, Problem 21.134,
arXiv:1401.0300v46, https://arxiv.org/abs/1401.0300v46. Moved from
`OpenConjectures/GroupTheory/Kourovka21Problem134b`.
-/
theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.GroupTheory.Kourovka21Problem134bWanted
