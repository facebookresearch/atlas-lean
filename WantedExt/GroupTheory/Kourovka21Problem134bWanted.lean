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

/-- **Same power-equation type.** Two groups $G$ and $H$ have the same power-equation type when,
for every positive integer $n$, the equation $x^n = 1$ has the same number of solutions in $G$ as
in $H$. An infinite set of solutions is counted as $0$, so the notion is meant for finite
groups. -/
def SamePowerEquationType (G H : Type*) [Group G] [Group H] : Prop :=
  ∀ n : ℕ, 0 < n →
    Nat.card {x : G // x ^ n = 1} = Nat.card {x : H // x ^ n = 1}

/-- **Almost simple group.** A group $G$ is almost simple when there is a nonabelian finite simple
group $S$ such that $G$ is isomorphic to a subgroup $A$ of the automorphism group
$\mathrm{Aut}(S)$ that contains the inner automorphism group $\mathrm{Inn}(S)$. -/
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

/-- **Characterization of almost simple groups by power-equation type (Kourovka 21.134(b)).**
The conjecture that for all finite groups $G$ and $H$, if $G$ is almost simple and $G$ and $H$
have the same power-equation type, then $G$ is isomorphic to $H$. -/
def conjecture : Prop :=
  ∀ (G H : Type*) [Group G] [Finite G] [Group H] [Finite H],
    IsAlmostSimple G → SamePowerEquationType G H → Nonempty (G ≃* H)

/--
**Power-equation type does not characterize almost simple groups.** There exist finite
groups $G$ and $H$ such that $G$ is almost simple, $G$ and $H$ have the same power-equation type,
and $G$ is not isomorphic to $H$. That is, the conjecture of Kourovka Problem 21.134(b) is false.

Kourovka Notebook v46 records that J. G. Thompson had already given a negative answer to part (b).

Source: Yu Li and Wujie Shi, A Note on Thompson Problem, arXiv:2303.09460v1 (2023);
published in Ricerche di Matematica 74(1) (2025), 559-563, https://arxiv.org/abs/2303.09460v1;
The Kourovka Notebook: Unsolved Problems in Group Theory, 21st edition, Problem 21.134,
arXiv:1401.0300v46, https://arxiv.org/abs/1401.0300v46. Moved from
`OpenConjectures/GroupTheory/Kourovka21Problem134b`.
-/
theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.GroupTheory.Kourovka21Problem134bWanted
