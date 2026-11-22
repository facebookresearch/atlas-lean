/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rationality of Sylow `2`-subgroups of symmetric groups (Kourovka Notebook Problem 15.25)

Kourovka Notebook, Archive of Solved Problems, Problem 15.25 (Ya. G. Berkovich): a finite group is
rational if every irreducible character takes only rational values. Are the Sylow `2`-subgroups of
the symmetric groups `S_{2ⁿ}` rational?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Sylow

@[expose] public section

namespace MathlibExt.GroupTheory.SylowTwoSymmetricRationalKourovka15Problem25Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.25 (Ya. G.
Berkovich). UnsolvedMath record UM-00701113 (`KOU-15.25`), dataset ulamai/UnsolvedMath v1.8.0.

Rationality is stated through the standard equivalent conjugacy criterion: a finite group is
rational if and only if every element `g` is conjugate to `gᵏ` for every `k` coprime to the order of
`g`. Conjugacy is taken inside the Sylow subgroup itself. Every `n ≥ 0` is included (`n = 0, 1` give
groups of order `1` and `2`).
-/

/-- `G` is rational in the conjugacy formulation: every element `g` is conjugate to `g ^ k` for
every `k` coprime to the order of `g`. For finite groups this is equivalent to every irreducible
complex character taking only rational values. -/
def IsRationalGroup (G : Type*) [Group G] : Prop :=
  ∀ (g : G) (k : ℕ), k.Coprime (orderOf g) → IsConj g (g ^ k)

/-- Kourovka 15.25 (Ya. G. Berkovich): for every `n`, every Sylow `2`-subgroup of the symmetric
group `S_{2ⁿ}` is rational. -/
def sylowTwoSubgroupSymmetricRational : Prop :=
  ∀ (n : ℕ) (P : Sylow 2 (Equiv.Perm (Fin (2 ^ n)))),
    IsRationalGroup (P : Subgroup (Equiv.Perm (Fin (2 ^ n))))

/--
Resolved true: the Kourovka Archive answers 15.25 "Yes, they are" (A. Mann): a Sylow `2`-subgroup
`Tₙ` of `S_{2ⁿ}` is the wreath product of `T_{n-1}` with a group of order `2`, which is rational
when `T_{n-1}` is (Kletzing, Corollary 70), and induction on `n` applies. Source: E. I. Khukhro and
V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.25 (Ya. G. Berkovich); resolution:
A. Mann, letter of 1 October 2002, as recorded in the Kourovka Archive, Problem 15.25, using D.
Kletzing, Structure and representations of Q-groups, Lecture Notes in Math. 1084, Springer, Berlin,
1984, Corollary 70, Kourovka Archive, Problem 15.25 (answer: Yes, they are; T_n = T_(n-1) wr C_2 and
wreath products with C_2 preserve rationality), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted sylowTwoSubgroupSymmetricRational_holds : sylowTwoSubgroupSymmetricRational

end MathlibExt.GroupTheory.SylowTwoSymmetricRationalKourovka15Problem25Wanted
