/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Indices of intersections of Sylow 2-subgroups (Kourovka Notebook Problem 5.12)

Kourovka Notebook, Archive of Solved Problems, Problem 5.12 (V. V. Kabanov): let G be a finite group
with trivial soluble radical in which there are Sylow 2-subgroups having non-trivial intersection;
suppose that for any two Sylow 2-subgroups P and Q of G with P ∩ Q ≠ 1 the index |P : P ∩ Q| does
not exceed 2^n. Is it then true that |P| ≤ 2^(2n)?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.RadicalHereditaryFormationKourovka12Problem7Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.SylowTwoIntersectionIndexKourovka5Problem12Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.12 (V. V.
Kabanov). UnsolvedMath record UM-00700296 (`KOU-5.12`), dataset ulamai/UnsolvedMath v1.8.0.

Trivial soluble radical: `⊥` is the soluble radical (`IsSolubleRadical` of the Kourovka 12.7 entry,
reused here: the largest soluble normal subgroup), that is, no non-trivial soluble normal subgroup
(equivalently `O_p(G) = 1` for every prime `p`, the hypothesis in Zenkov's abstract). "Sylow
2-subgroups having non-trivial intersection" means two distinct ones: with `P = Q` allowed it would
only say that `|G|` is even, and then the simple groups `PSL₂(2^k)`, `k ≥ 2`, whose distinct Sylow
2-subgroups meet trivially, satisfy the bound hypothesis with `n = 0` and refute `|P| ≤ 1`. `|P : P
∩ Q|` is `relIndex`.
-/

open MathlibExt.GroupTheory.RadicalHereditaryFormationKourovka12Problem7Wanted (IsSolubleRadical)

/-- Kourovka 5.12 (V. V. Kabanov): let `G` be a finite group with trivial soluble radical (`⊥` is
the soluble radical: no non-trivial soluble normal subgroup) having two distinct Sylow
`2`-subgroups with non-trivial intersection. If `|P : P ∩ Q| ≤ 2 ^ n` for all Sylow
`2`-subgroups `P`, `Q` with `P ∩ Q ≠ 1`, then `|P| ≤ 2 ^ (2 n)`. -/
def sylowTwoIntersectionIndexBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSolubleRadical (⊥ : Subgroup G) →
    (∃ P Q : Sylow 2 G, P ≠ Q ∧ (P : Subgroup G) ⊓ Q ≠ ⊥) → ∀ n : ℕ,
    (∀ P Q : Sylow 2 G, (P : Subgroup G) ⊓ Q ≠ ⊥ → ((P : Subgroup G) ⊓ Q).relIndex P ≤ 2 ^ n) →
    ∀ P : Sylow 2 G, Nat.card P ≤ 2 ^ (2 * n)

/--
Resolved true: the Kourovka Archive answers 5.12 "Yes, it is, mod CFSG", citing Zenkov (Algebra and
Logic 36 (1997), 93-98), whose abstract states that he settles Problem 5.12 for finite groups with
`O_p(G) = 1` for every prime `p`, that is, with trivial soluble radical. Source: E. I. Khukhro and
V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.12 (V. V. Kabanov); resolution: V.
I. Zenkov, Orders of intersections of Sylow p-subgroups in finite groups, Algebra and Logic 36
(1997), 93-98, abstract: using the classification of finite simple groups, Zenkov tackles Problem
5.12 for finite groups G with O_p(G) = 1 for every prime p; Kourovka Archive, Problem 5.12: Yes, it
is, mod CFSG, https://doi.org/10.1007/BF02672477.
-/
public theorem_wanted sylowTwoIntersectionIndexBound_holds : sylowTwoIntersectionIndexBound

end MathlibExt.GroupTheory.SylowTwoIntersectionIndexKourovka5Problem12Wanted
