/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Uniqueness of roots in pure braid groups (Kourovka Notebook Problem 11.55)

Kourovka Notebook, Archive of Solved Problems, Problem 11.55 (G. S. Makanin): is it true that
extraction of roots in the group of coloured braids is uniquely determined?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.GroupTheory.ArtinGroup

@[expose] public section

namespace MathlibExt.GroupTheory.PureBraidUniqueRootsKourovka11Problem55Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.55 (G. S.
Makanin). UnsolvedMath record UM-00700747 (`KOU-11.55`), dataset ulamai/UnsolvedMath v1.8.0.

The coloured (pure) braid group on `n + 1` strands is the normal closure of the squares `σᵢ²` of the
standard generators of the braid group `B_{n+1}`, which is MathlibExt's Artin group of the Coxeter
matrix of type `Aₙ`. This normal closure is the kernel of `B_{n+1} → S_{n+1}`: adding `σᵢ² = 1` to
the braid relations gives the Coxeter presentation of `S_{n+1}`. Kourovka's definition (Archive,
10.24) is the braids whose strings induce the identity permutation. Unique extraction of roots is `α
^ k = β ^ k → α = β` for `k ≥ 1`.
-/

/-- The coloured (pure) braid group on `n + 1` strands: the normal closure of the squares `σᵢ²` of
the standard generators of the braid group `B_{n+1}`, the Artin group of the Coxeter matrix of type
`Aₙ`. This is the kernel of `B_{n+1} → S_{n+1}`, since adding the relations `σᵢ² = 1` to the braid
relations presents the Coxeter group of type `Aₙ`, the symmetric group `S_{n+1}`. -/
def pureBraidGroup (n : ℕ) : Subgroup (CoxeterMatrix.A n).ArtinGroup :=
  Subgroup.normalClosure (Set.range fun i => CoxeterMatrix.ArtinGroup.of (CoxeterMatrix.A n) i ^ 2)

/-- Kourovka 11.55 (G. S. Makanin): extraction of roots in the group of coloured braids is unique:
if `α ^ k = β ^ k` for coloured braids `α`, `β` and some `k ≥ 1`, then `α = β`. -/
def pureBraidUniqueRoots : Prop :=
  ∀ n k : ℕ, 0 < k → ∀ α ∈ pureBraidGroup n, ∀ β ∈ pureBraidGroup n, α ^ k = β ^ k → α = β

/--
Resolved true: the Kourovka Archive answers 11.55 affirmatively (V. A. Roman'kov): the coloured
braid group embeds in the IA-automorphism group of a free group, which is residually torsion-free
nilpotent, and torsion-free nilpotent groups have unique roots. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.55 (G. S. Makanin); resolution: V.
A. Roman'kov, letter of 3 October 1990; see also V. G. Bardakov, Russ. Acad. Sci. Sb. Math. 76, no.
1 (1993), 123-153, Kourovka Archive, Problems 11.54 and 11.55: both affirmative, since the coloured
braid group embeds in the group of automorphisms of `F_n` acting trivially modulo `F_n'`, which is
residually torsion-free nilpotent, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted pureBraidUniqueRoots_holds : pureBraidUniqueRoots

end MathlibExt.GroupTheory.PureBraidUniqueRootsKourovka11Problem55Wanted
