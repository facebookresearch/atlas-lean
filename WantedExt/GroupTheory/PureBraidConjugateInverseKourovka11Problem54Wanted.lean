/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Pure braids conjugate to their inverses (Kourovka Notebook Problem 11.54)

Kourovka Notebook, Archive of Solved Problems, Problem 11.54 (G. S. Makanin): is it true that in the
group of coloured braids only the identity braid is conjugate to its inverse?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.GroupTheory.ArtinGroup

@[expose] public section

namespace MathlibExt.GroupTheory.PureBraidConjugateInverseKourovka11Problem54Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.54 (G. S.
Makanin). UnsolvedMath record UM-00700746 (`KOU-11.54`), dataset ulamai/UnsolvedMath v1.8.0.

The coloured (pure) braid group on `n + 1` strands is the normal closure of the squares `σᵢ²` of the
standard generators of the braid group `B_{n+1}`, which is MathlibExt's Artin group of the Coxeter
matrix of type `Aₙ`. This normal closure is the kernel of `B_{n+1} → S_{n+1}`: adding `σᵢ² = 1` to
the braid relations gives the Coxeter presentation of `S_{n+1}`. Kourovka's definition (Archive,
10.24) is the braids whose strings induce the identity permutation. Conjugacy is taken inside the
coloured braid group, as posed.
-/

/-- The coloured (pure) braid group on `n + 1` strands: the normal closure of the squares `σᵢ²` of
the standard generators of the braid group `B_{n+1}`, the Artin group of the Coxeter matrix of type
`Aₙ`. This is the kernel of `B_{n+1} → S_{n+1}`, since adding the relations `σᵢ² = 1` to the braid
relations presents the Coxeter group of type `Aₙ`, the symmetric group `S_{n+1}`. -/
def pureBraidGroup (n : ℕ) : Subgroup (CoxeterMatrix.A n).ArtinGroup :=
  Subgroup.normalClosure (Set.range fun i => CoxeterMatrix.ArtinGroup.of (CoxeterMatrix.A n) i ^ 2)

/-- Kourovka 11.54 (G. S. Makanin): in the group of coloured braids only the identity braid is
conjugate (within that group) to its inverse. -/
def pureBraidConjInvTrivial : Prop :=
  ∀ n : ℕ, ∀ β ∈ pureBraidGroup n, (∃ γ ∈ pureBraidGroup n, γ * β * γ⁻¹ = β⁻¹) → β = 1

/--
Resolved true: the Kourovka Archive answers 11.54 affirmatively (V. A. Roman'kov): the coloured
braid group embeds in the IA-automorphism group of a free group, which is residually torsion-free
nilpotent, and in a torsion-free nilpotent group `β` conjugate to `β⁻¹` forces `β = 1`. Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.54 (G. S. Makanin);
resolution: V. A. Roman'kov, letter of 3 October 1990; see also V. G. Bardakov, Russ. Acad. Sci. Sb.
Math. 76, no. 1 (1993), 123-153, Kourovka Archive, Problems 11.54 and 11.55: both affirmative, since
the coloured braid group embeds in the group of automorphisms of `F_n` acting trivially modulo
`F_n'`, which is residually torsion-free nilpotent, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted pureBraidConjInvTrivial_holds : pureBraidConjInvTrivial

end MathlibExt.GroupTheory.PureBraidConjugateInverseKourovka11Problem54Wanted
