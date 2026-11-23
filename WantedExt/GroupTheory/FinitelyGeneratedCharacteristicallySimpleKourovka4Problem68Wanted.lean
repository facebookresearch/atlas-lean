/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finitely generated characteristically simple groups (Kourovka Notebook Problem 4.68)

Kourovka Notebook, Archive of Solved Problems, Problem 4.68 (J. Wiegold): construct a finitely
generated (infinite) characteristically simple group that is not a direct power of a simple group.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.FinitelyGeneratedCharacteristicallySimpleKourovka4Problem68Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.68 (J.
Wiegold). UnsolvedMath record UM-00700275 (`KOU-4.68`), dataset ulamai/UnsolvedMath v1.8.0.

Characteristically simple means non-trivial with no characteristic subgroups other than `1` and the
whole group (Mathlib's `Subgroup.Characteristic`). A direct power of a simple group `S` is written
`ι → S` for an index type `ι`. For a finitely generated group this covers every direct power: an
infinite unrestricted power of a non-trivial group is uncountable, an infinite restricted power is
not finitely generated, and finite powers coincide with `ι → S` for finite `ι`.
-/

/-- `G` is characteristically simple: it is non-trivial and its only characteristic subgroups are
`⊥` and `⊤`. -/
def IsCharacteristicallySimple (G : Type) [Group G] : Prop :=
  Nontrivial G ∧ ∀ H : Subgroup G, H.Characteristic → H = ⊥ ∨ H = ⊤

/-- Kourovka 4.68 (J. Wiegold): there is an infinite finitely generated characteristically simple
group that is not a direct power `ι → S` of a simple group `S`. -/
def existsFGCharacteristicallySimpleNotSimplePower : Prop :=
  ∃ (G : Type) (_ : Group G), Group.FG G ∧ Infinite G ∧ IsCharacteristicallySimple G ∧
    ∀ (S : Type) [Group S], IsSimpleGroup S → ∀ ι : Type, IsEmpty (G ≃* (ι → S))

/--
Resolved true: the Kourovka Archive records 4.68 as done by Wilson, who constructs finitely
generated characteristically simple groups that are not direct powers of simple groups (Math. Proc.
Cambridge Philos. Soc. 80 (1976), §1.1); such a group is infinite, since finite characteristically
simple groups are direct powers of simple groups. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 4.68 (J. Wiegold); resolution: J. S. Wilson, On
characteristically simple groups, Math. Proc. Cambridge Philos. Soc. 80 (1976), 19-35, Kourovka
Archive, Problem 4.68: This was done (Wilson); §1.1 of the paper: "Our object here is to construct
finitely generated groups, and also groups satisfying the maximal condition for normal subgroups,
which are characteristically simple but which are not direct powers of simple groups",
https://doi.org/10.1017/S0305004100052622.
-/
public theorem_wanted existsFGCharacteristicallySimpleNotSimplePower_holds :
    existsFGCharacteristicallySimpleNotSimplePower

end MathlibExt.GroupTheory.FinitelyGeneratedCharacteristicallySimpleKourovka4Problem68Wanted
