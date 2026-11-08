/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finitely presented elementary amenable groups (Kourovka Notebook Problem 16.52)

Kourovka Notebook, Archive of Solved Problems, Problem 16.52 (P. Linnell, T. Schick): is every
finitely presented elementary amenable group solvable-by-finite?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.ElementaryAmenableVirtuallySolvableKourovka16Problem52Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.52 (P.
Linnell, T. Schick). UnsolvedMath record UM-00701244 (`KOU-16.52`), dataset ulamai/UnsolvedMath
v1.8.0.

Elementary amenable groups are the smallest class containing finite and abelian groups and closed
under isomorphisms, subgroups, quotients, extensions and directed unions (Chou), an inductive
predicate on groups in `Type`. Solvable-by-finite means having a solvable subgroup of finite index
(its normal core is a solvable normal subgroup of finite index).
-/

/-- The class of elementary amenable groups (in `Type`): the smallest class of groups containing
finite and abelian groups and closed under isomorphisms, subgroups, quotients, extensions and
directed unions. -/
inductive IsElementaryAmenable : (G : Type) → [Group G] → Prop
  | of_finite (G : Type) [Group G] [Finite G] : IsElementaryAmenable G
  | of_comm (G : Type) [Group G] (h : ∀ a b : G, a * b = b * a) : IsElementaryAmenable G
  | of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) :
      IsElementaryAmenable G → IsElementaryAmenable H
  | subgroup {G : Type} [Group G] (K : Subgroup G) : IsElementaryAmenable G → IsElementaryAmenable K
  | quotient {G : Type} [Group G] (N : Subgroup G) [N.Normal] :
      IsElementaryAmenable G → IsElementaryAmenable (G ⧸ N)
  | extension {G : Type} [Group G] (N : Subgroup G) [N.Normal] :
      IsElementaryAmenable N → IsElementaryAmenable (G ⧸ N) → IsElementaryAmenable G
  | directedUnion {G : Type} [Group G] (S : Set (Subgroup G)) :
      DirectedOn (· ≤ ·) S → (∀ K ∈ S, IsElementaryAmenable K) → (∀ g : G, ∃ K ∈ S, g ∈ K) →
      IsElementaryAmenable G

/-- Kourovka 16.52 (P. Linnell, T. Schick): every finitely presented elementary amenable group is
solvable-by-finite (has a solvable subgroup of finite index). -/
def finitelyPresentedElementaryAmenableVirtuallySolvable : Prop :=
  ∀ (G : Type) [Group G], Group.IsFinitelyPresented G → IsElementaryAmenable G →
    ∃ N : Subgroup G, N.FiniteIndex ∧ Group.IsSolvable N

/--
Resolved false: the Kourovka Archive answers 16.52 "No, not every": as Belegradek and Cornulier
observed, Houghton's groups `Hₙ`, finitely presented for `n ≥ 3` by Brown, are elementary amenable
(the locally finite group of finitary permutations extended by `ℤ^{n-1}`) but not virtually
solvable. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.52
(P. Linnell, T. Schick); resolution: C. H. Houghton, Arch. Math. (Basel) 31 (1978/79), 254-258; K.
S. Brown, J. Pure Appl. Algebra 44 (1987), 45-75; observation of I. Belegradek and Y. Cornulier,
MathOverflow question 107996, Kourovka Archive, Problem 16.52 (No, not every: Houghton's groups are
finitely presented (Brown) and elementary amenable, but not virtually solvable),
https://mathoverflow.net/questions/107996.
-/
public theorem_wanted finitelyPresentedElementaryAmenableVirtuallySolvable_refuted :
    ¬ finitelyPresentedElementaryAmenableVirtuallySolvable

end MathlibExt.GroupTheory.ElementaryAmenableVirtuallySolvableKourovka16Problem52Wanted
