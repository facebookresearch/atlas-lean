/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sylow 2-subgroups of rational groups (Kourovka Notebook Problem 16.36)

Kourovka Notebook, Archive of Solved Problems, Problem 16.36 (M. R. Darafsheh): (well-known problem)
a finite group is rational if all of its ordinary characters are rational-valued. Is every Sylow
2-subgroup of a rational group also a rational group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Sylow

@[expose] public section

namespace MathlibExt.GroupTheory.RationalGroupSylowTwoKourovka16Problem36Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.36 (M. R.
Darafsheh). UnsolvedMath record UM-00701228 (`KOU-16.36`), dataset ulamai/UnsolvedMath v1.8.0.

Rationality is stated by the classical equivalent condition for finite groups: every `g` is
conjugate to every generator `g^k` (`k` coprime to the order of `g`) of `⟨g⟩`, since `χ(g)` is
rational iff it is fixed by the Galois automorphisms `ζ ↦ ζ^k` and characters separate conjugacy
classes. The Sylow subgroup is a group in its own right, so its conjugacy is internal.
-/

/-- `G` is rational (all ordinary characters are rational-valued), in the classical equivalent
form for finite groups: every `g` is conjugate to `g ^ k` for every `k` coprime to the order of
`g`. -/
def IsRationalGroup (G : Type*) [Group G] : Prop :=
  ∀ g : G, ∀ k : ℕ, Nat.Coprime k (orderOf g) → IsConj g (g ^ k)

/-- Kourovka 16.36 (M. R. Darafsheh): every Sylow 2-subgroup of a finite rational group is
rational. -/
def sylowTwoOfRationalIsRational : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsRationalGroup G →
    ∀ P : Sylow 2 G, IsRationalGroup (P : Subgroup G)

/--
Resolved false: the Kourovka Archive answers 16.36 "No, not always", citing Isaacs and Navarro
(2012): some finite rational group has a Sylow 2-subgroup that is not rational. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.36 (M. R. Darafsheh);
resolution: I. M. Isaacs and G. Navarro, Math. Z. 272 (2012), 937-945, Kourovka Archive, Problem
16.36 (No, not always).
-/
public theorem_wanted sylowTwoOfRationalIsRational_refuted : ¬ sylowTwoOfRationalIsRational

end MathlibExt.GroupTheory.RationalGroupSylowTwoKourovka16Problem36Wanted
