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

/-- **Rational groups, conjugacy form.** A group $G$ is rational if every element $g \in G$ is
conjugate to $g^k$ for every natural number $k$ coprime to the order of $g$, where an element of
infinite order has order $0$, so that only $k = 1$ is coprime to it. For finite groups this is the
classical equivalent form of the condition that all ordinary characters of $G$ are
rational-valued. -/
def IsRationalGroup (G : Type*) [Group G] : Prop :=
  ∀ g : G, ∀ k : ℕ, Nat.Coprime k (orderOf g) → IsConj g (g ^ k)

/-- **Darafsheh's question on Sylow 2-subgroups of rational groups (Kourovka 16.36).** The
conjecture that for every finite rational group $G$, every Sylow $2$-subgroup of $G$, viewed as a
group in its own right, is rational. Here a group is rational if every element $g$ is conjugate
to $g^k$ for every natural number $k$ coprime to the order of $g$. -/
def sylowTwoOfRationalIsRational : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsRationalGroup G →
    ∀ P : Sylow 2 G, IsRationalGroup (P : Subgroup G)

/--
**Sylow 2-subgroups of rational groups need not be rational (Kourovka 16.36).** There is a
finite rational group with a Sylow $2$-subgroup that is not rational as a group in its own right.
Here a group is rational if every element $g$ is conjugate to $g^k$ for every natural number $k$
coprime to the order of $g$.

The Kourovka Archive answers 16.36 "No, not always", citing Isaacs and Navarro (2012).

Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.36 (M. R. Darafsheh);
resolution: I. M. Isaacs and G. Navarro, Math. Z. 272 (2012), 937-945, Kourovka Archive, Problem
16.36 (No, not always).
-/
public theorem_wanted sylowTwoOfRationalIsRational_refuted : ¬ sylowTwoOfRationalIsRational

end MathlibExt.GroupTheory.RationalGroupSylowTwoKourovka16Problem36Wanted
