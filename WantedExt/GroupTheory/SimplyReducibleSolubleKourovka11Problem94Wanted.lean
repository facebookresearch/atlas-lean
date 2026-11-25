/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Solubility of finite simply reducible groups (Kourovka Notebook Problem 11.94)

Kourovka Notebook, Archive of Solved Problems, Problem 11.94 (S. P. Strunkov): a group is simply
reducible if all its characters are real and the tensor product of any two irreducible
representations contains no multiple components. Is every finite simply reducible group soluble?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.GroupTheory.Solvable
public import Mathlib.RepresentationTheory.Character

@[expose] public section

namespace MathlibExt.GroupTheory.SimplyReducibleSolubleKourovka11Problem94Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.94 (S. P.
Strunkov). UnsolvedMath record UM-00700786 (`KOU-11.94`), dataset ulamai/UnsolvedMath v1.8.0.

Representations are finite-dimensional complex representations (`FDRep ℂ G`), irreducible ones are
the simple objects. All characters are real iff all irreducible characters are. The multiplicity of
an irreducible `U` in `V ⊗ W` is `dim Hom_G(U, V ⊗ W)` (Maschke and Schur), so "no multiple
components" is that dimension being at most 1. The first request of the problem, to describe all
simply reducible groups, is not a proposition and is not stated.
-/

open CategoryTheory MonoidalCategory

/-- **Simply reducible group.** A group $G$ is simply reducible when the character of every
irreducible finite-dimensional complex representation of $G$ is real-valued, and for all
irreducible finite-dimensional complex representations $U$, $V$ and $W$ of $G$, the space
$\mathrm{Hom}_G(U, V \otimes W)$ of $G$-equivariant linear maps from $U$ to the tensor product
$V \otimes W$ has complex dimension at most $1$.

For finite $G$, by Maschke's and Schur's theorems this dimension is the multiplicity of $U$ in
$V \otimes W$, so the second condition says that $V \otimes W$ has no repeated irreducible
constituents. -/
def IsSimplyReducible (G : Type) [Group G] : Prop :=
  (∀ V : FDRep ℂ G, Simple V → ∀ g : G, (V.character g).im = 0) ∧
    ∀ V W U : FDRep ℂ G, Simple V → Simple W → Simple U → Module.finrank ℂ (U ⟶ V ⊗ W) ≤ 1

/-- **Solubility of finite simply reducible groups (Kourovka 11.94).** The statement, asked by
S. P. Strunkov as Kourovka Problem 11.94, that every finite simply reducible group is soluble. -/
def simplyReducibleSoluble : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimplyReducible G → Group.IsSolvable G

/--
**Finite simply reducible groups are soluble.** Every finite simply reducible group is soluble;
that is, the statement of Kourovka Problem 11.94 holds.

This was proved by Kazarin and Chankov; the Kourovka Archive answers 11.94 "Yes, it is".

Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 11.94 (S. P. Strunkov); resolution: L. S. Kazarin and E. I.
Chankov, Sb. Math. 201, no. 5 (2010), 655-668, Kourovka Archive, Problem 11.94: "Yes, it is",
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted simplyReducibleSoluble_holds : simplyReducibleSoluble

end MathlibExt.GroupTheory.SimplyReducibleSolubleKourovka11Problem94Wanted
