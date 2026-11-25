/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Blocks of defect zero and solutions of `[x, y] = g` (Kourovka Notebook Problem 12.80)

Kourovka Notebook, Archive of Solved Problems, Problem 12.80 (K. W. Roggenkamp; S. P. Strunkov): (a)
is the number of `p`-blocks of defect 0 of a finite group `G` equal to the number of conjugacy
classes of elements `g ∈ G` such that the number of solutions of `[x, y] = g` in `G` is not
divisible by `p`? (b) The same question for simple groups `G`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Character

@[expose] public section

namespace MathlibExt.GroupTheory.DefectZeroBlocksCommutatorCountKourovka12Problem80Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.80 (K. W.
Roggenkamp; S. P. Strunkov). UnsolvedMath record UM-00700898 (`KOU-12.80`), dataset
ulamai/UnsolvedMath v1.8.0.

Blocks of defect zero are counted by the irreducible complex characters of `p`-defect zero: each
such block contains exactly one irreducible character `χ`, characterized by `|G|ₚ ∣ χ(1)` (Brauer);
characters are compared as functions. Both parts are stated for primes `p` dividing `|G|`: for `p ∤
|G|` the literal claim fails trivially (for `G = ℤ₂`, `p = 3` there are two blocks of defect zero
and one such class), and both counterexamples of the Archive have `p ∣ |G|`. Simple is
`IsSimpleGroup`.
-/

open scoped commutatorElement

/-- **Characters of $p$-defect zero.** For a natural number $p$ and a group $G$, the set of
characters $\chi \colon G \to \mathbb{C}$ of irreducible finite-dimensional complex representations
of $G$ whose degree is divisible by $p^a$, where $a$ is the exponent of $p$ in the prime
factorization of the order $|G|$ (and $a = 0$ when $G$ is infinite or $p$ is not prime).

For a prime $p$ and a finite group $G$, each $p$-block of defect zero contains exactly one
irreducible character, and every such character forms a block of defect zero (Brauer), so these
characters count the $p$-blocks of defect zero. -/
def defectZeroCharacters (p : ℕ) (G : Type) [Group G] : Set (G → ℂ) :=
  {χ | ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (ρ : Representation ℂ G V), ρ.IsIrreducible ∧ ρ.character = χ ∧
      p ^ (Nat.card G).factorization p ∣ Module.finrank ℂ V}

/-- **Number of solutions of a commutator equation.** For an element $g$ of a group $G$, the
number of pairs $(x, y) \in G \times G$ with $[x, y] = x y x^{-1} y^{-1} = g$, taken to be $0$ when
there are infinitely many such pairs. -/
noncomputable def commutatorSolutionCount {G : Type*} [Group G] (g : G) : ℕ :=
  Nat.card {xy : G × G // ⁅xy.1, xy.2⁆ = g}

/-- **Conjugacy classes with commutator count not divisible by $p$.** For a natural number $p$ and
a group $G$, the set of conjugacy classes of $G$ containing an element $g$ such that the number of
pairs $(x, y) \in G \times G$ with $[x, y] = x y x^{-1} y^{-1} = g$ (taken to be $0$ when there are
infinitely many) is not divisible by $p$. -/
def nondivisibleCommutatorClasses (p : ℕ) (G : Type*) [Group G] : Set (ConjClasses G) :=
  {c | ∃ g : G, ConjClasses.mk g = c ∧ ¬ p ∣ commutatorSolutionCount g}

/-- **Kourovka Problem 12.80(a): blocks of defect zero and commutator equations.** For every prime
$p$ and every finite group $G$ whose order is divisible by $p$, the number of irreducible complex
characters of $G$ of $p$-defect zero equals the number of conjugacy classes of $G$ containing an
element $g$ for which the number of pairs $(x, y) \in G \times G$ with
$[x, y] = x y x^{-1} y^{-1} = g$ is not divisible by $p$.

Each $p$-block of defect zero contains exactly one irreducible character, and every irreducible
character of $p$-defect zero forms such a block (Brauer), so this is K. W. Roggenkamp's question
whether the number of $p$-blocks of defect zero equals that number of classes. -/
def defectZeroBlocksEqNondivisibleClasses : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G], p ∣ Nat.card G →
    Nat.card (defectZeroCharacters p G) = Nat.card (nondivisibleCommutatorClasses p G)

/-- **Kourovka Problem 12.80(b): the case of simple groups.** For every prime $p$ and every
finite simple group $G$ whose order is divisible by $p$, the number of irreducible complex
characters of $G$ of $p$-defect zero equals the number of conjugacy classes of $G$ containing an
element $g$ for which the number of pairs $(x, y) \in G \times G$ with
$[x, y] = x y x^{-1} y^{-1} = g$ is not divisible by $p$. -/
def simpleDefectZeroBlocksEqNondivisibleClasses : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → p ∣ Nat.card G →
    Nat.card (defectZeroCharacters p G) = Nat.card (nondivisibleCommutatorClasses p G)

/--
**Kourovka Problem 12.80(a) has a negative answer.** It is not true that for every prime $p$ and
every finite group $G$ whose order is divisible by $p$, the number of irreducible complex characters
of $G$ of $p$-defect zero equals the number of conjugacy classes of $G$ containing an element $g$
for which the number of pairs $(x, y) \in G \times G$ with $[x, y] = x y x^{-1} y^{-1} = g$ is not
divisible by $p$.

L. Barker's counterexample: for $p = 2$ and $G = \mathbb{Z}_3 \times S_3$ there are three
irreducible characters of degree $2$, all of $2$-defect zero (so three $2$-blocks of defect zero),
but only one class, that of $(1, (123))$, with an odd number of solutions of $[x, y] = g$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.80 (K. W.
Roggenkamp; S. P. Strunkov); resolution: L. Barker, letter of 27 May 1996 (part a); B. Sambale,
letter of 5 May 2021 (part b); as recorded in the Kourovka Archive, Problem 12.80, (a) p = 2, G =
ℤ_3 × S_3; (b) p = 2, G = A_5: one 2-block of defect zero, three classes ((123), (12345), (13524))
with an odd number of solutions of [x, y] = g, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted defectZeroBlocksEqNondivisibleClasses_refuted :
    ¬ defectZeroBlocksEqNondivisibleClasses

/--
**Kourovka Problem 12.80(b) has a negative answer.** It is not true that for every prime $p$ and
every finite simple group $G$ whose order is divisible by $p$, the number of irreducible complex
characters of $G$ of $p$-defect zero equals the number of conjugacy classes of $G$ containing an
element $g$ for which the number of pairs $(x, y) \in G \times G$ with
$[x, y] = x y x^{-1} y^{-1} = g$ is not divisible by $p$.

B. Sambale's counterexample: in $A_5$ with $p = 2$ there is one irreducible character of $2$-defect
zero (the character of degree $4$, so one $2$-block of defect zero) but three classes, those of
$(123)$, $(12345)$ and $(13524)$, with an odd number of solutions of $[x, y] = g$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.80 (K. W.
Roggenkamp; S. P. Strunkov); resolution: L. Barker, letter of 27 May 1996 (part a); B. Sambale,
letter of 5 May 2021 (part b); as recorded in the Kourovka Archive, Problem 12.80, (a) p = 2, G =
ℤ_3 × S_3; (b) p = 2, G = A_5: one 2-block of defect zero, three classes ((123), (12345), (13524))
with an odd number of solutions of [x, y] = g, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted simpleDefectZeroBlocksEqNondivisibleClasses_refuted :
    ¬ simpleDefectZeroBlocksEqNondivisibleClasses

end MathlibExt.GroupTheory.DefectZeroBlocksCommutatorCountKourovka12Problem80Wanted
