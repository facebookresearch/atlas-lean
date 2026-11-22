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

/-- The irreducible complex characters of `G` of `p`-defect zero (degree divisible by the full
power of `p` dividing `|G|`). Each `p`-block of defect zero contains exactly one irreducible
character, and every such character forms a block of defect zero (Brauer), so these characters
count the `p`-blocks of defect zero. -/
def defectZeroCharacters (p : ℕ) (G : Type) [Group G] : Set (G → ℂ) :=
  {χ | ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (ρ : Representation ℂ G V), ρ.IsIrreducible ∧ ρ.character = χ ∧
      p ^ (Nat.card G).factorization p ∣ Module.finrank ℂ V}

/-- The number of solutions `(x, y)` of `[x, y] = g`. -/
noncomputable def commutatorSolutionCount {G : Type*} [Group G] (g : G) : ℕ :=
  Nat.card {xy : G × G // ⁅xy.1, xy.2⁆ = g}

/-- The conjugacy classes of elements `g` for which the number of solutions of `[x, y] = g` is
not divisible by `p`. -/
def nondivisibleCommutatorClasses (p : ℕ) (G : Type*) [Group G] : Set (ConjClasses G) :=
  {c | ∃ g : G, ConjClasses.mk g = c ∧ ¬ p ∣ commutatorSolutionCount g}

/-- Kourovka 12.80(a) (K. W. Roggenkamp): for every prime `p` dividing `|G|`, the number of
`p`-blocks of defect zero of a finite group `G` equals the number of conjugacy classes of elements
`g` such that the number of solutions of `[x, y] = g` is not divisible by `p`. -/
def defectZeroBlocksEqNondivisibleClasses : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G], p ∣ Nat.card G →
    Nat.card (defectZeroCharacters p G) = Nat.card (nondivisibleCommutatorClasses p G)

/-- Kourovka 12.80(b): the same for finite simple groups `G`. -/
def simpleDefectZeroBlocksEqNondivisibleClasses : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → p ∣ Nat.card G →
    Nat.card (defectZeroCharacters p G) = Nat.card (nondivisibleCommutatorClasses p G)

/--
Resolved false: the Kourovka Archive answers 12.80(a) No (L. Barker): for `p = 2` and `G = ℤ₃ × S₃`
there are three 2-blocks of defect zero (the irreducible characters of degree 2) but only one class,
that of `(1, (123))`, with an odd number of solutions of `[x, y] = g`. Source: E. I. Khukhro and V.
D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.80 (K. W. Roggenkamp; S. P.
Strunkov); resolution: L. Barker, letter of 27 May 1996 (part a); B. Sambale, letter of 5 May 2021
(part b); as recorded in the Kourovka Archive, Problem 12.80, (a) p = 2, G = ℤ_3 × S_3; (b) p = 2, G
= A_5: one 2-block of defect zero, three classes ((123), (12345), (13524)) with an odd number of
solutions of [x, y] = g, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted defectZeroBlocksEqNondivisibleClasses_refuted :
    ¬ defectZeroBlocksEqNondivisibleClasses

/--
Resolved false: the Kourovka Archive answers 12.80(b) "No, not always" (B. Sambale): in `A₅` with `p
= 2` there is one 2-block of defect zero (the character of degree 4) but three classes, those of
`(123)`, `(12345)` and `(13524)`, with an odd number of solutions of `[x, y] = g`. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.80 (K. W. Roggenkamp; S. P.
Strunkov); resolution: L. Barker, letter of 27 May 1996 (part a); B. Sambale, letter of 5 May 2021
(part b); as recorded in the Kourovka Archive, Problem 12.80, (a) p = 2, G = ℤ_3 × S_3; (b) p = 2, G
= A_5: one 2-block of defect zero, three classes ((123), (12345), (13524)) with an odd number of
solutions of [x, y] = g, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted simpleDefectZeroBlocksEqNondivisibleClasses_refuted :
    ¬ simpleDefectZeroBlocksEqNondivisibleClasses

end MathlibExt.GroupTheory.DefectZeroBlocksCommutatorCountKourovka12Problem80Wanted
