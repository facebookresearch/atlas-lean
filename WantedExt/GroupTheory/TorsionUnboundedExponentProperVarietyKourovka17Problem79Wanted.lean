/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Torsion groups of unbounded exponent in proper varieties (Kourovka Notebook Problem 17.79)

Kourovka Notebook, Archive of Solved Problems, Problem 17.79 (O. Macedońska): does there exist a
finitely generated torsion group of unbounded exponent generating a proper variety?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.Finiteness

@[expose] public section

namespace MathlibExt.GroupTheory.TorsionUnboundedExponentProperVarietyKourovka17Problem79Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.79 (O.
Macedońska). UnsolvedMath record UM-00701381 (`KOU-17.79`), dataset ulamai/UnsolvedMath v1.8.0.

Torsion: every element has finite order; unbounded exponent: `Monoid.exponent G = 0` (no `n > 0`
with `gⁿ = 1` for all `g`); generating a proper variety: `G` satisfies a nontrivial law, an element
`w ≠ 1` of `FreeGroup ℕ` killed by every homomorphism to `G`.
-/

/-- **Kourovka Problem 17.79 (torsion groups of unbounded exponent in proper varieties).** The
statement, asked by O. Macedońska, that there exists a finitely generated group $G$ in which every
element has finite order, which has unbounded exponent (there is no $n \ge 1$ with $g^n = 1$ for
all $g \in G$), and which satisfies a nontrivial law, that is, some element $w \ne 1$ of the free
group $F$ on countably infinitely many generators is mapped to $1$ by every homomorphism
$F \to G$ (equivalently, $G$ generates a proper variety of groups). -/
def torsionUnboundedExponentProperVariety : Prop :=
  ∃ (G : Type) (_ : Group G), Group.FG G ∧ (∀ g : G, IsOfFinOrder g) ∧ Monoid.exponent G = 0 ∧
    ∃ w : FreeGroup ℕ, w ≠ 1 ∧ ∀ φ : FreeGroup ℕ →* G, φ w = 1

/--
Resolved true: the Kourovka Archive answers 17.79 "Yes, moreover, there is a continuum of such
groups" (Atabekyan, 1986), and records Osin's example: a free group of the variety defined by `xⁿ y
= y xⁿ` is a central extension of a free Burnside group of exponent `n` with free abelian centre of
countable rank (Ashmanov-Olshanskii), and adding the relations `xᵢ^i = 1` for a basis `(xᵢ)` of the
centre gives a periodic group of unbounded exponent satisfying that law. Source: E. I. Khukhro and
V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.79 (O. Macedońska); resolution: V.
S. Atabekyan, Infinite simple groups satisfying an identity, Dep. VINITI no. 5381-V86, Moscow, 1986
(Russian); D. Osin, letter of 31 August 2013, as recorded in the Kourovka Archive, Kourovka Archive,
Problem 17.79 (Yes, moreover there is a continuum of such groups (Atabekyan); Osin: a quotient of a
free group of the variety defined by x^n y = y x^n, by the relations x_i^i = 1 for a basis (x_i) of
its free abelian centre, is a periodic group of unbounded exponent in that variety).
-/
public theorem_wanted torsionUnboundedExponentProperVariety_holds :
    torsionUnboundedExponentProperVariety

end MathlibExt.GroupTheory.TorsionUnboundedExponentProperVarietyKourovka17Problem79Wanted
