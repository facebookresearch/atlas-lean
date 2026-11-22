/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite-index subgroups of Aut(Fₙ) with positive b₁ [AMR-109-0273]

Source: Farb, Problems on Mapping Class Groups and Related Topics,
Question 2.5, PDF p. 330.

Resolution: the universal statement below is false at `n = 5`.
Kaluba–Nowak–Ozawa (Math. Ann. 375 (2019), 1169–1191, Corollary 2)
proved that `Aut(F₅)` has Kazhdan's property (T). Property (T) passes
to finite-index subgroups (the problem list, before Question 2.5;
Bekka–de la Harpe–Valette, Kazhdan's Property (T), Introduction, p. 5),
and a countable group with property (T) has finite abelianization
(ibid.), so no finite-index subgroup of `Aut(F₅)` has positive first
Betti number.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dimension.Basic

@[expose] public section

namespace MathlibExt.Topology.AutFnFiniteIndexPositiveBettiWanted

/-!
[AMR-109-0273] Farb Question 2.5.
Source: Farb, Problems on Mapping Class Groups and Related Topics,
Question 2.5, PDF p. 330,
`https://www.math.uchicago.edu/~farb/papers/mcgbook.pdf`.

Clause list (every item below appears in the formal text below):
1. `n` ranges over natural numbers (rank of the free group).
2. Numeric threshold `n > 3` (equivalently `3 < n`), copied exactly.
3. `F_n` is the free group on `n` generators.
4. `Aut(F_n)` is the automorphism group of `F_n`.
5. The witness is a subgroup of `Aut(F_n)`.
6. That subgroup has finite index.
7. That subgroup has positive first Betti number (ℤ-rank of its
   abelianization).
8. Status: resolved false (`conjecture_refuted` below).
-/

/-- First Betti rank of a group, as the `ℤ`-rank of its abelianization
[AMR-109-0273] (Question 2.5, PDF p. 330). -/
noncomputable def firstBettiRank (G : Type*) [Group G] : Cardinal :=
  Module.rank ℤ (Additive (Abelianization G))

/-- Farb Question 2.5 [AMR-109-0273] (PDF p. 330): for `n > 3`, does
`Aut(F_n)` have a finite-index subgroup with positive first Betti
number? -/
def conjecture : Prop :=
  ∀ (n : ℕ), 3 < n →
    ∃ (H : Subgroup (MulAut (FreeGroup (Fin n)))),
      H.FiniteIndex ∧ 0 < firstBettiRank ↥H

/--
Resolved false: Kaluba-Nowak-Ozawa proved that Aut(F5) has Kazhdan's property (T) (Math. Ann.
375 (2019), 1169-1191, Corollary 2: "The groups Aut(F5) and Out(F5) have property (T)."). Every
finite-index subgroup of Aut(F5) therefore has property (T): the problem list notes, in the
paragraph before Question 2.5 (Bridson-Vogtmann, Farb (ed.), Chapter 20, Section 2.2, PDF p.
330), that "property (T) passes to finite-index subgroups", and Bekka-de la Harpe-Valette
(Kazhdan's Property (T), Introduction, p. 5) state that "a lattice in a locally compact group G
has Property (T) if and only if G has Property (T)". The same page states that "a countable
group Γ with Property (T) is finitely generated and its first homology group H1(Γ, Z) = Γ/[Γ, Γ]
is finite", so every finite-index subgroup of Aut(F5) has finite abelianization and first Betti
number 0, and the n = 5 instance refutes the universal claim over n > 3. Source: M. Kaluba, P.
W. Nowak, N. Ozawa, Aut(F5) has property (T), Math. Ann. 375 (2019), no. 3-4, 1169-1191,
https://arxiv.org/abs/1712.07167; B. Bekka, P. de la Harpe, A. Valette, Kazhdan's Property (T),
New Mathematical Monographs 11, Cambridge University Press, 2008, Introduction, p. 5,
https://assets.cambridge.org/97805218/87205/excerpt/9780521887205_excerpt.pdf. Moved from
`OpenConjectures/Topology/AutFnFiniteIndexPositiveBetti`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Topology.AutFnFiniteIndexPositiveBettiWanted
