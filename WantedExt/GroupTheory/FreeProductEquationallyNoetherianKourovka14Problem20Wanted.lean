/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Free products of equationally Noetherian groups (Kourovka Notebook Problem 14.20)

Kourovka Notebook, Problem 14.20 (G. Baumslag, A. G. Myasnikov, V. N. Remeslennikov): does a free
product of two groups have the Noetherian Equation Property if both factors have it?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.FreeProductEquationallyNoetherianKourovka14Problem20Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.20 (G. Baumslag, A. G. Myasnikov, V. N.
Remeslennikov). UnsolvedMath record UM-00701005 (`KOU-14.20`), dataset ulamai/UnsolvedMath v1.8.0.

Equations and the Noetherian Equation Property as in
`HyperbolicEquationallyNoetherianKourovka14Problem19Wanted`; the free product is `Monoid.Coprod G
H`. The problem concerns two factors; free products of infinitely many equationally Noetherian
groups can fail (Groves-Hull).
-/

/-- The value at the assignment `x : Fin n → G` of a word `w ∈ G ∗ F(x₀, …, xₙ₋₁)` (an equation
over `G` with coefficients in `G` and unknowns `x₀, …, xₙ₋₁`). -/
def evalEquation {G : Type*} [Group G] {n : ℕ} (x : Fin n → G) :
    Monoid.Coprod G (FreeGroup (Fin n)) →* G :=
  Monoid.Coprod.lift (MonoidHom.id G) (FreeGroup.lift x)

/-- The solution set in `G` of the system of equations `S`. -/
def solutions {G : Type*} [Group G] {n : ℕ} (S : Set (Monoid.Coprod G (FreeGroup (Fin n)))) :
    Set (Fin n → G) :=
  {x | ∀ w ∈ S, evalEquation x w = 1}

/-- `G` has the Noetherian Equation Property (is equationally Noetherian): every system of
equations over `G` in finitely many unknowns has the same solutions as some finite subsystem. -/
def EquationallyNoetherian (G : Type*) [Group G] : Prop :=
  ∀ (n : ℕ) (S : Set (Monoid.Coprod G (FreeGroup (Fin n)))),
    ∃ S₀ ⊆ S, S₀.Finite ∧ solutions S₀ = solutions S

/-- Kourovka 14.20 (G. Baumslag, A. G. Myasnikov, V. N. Remeslennikov): the free product `G ∗ H` of
two groups with the Noetherian Equation Property has the Noetherian Equation Property. -/
def freeProductEquationallyNoetherian : Prop :=
  ∀ (G H : Type) [Group G] [Group H], EquationallyNoetherian G → EquationallyNoetherian H →
    EquationallyNoetherian (Monoid.Coprod G H)

/--
Resolved true: the Kourovka Notebook (21st issue) answers 14.20 "Yes, it does", citing Sela's
preprint (Theorem 9.1): the free product of two equationally Noetherian groups is equationally
Noetherian. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.20 (G. Baumslag, A. G.
Myasnikov, V. N. Remeslennikov); resolution: Z. Sela, Diophantine geometry over groups X: The
elementary theory of free products of groups, preprint, arXiv:1012.0044 (2010), Section 9, Theorem
9.1: the free product of two equationally Noetherian groups is equationally Noetherian; the Kourovka
Notebook (21st issue) marks 14.20 solved (Yes, it does), citing this preprint,
https://arxiv.org/abs/1012.0044.
-/
public theorem_wanted freeProductEquationallyNoetherian_holds : freeProductEquationallyNoetherian

end MathlibExt.GroupTheory.FreeProductEquationallyNoetherianKourovka14Problem20Wanted
