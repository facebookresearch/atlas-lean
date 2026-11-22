/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hyperbolic groups are equationally Noetherian (Kourovka Notebook Problem 14.19)

Kourovka Notebook, Problem 14.19 (G. Baumslag, A. G. Myasnikov, V. N. Remeslennikov): a group has
the Noetherian Equation Property if every system of equations over it in finitely many variables is
equivalent to some finite part of it. Does every hyperbolic group have it?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Coprod.Basic
public import MathlibExt.GroupTheory.HyperbolicGroup

@[expose] public section

namespace MathlibExt.GroupTheory.HyperbolicEquationallyNoetherianKourovka14Problem19Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.19 (G. Baumslag, A. G. Myasnikov, V. N.
Remeslennikov). UnsolvedMath record UM-00701004 (`KOU-14.19`), dataset ulamai/UnsolvedMath v1.8.0.

An equation over `G` in the unknowns `x₀, …, xₙ₋₁` is an element of `G ∗ F(x₀, …, xₙ₋₁)`
(`Monoid.Coprod`); its solutions are assignments `x : Fin n → G` at which it evaluates to `1`.
Equivalent systems have the same solution sets. Hyperbolic is `Group.IsHyperbolic` from `MathlibExt`
(some finite generating family has a Gromov-hyperbolic word metric).
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

/-- Kourovka 14.19 (G. Baumslag, A. G. Myasnikov, V. N. Remeslennikov): every word-hyperbolic
group has the Noetherian Equation Property. -/
def hyperbolicGroupEquationallyNoetherian : Prop :=
  ∀ (G : Type) [Group G], Group.IsHyperbolic G → EquationallyNoetherian G

/--
Resolved true: Weidmann and Reinfeldt prove that every hyperbolic group is equationally Noetherian
(Sela had the torsion-free case); the Kourovka Notebook (21st issue) answers 14.19 "Yes, it does".
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.19 (G. Baumslag, A. G. Myasnikov, V. N.
Remeslennikov); resolution: R. Weidmann and C. Reinfeldt, Ann. Math. Blaise Pascal 26 (2019), no. 2,
125-214, the Kourovka Notebook (21st issue) marks 14.19 solved (Yes); the torsion-free case is due
to Z. Sela, Proc. London Math. Soc. 99 (2009), 217-273.
-/
public theorem_wanted hyperbolicGroupEquationallyNoetherian_holds :
    hyperbolicGroupEquationallyNoetherian

end MathlibExt.GroupTheory.HyperbolicEquationallyNoetherianKourovka14Problem19Wanted
