/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Decidability of equations in free groups (Kourovka Notebook Problem 1.18)

Kourovka Notebook, Archive of Solved Problems, Problem 1.18 (A. Tarski; Yu. L. Ershov): a) does
there exist an algorithm for determining the solubility of equations in a free group? b) describe
the structure of all solutions of an equation when it has at least one solution.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.FreeGroupEquationsDecidableKourovka1Problem18Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.18 (A.
Tarski; Yu. L. Ershov). UnsolvedMath record UM-00700014 (`KOU-1.18`), dataset ulamai/UnsolvedMath
v1.8.0.

Only part (a) is formalized; part (b) asks for a description, not a proposition. An equation over
`Fₖ` with unknowns `x₀, x₁, …` is a word in the generators of `Fₖ` (constants) and the unknowns,
coded as a list of letters, so equations form a `Primcodable` type; it is solvable if some
assignment of elements of `Fₖ` to the unknowns makes it trivial. Decidability is `ComputablePred`,
for each finite rank `k`, uniformly in the number of unknowns.
-/

/-- An equation over the free group `F_k = FreeGroup (Fin k)` in the unknowns `x₀, x₁, …`: a word
in the letters `(Sum.inl a, b)` (the generator `a` of `F_k`, inverted when `b = false`) and
`(Sum.inr i, b)` (the unknown `xᵢ`, inverted when `b = false`), read through `FreeGroup.mk`. -/
abbrev Equation (k : ℕ) := List ((Fin k ⊕ ℕ) × Bool)

/-- The equation `w = 1` has a solution in `F_k`: some assignment of elements of `F_k` to the
unknowns makes the left side trivial. -/
def Equation.Solvable {k : ℕ} (w : Equation k) : Prop :=
  ∃ s : ℕ → FreeGroup (Fin k), FreeGroup.lift (Sum.elim FreeGroup.of s) (FreeGroup.mk w) = 1

/-- Kourovka 1.18(a) (A. Tarski): for every finite rank `k`, solubility of equations (with
constants) in the free group `F_k` is decidable. -/
def freeGroupEquationSolvabilityDecidable : Prop :=
  ∀ k : ℕ, ComputablePred (Equation.Solvable (k := k))

/--
Resolved true: the Kourovka Archive answers 1.18(a) "Yes, there does", citing Makanin's algorithm
deciding whether an equation with constants in a free group has a solution. Source: E. I. Khukhro
and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.18 (A. Tarski; Yu. L. Ershov);
resolution: G. S. Makanin, Equations in a free group, Math. USSR-Izv. 21 (1983), 483-546; G. S.
Makanin, Decidability of the universal and positive theories of a free group, Math. USSR-Izv. 25
(1985), 75-88, Kourovka Archive, Problem 1.18 (a): Yes, there does.
-/
public theorem_wanted freeGroupEquationSolvabilityDecidable_holds :
    freeGroupEquationSolvabilityDecidable

end MathlibExt.GroupTheory.FreeGroupEquationsDecidableKourovka1Problem18Wanted
