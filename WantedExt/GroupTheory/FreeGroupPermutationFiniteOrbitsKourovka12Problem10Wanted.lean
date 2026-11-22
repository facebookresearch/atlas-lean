/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Free groups of permutations with finitely many orbits (Kourovka Notebook Problem 12.10)

Kourovka Notebook, Archive of Solved Problems, Problem 12.10 (P. Neumann; A. M. W. Glass): can the
free group on two generators be embedded in `Sym(ℕ)` so that the image of every non-identity element
has only a finite number of orbits?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.GroupAction.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.FreeGroupPermutationFiniteOrbitsKourovka12Problem10Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.10 (A. M. W.
Glass). UnsolvedMath record UM-00700830 (`KOU-12.10`), dataset ulamai/UnsolvedMath v1.8.0.

An embedding is an injective homomorphism `F₂ → Equiv.Perm ℕ`. The orbits of a permutation are the
orbits of the cyclic subgroup it generates.
-/

/-- Kourovka 12.10 (P. Neumann; A. M. W. Glass): the free group of rank 2 embeds in `Sym(ℕ)` so that
every non-identity element has only finitely many orbits on `ℕ` (the orbits of the cyclic subgroup
it generates). -/
def freeGroupEmbedsFiniteOrbits : Prop :=
  ∃ f : FreeGroup (Fin 2) →* Equiv.Perm ℕ, Function.Injective f ∧
    ∀ w : FreeGroup (Fin 2), w ≠ 1 →
      Finite (MulAction.orbitRel.Quotient (Subgroup.zpowers (f w)) ℕ)

/--
Resolved true: the Kourovka Archive answers 12.10 "Yes, it can" (Macpherson): the free group of rank
2 embeds in `Sym(ℕ)` so that every non-identity element has finitely many orbits. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.10 (A. M. W. Glass);
resolution: H. D. Macpherson, in: Ordered groups and infinite permutation groups (Mathematics and
its Applications 354), Kluwer, Dordrecht, 1996, 221-230, Kourovka Archive, Problem 12.10: "Yes, it
can", https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted freeGroupEmbedsFiniteOrbits_holds : freeGroupEmbedsFiniteOrbits

end MathlibExt.GroupTheory.FreeGroupPermutationFiniteOrbitsKourovka12Problem10Wanted
