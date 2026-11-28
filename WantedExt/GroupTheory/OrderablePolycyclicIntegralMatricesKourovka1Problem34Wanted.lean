/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `e4e4de3e175eab51e689706fcab2456068d90482`.

Original formalization by Adam Kiezun, with contributions by Metamate
(consolidation commit `f204b2a6`, PR #9859); ported with attribution.
-/

/-
# Integral matrix representations of orderable polycyclic groups (Kourovka Notebook Problem 1.34)

Kourovka Notebook, Archive of Solved Problems, Problem 1.34 (M. I. Kargapolov): has every orderable
polycyclic group a faithful representation by matrices over the integers?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Solvable
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import MathlibExt.GroupTheory.Orderability
public import MathlibExt.GroupTheory.GroupClassesShared

@[expose] public section

namespace MathlibExt.GroupTheory.OrderablePolycyclicIntegralMatricesKourovka1Problem34Wanted

open MathlibExt.GroupTheory.GroupClassesShared

export MathlibExt.GroupTheory (IsBiInvariantOrder IsOrderable)

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.34 (M. I.
Kargapolov). UnsolvedMath record UM-00700029 (`KOU-1.34`), dataset ulamai/UnsolvedMath v1.8.0.

"Orderable" is the Kokorin-Kopytov sense of the problem list (fully ordered): `G` admits a linear
order invariant under multiplication on both sides (`IsOrderable`). Polycyclic is the
finite-series notion (`IsPolycyclic` in `GroupClassesShared`), equivalent by Hirsch's theorem
to soluble with every subgroup finitely generated. A faithful representation is an
injective homomorphism into some `GL_n(ℤ)`. The resolution covers all polycyclic groups; the
orderability hypothesis of the problem is kept.
-/

/-- Kourovka 1.34 (M. I. Kargapolov): every orderable polycyclic group has a faithful
representation by integer matrices, an injective homomorphism into some `GL_n(ℤ)`. -/
def orderablePolycyclicEmbedsInGLnZ : Prop :=
  ∀ (G : Type) [Group G], IsPolycyclic G → IsOrderable G →
    ∃ (n : ℕ) (f : G →* GL (Fin n) ℤ), Function.Injective f

/--
Resolved true: the Kourovka Archive answers 1.34 "Yes, it has", citing Auslander and Swan, who prove
that every polycyclic group, orderable or not, has a faithful representation in some `GL_n(ℤ)`.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.34 (M. I.
Kargapolov); resolution: L. Auslander, On a problem of Philip Hall, Ann. Math. (2) 86 (1967),
112-117; R. G. Swan, Representations of polycyclic groups, Proc. Amer. Math. Soc. 18 (1967),
573-574, Kourovka Archive, Problem 1.34 (Yes, it has); every polycyclic group embeds in some
GL_n(ℤ).
-/
public theorem_wanted orderablePolycyclicEmbedsInGLnZ_holds : orderablePolycyclicEmbedsInGLnZ

private example : ProofWanted.Stmt orderablePolycyclicEmbedsInGLnZ_holds ↔
    orderablePolycyclicEmbedsInGLnZ :=
  Iff.rfl

end MathlibExt.GroupTheory.OrderablePolycyclicIntegralMatricesKourovka1Problem34Wanted
