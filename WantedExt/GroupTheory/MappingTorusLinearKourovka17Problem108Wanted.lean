/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linearity of a mapping torus of the free group of rank two (Kourovka Notebook Problem 17.108)

Kourovka Notebook, Archive of Solved Problems, Problem 17.108 (M. Sapir): is the group `⟨a, b, t |
a^t = ab, b^t = ba⟩` linear? If not, this would be an easy example of a non-linear hyperbolic group.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.MappingTorusLinearKourovka17Problem108Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.108 (M.
Sapir). UnsolvedMath record UM-00701409 (`KOU-17.108`), dataset ulamai/UnsolvedMath v1.8.0.

`a^t = t⁻¹ a t`; the other convention `t a t⁻¹` gives an isomorphic group (replace `t` by `t⁻¹`).
The target is the Archive's form: the group embeds in `GL_n(ℤ)` for some `n`, which implies
linearity over the field `ℚ`.
-/

/-- The group `⟨a, b, t | a^t = ab, b^t = ba⟩` (M. Sapir), with `a^t = t⁻¹ a t`; the generators
are `a = x₀`, `b = x₁`, `t = x₂`. -/
abbrev SapirGroup : Type :=
  PresentedGroup ({(FreeGroup.of 2)⁻¹ * FreeGroup.of 0 * FreeGroup.of 2 *
      (FreeGroup.of 0 * FreeGroup.of 1)⁻¹,
    (FreeGroup.of 2)⁻¹ * FreeGroup.of 1 * FreeGroup.of 2 * (FreeGroup.of 1 * FreeGroup.of 0)⁻¹} :
      Set (FreeGroup (Fin 3)))

/-- Kourovka 17.108 (M. Sapir), in the form of its resolution: the group
`⟨a, b, t | a^t = ab, b^t = ba⟩` is `ℤ`-linear, that is, it embeds in `GL_n(ℤ)` for some `n`. -/
def sapirGroupIntegerLinear : Prop :=
  ∃ n : ℕ, ∃ f : SapirGroup →* Matrix.GeneralLinearGroup (Fin n) ℤ, Function.Injective f

/--
Resolved true: the Kourovka Archive answers 17.108 "Yes, this group is linear" (M. F. Hagen, letter
of 6 August 2018): the group is the mapping torus of an irreducible atoroidal self-monomorphism of a
free group, so it is virtually special and hence `ℤ`-linear by Theorem B of Hagen and Wise (2016).
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.108 (M.
Sapir); resolution: M. F. Hagen, letter of 6 August 2018, as recorded in the Kourovka Archive; M. F.
Hagen and D. T. Wise, Duke Math. J. 165 (2016), 1753-1813, Kourovka Archive, Problem 17.108 (Yes,
this group is linear: as noticed by M. Sapir it is the mapping torus of an irreducible atoroidal
self-monomorphism of a free group, hence virtually special, hence Z-linear by Theorem B of
Hagen-Wise).
-/
public theorem_wanted sapirGroupIntegerLinear_holds : sapirGroupIntegerLinear

end MathlibExt.GroupTheory.MappingTorusLinearKourovka17Problem108Wanted
