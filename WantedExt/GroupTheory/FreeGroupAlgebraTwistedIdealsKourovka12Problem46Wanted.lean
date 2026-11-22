/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Twisted right ideals in the group algebra of a free group (Kourovka Notebook Problem 12.46)

Kourovka Notebook, Archive of Solved Problems, Problem 12.46 (P. A. Linnell): let `F` be free on `x,
y`, and for `|a| = |b| = 1` let `ϑ_{a,b}` be the automorphism of `ℂF` with `x ↦ a x`, `y ↦ b y`.
Given `0 ≠ α ∈ ℂF`, can we always find `a, b ∈ ℂ ∖ {1}` with `|a| = |b| = 1` such that `α ℂF ∩
ϑ_{a,b}(α) ℂF ≠ 0`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.FreeGroupAlgebraTwistedIdealsKourovka12Problem46Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.46 (P. A.
Linnell). UnsolvedMath record UM-00700865 (`KOU-12.46`), dataset ulamai/UnsolvedMath v1.8.0.

`ℂF` is `MonoidAlgebra ℂ F`; `ϑ_{a,b}` multiplies the coefficient of `g` by `χ(g)`, where `χ` is the
character with `χ(x) = a`, `χ(y) = b`, which is the algebra automorphism with `x ↦ a x`, `y ↦ b y`.
A nonzero element of `α ℂF ∩ ϑ_{a,b}(α) ℂF` is written `α β = ϑ_{a,b}(α) γ ≠ 0`; `a, b` are units of
absolute value 1 different from 1.
-/

/-- The character of `F = ⟨x, y⟩` with `x ↦ a` and `y ↦ b`. -/
noncomputable def twistCharacter (a b : ℂˣ) : FreeGroup (Fin 2) →* ℂˣ :=
  FreeGroup.lift ![a, b]

/-- `ϑ_{a,b}`: the automorphism of `ℂF` with `g ↦ χ(g) g` for the character `χ` above, so that
`ϑ_{a,b}(x) = a x` and `ϑ_{a,b}(y) = b y`. -/
noncomputable def theta (a b : ℂˣ) (α : MonoidAlgebra ℂ (FreeGroup (Fin 2))) :
    MonoidAlgebra ℂ (FreeGroup (Fin 2)) :=
  α.coeff.sum fun g c => MonoidAlgebra.single g ((twistCharacter a b g : ℂ) * c)

/-- Kourovka 12.46 (P. A. Linnell): for every nonzero `α ∈ ℂF` there are `a, b ∈ ℂ ∖ {1}` with
`|a| = |b| = 1` such that the right ideals `α ℂF` and `ϑ_{a,b}(α) ℂF` intersect nontrivially. -/
def twistedRightIdealsIntersect : Prop :=
  ∀ α : MonoidAlgebra ℂ (FreeGroup (Fin 2)), α ≠ 0 →
    ∃ a b : ℂˣ, ‖(a : ℂ)‖ = 1 ∧ ‖(b : ℂ)‖ = 1 ∧ (a : ℂ) ≠ 1 ∧ (b : ℂ) ≠ 1 ∧
      ∃ β γ : MonoidAlgebra ℂ (FreeGroup (Fin 2)), α * β = theta a b α * γ ∧ α * β ≠ 0

/--
Resolved false: the Kourovka Archive answers 12.46 "No, not always" (A. V. Tushev, 1995): some
nonzero `α ∈ ℂF` has `α ℂF ∩ ϑ_{a,b}(α) ℂF = 0` for all `a, b ≠ 1` with `|a| = |b| = 1`. Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.46 (P. A. Linnell);
resolution: A. V. Tushev, Ukrain. Mat. Zh. 47 (1995), no. 4, 571-572, Kourovka Archive, Problem
12.46: No, not always.
-/
public theorem_wanted twistedRightIdealsIntersect_refuted : ¬ twistedRightIdealsIntersect

end MathlibExt.GroupTheory.FreeGroupAlgebraTwistedIdealsKourovka12Problem46Wanted
