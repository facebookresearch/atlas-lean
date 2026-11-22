/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Thompson's group F is not Howson (Kourovka Notebook Problem 19.40)

Kourovka Notebook, Archive of Solved Problems, Problem 19.40 (I. Kapovich): does Thompson's group
`F` have the Howson property, that is, is the intersection of any two finitely generated subgroups
of `F` finitely generated?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.ThompsonGroupHowsonKourovka19Problem40Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.40 (I.
Kapovich). UnsolvedMath record UM-00701588 (`KOU-19.40`), dataset ulamai/UnsolvedMath v1.8.0.

`F` is the presented group `⟨x₀, x₁ | [x₀x₁⁻¹, x₀⁻¹x₁x₀], [x₀x₁⁻¹, x₀⁻²x₁x₀²]⟩`, the standard
two-relator presentation (as in the introductory notes of Cannon, Floyd and Parry), with `[a, b] = a
b a⁻¹ b⁻¹`.
-/

/-- The relators of the standard presentation `⟨x₀, x₁ | [x₀x₁⁻¹, x₀⁻¹x₁x₀], [x₀x₁⁻¹, x₀⁻²x₁x₀²]⟩`
of Thompson's group `F`, with `[a, b] = a b a⁻¹ b⁻¹`. -/
def thompsonRelators : Set (FreeGroup (Fin 2)) :=
  let x₀ := FreeGroup.of (0 : Fin 2)
  let x₁ := FreeGroup.of (1 : Fin 2)
  let a := x₀ * x₁⁻¹
  let b := x₀⁻¹ * x₁ * x₀
  let c := x₀⁻¹ ^ 2 * x₁ * x₀ ^ 2
  {a * b * a⁻¹ * b⁻¹, a * c * a⁻¹ * c⁻¹}

/-- Thompson's group `F`. -/
abbrev ThompsonF := PresentedGroup thompsonRelators

/-- Kourovka 19.40 (I. Kapovich): Thompson's group `F` has the Howson property: the intersection of
any two finitely generated subgroups is finitely generated. -/
def thompsonFHowson : Prop :=
  ∀ H K : Subgroup ThompsonF, H.FG → K.FG → (H ⊓ K).FG

/--
Resolved false: the Kourovka Archive answers 19.40 "No": `ℤ ≀ ℤ` fails the Howson property
(Kirkinskiĭ) and embeds in `F` (Cleary), and the property is inherited by subgroups. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.40 (I. Kapovich);
resolution: A. S. Kirkinskiĭ, Algebra Logic 20 (1981), no. 1, 24-36; S. Cleary, Pacific J. Math. 228
(2006), no. 1, 53-61; D. Robertson, letter of 24 April 2018, Kourovka Archive, Problem 19.40: No; ℤ
≀ ℤ does not have the Howson property (Kirkinskiĭ) and embeds in F (Cleary), and the Howson property
passes to subgroups, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted thompsonFHowson_refuted : ¬ thompsonFHowson

end MathlibExt.GroupTheory.ThompsonGroupHowsonKourovka19Problem40Wanted
