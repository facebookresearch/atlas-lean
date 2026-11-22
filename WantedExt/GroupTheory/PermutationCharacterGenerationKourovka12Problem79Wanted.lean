/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Permutation characters and two-generation (Kourovka Notebook Problem 12.79)

Kourovka Notebook, Archive of Solved Problems, Problem 12.79 (S. P. Strunkov): suppose that `a, b`
are elements of a finite group `G` such that `φ = 1^G - 1_{⟨a⟩}^G - 1_{⟨b⟩}^G - 1_{⟨ab⟩}^G + 2` is a
character of `G`. Is it true that `G = ⟨a, b⟩`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Character

@[expose] public section

namespace MathlibExt.GroupTheory.PermutationCharacterGenerationKourovka12Problem79Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.79 (S. P.
Strunkov). UnsolvedMath record UM-00700897 (`KOU-12.79`), dataset ulamai/UnsolvedMath v1.8.0.

`1^G` is the regular character (the permutation character on `G ⧸ 1`), `1_H^G` the permutation
character on `G ⧸ H`, computed as the number of cosets fixed by `g`, and `2` is twice the trivial
character. A character is the character of a finite-dimensional complex representation.
-/

/-- The permutation character `1_H^G` of `G` on the cosets `G ⧸ H`: `g` is sent to the number of
cosets it fixes. For `H = ⊥` this is the regular character `1^G`. -/
noncomputable def permChar {G : Type*} [Group G] (H : Subgroup G) (g : G) : ℂ :=
  (Nat.card {q : G ⧸ H // g • q = q} : ℂ)

/-- Strunkov's class function
`φ = 1^G - 1_{⟨a⟩}^G - 1_{⟨b⟩}^G - 1_{⟨ab⟩}^G + 2`. -/
noncomputable def strunkovFunction {G : Type*} [Group G] (a b : G) (g : G) : ℂ :=
  permChar ⊥ g - permChar (Subgroup.zpowers a) g - permChar (Subgroup.zpowers b) g -
    permChar (Subgroup.zpowers (a * b)) g + 2

/-- `φ` is a character of `G`: the character of a finite-dimensional complex representation. -/
def IsCharacter {G : Type} [Group G] (φ : G → ℂ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (ρ : Representation ℂ G V), ρ.character = φ

/-- Kourovka 12.79 (S. P. Strunkov): if `a, b` are elements of a finite group `G` such that
`1^G - 1_{⟨a⟩}^G - 1_{⟨b⟩}^G - 1_{⟨ab⟩}^G + 2` is a character of `G`, then `G = ⟨a, b⟩`. -/
def strunkovCharacterImpliesGeneration : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a b : G), IsCharacter (strunkovFunction a b) →
    Subgroup.closure {a, b} = ⊤

/--
Resolved false: the Kourovka Archive gives the counterexample `G = A₄`, `a = b = (1 2 3)` (S. V.
Skresanov, 2019): `φ` takes the values `2, 2, -1, -1` on the classes of `1`, `(12)(34)`, `(123)`,
`(132)`, so it is the sum of the two nontrivial linear characters of `A₄`, while `⟨a, b⟩` has order
3. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.79 (S. P.
Strunkov); resolution: S. V. Skresanov, Algebra Logic 58 (2019), no. 3, 249-253, Kourovka Archive,
Problem 12.79: No, not always; counterexample G = A_4, a = b = (123).
-/
public theorem_wanted strunkovCharacterImpliesGeneration_refuted :
    ¬ strunkovCharacterImpliesGeneration

end MathlibExt.GroupTheory.PermutationCharacterGenerationKourovka12Problem79Wanted
