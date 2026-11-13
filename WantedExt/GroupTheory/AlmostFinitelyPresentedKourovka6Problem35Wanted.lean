/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Almost finitely presented groups that are not finitely presented (Kourovka Notebook Problem 6.35)

Kourovka Notebook, Archive of Solved Problems, Problem 6.35 (Yu. I. Merzlyakov; question of R. Bieri
and R. Strebel): a group G is almost finitely presented over a ring 𝔬 if it has a presentation G =
F/R with F a finitely generated free group and the 𝔬G-module R/[R, R] ⊗ 𝔬 finitely generated. Every
finitely presented group is almost finitely presented over ℤ, hence over every 𝔬. Is the converse
true?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FinitelyPresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.AlmostFinitelyPresentedKourovka6Problem35Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.35 (Yu. I.
Merzlyakov; question of R. Bieri and R. Strebel). UnsolvedMath record UM-00700380 (`KOU-6.35`),
dataset ulamai/UnsolvedMath v1.8.0.

The target is the converse for `𝔬 = ℤ`; a group almost finitely presented over `ℤ` is almost
finitely presented over every `𝔬`, so its refutation refutes the converse for every ring `𝔬`. The
relation module `R ⧸ [R, R]` (with `G` acting by conjugation) is generated as a `ℤG`-module by the
images of a finite set `S ⊆ R` exactly when `R` is the product of the normal closure of `S` in `F`
and `[R, R]`; the target uses this form. Finitely presented is Mathlib's
`Group.IsFinitelyPresented`.
-/

/-- Kourovka 6.35 (R. Bieri, R. Strebel; Yu. I. Merzlyakov): every group that is almost finitely
presented over `ℤ` is finitely presented. `G = F ⧸ R` with `F` free of finite rank is almost
finitely presented over `ℤ` when the relation module `R ⧸ [R, R]` is a finitely generated
`ℤG`-module, i.e. `R = ⟨⟨S⟩⟩ [R, R]` for a finite set `S`. -/
def almostFinitelyPresentedIsFinitelyPresented : Prop :=
  ∀ (G : Type) [Group G] (n : ℕ) (φ : FreeGroup (Fin n) →* G), Function.Surjective φ →
    (∃ S : Finset (FreeGroup (Fin n)),
      φ.ker = Subgroup.normalClosure (S : Set (FreeGroup (Fin n))) ⊔ ⁅φ.ker, φ.ker⁆) →
    Group.IsFinitelyPresented G

/--
Resolved false: the Kourovka Archive answers 6.35 "No, it is not true", citing Bestvina and Brady
(1997), whose groups of type `FP` over `ℤ` that are not finitely presented are almost finitely
presented over `ℤ` (hence over every ring). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 6.35 (Yu. I. Merzlyakov; question of R. Bieri and R. Strebel); resolution:
M. Bestvina and N. Brady, Morse theory and finiteness properties of groups, Invent. Math. 129, no. 3
(1997), 445-470, Main Theorem: for a finite flag complex L the kernel H_L of the right-angled Artin
group G_L → ℤ is of type FP(R) if and only if L is R-acyclic and is finitely presented if and only
if L is simply connected, so an acyclic flag complex that is not simply connected gives a group of
type FP over ℤ (in particular FP₂, i.e. almost finitely presented over ℤ) that is not finitely
presented (zbMATH review Zbl 0888.20021); Kourovka Archive, Problem 6.35: No, it is not true
(Bestvina, Brady), https://doi.org/10.1007/s002220050168.
-/
public theorem_wanted almostFinitelyPresentedIsFinitelyPresented_refuted :
    ¬ almostFinitelyPresentedIsFinitelyPresented

end MathlibExt.GroupTheory.AlmostFinitelyPresentedKourovka6Problem35Wanted
