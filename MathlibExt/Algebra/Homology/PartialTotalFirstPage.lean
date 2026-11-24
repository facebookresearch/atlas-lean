/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.PartialTotalCoreInterval

/-!
# First-page objects of the partial-total spectral object

This file identifies the homology object attached to a core interval with
the corresponding signed-row homology.  Under the exact
`HasSpectralSequence` hypothesis required by Mathlib, it packages this as an
isomorphism from the actual first-page object.

No `HasSpectralSequence` instance, differential formula, E₂ computation, or
convergence theorem is proved here.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

/-- The `H`-object of the mapped spectral object on the interval selected by
the increasing core is the green mapping-cone homology object of the uniform
filtration step. -/
noncomputable def partialTotalSpectralObjectHStepIso (p q : ℕ) :
    ((B.partialTotalSpectralObject.H ((core).deg (p, q))).obj
        (CategoryTheory.ComposableArrows.mk₁
          (homOfLE ((core).le₁₂ (p, q))))) ≅
      B.partialTotalStepE₁Homology p q :=
  B.partialTotalSpectralObjectHObjIso ((core).deg (p, q))
      ((core).le₁₂ (p, q)) ≪≫
    HomologicalComplex.homologyMapIso
      ((HomotopyCategory.composableArrowsFunctor C).mapIso
        (B.partialTotalE₁CochainStepIso p q))
      ((core).deg (p, q))

section Page

variable [B.partialTotalSpectralObject.HasSpectralSequence core]

set_option backward.isDefEq.respectTransparency false in
/-- The actual first-page object at `(p,q)` is canonically the homology of
the signed `p`th row in total degree `p+q`.

The only hypothesis beyond abelianness is Mathlib's exact
`HasSpectralSequence` condition for the custom increasing core. -/
noncomputable def partialTotalSpectralSequenceFirstPageRowIso (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).X (p, q) ≅
      (B.totalRow p).homology (p + q) :=
  B.partialTotalSpectralObject.spectralSequenceFirstPageXIso core (p, q)
      ((core).i₁ (p, q)) ((core).i₂ (p, q)) rfl rfl
      ((core).deg (p, q)) rfl ≪≫
    B.partialTotalSpectralObjectHStepIso p q ≪≫
    B.partialTotalStepE₁HomologyIso p q

/-- The first-page object at `(p,q)` in a chosen total degree `n=p+q`. -/
noncomputable def partialTotalSpectralSequenceFirstPageRowIsoAt
    (p q n : ℕ) (h : p + q = n) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).X (p, q) ≅
      (B.totalRow p).homology n :=
  B.partialTotalSpectralObject.spectralSequenceFirstPageXIso core (p, q)
      ((core).i₁ (p, q)) ((core).i₂ (p, q)) rfl rfl
      ((core).deg (p, q)) rfl ≪≫
    B.partialTotalSpectralObjectHStepIso p q ≪≫
    B.partialTotalStepE₁HomologyIsoAt p q n h

end Page

end HomologicalComplex₂

end
