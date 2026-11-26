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
# Signed-row coordinates on the first page

Let `B` be a first-quadrant bicomplex in an abelian category. Its partial-total filtration has
successive quotients given by the rows `B.totalRow p`, whose degree `p + q` term is `B.X p q`
and whose vertical differential has sign `(-1)^p`. The homology of the core interval for `(p,
q)` is therefore the degree `p + q` homology of this signed row.

When the partial-total spectral object has a spectral sequence for the increasing homological
core, these isomorphisms identify `E¹_(p,q)` with the same signed-row homology. An additional
equality `p + q = n` expresses the coordinate in a specified total degree.
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

/-- Core-interval homology as partial-total step homology.

For natural indices `p` and `q`, the spectral homology of the first core interval in
cochain degree `-p - q` is isomorphic to `B.partialTotalStepE₁Homology p q`. The
isomorphism uses the mapping cone of the inclusion between the two adjacent
partial-total stages. -/
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
/-- First-page homology in signed-row coordinates.

Assume the partial-total spectral object has a spectral sequence for the increasing
homological core. Its first-page object at `(p, q)` is isomorphic to `H_(p+q)(B.totalRow p)`,
with the vertical sign and the total-degree placement carried by `B.totalRow p`. -/
noncomputable def partialTotalSpectralSequenceFirstPageRowIso (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).X (p, q) ≅
      (B.totalRow p).homology (p + q) :=
  B.partialTotalSpectralObject.spectralSequenceFirstPageXIso core (p, q)
      ((core).i₁ (p, q)) ((core).i₂ (p, q)) rfl rfl
      ((core).deg (p, q)) rfl ≪≫
    B.partialTotalSpectralObjectHStepIso p q ≪≫
    B.partialTotalStepE₁HomologyIso p q

/-- First-page row coordinate in a specified total degree.

Under the same spectral-sequence hypothesis, an equality `p + q = n` gives an isomorphism from
the first-page object at `(p, q)` to `H_n(B.totalRow p)`. The change of degree is the homology
transport along this equality. -/
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
