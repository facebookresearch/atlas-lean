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


public import MathlibExt.Algebra.Homology.CartanEilenberg.TensorSecondPage
public import MathlibExt.Algebra.Homology.PartialTotalStablePage
public import MathlibExt.Algebra.Homology.CartanEilenberg.TensorAbutment

/-!
# The ordinary Künneth spectral-sequence filtration

For a supplied Cartan--Eilenberg resolution and a degreewise-flat first
complex, the finite partial-total filtration is transported along the
canonical ordinary-tensor abutment isomorphism.  Its diagram and adjacent
graded objects remain the generic CE ones; only the inclusions acquire the
abutment map.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace HomologicalComplex

variable {R : Type u} [CommRing R]
variable (K : ChainComplex (ModuleCat.{u} R) ℕ)
variable {L : ChainComplex (ModuleCat.{u} R) ℕ}
variable (P : CartanEilenbergResolution L)
variable (hK : ∀ i : ℕ, Module.Flat R (K.X i))

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

/-- The partial-total image filtration transported to ordinary tensor-product
homology through the canonical Cartan--Eilenberg abutment isomorphism. -/
noncomputable def kunnethHomologyFiltration (n : ℕ) :
    Filtration ((tensorObj K L).homology n) EInt where
  toMonoOver :=
    ((kunnethCEBicomplex K P).partialTotalHomologyFiltration n).toMonoOver ⋙
      MonoOver.map (tensorCartanEilenbergAbutmentIso K P hK n).hom

/-- The explicit stable page is the adjacent graded piece of the ordinary
tensor-homology filtration. -/
noncomputable def kunnethStablePageGradedIso (p q : ℕ) :
    (((kunnethCEBicomplex K P).partialTotalSpectralObject.spectralSequence
        core).page (((p + q + 2 : ℕ) : ℤ))).X (p, q) ≅
      cokernel
        ((kunnethHomologyFiltration K P hK (p + q)).diagram.map
          (homOfLE (HomologicalComplex₂.partialTotalHomologyPreviousIndex_le p))) := by
  change
    (((kunnethCEBicomplex K P).partialTotalSpectralObject.spectralSequence
        core).page (((p + q + 2 : ℕ) : ℤ))).X (p, q) ≅
      cokernel
        (((kunnethCEBicomplex K P).partialTotalHomologyFiltration
          (p + q)).diagram.map
            (homOfLE (HomologicalComplex₂.partialTotalHomologyPreviousIndex_le p)))
  exact (kunnethCEBicomplex K P).partialTotalStablePageGradedIso p q

/-- The ordinary-target stable-page coordinate has the literal generic
partial-total grading morphism. -/
theorem kunnethStablePageGradedIso_hom (p q : ℕ) :
    (kunnethStablePageGradedIso K P hK p q).hom =
      ((kunnethCEBicomplex K P).partialTotalStablePageGradedIso p q).hom :=
  rfl

end HomologicalComplex

end
