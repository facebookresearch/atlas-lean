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

public import MathlibExt.Algebra.Homology.CartanEilenberg.TensorCollapse
public import MathlibExt.Algebra.Homology.PartialTotalSecondPageVerticalHomology

/-!
# The tensor Cartan--Eilenberg second page

For a supplied Cartan--Eilenberg resolution, the generic partial-total second
page is identified, via the canonical vertical-homology comparison, with the
finite antidiagonal sum of `Tor` objects.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex

variable {R : Type u} [CommRing R]
variable (K : ChainComplex (ModuleCat.{u} R) ℕ)
variable {L : ChainComplex (ModuleCat.{u} R) ℕ}
variable (P : CartanEilenbergResolution L)

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

local instance : HasFiniteBiproducts (ModuleCat.{u} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

/-- Page two of the tensor Cartan--Eilenberg spectral sequence, in the finite
antidiagonal `Tor` coordinate for the supplied resolution. -/
noncomputable def tensorCartanEilenbergSecondPageIso (p q : ℕ) :
    (((kunnethCEBicomplex K P).partialTotalSpectralObject.spectralSequence
      core).page 2).X (p, q) ≅
      ⨁ fun ij : KunnethAntidiagonal q =>
        ((CategoryTheory.Tor (ModuleCat.{u} R) p).obj
          (K.homology ij.val.1)).obj (L.homology ij.val.2) :=
  (kunnethCEBicomplex K P).partialTotalSecondPageVerticalHomologyIso p q ≪≫
    HomologicalComplex.homologyMapIso
      (kunnethCEVerticalHomologyComplexIso K P q) p ≪≫
    kunnethTorResolutionHomologyIso K P p q

/-- The Künneth page-two coordinate is exactly the generic page coordinate,
homology of the canonical vertical-homology comparison, and the finite `Tor`
coordinate. -/
theorem tensorCartanEilenbergSecondPageIso_hom (p q : ℕ) :
    (tensorCartanEilenbergSecondPageIso K P p q).hom =
      ((kunnethCEBicomplex K P).partialTotalSecondPageVerticalHomologyIso
        p q).hom ≫
      HomologicalComplex.homologyMap
        (kunnethCEVerticalHomologyComplexIso K P q).hom p ≫
      (kunnethTorResolutionHomologyIso K P p q).hom :=
  rfl

/-- Page two of the tensor Cartan--Eilenberg spectral sequence in the chosen
total-degree coordinate, identified with the finite antidiagonal Tor sum. -/
noncomputable def tensorCartanEilenbergSecondPageIsoAt (p q : ℕ) :
    let χ := (kunnethCEBicomplex K P).partialTotalFirstPageChoice
    χ.pageTwo.X (p, q) ≅
      ⨁ fun ij : KunnethAntidiagonal q =>
        ((CategoryTheory.Tor (ModuleCat.{u} R) p).obj
          (K.homology ij.val.1)).obj (L.homology ij.val.2) :=
  let χ := (kunnethCEBicomplex K P).partialTotalFirstPageChoice
  χ.secondPageVerticalHomologyIso p q ≪≫
    HomologicalComplex.homologyMapIso
      (kunnethCEVerticalHomologyComplexIso K P q) p ≪≫
    kunnethTorResolutionHomologyIso K P p q

end HomologicalComplex

end
