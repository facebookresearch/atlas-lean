/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageMappingConeNaturality
public import MathlibExt.Algebra.Homology.FirstQuadrantSecondPageMap

/-!
# Naturality of the coherent first-page presentation

The map on the first page of the horizontal-filtration spectral sequence
commutes with the canonical identification of a page object as relative
homology of its coherent complete-filtration window.  This is the
first-quadrant specialization of generic first-page page-map naturality.

No direct-column, normalized-row, second-page, or Bousfield--Kan comparison
is asserted here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits ComposableArrows
open CategoryTheory.Abelian.SpectralObject

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

local notation "data" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- The page-one map commutes with the coherent relative-homology
identification. -/
@[reassoc]
theorem horizontalFirstPageCoherentXIso_hom_naturality_of_bicomplex
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalPageMapOfBicomplex f 1 (by omega)).f (p, q) ≫
        (horizontalFirstPageCoherentXIso L p q).hom =
      (horizontalFirstPageCoherentXIso K p q).hom ≫
        ((horizontalCompleteFiltrationSpectralObjectMap f).hom
          (-(p : ℤ) - q)).app
            (mk₁ (homOfLE
              (horizontalFirstPageCoherentIndex_le p))) := by
  rw [horizontalPageMapOfBicomplex_f]
  unfold horizontalFirstPageCoherentXIso
  simpa only using
    Hom.pageMapComponent_spectralSequenceFirstPageXIso_hom
        (horizontalCompleteFiltrationSpectralObjectMap f) data (p, q)
        (horizontalFirstPageCoherentLowerIndex p)
        (horizontalFirstPageUpperIndex p)
        (horizontalFirstPageCoherentLowerIndex_eq_i₁ p q)
        (horizontalFirstPageUpperIndex_eq_i₂ p q)
        (-(p : ℤ) - q - 1) (-(p : ℤ) - q)
        (-(p : ℤ) - q + 1) (horizontalFirstPageDegree_eq p q)
        (by omega) (by omega)

end HomologicalComplex₂

end
