/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageMappingConeNaturality
public import MathlibExt.Algebra.Homology.FirstQuadrantSecondPageMap

/-!
# First-page maps in coherent relative-homology coordinates

Let f : K → L be a map of nonnegative homological bicomplexes in an
abelian category C. In column p, use the complete filtration window
F_(ℓ_p) → F_p, where ℓ_0=−1 and ℓ_(p+1)=p.

The coherent first-page isomorphism identifies E¹_(p,q) with the
relative homology of this window in cochain degree −p−q.
The first-page morphism induced by f commutes with this isomorphism:
θ_L ∘ E¹(f)_(p,q) = H_(−p−q)(window(f)) ∘ θ_K.
The relative map is the interval component of the complete abelian
spectral-object morphism. The category object and morphism worlds
remain independent.
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
/-- For a map f : K → L of nonnegative homological bicomplexes
in an abelian category and p,q ≥ 0, let θ_K,θ_L identify the
first-page objects with the coherent window homology in degree
−p−q. Then
θ_L ∘ E¹(f)_(p,q) = H_(−p−q)(window(f)) ∘ θ_K.
The window endpoints are ℓ_0=−1, ℓ_(p+1)=p and upper endpoint p;
its relative map is induced by the complete spectral morphism of f. -/
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
