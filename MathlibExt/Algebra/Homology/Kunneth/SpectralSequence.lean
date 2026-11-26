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
# The Künneth filtration on ordinary tensor homology

Let `R` be a commutative ring, `K,L` nonnegative module chain complexes in the common
universe, and `P` a Cartan–Eilenberg resolution of `L`. Assume every term of `K` is flat over
`R`.

Transport the partial-total image filtration of the tensor resolution bicomplex to `H_n(K ⊗
L)` through the ordinary tensor abutment isomorphism. At bidegree `(p,q)`, page `p+q+2` is the
adjacent graded cokernel of this filtration in total degree `p+q`. Its comparison map is the
partial-total grading map.
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

/-- The transported Künneth filtration of ordinary tensor homology.

For a supplied Cartan–Eilenberg resolution and termwise-flat first complex, postcompose
partial-total homology filtration inclusions with the tensor abutment isomorphism. -/
noncomputable def kunnethHomologyFiltration (n : ℕ) :
    Filtration ((tensorObj K L).homology n) EInt where
  toMonoOver :=
    ((kunnethCEBicomplex K P).partialTotalHomologyFiltration n).toMonoOver ⋙
      MonoOver.map (tensorCartanEilenbergAbutmentIso K P hK n).hom

/-- The stable Künneth page as an adjacent homology-filtration quotient.

At `(p,q)`, page `p+q+2` is isomorphic to the cokernel of the preceding-to-current filtration
map on `H_(p+q)(K ⊗ L)`. -/
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

/-- The partial-total map of the stable Künneth graded comparison.

The forward ordinary-tensor filtration comparison is the forward partial-total stable-page
grading isomorphism. -/
theorem kunnethStablePageGradedIso_hom (p q : ℕ) :
    (kunnethStablePageGradedIso K P hK p q).hom =
      ((kunnethCEBicomplex K P).partialTotalStablePageGradedIso p q).hom :=
  rfl

end HomologicalComplex

end
