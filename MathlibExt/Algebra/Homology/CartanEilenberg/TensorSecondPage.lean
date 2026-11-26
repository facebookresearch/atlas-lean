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
# The tensor Cartan–Eilenberg second page in Tor coordinates

Let R be a commutative ring and K,L be ℕ-indexed chain complexes in
ModuleCat^u(R). Given a Cartan–Eilenberg resolution P of L, form the
tensor bicomplex associated with K and P and its increasing
partial-total spectral sequence.

In bidegree (p,q), its second page is
E²_(p,q) ≅ ⨁_(i+j=q) Tor_p^R(H_i(K),H_j(L)).
The antidiagonal is finite, with i,j ∈ ℕ and p,q ≥ 0. The comparison
first identifies the second page with homology of the vertical-homology
complex, then uses the canonical vertical-homology comparison, and
finally the Tor resolution comparison. The same formula holds in the
chosen first-page and total-degree coordinates.
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

/-- For a commutative ring R, chain complexes K,L in
ModuleCat^u(R) and a Cartan–Eilenberg resolution P of L, the
tensor partial-total spectral sequence has
E²_(p,q) ≅ ⨁_(i+j=q) Tor_p^R(H_i(K),H_j(L)) for p,q ≥ 0.
The sum ranges over the finite nonnegative antidiagonal of q. -/
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

/-- For the tensor bicomplex of K and a Cartan–Eilenberg
resolution P of L over a commutative ring R, the forward map
E²_(p,q) → ⨁_(i+j=q) Tor_p^R(H_i(K),H_j(L)) is
χ_Tor ∘ H_p(v_q) ∘ χ_page.
Here χ_page is the second-page-to-vertical-homology comparison,
v_q is the canonical isomorphism of vertical-homology complexes,
and χ_Tor is the finite Tor-resolution homology comparison. -/
theorem tensorCartanEilenbergSecondPageIso_hom (p q : ℕ) :
    (tensorCartanEilenbergSecondPageIso K P p q).hom =
      ((kunnethCEBicomplex K P).partialTotalSecondPageVerticalHomologyIso
        p q).hom ≫
      HomologicalComplex.homologyMap
        (kunnethCEVerticalHomologyComplexIso K P q).hom p ≫
      (kunnethTorResolutionHomologyIso K P p q).hom :=
  rfl

/-- For a commutative ring R, K,L ∈ ChainComplex(ModuleCat^u(R),ℕ)
and a Cartan–Eilenberg resolution P of L, the second page in the
canonical first-page choice has
E²_(p,q) ≅ ⨁_(i+j=q) Tor_p^R(H_i(K),H_j(L)).
The choice is that of the tensor bicomplex's partial-total spectral
object, and p,q are arbitrary nonnegative degrees. -/
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
