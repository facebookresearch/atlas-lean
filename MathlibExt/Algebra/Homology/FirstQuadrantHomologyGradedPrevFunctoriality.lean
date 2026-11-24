/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedCurrentFunctoriality

/-!
# Functoriality of the positive predecessor homology-filtration map

At a positive column, the map on the preceding complete-filtration stage is
transported from finite stage `p - 1`.  These transported maps preserve
identities and composition by the finite filtered-object functor laws and
cancellation of the positive predecessor comparison isomorphisms.

This file proves no law for the unified predecessor map at `p = 0` and does
not package the predecessor maps as a functor.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The transported positive predecessor-stage map of an identity bicomplex
morphism is the identity. -/
@[simp 1100]
theorem horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_id
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) (hp : 0 < p) :
    horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
        (𝟙 K) p q hp = 𝟙 _ := by
  let F := horizontalFiniteTotalHomologyFilteredObjectFunctor
    (C := C) (p + q)
  let e := horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
    K (p + q) p hp
  have hId := congrArg CategoryTheory.FilteredObject.Hom.natTrans
    (F.map_id K)
  have hIdApp :
      ((horizontalFiniteTotalHomologyFilteredObjectFunctor
        (C := C) (p + q)).map (𝟙 K)).natTrans.app (p - 1) =
        𝟙 ((horizontalFiniteTotalHomologyFiltration K
          (p + q)).diagram.obj (p - 1)) := by
    have hIdApp := NatTrans.congr_app hId (p - 1)
    change ((horizontalFiniteTotalHomologyFilteredObjectFunctor
      (C := C) (p + q)).map (𝟙 K)).natTrans.app (p - 1) =
        𝟙 ((horizontalFiniteTotalHomologyFiltration K
          (p + q)).diagram.obj (p - 1)) at hIdApp
    exact hIdApp
  change e.hom ≫
    ((horizontalFiniteTotalHomologyFilteredObjectFunctor
      (C := C) (p + q)).map (𝟙 K)).natTrans.app (p - 1) ≫ e.inv = 𝟙 _
  rw [hIdApp]
  rw [Category.id_comp]
  exact e.hom_inv_id

/-- Transported positive predecessor-stage maps preserve composition of
bicomplex morphisms. -/
@[simp 1100]
theorem horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_comp
    (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) (hp : 0 < p) :
    horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
        (f ≫ g) p q hp =
      horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex f p q hp ≫
        horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex g p q hp := by
  let F := horizontalFiniteTotalHomologyFilteredObjectFunctor
    (C := C) (p + q)
  let eK := horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
    K (p + q) p hp
  let eL := horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
    L (p + q) p hp
  let eM := horizontalPositivePrevCompleteFiniteHomologyFiltrationIso
    M (p + q) p hp
  have hComp := congrArg CategoryTheory.FilteredObject.Hom.natTrans
    (F.map_comp f g)
  have hCompApp := NatTrans.congr_app hComp (p - 1)
  change (F.map (f ≫ g)).natTrans.app (p - 1) =
    (F.map f).natTrans.app (p - 1) ≫
      (F.map g).natTrans.app (p - 1) at hCompApp
  change eK.hom ≫ (F.map (f ≫ g)).natTrans.app (p - 1) ≫ eM.inv =
    (eK.hom ≫ (F.map f).natTrans.app (p - 1) ≫ eL.inv) ≫
      (eL.hom ≫ (F.map g).natTrans.app (p - 1) ≫ eM.inv)
  rw [hCompApp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end HomologicalComplex₂

end
