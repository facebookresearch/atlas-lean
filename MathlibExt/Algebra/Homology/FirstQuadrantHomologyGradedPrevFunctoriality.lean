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
  rw [horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_eq,
    horizontalFiniteTotalHomologyFilteredObjectFunctor_map_natTrans_app]
  have hId :
      horizontalFiniteHomologyImageMapOfBicomplex (𝟙 K) (p + q) (p - 1) =
        𝟙 ((horizontalFiniteTotalHomologyFiltration K (p + q)).obj (p - 1)) := by
    simpa only [horizontalFiniteTotalHomologyFiltrationDiagramFunctor_map_app,
      NatTrans.id_app, horizontalFiniteTotalHomologyFiltrationDiagramFunctor_obj_obj] using
      NatTrans.congr_app
        ((horizontalFiniteTotalHomologyFiltrationDiagramFunctor
          (C := C) (p + q)).map_id K) (p - 1)
  simpa only [hId, Category.id_comp] using
    (horizontalPositivePrevCompleteFiniteHomologyFiltrationIso K (p + q) p hp).hom_inv_id

/-- Transported positive predecessor-stage maps preserve composition of
bicomplex morphisms. -/
@[simp 1100]
theorem horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_comp
    (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) (hp : 0 < p) :
    horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
        (f ≫ g) p q hp =
      horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex f p q hp ≫
        horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex g p q hp := by
  rw [horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_eq (f ≫ g) p q hp,
    horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_eq f p q hp,
    horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_eq g p q hp,
    horizontalFiniteTotalHomologyFilteredObjectFunctor_map_natTrans_app (p + q) (f ≫ g),
    horizontalFiniteTotalHomologyFilteredObjectFunctor_map_natTrans_app (p + q) f,
    horizontalFiniteTotalHomologyFilteredObjectFunctor_map_natTrans_app (p + q) g]
  have hComp :
      horizontalFiniteHomologyImageMapOfBicomplex (f ≫ g) (p + q) (p - 1) =
        horizontalFiniteHomologyImageMapOfBicomplex f (p + q) (p - 1) ≫
          horizontalFiniteHomologyImageMapOfBicomplex g (p + q) (p - 1) := by
    simpa only [NatTrans.comp_app,
      horizontalFiniteTotalHomologyFiltrationDiagramFunctor_map_app] using
      NatTrans.congr_app
        ((horizontalFiniteTotalHomologyFiltrationDiagramFunctor
          (C := C) (p + q)).map_comp f g) (p - 1)
  rw [hComp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end HomologicalComplex₂

end
