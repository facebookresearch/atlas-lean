/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedMap

/-!
# Functoriality of the current total-homology filtration-stage map

The current-stage map transported through the complete/finite filtration
comparison preserves identities and composition.  Both laws follow by
projecting the corresponding laws of the finite filtered-object functor to
the selected stage and cancelling the comparison isomorphisms.

This file proves no predecessor-map, arrow-functor, or cokernel-functor law.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The transported current-stage map of an identity bicomplex morphism is
the identity. -/
@[simp 1100]
theorem
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_id
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
        (𝟙 K) p q = 𝟙 _ := by
  rw [horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_eq,
    horizontalFiniteTotalHomologyFilteredObjectFunctor_map_natTrans_app]
  have hId :
      horizontalFiniteHomologyImageMapOfBicomplex (𝟙 K) (p + q) p =
        𝟙 ((horizontalFiniteTotalHomologyFiltration K (p + q)).obj p) := by
    simpa only [horizontalFiniteTotalHomologyFiltrationDiagramFunctor_map_app,
      NatTrans.id_app, horizontalFiniteTotalHomologyFiltrationDiagramFunctor_obj_obj] using
      NatTrans.congr_app
        ((horizontalFiniteTotalHomologyFiltrationDiagramFunctor
          (C := C) (p + q)).map_id K) p
  simpa only [hId, Category.id_comp] using
    Iso.hom_inv_id_app (horizontalCompleteFiniteHomologyFiltrationDiagramIso K (p + q)) p

/-- Transported current-stage maps preserve composition of bicomplex
morphisms. -/
@[simp 1100]
theorem
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_comp
    (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
        (f ≫ g) p q =
      horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex g p q := by
  rw [horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_eq (f ≫ g) p q,
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_eq f p q,
    horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex_eq g p q,
    horizontalFiniteTotalHomologyFilteredObjectFunctor_map_natTrans_app (p + q) (f ≫ g),
    horizontalFiniteTotalHomologyFilteredObjectFunctor_map_natTrans_app (p + q) f,
    horizontalFiniteTotalHomologyFilteredObjectFunctor_map_natTrans_app (p + q) g]
  have hComp :
      horizontalFiniteHomologyImageMapOfBicomplex (f ≫ g) (p + q) p =
        horizontalFiniteHomologyImageMapOfBicomplex f (p + q) p ≫
          horizontalFiniteHomologyImageMapOfBicomplex g (p + q) p := by
    simpa only [NatTrans.comp_app,
      horizontalFiniteTotalHomologyFiltrationDiagramFunctor_map_app] using
      NatTrans.congr_app
        ((horizontalFiniteTotalHomologyFiltrationDiagramFunctor
          (C := C) (p + q)).map_comp f g) p
  have hCancel :
      (horizontalCompleteFiniteHomologyFiltrationDiagramIso L (p + q)).inv.app p ≫
        (horizontalCompleteFiniteHomologyFiltrationDiagramIso L (p + q)).hom.app p ≫
          (horizontalFiniteHomologyImageMapOfBicomplex g (p + q) p ≫
            (horizontalCompleteFiniteHomologyFiltrationDiagramIso M (p + q)).inv.app p) =
      horizontalFiniteHomologyImageMapOfBicomplex g (p + q) p ≫
        (horizontalCompleteFiniteHomologyFiltrationDiagramIso M (p + q)).inv.app p := by
    rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rw [hComp]
  simp only [Category.assoc, hCancel]

end HomologicalComplex₂

end
