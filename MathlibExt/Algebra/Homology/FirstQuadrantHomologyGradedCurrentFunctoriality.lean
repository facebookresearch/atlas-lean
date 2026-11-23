/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
  let F := horizontalFiniteTotalHomologyFilteredObjectFunctor
    (C := C) (p + q)
  let e := (horizontalCompleteFiniteHomologyFiltrationDiagramIso
    K (p + q)).app p
  have hId := congrArg CategoryTheory.FilteredObject.Hom.natTrans
    (F.map_id K)
  have hIdApp :
      ((horizontalFiniteTotalHomologyFilteredObjectFunctor
        (C := C) (p + q)).map (𝟙 K)).natTrans.app p =
        𝟙 ((horizontalFiniteTotalHomologyFiltration K
          (p + q)).diagram.obj p) := by
    have hIdApp := NatTrans.congr_app hId p
    change ((horizontalFiniteTotalHomologyFilteredObjectFunctor
      (C := C) (p + q)).map (𝟙 K)).natTrans.app p =
        𝟙 ((horizontalFiniteTotalHomologyFiltration K
          (p + q)).diagram.obj p) at hIdApp
    exact hIdApp
  change e.hom ≫
    ((horizontalFiniteTotalHomologyFilteredObjectFunctor
      (C := C) (p + q)).map (𝟙 K)).natTrans.app p ≫ e.inv = 𝟙 _
  rw [hIdApp]
  rw [Category.id_comp]
  exact e.hom_inv_id

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
  let F := horizontalFiniteTotalHomologyFilteredObjectFunctor
    (C := C) (p + q)
  let eK := (horizontalCompleteFiniteHomologyFiltrationDiagramIso
    K (p + q)).app p
  let eL := (horizontalCompleteFiniteHomologyFiltrationDiagramIso
    L (p + q)).app p
  let eM := (horizontalCompleteFiniteHomologyFiltrationDiagramIso
    M (p + q)).app p
  have hComp := congrArg CategoryTheory.FilteredObject.Hom.natTrans
    (F.map_comp f g)
  have hCompApp := NatTrans.congr_app hComp p
  change (F.map (f ≫ g)).natTrans.app p =
    (F.map f).natTrans.app p ≫ (F.map g).natTrans.app p at hCompApp
  change eK.hom ≫ (F.map (f ≫ g)).natTrans.app p ≫ eM.inv =
    (eK.hom ≫ (F.map f).natTrans.app p ≫ eL.inv) ≫
      (eL.hom ≫ (F.map g).natTrans.app p ≫ eM.inv)
  rw [hCompApp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end HomologicalComplex₂

end
