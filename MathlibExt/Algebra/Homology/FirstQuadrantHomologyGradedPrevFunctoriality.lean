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
  let F := horizontalFiniteTotalHomologyFilteredObjectFunctor (C := C) (p + q)
  let eK : (horizontalTotalHomologyFiltration K (p + q)).obj
      ((((p : ℤ) - 1 : ℤ) : EInt)) ≅
      ((F.obj K).filtration.diagram).obj (p - 1) :=
    eqToIso (congrArg
      (fun i : EInt => (horizontalTotalHomologyFiltration K (p + q)).obj i)
      (horizontalTotalHomologyPrevNatIndexEq p hp)) ≪≫
      ((evaluation ℕ C).obj (p - 1)).mapIso
        (horizontalCompleteFiniteHomologyFiltrationDiagramIso K (p + q))
  let θ : (F.obj K ⟶ F.obj K) →
      ((horizontalTotalHomologyFiltration K (p + q)).obj
        ((((p : ℤ) - 1 : ℤ) : EInt)) ⟶
      (horizontalTotalHomologyFiltration K (p + q)).obj
        ((((p : ℤ) - 1 : ℤ) : EInt))) :=
    fun h => eK.hom ≫ h.natTrans.app (p - 1) ≫ eK.inv
  change θ (F.map (𝟙 K)) = 𝟙 _
  calc
    θ (F.map (𝟙 K)) = θ (𝟙 (F.obj K)) := congrArg θ (F.map_id K)
    _ = 𝟙 _ := by
      change eK.hom ≫ 𝟙 _ ≫ eK.inv = 𝟙 _
      calc
        eK.hom ≫ 𝟙 _ ≫ eK.inv = eK.hom ≫ eK.inv :=
          congrArg (fun h => eK.hom ≫ h) (Category.id_comp eK.inv)
        _ = 𝟙 _ := eK.hom_inv_id

/-- Transported positive predecessor-stage maps preserve composition of
bicomplex morphisms. -/
@[simp 1100]
theorem horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex_comp
    (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) (hp : 0 < p) :
    horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
        (f ≫ g) p q hp =
      horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex f p q hp ≫
        horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex g p q hp := by
  let F := horizontalFiniteTotalHomologyFilteredObjectFunctor (C := C) (p + q)
  let eK : (horizontalTotalHomologyFiltration K (p + q)).obj
      ((((p : ℤ) - 1 : ℤ) : EInt)) ≅
      ((F.obj K).filtration.diagram).obj (p - 1) :=
    eqToIso (congrArg
      (fun i : EInt => (horizontalTotalHomologyFiltration K (p + q)).obj i)
      (horizontalTotalHomologyPrevNatIndexEq p hp)) ≪≫
      ((evaluation ℕ C).obj (p - 1)).mapIso
        (horizontalCompleteFiniteHomologyFiltrationDiagramIso K (p + q))
  let eL : (horizontalTotalHomologyFiltration L (p + q)).obj
      ((((p : ℤ) - 1 : ℤ) : EInt)) ≅
      ((F.obj L).filtration.diagram).obj (p - 1) :=
    eqToIso (congrArg
      (fun i : EInt => (horizontalTotalHomologyFiltration L (p + q)).obj i)
      (horizontalTotalHomologyPrevNatIndexEq p hp)) ≪≫
      ((evaluation ℕ C).obj (p - 1)).mapIso
        (horizontalCompleteFiniteHomologyFiltrationDiagramIso L (p + q))
  let eM : (horizontalTotalHomologyFiltration M (p + q)).obj
      ((((p : ℤ) - 1 : ℤ) : EInt)) ≅
      ((F.obj M).filtration.diagram).obj (p - 1) :=
    eqToIso (congrArg
      (fun i : EInt => (horizontalTotalHomologyFiltration M (p + q)).obj i)
      (horizontalTotalHomologyPrevNatIndexEq p hp)) ≪≫
      ((evaluation ℕ C).obj (p - 1)).mapIso
        (horizontalCompleteFiniteHomologyFiltrationDiagramIso M (p + q))
  let θ : (F.obj K ⟶ F.obj M) →
      ((horizontalTotalHomologyFiltration K (p + q)).obj
        ((((p : ℤ) - 1 : ℤ) : EInt)) ⟶
      (horizontalTotalHomologyFiltration M (p + q)).obj
        ((((p : ℤ) - 1 : ℤ) : EInt))) :=
    fun h => eK.hom ≫ h.natTrans.app (p - 1) ≫ eM.inv
  change θ (F.map (f ≫ g)) =
    (eK.hom ≫ (F.map f).natTrans.app (p - 1) ≫ eL.inv) ≫
      (eL.hom ≫ (F.map g).natTrans.app (p - 1) ≫ eM.inv)
  calc
    θ (F.map (f ≫ g)) = θ (F.map f ≫ F.map g) := congrArg θ (F.map_comp f g)
    _ = (eK.hom ≫ (F.map f).natTrans.app (p - 1) ≫ eL.inv) ≫
        (eL.hom ≫ (F.map g).natTrans.app (p - 1) ≫ eM.inv) := by
      change eK.hom ≫ ((F.map f).natTrans.app (p - 1) ≫
        (F.map g).natTrans.app (p - 1)) ≫ eM.inv = _
      exact Iso.homCongr_comp eK.symm eL.symm eM.symm
        ((F.map f).natTrans.app (p - 1)) ((F.map g).natTrans.app (p - 1))

end HomologicalComplex₂

end
