/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverCotensor
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Original fixed-base scalar tensor/cotensor parametrized adjunction

Scalar maps act on the same original product functors. The native right
mates give the actual contravariant cotensor maps. Identity, composition,
and the parametrized adjunction equations follow from the original units
and counits. No model, fibration or localization hypothesis is included.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace SSet.Marked

/-- The fixed-scalar action is the original source/parameter bifunctor with its two variables exchanged. -/
def overScalarBifunctor (Z : Marked.{u}) : SSet.{u} ⥤ Over Z ⥤ Over Z :=
  (overParameterBifunctor Z).flip

/-- The original scalar product map is a natural transformation between the actual fixed-scalar slice functors. -/
def overScalarMap {Z : Marked.{u}} {A D : SSet.{u}} (a : A ⟶ D) :
    overScalarTensor Z A ⟶ overScalarTensor Z D := (overScalarBifunctor Z).map a

/-- The actual fixed-scalar source transformation retains the original identity map. -/
theorem overScalarMap_id (Z : Marked.{u}) (A : SSet.{u}) :
    overScalarMap (Z := Z) (𝟙 A) = 𝟙 (overScalarTensor Z A) :=
  CategoryTheory.Functor.map_id _ _

/-- The original fixed-scalar source maps retain the same whole composition. -/
theorem overScalarMap_comp {Z : Marked.{u}} {A D L : SSet.{u}} (a : A ⟶ D) (b : D ⟶ L) :
    overScalarMap (Z := Z) (a ≫ b) = overScalarMap a ≫ overScalarMap b :=
  CategoryTheory.Functor.map_comp _ _ _

/-- Original scalar maps induce their actual cotensor right mates, retaining the same slice adjunctions. -/
def overCotensorScalarMap {Z : Marked.{u}} {A D : SSet.{u}} (a : A ⟶ D) :
    overCotensor Z D ⟶ overCotensor Z A :=
  conjugateEquiv (overScalarTensorAdjunction Z D) (overScalarTensorAdjunction Z A)
    (overScalarMap a)

/-- The native scalar mate retains the whole original identity parameter map. -/
theorem overCotensorScalarMap_id (Z : Marked.{u}) (A : SSet.{u}) :
    overCotensorScalarMap (Z := Z) (𝟙 A) = 𝟙 (overCotensor Z A) := by
  unfold overCotensorScalarMap
  rw [overScalarMap_id]
  exact conjugateEquiv_id _

/-- Composable original scalar maps retain the original reversed order of their full cotensor mates. -/
theorem overCotensorScalarMap_comp {Z : Marked.{u}} {A D L : SSet.{u}}
    (a : A ⟶ D) (b : D ⟶ L) :
    overCotensorScalarMap (Z := Z) (a ≫ b) = overCotensorScalarMap b ≫ overCotensorScalarMap a := by
  let α : overScalarTensor Z A ⟶ overScalarTensor Z D := overScalarMap a
  let β : overScalarTensor Z D ⟶ overScalarTensor Z L := overScalarMap b
  have h : overScalarMap (Z := Z) (a ≫ b) = α ≫ β := overScalarMap_comp a b
  have hh := conjugateEquiv_comp (overScalarTensorAdjunction Z L)
    (overScalarTensorAdjunction Z D) (overScalarTensorAdjunction Z A) β α
  exact (congrArg (conjugateEquiv (overScalarTensorAdjunction Z L) (overScalarTensorAdjunction Z A)) h).trans hh.symm

/-- The same original cotensors and right mates form the scalar-contravariant slice bifunctor. -/
def overCotensorBifunctor (Z : Marked.{u}) : SSet.{u}ᵒᵖ ⥤ Over Z ⥤ Over Z where
  obj K := overCotensor Z K.unop
  map a := overCotensorScalarMap a.unop
  map_id K := overCotensorScalarMap_id Z K.unop
  map_comp a b := overCotensorScalarMap_comp b.unop a.unop

/-- The original scalar action and native mate cotensors have the genuine two-variable adjunction. -/
def overScalarCotensorAdjunction₂ (Z : Marked.{u}) :
    overScalarBifunctor Z ⊣₂ overCotensorBifunctor Z where
  adj K := overScalarTensorAdjunction Z K
  unit_whiskerRight_map {A D} a := by
    apply NatTrans.ext
    funext X
    exact (unit_conjugateEquiv (overScalarTensorAdjunction Z D) (overScalarTensorAdjunction Z A)
      (overScalarMap a) X).symm

end SSet.Marked
