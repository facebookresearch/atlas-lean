/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Actual small-etale base change and inverse-image implementation proofs

The category/topology, scheme fibre products, maps and adjunctions are native
Mathlib constructions. The input class supplies continuity and adjoint proofs
for those fixed functors, without replacing their operations or carriers.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.SmallEtaleGeometry
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
universe u

def etaleBaseChange {X T : Scheme.{u}} (f : T ⟶ X) : X.Etale ⥤ T.Etale where
  obj U := Scheme.Etale.mk (pullback.snd U.hom f)
  map {U V} a := MorphismProperty.Over.homMk
    ((Over.pullback f).map ((Scheme.Etale.forget X).map a)).left
    (Over.w ((Over.pullback f).map ((Scheme.Etale.forget X).map a)))
  map_id U := by
    apply (Scheme.Etale.forget T).map_injective
    exact (Over.pullback f).map_id _
  map_comp a b := by
    apply (Scheme.Etale.forget T).map_injective
    exact (Over.pullback f).map_comp _ _

abbrev projection {X T : Scheme.{u}} (f : T ⟶ X) (U : X.Etale) :
    ((etaleBaseChange f).obj U).left ⟶ U.left := pullback.fst U.hom f

lemma projection_naturality {X T : Scheme.{u}} (f : T ⟶ X)
    {U V : X.Etale} (a : V ⟶ U) :
    ((etaleBaseChange f).map a).left ≫ projection f U = projection f V ≫ a.left := by
  simp [etaleBaseChange, projection, Over.pullback]
  rfl

class HasInverseImage {X T : Scheme.{u}} (f : T ⟶ X) where
  [continuous : Functor.IsContinuous (etaleBaseChange f)
    X.smallEtaleTopology T.smallEtaleTopology]
  [adjoint : ((etaleBaseChange f).sheafPushforwardContinuous CommMonCat.{u}
    X.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]

attribute [instance] HasInverseImage.continuous HasInverseImage.adjoint

end MathlibExt.AlgebraicGeometry.SmallEtaleGeometry
