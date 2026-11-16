/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralCoverDescentModels

/-!
# Actual regularizers over a fixed cameral cover

Objects have the actual G torsor and sigma, its descended incidence
cover, and a W-equivariant marking by the specified cameral cover.
Arrows are actual equivariant G-torsor isomorphisms, preserving sigma
and every pulled incidence point under that marking. The native
identities and compositions give a concrete category of this fibre.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections 2 and 4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralMarkedRegularizers

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralRamificationReindexing CameralRegularizedHiggsModels
open CameralCoverDescentModels GroupTorsorGeometry ExpansionParameterModels

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori) (I : IncidenceAction F) {X : Over (Spec (.of ℂ))} (C : Cover F X)

attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction

structure Object where
  regularizer : Regularizer F X
  descent : CoverDescent F I regularizer
  marking : C.cover.scheme ≅ descent.cameral.cover.scheme
  weyl : ∀ w : F.Weyl,
    (C.cover.action w).asIso.hom ≫ marking.hom =
      marking.hom ≫ (descent.cameral.cover.action w).asIso.hom

def markingTotal (H : Object F I C) : total F C ≅ total F H.descent.cameral :=
  (Over.map X.hom).mapIso H.marking

theorem markingProjection (H : Object F I C) :
    (markingTotal F I C H).hom ≫ projection F H.descent.cameral = projection F C := by
  apply Over.OverMorphism.ext
  exact H.marking.hom.w

def incidencePoint (H : Object F I C) (V : Over (Spec (.of ℂ))) (c : V ⟶ total F C)
    (p : V ⟶ H.regularizer.torsor.total)
    (hp : p ≫ H.regularizer.torsor.projection = c ≫ projection F C) : V ⟶ universalTotal F I :=
  pullback.lift (c ≫ (markingTotal F I C H).hom) p (by
    rw [Category.assoc, markingProjection]
    exact hp.symm) ≫ incidenceMap F I H.regularizer H.descent

structure Hom (H H' : Object F I C) where
  map : H.regularizer ⟶ H'.regularizer
  incidence : ∀ (V : Over (Spec (.of ℂ))) (c : V ⟶ total F C)
      (p : V ⟶ H.regularizer.torsor.total)
      (hp : p ≫ H.regularizer.torsor.projection = c ≫ projection F C),
    incidencePoint F I C H V c p hp =
      incidencePoint F I C H' V c (p ≫ map.iso.hom) (by
        rw [Category.assoc, map.over]
        exact hp)

@[ext] theorem Hom.ext {H H' : Object F I C} (a b : Hom F I C H H')
    (h : a.map = b.map) : a = b := by
  cases a
  cases b
  cases h
  rfl

theorem regularizer_comp_hom {P P' P'' : Regularizer F X} (f : P ⟶ P') (g : P' ⟶ P'') :
    (f ≫ g).iso.hom = f.iso.hom ≫ g.iso.hom := rfl

def idHom (H : Object F I C) : Hom F I C H H where
  map := GroupTorsorGeometry.QuotientIso.id G F.centralizers.scheme H.regularizer
  incidence V c p hp := by
    simp only [GroupTorsorGeometry.QuotientIso.id, Iso.refl_hom, Category.comp_id]

def compHom {H H' H'' : Object F I C} (a : Hom F I C H H') (b : Hom F I C H' H'') :
    Hom F I C H H'' where
  map := a.map ≫ b.map
  incidence V c p hp := by
    have ha := a.incidence V c p hp
    have hb := b.incidence V c (p ≫ a.map.iso.hom) (by rw [Category.assoc, a.map.over]; exact hp)
    simpa only [regularizer_comp_hom, Category.assoc] using ha.trans hb

instance category : Category (Object F I C) where
  Hom := Hom F I C
  id := idHom F I C
  comp := compHom F I C
  id_comp := by
    intro H H' a
    apply Hom.ext
    exact Category.id_comp a.map
  comp_id := by
    intro H H' a
    apply Hom.ext
    exact Category.comp_id a.map
  assoc := by
    intro H H' H'' H''' a b c
    apply Hom.ext
    exact Category.assoc a.map b.map c.map

def forget : Object F I C ⥤ Regularizer F X where
  obj H := H.regularizer
  map a := a.map

instance forgetFaithful : (forget F I C).Faithful where
  map_injective := fun {_H _H'} {a b} h => Hom.ext F I C a b h

end MathlibExt.AlgebraicGeometry.CameralMarkedRegularizers
