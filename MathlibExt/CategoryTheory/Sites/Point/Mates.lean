/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Concrete product coordinates of the mate of a point morphism

These stock-adjunction consequences identify the same point-induced stalk
map and its skyscraper mate. They will be used for the original geometric
point comparisons, without supplying a coherence certificate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u v w u' v'

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual skyscraper counit on a neighborhood is its original product projection. -/
@[reassoc (attr := simp)]
lemma toPresheafFiber_skyscraperSheafAdjunction_counit (Φ : Point.{w} J)
    (M : A) (U : C) (x : Φ.fiber.obj U) :
    Φ.toPresheafFiber U x ((Φ.skyscraperSheafFunctor.obj M).obj) ≫
        Φ.skyscraperSheafAdjunction.counit.app M = Pi.π (fun (_ : Φ.fiber.obj U) => M) x := by
  let Q : Sheaf J A := Φ.skyscraperSheafFunctor.obj M
  let g : Q.obj ⟶ Φ.skyscraperPresheaf M :=
    (sheafToPresheaf J A).map (𝟙 Q)
  have h := Φ.toPresheafFiber_skyscraperPresheafHomEquiv_symm g U x
  have hc := Φ.skyscraperSheafAdjunction_homEquiv_symm_apply (𝟙 Q)
  change (Φ.skyscraperSheafAdjunction.homEquiv Q M).symm (𝟙 Q) =
    Φ.skyscraperPresheafHomEquiv.symm g at hc
  have hg : g = 𝟙 Q.obj := (sheafToPresheaf J A).map_id Q
  rw [← hc, Adjunction.homEquiv_counit, Functor.map_id, Category.id_comp,
    hg, NatTrans.id_app, Category.id_comp] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The mate of the same point-induced stalk map reindexes the actual
skyscraper products by the original fiber map. -/
lemma conjugateEquiv_sheafFiber_app_π {Φ Ψ : Point.{w} J} (j : Φ ⟶ Ψ)
    (M : A) (U : C) (y : Ψ.fiber.obj U) :
    ((conjugateEquiv Φ.skyscraperSheafAdjunction Ψ.skyscraperSheafAdjunction
          (j.sheafFiber (A := A))).app M).hom.app (op U) ≫
        Pi.π (fun (_ : Ψ.fiber.obj U) => M) y =
      Pi.π (fun (_ : Φ.fiber.obj U) => M) (j.hom.app U y) := by
  have h := congrArg (fun k => Ψ.toPresheafFiber U y ((Φ.skyscraperSheafFunctor.obj M).obj) ≫ k)
    (conjugateEquiv_counit Φ.skyscraperSheafAdjunction Ψ.skyscraperSheafAdjunction
      (j.sheafFiber (A := A)) M)
  change Ψ.toPresheafFiber U y ((Φ.skyscraperSheafFunctor.obj M).obj) ≫
      Ψ.presheafFiber.map
        (((conjugateEquiv Φ.skyscraperSheafAdjunction Ψ.skyscraperSheafAdjunction
          (j.sheafFiber (A := A))).app M).hom) ≫
      Ψ.skyscraperSheafAdjunction.counit.app M =
    Ψ.toPresheafFiber U y ((Φ.skyscraperSheafFunctor.obj M).obj) ≫
      j.presheafFiber.app ((Φ.skyscraperSheafFunctor.obj M).obj) ≫
      Φ.skyscraperSheafAdjunction.counit.app M at h
  rw [Ψ.toPresheafFiber_naturality_assoc,
    toPresheafFiber_skyscraperSheafAdjunction_counit] at h
  have hj : Ψ.toPresheafFiber U y ((Φ.skyscraperSheafFunctor.obj M).obj) ≫
      j.presheafFiber.app ((Φ.skyscraperSheafFunctor.obj M).obj) =
    Φ.toPresheafFiber U (j.hom.app U y) ((Φ.skyscraperSheafFunctor.obj M).obj) := by
    simpa only [Hom.presheafFiber] using
      (Ψ.toPresheafFiber_presheafFiberDesc
        (φ := fun X x => Φ.toPresheafFiber X (j.hom.app X x)
          ((Φ.skyscraperSheafFunctor.obj M).obj))
        (hφ := by
          intro X Y f x
          rw [Φ.toPresheafFiber_w]
          exact congrArg
            (fun z => Φ.toPresheafFiber Y z ((Φ.skyscraperSheafFunctor.obj M).obj))
            (j.hom.naturality_apply f x).symm) U y)
  rw [← Category.assoc, hj] at h
  rw [toPresheafFiber_skyscraperSheafAdjunction_counit] at h
  exact h

end CategoryTheory.GrothendieckTopology.Point

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {A : Type*} [Category* A] [HasProducts.{w} A]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original skyscraper restriction is the actual fiber reindexing of product coordinates. -/
lemma skyscraperSheaf_restrict_π (Φ : Point.{w} J) (M : A)
    {U V : C} (g : U ⟶ V) (z : Φ.fiber.obj U) :
    (Φ.skyscraperSheafFunctor.obj M).obj.map g.op ≫ Pi.π (fun (_ : Φ.fiber.obj U) => M) z =
      Pi.π (fun (_ : Φ.fiber.obj V) => M) (Φ.fiber.map g z) := by
  simp [skyscraperSheafFunctor, skyscraperPresheafFunctor]

end CategoryTheory.GrothendieckTopology.Point
