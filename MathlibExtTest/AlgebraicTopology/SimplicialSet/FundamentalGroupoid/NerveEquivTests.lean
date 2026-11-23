/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NerveEquiv
public import Mathlib.AlgebraicTopology.SimplicialSet.CoherentIso
public import Mathlib.CategoryTheory.Groupoid.Discrete
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Tests for the fundamental-groupoid/nerve hom equivalence

The tests use the public equivalence and its two naturality laws to rebuild
the unit, both triangle identities, and the homotopy-to-natural-isomorphism
bridge.  Concrete fixtures include a two-object walking isomorphism and a
non-thin one-object groupoid.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Nerve Opposite Simplicial
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.FundamentalGroupoid
namespace NerveEquivTests

section PublicTypes

variable (X : SSet.{u}) (G : Type u) [Groupoid.{u} G]

example : (SSet.FundamentalGroupoid X ⥤ G) ≃
    (X ⟶ CategoryTheory.nerve G) :=
  SSet.fundamentalGroupoidNerveEquiv X G

example (X : SSet.{1}) (G : Type 1) [Groupoid.{1} G] :
    (SSet.FundamentalGroupoid X ⥤ G) ≃
      (X ⟶ CategoryTheory.nerve G) :=
  SSet.fundamentalGroupoidNerveEquiv X G

example (X : SSet.{0}) (G : Type) [Groupoid G] :
    (SSet.FundamentalGroupoid X ⥤ G) ≃
      (X ⟶ CategoryTheory.nerve G) :=
  SSet.fundamentalGroupoidNerveEquiv X G

example (X : SSet.{0}) :
    (SSet.FundamentalGroupoid X ⥤ Discrete Empty) ≃
      (X ⟶ CategoryTheory.nerve (Discrete Empty)) :=
  SSet.fundamentalGroupoidNerveEquiv X (Discrete Empty)

example (G : Type u) [Groupoid.{u} G] :
    (SSet.FundamentalGroupoid (⊥_ SSet.{u}) ⥤ G) ≃
      ((⊥_ SSet.{u}) ⟶ CategoryTheory.nerve G) :=
  SSet.fundamentalGroupoidNerveEquiv (⊥_ SSet.{u}) G

end PublicTypes

section Computations

variable {X : SSet.{u}} {G : Type u} [Groupoid.{u} G]

example (F : SSet.FundamentalGroupoid X ⥤ G) (x : X _⦋0⦌) :
    (SSet.fundamentalGroupoidNerveEquiv X G F).app _ x =
      CategoryTheory.nerveEquiv.symm
        (F.obj (SSet.FundamentalGroupoid.mk x)) := by
  apply SSet.fundamentalGroupoidNerveEquiv_app_zero

example (F : SSet.FundamentalGroupoid X ⥤ G)
    {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    (SSet.fundamentalGroupoidNerveEquiv X G F).app _ e.edge =
      ComposableArrows.mk₁
        (F.map (SSet.FundamentalGroupoid.homMk e)) := by
  apply SSet.fundamentalGroupoidNerveEquiv_app_edge

example (φ : X ⟶ CategoryTheory.nerve G) (x : X _⦋0⦌) :
    ((SSet.fundamentalGroupoidNerveEquiv X G).symm φ).obj
        (SSet.FundamentalGroupoid.mk x) =
      CategoryTheory.nerveEquiv (φ.app _ x) := by
  apply SSet.fundamentalGroupoidNerveEquiv_symm_obj_mk

example (F : SSet.FundamentalGroupoid X ⥤ G) :
    (SSet.fundamentalGroupoidNerveEquiv X G).symm
        (SSet.fundamentalGroupoidNerveEquiv X G F) = F :=
  (SSet.fundamentalGroupoidNerveEquiv X G).left_inv F

example (φ : X ⟶ CategoryTheory.nerve G) :
    SSet.fundamentalGroupoidNerveEquiv X G
        ((SSet.fundamentalGroupoidNerveEquiv X G).symm φ) = φ :=
  (SSet.fundamentalGroupoidNerveEquiv X G).apply_symm_apply φ

end Computations

private noncomputable def unitMap (X : SSet.{u}) :
    X ⟶ CategoryTheory.nerve (SSet.FundamentalGroupoid X) :=
  SSet.fundamentalGroupoidNerveEquiv X
    (SSet.FundamentalGroupoid X) (𝟭 _)

private noncomputable def counitFunctor
    (G : Type u) [Groupoid.{u} G] :
    SSet.FundamentalGroupoid (CategoryTheory.nerve G) ⥤ G :=
  (SSet.fundamentalGroupoidNerveEquiv
    (CategoryTheory.nerve G) G).symm
      (𝟙 (CategoryTheory.nerve G) :
        CategoryTheory.nerve G ⟶ CategoryTheory.nerve G)

private theorem symm_unitMap (X : SSet.{u}) :
    (SSet.fundamentalGroupoidNerveEquiv X
      (SSet.FundamentalGroupoid X)).symm (unitMap X) = 𝟭 _ :=
  (SSet.fundamentalGroupoidNerveEquiv X
    (SSet.FundamentalGroupoid X)).left_inv (𝟭 _)

private theorem equiv_eq_unit_comp_nerveMap
    {X : SSet.{u}} {G : Type u} [Groupoid.{u} G]
    (F : SSet.FundamentalGroupoid X ⥤ G) :
    SSet.fundamentalGroupoidNerveEquiv X G F =
      unitMap X ≫ CategoryTheory.nerveMap F := by
  have h := SSet.fundamentalGroupoidNerveEquiv_postcomp
    (X := X) (𝟭 (SSet.FundamentalGroupoid X)) F
  exact (congrArg (SSet.fundamentalGroupoidNerveEquiv X G)
    (Functor.id_comp F)).symm.trans h

private theorem unitMap_naturality
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    f ≫ unitMap Y =
      unitMap X ≫
        CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f) := by
  calc
    f ≫ unitMap Y =
        SSet.fundamentalGroupoidNerveEquiv X
          (SSet.FundamentalGroupoid Y)
          (SSet.mapFundamentalGroupoid f ⋙ 𝟭 _) :=
      (SSet.fundamentalGroupoidNerveEquiv_precomp f (𝟭 _)).symm
    _ = SSet.fundamentalGroupoidNerveEquiv X
        (SSet.FundamentalGroupoid Y)
        (SSet.mapFundamentalGroupoid f) :=
      congrArg (SSet.fundamentalGroupoidNerveEquiv X
        (SSet.FundamentalGroupoid Y))
        (Functor.comp_id (SSet.mapFundamentalGroupoid f))
    _ = unitMap X ≫ CategoryTheory.nerveMap
        (SSet.mapFundamentalGroupoid f) := by
      have h := SSet.fundamentalGroupoidNerveEquiv_postcomp
        (X := X) (𝟭 (SSet.FundamentalGroupoid X))
        (SSet.mapFundamentalGroupoid f)
      exact (congrArg (SSet.fundamentalGroupoidNerveEquiv X
        (SSet.FundamentalGroupoid Y))
          (Functor.id_comp (SSet.mapFundamentalGroupoid f))).symm.trans h

private theorem unit_comp_nerveMap_counit
    (G : Type u) [Groupoid.{u} G] :
    unitMap (CategoryTheory.nerve G) ≫
        CategoryTheory.nerveMap (counitFunctor G) =
      (𝟙 (CategoryTheory.nerve G) :
        CategoryTheory.nerve G ⟶ CategoryTheory.nerve G) := by
  rw [← equiv_eq_unit_comp_nerveMap]
  exact (SSet.fundamentalGroupoidNerveEquiv
    (CategoryTheory.nerve G) G).apply_symm_apply
      (𝟙 (CategoryTheory.nerve G) :
        CategoryTheory.nerve G ⟶ CategoryTheory.nerve G)

private theorem mapFundamentalGroupoid_comp_counit
    {X : SSet.{u}} {G : Type u} [Groupoid.{u} G]
    (φ : X ⟶ CategoryTheory.nerve G) :
    SSet.mapFundamentalGroupoid φ ⋙ counitFunctor G =
      (SSet.fundamentalGroupoidNerveEquiv X G).symm φ := by
  apply (SSet.fundamentalGroupoidNerveEquiv X G).injective
  rw [SSet.fundamentalGroupoidNerveEquiv_precomp]
  change φ ≫ SSet.fundamentalGroupoidNerveEquiv
      (CategoryTheory.nerve G) G
        ((SSet.fundamentalGroupoidNerveEquiv
          (CategoryTheory.nerve G) G).symm
            (𝟙 (CategoryTheory.nerve G) :
              CategoryTheory.nerve G ⟶ CategoryTheory.nerve G)) =
    SSet.fundamentalGroupoidNerveEquiv X G
      ((SSet.fundamentalGroupoidNerveEquiv X G).symm φ)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Category.comp_id]

private noncomputable def homotopyIso
    {X : SSet.{u}} {G : Type u} [Groupoid.{u} G]
    {φ ψ : X ⟶ CategoryTheory.nerve G} (h : SSet.Homotopy φ ψ) :
    (SSet.fundamentalGroupoidNerveEquiv X G).symm φ ≅
      (SSet.fundamentalGroupoidNerveEquiv X G).symm ψ :=
  eqToIso (mapFundamentalGroupoid_comp_counit φ).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight
      (SSet.congrMapFundamentalGroupoid h) (counitFunctor G) ≪≫
    eqToIso (mapFundamentalGroupoid_comp_counit ψ)

private noncomputable def reflHomotopy
    {X Y : SSet.{u}} (φ : X ⟶ Y) : SSet.Homotopy φ φ :=
  SSet.RelativeMorphism.Homotopy.refl
    (SSet.RelativeMorphism.botEquiv.symm φ)

set_option backward.isDefEq.respectTransparency false in
private theorem congrMapFundamentalGroupoid_refl_app
    {X Y : SSet.{u}} (φ : X ⟶ Y) (x : X _⦋0⦌) :
    (SSet.congrMapFundamentalGroupoid (reflHomotopy φ)).hom.app
        (SSet.FundamentalGroupoid.mk x) = 𝟙 _ := by
  change SSet.FundamentalGroupoid.homMk _ = 𝟙 _
  rw [← SSet.FundamentalGroupoid.homMk_id]
  congr 1
  ext
  simp [reflHomotopy, SSet.Homotopy.toSimplicialObjectHomotopy,
    SSet.RelativeMorphism.Homotopy.refl]
  change Y.map (SSet.stdSimplex.objEquiv
    (SSet.prodStdSimplex₁.nonDegenerateEquiv.{u} 0).val.1).op
      (φ.app _ x) = Y.σ 0 (φ.app _ x)
  rw [SSet.prodStdSimplex₁.nonDegenerateEquiv_fst]
  rfl

section ReconstructedClients

variable {X Y : SSet.{u}} (f : X ⟶ Y)
  {G H : Type u} [Groupoid.{u} G] [Groupoid.{u} H]
  (F : SSet.FundamentalGroupoid Y ⥤ G) (Q : G ⥤ H)

example : SSet.fundamentalGroupoidNerveEquiv X G
      (SSet.mapFundamentalGroupoid f ⋙ F) =
    f ≫ SSet.fundamentalGroupoidNerveEquiv Y G F := by
  apply SSet.fundamentalGroupoidNerveEquiv_precomp

example : SSet.fundamentalGroupoidNerveEquiv Y H (F ⋙ Q) =
    SSet.fundamentalGroupoidNerveEquiv Y G F ≫
      CategoryTheory.nerveMap Q := by
  apply SSet.fundamentalGroupoidNerveEquiv_postcomp

example : f ≫ unitMap Y = unitMap X ≫
    CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid f) :=
  unitMap_naturality f

example : (SSet.fundamentalGroupoidNerveEquiv X
    (SSet.FundamentalGroupoid X)).symm (unitMap X) = 𝟭 _ :=
  symm_unitMap X

example : unitMap (CategoryTheory.nerve G) ≫
      CategoryTheory.nerveMap (counitFunctor G) =
        (𝟙 (CategoryTheory.nerve G) :
          CategoryTheory.nerve G ⟶ CategoryTheory.nerve G) :=
  unit_comp_nerveMap_counit G

example {φ ψ : X ⟶ CategoryTheory.nerve G}
    (h : SSet.Homotopy φ ψ) :
    (SSet.fundamentalGroupoidNerveEquiv X G).symm φ ≅
      (SSet.fundamentalGroupoidNerveEquiv X G).symm ψ :=
  homotopyIso h

example (φ : X ⟶ CategoryTheory.nerve G) :
    (SSet.fundamentalGroupoidNerveEquiv X G).symm φ ≅
      (SSet.fundamentalGroupoidNerveEquiv X G).symm φ :=
  homotopyIso (reflHomotopy φ)

example (φ : X ⟶ CategoryTheory.nerve G) (x : X _⦋0⦌) :
    (homotopyIso (reflHomotopy φ)).hom.app
        (SSet.FundamentalGroupoid.mk x) = 𝟙 _ := by
  dsimp [homotopyIso]
  rw [congrMapFundamentalGroupoid_refl_app]
  let e := eqToIso (mapFundamentalGroupoid_comp_counit φ)
  change e.inv.app (SSet.FundamentalGroupoid.mk x) ≫
      (counitFunctor G).map
        (𝟙 ((SSet.mapFundamentalGroupoid φ).obj (SSet.FundamentalGroupoid.mk x))) ≫
      e.hom.app (SSet.FundamentalGroupoid.mk x) = 𝟙 _
  have hmap := (counitFunctor G).map_id
    ((SSet.mapFundamentalGroupoid φ).obj (SSet.FundamentalGroupoid.mk x))
  rw [hmap]
  have hid := Category.id_comp (e.hom.app (SSet.FundamentalGroupoid.mk x))
  have hcomp := congrArg
    (fun z => e.inv.app (SSet.FundamentalGroupoid.mk x) ≫ z) hid
  exact hcomp.trans (NatTrans.congr_app e.inv_hom_id (SSet.FundamentalGroupoid.mk x))

end ReconstructedClients

section ConcreteGroupoids

private def swap₂ : Equiv.Perm (Fin 2) := Equiv.swap 0 1

private def swapEnd :
    End (SingleObj.star (Equiv.Perm (Fin 2))) :=
  SingleObj.toEnd (Equiv.Perm (Fin 2)) swap₂

example : swap₂ ≠ 1 := by decide

example : CategoryTheory.nerve.homEquiv
      (CategoryTheory.nerve.edgeMk swapEnd.asHom) = swapEnd.asHom := by
  rw [CategoryTheory.nerve.homEquiv_edgeMk]

set_option backward.isDefEq.respectTransparency false in
example :
    ((SSet.fundamentalGroupoidNerveEquiv
      (CategoryTheory.nerve (SingleObj (Equiv.Perm (Fin 2))))
      (SingleObj (Equiv.Perm (Fin 2)))).symm
        (𝟙 (CategoryTheory.nerve (SingleObj (Equiv.Perm (Fin 2)))) :
          CategoryTheory.nerve (SingleObj (Equiv.Perm (Fin 2))) ⟶
            CategoryTheory.nerve (SingleObj (Equiv.Perm (Fin 2))))).map
        (SSet.FundamentalGroupoid.homMk
          (CategoryTheory.nerve.edgeMk swapEnd.asHom)) = swapEnd.asHom := by
  rw [SSet.fundamentalGroupoidNerveEquiv_symm_map_homMk]
  have he : (CategoryTheory.nerve.edgeMk swapEnd.asHom).map
      (𝟙 (CategoryTheory.nerve (SingleObj (Equiv.Perm (Fin 2))))) =
        CategoryTheory.nerve.edgeMk swapEnd.asHom := by
    ext
    rfl
  rw [he]
  have h := CategoryTheory.nerve.homEquiv_edgeMk swapEnd.asHom
  cat_disch

set_option backward.isDefEq.respectTransparency false in
example :
    letI : Groupoid CategoryTheory.WalkingIso :=
      { inv := fun _ => ()
        inv_comp := by intros; rfl
        comp_inv := by intros; rfl }
    ((SSet.fundamentalGroupoidNerveEquiv
      (CategoryTheory.nerve CategoryTheory.WalkingIso)
      CategoryTheory.WalkingIso).symm
        (𝟙 (CategoryTheory.nerve CategoryTheory.WalkingIso) :
          CategoryTheory.nerve CategoryTheory.WalkingIso ⟶
            CategoryTheory.nerve CategoryTheory.WalkingIso)).obj
        (SSet.FundamentalGroupoid.mk
          (CategoryTheory.nerveEquiv.symm
            CategoryTheory.WalkingIso.zero)) =
      CategoryTheory.WalkingIso.zero := by
  rw [SSet.fundamentalGroupoidNerveEquiv_symm_obj_mk]
  simp

set_option backward.isDefEq.respectTransparency false in
example :
    letI : Groupoid CategoryTheory.WalkingIso :=
      { inv := fun _ => ()
        inv_comp := by intros; rfl
        comp_inv := by intros; rfl }
    ((SSet.fundamentalGroupoidNerveEquiv
      (CategoryTheory.nerve CategoryTheory.WalkingIso)
      CategoryTheory.WalkingIso).symm
        (𝟙 (CategoryTheory.nerve CategoryTheory.WalkingIso) :
          CategoryTheory.nerve CategoryTheory.WalkingIso ⟶
            CategoryTheory.nerve CategoryTheory.WalkingIso)).obj
        (SSet.FundamentalGroupoid.mk
          (CategoryTheory.nerveEquiv.symm
            CategoryTheory.WalkingIso.one)) =
      CategoryTheory.WalkingIso.one := by
  rw [SSet.fundamentalGroupoidNerveEquiv_symm_obj_mk]
  simp

end ConcreteGroupoids

#print axioms SSet.fundamentalGroupoidNerveEquiv
#print axioms SSet.fundamentalGroupoidNerveEquiv_precomp
#print axioms SSet.fundamentalGroupoidNerveEquiv_postcomp
#print axioms symm_unitMap
#print axioms homotopyIso

end NerveEquivTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet.FundamentalGroupoid

end
