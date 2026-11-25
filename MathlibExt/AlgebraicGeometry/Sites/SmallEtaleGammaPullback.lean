/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado

module

public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleInverseImageStalks
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleCoefficientSections

/-!
# Global-section pullback on small étale sites

Global-section pullback respects identity and composition for morphisms of
schemes.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- Identify global sections with evaluation at the terminal object of the small étale site. -/
abbrev smallEtaleGlobalTerminalIso (X : Scheme.{u}) :
    Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w} ≅
      (sheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}).obj
        (op (Scheme.Etale.mk (𝟙 X))) :=
  Sheaf.ΓNatIsoSheafSections _ _ (identityEtaleIsTerminal X)

/-- The actual original terminal étale object is preserved by every base change. -/
def smallEtaleBaseChangeTerminalIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtaleBaseChange f).obj (Scheme.Etale.mk (𝟙 Y)) ≅ Scheme.Etale.mk (𝟙 X) := by
  let := smallEtaleBaseChange_preservesFiniteLimits f
  exact ((identityEtaleIsTerminal Y).isTerminalObj (smallEtaleBaseChange f)
    (Scheme.Etale.mk (𝟙 Y))).uniqueUpToIso (identityEtaleIsTerminal X)

/-- Pull back actual Γ through its actual adjunction unit and original terminal restriction. -/
def smallEtalePullbackGlobalSections {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max u w} ⟶
      smallEtaleInverseImage.{u, w} f ⋙ Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w} :=
  let EY := (sheafSections Y.smallEtaleTopology AddCommGrpCat.{max u w}).obj
    (op (Scheme.Etale.mk (𝟙 Y)))
  let EB := (sheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}).obj
    (op ((smallEtaleBaseChange f).obj (Scheme.Etale.mk (𝟙 Y))))
  let η : EY ⟶ smallEtaleInverseImage.{u, w} f ⋙ EB :=
    Functor.whiskerRight (smallEtaleInverseImageAdjunction.{u, w} f).unit EY
  let r := (sheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}).map
    (smallEtaleBaseChangeTerminalIso f).inv.op
  (smallEtaleGlobalTerminalIso.{u, w} Y).hom ≫ η ≫
    Functor.whiskerLeft (smallEtaleInverseImage.{u, w} f) r ≫
    Functor.whiskerLeft (smallEtaleInverseImage.{u, w} f)
      (smallEtaleGlobalTerminalIso.{u, w} X).inv

set_option backward.isDefEq.respectTransparency false in
-- V1 implicit simplification did not unfold the same terminal-evaluation components.
/-- The actual Γ pullback retains its literal original terminal component. -/
theorem smallEtalePullbackGlobalSections_terminal_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Q : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtalePullbackGlobalSections.{u, w} f).app Q ≫
      (smallEtaleGlobalTerminalIso.{u, w} X).hom.app ((smallEtaleInverseImage.{u, w} f).obj Q) =
    (smallEtaleGlobalTerminalIso.{u, w} Y).hom.app Q ≫
      ((smallEtaleInverseImageAdjunction.{u, w} f).unit.app Q).hom.app
        (op (Scheme.Etale.mk (𝟙 Y))) ≫
      (((smallEtaleInverseImage.{u, w} f).obj Q).obj.map
        (smallEtaleBaseChangeTerminalIso f).inv.op) := by
  change ((smallEtaleGlobalTerminalIso.{u, w} Y).hom.app Q ≫
    (((smallEtaleInverseImageAdjunction.{u, w} f).unit.app Q).hom.app
      (op (Scheme.Etale.mk (𝟙 Y))) ≫
      ((((smallEtaleInverseImage.{u, w} f).obj Q).obj.map
        (smallEtaleBaseChangeTerminalIso f).inv.op) ≫
        (smallEtaleGlobalTerminalIso.{u, w} X).inv.app
          ((smallEtaleInverseImage.{u, w} f).obj Q)))) ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact congrArg (fun a => (smallEtaleGlobalTerminalIso.{u, w} Y).hom.app Q ≫
      ((smallEtaleInverseImageAdjunction.{u, w} f).unit.app Q).hom.app
        (op (Scheme.Etale.mk (𝟙 Y))) ≫ a)
    (Category.comp_id (((smallEtaleInverseImage.{u, w} f).obj Q).obj.map
      (smallEtaleBaseChangeTerminalIso f).inv.op))

/-- Terminal uniqueness binds the terminal comparison to the same base-change identity. -/
theorem smallEtaleBaseChangeTerminalIso_id (X : Scheme.{u}) :
    smallEtaleBaseChangeTerminalIso (𝟙 X) =
      (smallEtaleBaseChangeId X).app (Scheme.Etale.mk (𝟙 X)) := by
  apply Iso.ext
  exact (identityEtaleIsTerminal X).hom_ext _ _

/-- The actual identity unit has the literal original terminal restriction coordinate. -/
theorem smallEtaleInverseImageIdIso_unit_app (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (U : X.Etale) :
    ((smallEtaleInverseImageAdjunction.{u, w} (𝟙 X)).unit.app Q).hom.app (op U) ≫
      ((smallEtaleInverseImageIdIso.{u, w} X).hom.app Q).hom.app
        (op ((smallEtaleBaseChange (𝟙 X)).obj U)) =
    Q.obj.map ((smallEtaleBaseChangeId X).hom.app U).op := by
  have h := congrArg (fun a => a.hom.app (op U))
    (smallEtaleInverseImageIdIso_unit.{u, w} X Q)
  change ((smallEtaleDirectImageIdIso.{u, w} X).inv.app Q).hom.app (op U) =
    ((smallEtaleInverseImageAdjunction.{u, w} (𝟙 X)).unit.app Q).hom.app (op U) ≫
      ((smallEtaleInverseImageIdIso.{u, w} X).hom.app Q).hom.app
        (op ((smallEtaleBaseChange (𝟙 X)).obj U)) at h
  exact h.symm.trans (smallEtaleDirectImageIdIso_inv_app_hom_app.{u, w} X Q (op U))

set_option backward.isDefEq.respectTransparency false in
-- The actual terminal restriction and adjunction unit enter the same identity comparison.
theorem smallEtalePullbackGlobalSections_id (X : Scheme.{u}) :
    smallEtalePullbackGlobalSections.{u, w} (𝟙 X) ≫
      Functor.whiskerRight (smallEtaleInverseImageIdIso.{u, w} X).hom
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}) =
      𝟙 (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}) := by
  apply NatTrans.ext
  funext Q
  let U := Scheme.Etale.mk (𝟙 X)
  let L := smallEtaleInverseImage.{u, w} (𝟙 X)
  let a := (smallEtaleInverseImageIdIso.{u, w} X).hom.app Q
  let t := smallEtaleBaseChangeTerminalIso (𝟙 X)
  let z := smallEtaleGlobalTerminalIso.{u, w} X
  apply (cancel_mono (z.hom.app Q)).mp
  change ((smallEtalePullbackGlobalSections.{u, w} (𝟙 X)).app Q ≫
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).map a) ≫ z.hom.app Q =
      𝟙 _ ≫ z.hom.app Q
  have hn := z.hom.naturality a
  have hr := a.hom.naturality t.inv.op
  have hs := smallEtalePullbackGlobalSections_terminal_section.{u, w} (𝟙 X) Q
  have hu := smallEtaleInverseImageIdIso_unit_app.{u, w} X Q U
  calc
    _ = (smallEtalePullbackGlobalSections.{u, w} (𝟙 X)).app Q ≫
        (z.hom.app (L.obj Q) ≫ a.hom.app (op U)) :=
      (Category.assoc _ _ _).trans (congrArg (fun b => _ ≫ b) hn)
    _ = z.hom.app Q ≫
        ((smallEtaleInverseImageAdjunction.{u, w} (𝟙 X)).unit.app Q).hom.app (op U) ≫
        ((L.obj Q).obj.map t.inv.op ≫ a.hom.app (op U)) := by
      rw [← Category.assoc, hs, Category.assoc, Category.assoc]
    _ = z.hom.app Q ≫
        ((smallEtaleInverseImageAdjunction.{u, w} (𝟙 X)).unit.app Q).hom.app (op U) ≫
        (a.hom.app (op ((smallEtaleBaseChange (𝟙 X)).obj U)) ≫ Q.obj.map t.inv.op) :=
      congrArg (fun b => z.hom.app Q ≫
        ((smallEtaleInverseImageAdjunction.{u, w} (𝟙 X)).unit.app Q).hom.app (op U) ≫ b) hr
    _ = z.hom.app Q ≫ Q.obj.map ((smallEtaleBaseChangeId X).hom.app U).op ≫
        Q.obj.map t.inv.op := by
      simpa only [Category.assoc] using
        congrArg (fun b => z.hom.app Q ≫ b ≫ Q.obj.map t.inv.op) hu
    _ = z.hom.app Q ≫
        (Q.obj.map ((smallEtaleBaseChangeId X).hom.app U).op ≫
          Q.obj.map ((smallEtaleBaseChangeId X).inv.app U).op) := by
      have ht : t = (smallEtaleBaseChangeId X).app U := smallEtaleBaseChangeTerminalIso_id X
      have hi := congrArg Iso.inv ht
      exact congrArg (fun b => z.hom.app Q ≫ Q.obj.map
        ((smallEtaleBaseChangeId X).hom.app U).op ≫ Q.obj.map b.op) hi
    _ = z.hom.app Q ≫ 𝟙 _ :=
      congrArg (fun b => z.hom.app Q ≫ b)
        (Q.obj.mapIso ((smallEtaleBaseChangeId X).app U).symm.op).inv_hom_id
    _ = _ := (Category.comp_id _).trans (Category.id_comp _).symm

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- The same canonical direct-image composition has its original restriction component. -/
theorem smallEtaleDirectImageCompIso_hom_app_hom_app
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (R : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (U : Z.Etale) :
    ((smallEtaleDirectImageCompIso.{u, w} f g).hom.app R).hom.app (op U) =
      R.obj.map ((smallEtaleBaseChangeComp f g).hom.app U).op := by
  exact smallEtaleDirectImageCompTo_hom_app_hom_app.{u, w} f g (f ≫ g) rfl R (op U)

/-- The genuine composed adjunction unit has the literal original two-stage section coordinate. -/
theorem smallEtaleInverseImageCompIso_unit_app
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (Q : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max u w}) (U : Z.Etale) :
    ((smallEtaleInverseImageAdjunction.{u, w} g).unit.app Q).hom.app (op U) ≫
      ((smallEtaleInverseImageAdjunction.{u, w} f).unit.app
        ((smallEtaleInverseImage.{u, w} g).obj Q)).hom.app
          (op ((smallEtaleBaseChange g).obj U)) ≫
      (((smallEtaleInverseImage.{u, w} g ⋙ smallEtaleInverseImage.{u, w} f).obj Q).obj.map
        ((smallEtaleBaseChangeComp f g).hom.app U).op) =
    ((smallEtaleInverseImageAdjunction.{u, w} (f ≫ g)).unit.app Q).hom.app (op U) ≫
      ((smallEtaleInverseImageCompIso.{u, w} f g).inv.app Q).hom.app
        (op ((smallEtaleBaseChange (f ≫ g)).obj U)) := by
  have h := smallEtaleInverseImageCompIso_unit.{u, w} f g Q
  rw [Adjunction.comp_unit_app] at h
  have hv := congrArg (fun a => a.hom.app (op U)) h
  change ((smallEtaleInverseImageAdjunction.{u, w} g).unit.app Q).hom.app (op U) ≫
      ((smallEtaleInverseImageAdjunction.{u, w} f).unit.app
        ((smallEtaleInverseImage.{u, w} g).obj Q)).hom.app
          (op ((smallEtaleBaseChange g).obj U)) ≫
      ((smallEtaleDirectImageCompIso.{u, w} f g).hom.app
        ((smallEtaleInverseImage.{u, w} g ⋙ smallEtaleInverseImage.{u, w} f).obj Q)).hom.app (op U) =
    ((smallEtaleInverseImageAdjunction.{u, w} (f ≫ g)).unit.app Q).hom.app (op U) ≫
      ((smallEtaleInverseImageCompIso.{u, w} f g).inv.app Q).hom.app
        (op ((smallEtaleBaseChange (f ≫ g)).obj U)) at hv
  rw [smallEtaleDirectImageCompIso_hom_app_hom_app] at hv
  exact hv

/-- Terminal uniqueness supplies the actual base-change composition equality. -/
theorem smallEtaleBaseChangeTerminalIso_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleBaseChangeComp f g).app (Scheme.Etale.mk (𝟙 Z)) ≪≫
      (smallEtaleBaseChange f).mapIso (smallEtaleBaseChangeTerminalIso g) ≪≫
      smallEtaleBaseChangeTerminalIso f = smallEtaleBaseChangeTerminalIso (f ≫ g) := by
  apply Iso.ext
  exact (identityEtaleIsTerminal X).hom_ext _ _

/-- The corresponding inverse restriction is the SAME original two-stage arrow. -/
theorem smallEtaleBaseChangeTerminalIso_comp_inv
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleBaseChangeTerminalIso (f ≫ g)).inv ≫
      (smallEtaleBaseChangeComp f g).hom.app (Scheme.Etale.mk (𝟙 Z)) =
    (smallEtaleBaseChangeTerminalIso f).inv ≫
      (smallEtaleBaseChange f).map (smallEtaleBaseChangeTerminalIso g).inv := by
  have h := congrArg Iso.inv (smallEtaleBaseChangeTerminalIso_comp f g)
  change (smallEtaleBaseChangeTerminalIso f).inv ≫
      (smallEtaleBaseChange f).map (smallEtaleBaseChangeTerminalIso g).inv ≫
      (smallEtaleBaseChangeComp f g).inv.app (Scheme.Etale.mk (𝟙 Z)) =
    (smallEtaleBaseChangeTerminalIso (f ≫ g)).inv at h
  apply (cancel_mono ((smallEtaleBaseChangeComp f g).inv.app (Scheme.Etale.mk (𝟙 Z)))).mp
  rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  exact h.symm

/-- Cancel the inverse mate component in the SAME actual unit composition equation. -/
theorem smallEtaleInverseImageCompIso_unit_hom_app
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (Q : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max u w}) (U : Z.Etale) :
    ((smallEtaleInverseImageAdjunction.{u, w} g).unit.app Q).hom.app (op U) ≫
      ((smallEtaleInverseImageAdjunction.{u, w} f).unit.app
        ((smallEtaleInverseImage.{u, w} g).obj Q)).hom.app
          (op ((smallEtaleBaseChange g).obj U)) ≫
      (((smallEtaleInverseImage.{u, w} g ⋙ smallEtaleInverseImage.{u, w} f).obj Q).obj.map
        ((smallEtaleBaseChangeComp f g).hom.app U).op) ≫
      ((smallEtaleInverseImageCompIso.{u, w} f g).hom.app Q).hom.app
        (op ((smallEtaleBaseChange (f ≫ g)).obj U)) =
    ((smallEtaleInverseImageAdjunction.{u, w} (f ≫ g)).unit.app Q).hom.app (op U) := by
  let E := (sheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}).obj
    (op ((smallEtaleBaseChange (f ≫ g)).obj U))
  have hi := (E.mapIso ((smallEtaleInverseImageCompIso.{u, w} f g).app Q)).inv_hom_id
  have h := congrArg (fun a => a ≫
    ((smallEtaleInverseImageCompIso.{u, w} f g).hom.app Q).hom.app
      (op ((smallEtaleBaseChange (f ≫ g)).obj U)))
    (smallEtaleInverseImageCompIso_unit_app.{u, w} f g Q U)
  exact h.trans ((Category.assoc _ _ _).trans
    ((congrArg (fun a => ((smallEtaleInverseImageAdjunction.{u, w} (f ≫ g)).unit.app Q).hom.app
      (op U) ≫ a) hi).trans (Category.comp_id _)))

set_option backward.isDefEq.respectTransparency false in
-- Every section map below is an actual unit, original restriction, or canonical mate component.
theorem smallEtalePullbackGlobalSections_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtalePullbackGlobalSections.{u, w} g ≫
      Functor.whiskerLeft (smallEtaleInverseImage.{u, w} g)
        (smallEtalePullbackGlobalSections.{u, w} f) ≫
      (Functor.associator (smallEtaleInverseImage.{u, w} g)
        (smallEtaleInverseImage.{u, w} f)
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w})).inv ≫
      Functor.whiskerRight (smallEtaleInverseImageCompIso.{u, w} f g).hom
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}) =
    smallEtalePullbackGlobalSections.{u, w} (f ≫ g) := by
  apply NatTrans.ext
  funext Q
  let U := Scheme.Etale.mk (𝟙 Z)
  let V := Scheme.Etale.mk (𝟙 Y)
  let W := Scheme.Etale.mk (𝟙 X)
  let Lg := smallEtaleInverseImage.{u, w} g
  let Lf := smallEtaleInverseImage.{u, w} f
  let Lc := smallEtaleInverseImage.{u, w} (f ≫ g)
  let S := (Lg ⋙ Lf).obj Q
  let R := Lc.obj Q
  let τ := (smallEtaleInverseImageCompIso.{u, w} f g).hom.app Q
  let tg := smallEtaleBaseChangeTerminalIso g
  let tf := smallEtaleBaseChangeTerminalIso f
  let tc := smallEtaleBaseChangeTerminalIso (f ≫ g)
  let d := (smallEtaleBaseChangeComp f g).hom.app U
  let zX := smallEtaleGlobalTerminalIso.{u, w} X
  let zY := smallEtaleGlobalTerminalIso.{u, w} Y
  let zZ := smallEtaleGlobalTerminalIso.{u, w} Z
  let ηg := ((smallEtaleInverseImageAdjunction.{u, w} g).unit.app Q).hom
  let ηf := ((smallEtaleInverseImageAdjunction.{u, w} f).unit.app (Lg.obj Q)).hom
  let ηc := ((smallEtaleInverseImageAdjunction.{u, w} (f ≫ g)).unit.app Q).hom
  apply (cancel_mono (zX.hom.app R)).mp
  change (((smallEtalePullbackGlobalSections.{u, w} g).app Q ≫
      (smallEtalePullbackGlobalSections.{u, w} f).app (Lg.obj Q)) ≫
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).map τ) ≫ zX.hom.app R =
    (smallEtalePullbackGlobalSections.{u, w} (f ≫ g)).app Q ≫ zX.hom.app R
  have hn := zX.hom.naturality τ
  change (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).map τ ≫ zX.hom.app R =
    zX.hom.app S ≫ τ.hom.app (op W) at hn
  have hf := smallEtalePullbackGlobalSections_terminal_section.{u, w} f (Lg.obj Q)
  change (smallEtalePullbackGlobalSections.{u, w} f).app (Lg.obj Q) ≫ zX.hom.app S =
    zY.hom.app (Lg.obj Q) ≫ ηf.app (op V) ≫ S.obj.map tf.inv.op at hf
  have hg := smallEtalePullbackGlobalSections_terminal_section.{u, w} g Q
  have hc := smallEtalePullbackGlobalSections_terminal_section.{u, w} (f ≫ g) Q
  have hη := ηf.naturality tg.inv.op
  change (Lg.obj Q).obj.map tg.inv.op ≫ ηf.app (op V) =
    ηf.app (op ((smallEtaleBaseChange g).obj U)) ≫
      S.obj.map ((smallEtaleBaseChange f).map tg.inv).op at hη
  have hτ := τ.hom.naturality tc.inv.op
  have ht := smallEtaleBaseChangeTerminalIso_comp_inv f g
  have hu := smallEtaleInverseImageCompIso_unit_hom_app.{u, w} f g Q U
  calc
    _ = (smallEtalePullbackGlobalSections.{u, w} g).app Q ≫
        ((smallEtalePullbackGlobalSections.{u, w} f).app (Lg.obj Q) ≫ zX.hom.app S) ≫
        τ.hom.app (op W) := by
      simpa only [Category.assoc] using
        congrArg (fun a => ((smallEtalePullbackGlobalSections.{u, w} g).app Q ≫
          (smallEtalePullbackGlobalSections.{u, w} f).app (Lg.obj Q)) ≫ a) hn
    _ = (smallEtalePullbackGlobalSections.{u, w} g).app Q ≫ zY.hom.app (Lg.obj Q) ≫
        ηf.app (op V) ≫ S.obj.map tf.inv.op ≫ τ.hom.app (op W) := by
      simpa only [Category.assoc] using congrArg (fun a =>
        (smallEtalePullbackGlobalSections.{u, w} g).app Q ≫ a ≫ τ.hom.app (op W)) hf
    _ = zZ.hom.app Q ≫ ηg.app (op U) ≫ (Lg.obj Q).obj.map tg.inv.op ≫
        ηf.app (op V) ≫ S.obj.map tf.inv.op ≫ τ.hom.app (op W) := by
      simpa only [Category.assoc] using congrArg (fun a =>
        a ≫ ηf.app (op V) ≫ S.obj.map tf.inv.op ≫ τ.hom.app (op W)) hg
    _ = zZ.hom.app Q ≫ ηg.app (op U) ≫
        ηf.app (op ((smallEtaleBaseChange g).obj U)) ≫
        S.obj.map ((smallEtaleBaseChange f).map tg.inv).op ≫
        S.obj.map tf.inv.op ≫ τ.hom.app (op W) := by
      simpa only [Category.assoc] using congrArg (fun a =>
        zZ.hom.app Q ≫ ηg.app (op U) ≫ a ≫ S.obj.map tf.inv.op ≫ τ.hom.app (op W)) hη
    _ = zZ.hom.app Q ≫ ηg.app (op U) ≫
        ηf.app (op ((smallEtaleBaseChange g).obj U)) ≫
        S.obj.map (tc.inv ≫ d).op ≫ τ.hom.app (op W) := by
      have hm := S.obj.map_comp ((smallEtaleBaseChange f).map tg.inv).op tf.inv.op
      have he := congrArg (fun a => S.obj.map a.op) ht
      simpa only [Category.assoc, op_comp] using congrArg (fun a =>
        zZ.hom.app Q ≫ ηg.app (op U) ≫
        ηf.app (op ((smallEtaleBaseChange g).obj U)) ≫ a ≫ τ.hom.app (op W))
        (hm.symm.trans he.symm)
    _ = zZ.hom.app Q ≫ ηg.app (op U) ≫
        ηf.app (op ((smallEtaleBaseChange g).obj U)) ≫
        S.obj.map d.op ≫ S.obj.map tc.inv.op ≫ τ.hom.app (op W) := by
      rw [op_comp, S.obj.map_comp]
      simp only [Category.assoc]
    _ = zZ.hom.app Q ≫ ηg.app (op U) ≫
        ηf.app (op ((smallEtaleBaseChange g).obj U)) ≫
        S.obj.map d.op ≫ τ.hom.app (op ((smallEtaleBaseChange (f ≫ g)).obj U)) ≫
        R.obj.map tc.inv.op := by
      simpa only [Category.assoc] using congrArg (fun a =>
        zZ.hom.app Q ≫ ηg.app (op U) ≫ ηf.app (op ((smallEtaleBaseChange g).obj U)) ≫
        S.obj.map d.op ≫ a) hτ
    _ = zZ.hom.app Q ≫ ηc.app (op U) ≫ R.obj.map tc.inv.op := by
      simpa only [Category.assoc] using congrArg (fun a => zZ.hom.app Q ≫ a ≫ R.obj.map tc.inv.op) hu
    _ = _ := hc.symm

end AlgebraicGeometry.Scheme.DerivedSections

end
