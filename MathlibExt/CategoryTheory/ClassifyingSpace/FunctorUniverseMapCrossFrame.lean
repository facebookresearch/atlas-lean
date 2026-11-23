/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.ClassifyingSpace.FunctorUniverseMap
public import MathlibExt.CategoryTheory.NerveCrossUniverse

/-!
# Whole original realization of the Cross nerve functor

The existing mixed-world realization functor agrees with the actual
Cross nerve realization when both original nerve value worlds coincide.
Both object-lift and Hom-lift squares are derived on the entire original
chain carriers and transported by the actual realization universe Iso.
The original spaces and maps are retained, including the original value
of an arbitrary preceding mixed-world functor at every realization point.
-/

public section

noncomputable section

open CategoryTheory
open scoped Simplicial

attribute [local instance] CategoryTheory.uliftCategory

universe u v z uF vF

namespace SSet

section HomFrame

variable {C D : Type uF} [hC : Category.{vF} C] [hD : Category.{vF} D]

private def homFrameFunctor (F : C ⥤ D) :
    letI : Category.{max vF z} (ULiftHom.{z} C) :=
      @ULiftHom.category.{vF, z, uF} C hC
    letI : Category.{max vF z} (ULiftHom.{z} D) :=
      @ULiftHom.category.{vF, z, uF} D hD
    ULiftHom.{z} C ⥤ ULiftHom.{z} D := by
  letI : Category.{max vF z} (ULiftHom.{z} C) :=
    @ULiftHom.category.{vF, z, uF} C hC
  letI : Category.{max vF z} (ULiftHom.{z} D) :=
    @ULiftHom.category.{vF, z, uF} D hD
  exact
    { obj := fun X => ULiftHom.objUp (F.obj X.objDown)
      map := fun f => ULift.up (F.map f.down)
      map_id := fun X => by
        apply ULift.ext
        exact F.map_id X.objDown
      map_comp := fun f g => by
        apply ULift.ext
        exact F.map_comp f.down g.down }

private theorem homFrameFunctor_eq_composite (F : C ⥤ D) :
    letI : Category.{max vF z} (ULiftHom.{z} C) :=
      @ULiftHom.category.{vF, z, uF} C hC
    letI : Category.{max vF z} (ULiftHom.{z} D) :=
      @ULiftHom.category.{vF, z, uF} D hD
    homFrameFunctor F = ULiftHom.down ⋙ F ⋙ ULiftHom.up := by
  letI : Category.{max vF z} (ULiftHom.{z} C) :=
    @ULiftHom.category.{vF, z, uF} C hC
  letI : Category.{max vF z} (ULiftHom.{z} D) :=
    @ULiftHom.category.{vF, z, uF} D hD
  apply CategoryTheory.Functor.hext
  · intro X
    rfl
  · intro X Y f
    apply heq_of_eq
    rfl

private theorem homFrameNerveSquare (F : C ⥤ D) :
    nerveMap (homFrameFunctor F) ≫
        (nerveULiftHomIso.{uF, vF, z} D).hom =
      (nerveULiftHomIso.{uF, vF, z} C).hom ≫
        uliftFunctor.{z, max uF vF}.map (nerveMap F) := by
  ext n q
  change (nerveULiftHomIso.{uF, vF, z} D).hom.app n
      ((nerveMap (homFrameFunctor F)).app n q) =
    (uliftFunctor.{z, max uF vF}.map (nerveMap F)).app n
      ((nerveULiftHomIso.{uF, vF, z} C).hom.app n q)
  rw [nerveULiftHomIso_hom_app_eq, nerveULiftHomIso_hom_app_eq]
  change ULift.up ((q ⋙ homFrameFunctor F) ⋙ ULiftHom.down) =
    ULift.up ((q ⋙ ULiftHom.down) ⋙ F)
  apply ULift.ext
  exact CategoryTheory.Functor.ext (fun i => rfl) (fun i j f => by
    dsimp only [Functor.comp, homFrameFunctor, ULiftHom.down, ULiftHom.up,
      ULiftHom.objDown, ULiftHom.objUp]
    change F.map (q.map f).down =
      eqToHom (rfl : F.obj (q.obj i).objDown = F.obj (q.obj i).objDown) ≫
        F.map (q.map f).down ≫
          eqToHom (rfl : F.obj (q.obj j).objDown = F.obj (q.obj j).objDown)
    exact CategoryTheory.eq_conj_eqToHom (F.map (q.map f).down))

private theorem homFrameRealizationSquare (F : C ⥤ D)
    (x : toTop.obj (nerve (ULiftHom.{z} C))) :
    realizedNerveULiftHomHomeomorph.{uF, vF, z} D
        (toTop.map (nerveMap (homFrameFunctor F)) x) =
      toTop.map (nerveMap F) (realizedNerveULiftHomHomeomorph.{uF, vF, z} C x) := by
  rw [realizedNerveULiftHomHomeomorph_apply, realizedNerveULiftHomHomeomorph_apply]
  let y := toTop.map (nerveULiftHomIso.{uF, vF, z} C).hom x
  have hMap : toTop.map (nerveULiftHomIso.{uF, vF, z} D).hom
      (toTop.map (nerveMap (homFrameFunctor F)) x) =
    toTop.map (uliftFunctor.{z, max uF vF}.map (nerveMap F)) y := by
    have h := ConcreteCategory.congr_hom
      (congrArg (fun k : nerve (ULiftHom.{z} C) ⟶
          uliftFunctor.{z, max uF vF}.obj (nerve D) => toTop.map k)
        (homFrameNerveSquare F)) x
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using h
  rw [hMap]
  have hNat := ConcreteCategory.congr_hom
    (toTopULiftIso.{max uF vF, z}.hom.naturality (nerveMap F)) y
  change (toTopULiftIso.{max uF vF, z}.hom.app (nerve D))
      (toTop.map (uliftFunctor.{z, max uF vF}.map (nerveMap F)) y) =
    ULift.up (toTop.map (nerveMap F)
      ((toTopULiftIso.{max uF vF, z}.hom.app (nerve C)) y).down) at hNat
  exact congrArg ULift.down hNat

end HomFrame

section CrossFrame

variable {A : Type (max u v)} [Category.{v} A]
  {B : Type u} [Category.{v} B]

private def crossObjectFunctor (G : A ⥤ B) :
    ULift.{max u v z} A ⥤ ULift.{max u v z} B :=
  ULift.downFunctor ⋙ G ⋙ ULift.upFunctor

private theorem crossObjectNerveSquare (G : A ⥤ B) :
    nerveMap (crossObjectFunctor.{u, v, z} G) ≫
        (nerveULiftIso.{u, v, max u v z} B).hom =
      (nerveULiftIso.{max u v, v, max u v z} A).hom ≫
        uliftFunctor.{max u v z, max u v}.map (nerveMapCross G) := by
  ext n q
  change (nerveULiftIso.{u, v, max u v z} B).hom.app n
      ((nerveMap (crossObjectFunctor.{u, v, z} G)).app n q) =
    (uliftFunctor.{max u v z, max u v}.map (nerveMapCross G)).app n
      ((nerveULiftIso.{max u v, v, max u v z} A).hom.app n q)
  rw [nerveULiftIso_hom_app_eq, nerveULiftIso_hom_app_eq]
  change ULift.up ((q ⋙ crossObjectFunctor.{u, v, z} G) ⋙ ULift.downFunctor) =
    ULift.up ((q ⋙ ULift.downFunctor) ⋙ G)
  apply ULift.ext
  exact CategoryTheory.Functor.ext (fun i => rfl) (fun i j f => by
    dsimp only [Functor.comp, crossObjectFunctor, ULift.downFunctor, ULift.upFunctor]
    change G.map (q.map f) =
      eqToHom (rfl : G.obj (q.obj i).down = G.obj (q.obj i).down) ≫
        G.map (q.map f) ≫
          eqToHom (rfl : G.obj (q.obj j).down = G.obj (q.obj j).down)
    exact CategoryTheory.eq_conj_eqToHom (G.map (q.map f)))

private theorem crossObjectRealizationSquare (G : A ⥤ B)
    (x : toTop.obj (nerve (ULift.{max u v z} A))) :
    realizedNerveULiftHomeomorph.{u, v, max u v z} B
        (toTop.map (nerveMap (crossObjectFunctor.{u, v, z} G)) x) =
      toTop.map (nerveMapCross G)
        (realizedNerveULiftHomeomorph.{max u v, v, max u v z} A x) := by
  rw [realizedNerveULiftHomeomorph_apply, realizedNerveULiftHomeomorph_apply]
  let y := toTop.map (nerveULiftIso.{max u v, v, max u v z} A).hom x
  have hMap : toTop.map (nerveULiftIso.{u, v, max u v z} B).hom
      (toTop.map (nerveMap (crossObjectFunctor.{u, v, z} G)) x) =
    toTop.map (uliftFunctor.{max u v z, max u v}.map (nerveMapCross G)) y := by
    have h := ConcreteCategory.congr_hom
      (congrArg (fun k : nerve (ULift.{max u v z} A) ⟶
          uliftFunctor.{max u v z, max u v}.obj (nerve B) => toTop.map k)
        (crossObjectNerveSquare.{u, v, z} G)) x
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using h
  rw [hMap]
  have hNat := ConcreteCategory.congr_hom
    (toTopULiftIso.{max u v, max u v z}.hom.naturality (nerveMapCross G)) y
  change (toTopULiftIso.{max u v, max u v z}.hom.app (nerve B))
      (toTop.map (uliftFunctor.{max u v z, max u v}.map (nerveMapCross G)) y) =
    ULift.up (toTop.map (nerveMapCross G)
      ((toTopULiftIso.{max u v, max u v z}.hom.app (nerve A)) y).down) at hNat
  exact congrArg ULift.down hNat

/-- The actual combined lift charts are natural for the ORIGINAL Cross
functor on every original realization point, in every larger working lift. -/
private theorem crossCombinedRealizationComputed (G : A ⥤ B)
    (x : toTop.obj (nerve (ULiftHom.{max u v z} (ULift.{max u v z} A)))) :
    realizedNerveLiftHomeomorph.{u, v, max u v z} B
        (toTop.map (nerveMap
          (ULiftHom.down ⋙ (ULift.downFunctor ⋙ G ⋙ ULift.upFunctor) ⋙
            ULiftHom.up)) x) =
      toTop.map (nerveMapCross G)
        (realizedNerveLiftHomeomorph.{max u v, v, max u v z} A x) := by
  let H := realizedNerveULiftHomeomorph.{u, v, max u v z} B
  have hFunctor := homFrameFunctor_eq_composite (crossObjectFunctor.{u, v, z} G)
  have hNerve := congrArg CategoryTheory.nerveMap hFunctor
  have hTop := congrArg SSet.toTop.map hNerve
  have hValue := ConcreteCategory.congr_hom hTop x
  have hLeft := congrArg (realizedNerveLiftHomeomorph.{u, v, max u v z} B) hValue.symm
  refine hLeft.trans ?_
  rw [realizedNerveLiftHomeomorph_apply, realizedNerveLiftHomeomorph_apply]
  change H (realizedNerveULiftHomHomeomorph.{max u v z, v, max u v z}
      (ULift.{max u v z} B)
      (toTop.map (nerveMap (homFrameFunctor
        (crossObjectFunctor.{u, v, z} G))) x)) =
    toTop.map (nerveMapCross G)
      (realizedNerveULiftHomeomorph.{max u v, v, max u v z} A
        (realizedNerveULiftHomHomeomorph.{max u v z, v, max u v z}
          (ULift.{max u v z} A) x))
  exact (congrArg H (homFrameRealizationSquare
    (crossObjectFunctor.{u, v, z} G) x)).trans
      (crossObjectRealizationSquare.{u, v, z} G
        (realizedNerveULiftHomHomeomorph.{max u v z, v, max u v z}
          (ULift.{max u v z} A) x))

/-- The original combined lift charts are natural for the ACTUAL whole Cross functor. -/
theorem realizedNerveLiftHomeomorph_crossFunctor_naturality (G : A ⥤ B)
    (x : toTop.obj (nerve (ULiftHom.{max u v z} (ULift.{max u v z} A)))) :
    realizedNerveLiftHomeomorph.{u, v, max u v z} B
        (toTop.map (nerveMap
          (ULiftHom.down ⋙ (ULift.downFunctor ⋙ G ⋙ ULift.upFunctor) ⋙
            ULiftHom.up)) x) =
      toTop.map (nerveMapCross G)
        (realizedNerveLiftHomeomorph.{max u v, v, max u v z} A x) :=
  crossCombinedRealizationComputed G x

end CrossFrame

end SSet

namespace CategoryTheory

section CrossFrame

variable {A : Type (max u v)} [Category.{v} A]
  {B : Type u} [Category.{v} B]

/-- The WHOLE selected mixed-world realization map is the ORIGINAL Cross
nerve realization when the original nerve value worlds coincide. -/
theorem realizedNerveFunctorMap_crossFrame (G : A ⥤ B) :
    realizedNerveFunctorMap G = (SSet.toTop.map (nerveMapCross G)).hom := by
  rw [realizedNerveFunctorMap_recipe]
  apply ContinuousMap.ext
  intro x
  let HA := SSet.realizedNerveLiftHomeomorph.{max u v, v, max u v} A
  let HB := SSet.realizedNerveLiftHomeomorph.{u, v, max u v} B
  let L := (ULiftHomULiftCategory.equiv.{max u v, max u v, v, max u v} A).inverse ⋙
    G ⋙ (ULiftHomULiftCategory.equiv.{max u v, max u v, v, u} B).functor
  have hL : L = ULiftHom.down ⋙ (ULift.downFunctor ⋙ G ⋙ ULift.upFunctor) ⋙
      ULiftHom.up := rfl
  have h := SSet.realizedNerveLiftHomeomorph_crossFunctor_naturality.{u, v, 0}
    G (HA.symm x)
  change HB (SSet.toTop.map (nerveMap L) (HA.symm x)) =
    SSet.toTop.map (nerveMapCross G) x
  exact (congrArg (fun J : ULiftHom.{max u v} (ULift.{max u v} A) ⥤
      ULiftHom.{max u v} (ULift.{max u v} B) =>
        HB (SSet.toTop.map (nerveMap J) (HA.symm x))) hL).trans
    (h.trans (congrArg (SSet.toTop.map (nerveMapCross G)) (HA.apply_symm_apply x)))


end CrossFrame

end CategoryTheory

end
