/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroConnectedCofan
public import MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroConnectedRealization
public import MathlibExt.AlgebraicTopology.SingularSet.Coproducts
public import Mathlib.CategoryTheory.NatIso

/-!
# Connected components of the realization–singular unit

The unit `X → Sing(|X|)` of realization and the singular simplicial-set functor
induces a bijection on simplicial connected components, for every simplicial set.
For a connected object both component types are nonempty subsingletons; the general
case follows by decomposition into connected components and assembly through the
component colimit cocones.

A componentwise-colimit approach also appears in Joël Riou's
topcat-model-category development.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace SSet

private noncomputable def unitπ₀NatTrans :
    SSet.π₀Functor.{u} ⟶
      (SSet.toTop.{u} ⋙ TopCat.toSSet.{u}) ⋙ SSet.π₀Functor.{u} :=
  (Functor.leftUnitor SSet.π₀Functor).inv ≫
    Functor.whiskerRight sSetTopAdj.{u}.unit SSet.π₀Functor

private lemma unitπ₀NatTrans_app_apply
    (X : SSet.{u}) (x : SSet.π₀ X) :
    (unitπ₀NatTrans.app X) x =
      SSet.mapπ₀ (sSetTopAdj.unit.app X) x := by
  rfl

private theorem unitπ₀NatTrans_app_isIso_of_cofan
    {J : Type u} (K : J → SSet.{u}) (c : Cofan K)
    (hF : IsColimit (SSet.π₀Functor.mapCocone c))
    (hG : IsColimit
      (((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}) ⋙
        SSet.π₀Functor.{u}).mapCocone c))
    (hτ : ∀ j, IsIso (unitπ₀NatTrans.app (K j))) :
    IsIso (unitπ₀NatTrans.app c.pt) := by
  let F := SSet.π₀Functor.{u}
  let G := (SSet.toTop.{u} ⋙ TopCat.toSSet.{u}) ⋙
    SSet.π₀Functor.{u}
  let e (j : J) : F.obj (K j) ≅ G.obj (K j) := by
    letI := hτ j
    exact asIso (unitπ₀NatTrans.app (K j))
  let inverseCocone : Cocone (Discrete.functor K ⋙ G) :=
    Cocone.mk (F.obj c.pt)
      { app := fun j ↦ (e j.as).inv ≫ F.map (c.ι.app j)
        naturality := by
          intro j k f
          obtain rfl : j = k := Discrete.ext (Discrete.eq_of_hom f)
          simp }
  let φ : G.obj c.pt ⟶ F.obj c.pt := hG.desc inverseCocone
  have hφ (j : Discrete J) :
      G.map (c.ι.app j) ≫ φ =
        (e j.as).inv ≫ F.map (c.ι.app j) :=
    hG.fac inverseCocone j
  have hnat (j : Discrete J) :
      F.map (c.ι.app j) ≫ unitπ₀NatTrans.app c.pt =
        unitπ₀NatTrans.app (K j.as) ≫ G.map (c.ι.app j) :=
    unitπ₀NatTrans.naturality (c.ι.app j)
  refine ⟨φ, hF.hom_ext (fun j ↦ ?_), hG.hom_ext (fun j ↦ ?_)⟩
  · change (F.map (c.ι.app j) ≫ unitπ₀NatTrans.app c.pt) ≫ φ =
      F.map (c.ι.app j) ≫ 𝟙 _
    rw [hnat, Category.assoc, hφ]
    simp [e]
  · change (G.map (c.ι.app j) ≫ φ) ≫ unitπ₀NatTrans.app c.pt =
      G.map (c.ι.app j) ≫ 𝟙 _
    rw [hφ, Category.assoc, hnat]
    simp [e]

/--
For a connected simplicial set `X`, the unit `X → Sing(|X|)` induces a bijection
on simplicial connected components.
-/
theorem bijective_mapπ₀_sSetTopAdj_unit_app_of_isConnected
    (X : SSet.{u}) [SSet.IsConnected X] :
    Function.Bijective (SSet.mapπ₀ (sSetTopAdj.unit.app X)) := by
  let _ : PathConnectedSpace ↑(SSet.toTop.obj X) :=
    SSet.pathConnectedSpace_realization_of_isConnected X
  exact Function.bijective_of_subsingleton'
    (α := SSet.π₀ X)
    (β := SSet.π₀ (TopCat.toSSet.obj (SSet.toTop.obj X)))
    (SSet.mapπ₀ (sSetTopAdj.unit.app X))

/--
For every simplicial set `X`, the unit `X → Sing(|X|)` induces a bijection on
simplicial connected components.
-/
theorem bijective_mapπ₀_sSetTopAdj_unit_app (X : SSet.{u}) :
    Function.Bijective (SSet.mapπ₀ (sSetTopAdj.unit.app X)) := by
  let K : SSet.π₀ X → SSet.{u} := fun c ↦
    (SSet.π₀.component c : SSet)
  let cX : Cofan K := SSet.π₀.cofan X
  let R := SSet.toTop.{u} ⋙ TopCat.toSSet.{u}
  have hX : IsColimit cX := SSet.π₀.isColimitCofan X
  have hF : IsColimit (SSet.π₀Functor.mapCocone cX) :=
    SSet.π₀.isColimitMapCoconeOfConnected K cX hX
  have hR : IsColimit (R.mapCocone cX) :=
    isColimitOfPreserves R hX
  let _ (c : SSet.π₀ X) :
      PathConnectedSpace ↑(SSet.toTop.obj (K c)) :=
    SSet.pathConnectedSpace_realization_of_isConnected (K c)
  let _ (c : SSet.π₀ X) : SSet.IsConnected (R.obj (K c)) := by
    change SSet.IsConnected
      (TopCat.toSSet.obj (SSet.toTop.obj (K c)))
    infer_instance
  let RcX : Cofan (fun c : SSet.π₀ X ↦ R.obj (K c)) :=
    Cofan.mk (R.obj cX.pt) (fun c ↦ R.map (cX.inj c))
  have hRcX : IsColimit RcX :=
    (isColimitMapCoconeCofanMkEquiv R K
      (fun c ↦ cX.inj c)) hR
  have hπRcX : IsColimit (SSet.π₀Functor.mapCocone RcX) :=
    SSet.π₀.isColimitMapCoconeOfConnected
      (fun c ↦ R.obj (K c)) RcX hRcX
  have hExplicitG : IsColimit
      (Cofan.mk _
        (fun c : SSet.π₀ X ↦
          SSet.π₀Functor.map (R.map (cX.inj c))) :
        Cofan (fun c : SSet.π₀ X ↦
          SSet.π₀Functor.obj (R.obj (K c)))) :=
    (isColimitMapCoconeCofanMkEquiv SSet.π₀Functor
      (fun c : SSet.π₀ X ↦ R.obj (K c))
      (fun c ↦ R.map (cX.inj c))) hπRcX
  have hG : IsColimit
      ((R ⋙ SSet.π₀Functor.{u}).mapCocone cX) :=
    (isColimitMapCoconeCofanMkEquiv (R ⋙ SSet.π₀Functor) K
      (fun c ↦ cX.inj c)).symm hExplicitG
  have hτ (c : SSet.π₀ X) :
      IsIso (unitπ₀NatTrans.app (K c)) := by
    rw [CategoryTheory.isIso_iff_bijective]
    have heq :
        (unitπ₀NatTrans.app (K c) :
          SSet.π₀ (K c) → SSet.π₀ (R.obj (K c))) =
        SSet.mapπ₀ (sSetTopAdj.unit.app (K c)) := by
      funext q
      exact unitπ₀NatTrans_app_apply (K c) q
    rw [heq]
    exact bijective_mapπ₀_sSetTopAdj_unit_app_of_isConnected (K c)
  have hIso : IsIso (unitπ₀NatTrans.app cX.pt) :=
    unitπ₀NatTrans_app_isIso_of_cofan K cX hF hG hτ
  have hIsoX : IsIso (unitπ₀NatTrans.app X) := by
    simpa [cX] using hIso
  have h : Function.Bijective
      (unitπ₀NatTrans.app X :
        SSet.π₀ X → SSet.π₀ (R.obj X)) :=
    (CategoryTheory.isIso_iff_bijective _).mp hIsoX
  have heq :
      (unitπ₀NatTrans.app X :
        SSet.π₀ X → SSet.π₀ (R.obj X)) =
      SSet.mapπ₀ (sSetTopAdj.unit.app X) := by
    funext q
    exact unitπ₀NatTrans_app_apply X q
  rw [← heq]
  exact h

end SSet
