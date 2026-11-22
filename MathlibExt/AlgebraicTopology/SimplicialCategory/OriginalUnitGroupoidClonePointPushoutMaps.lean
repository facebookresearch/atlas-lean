/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnitGroupoidCloneMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnitGroupoidClonePushout

/-!
# The SAME original maps between actual unit-groupoid point pushouts are weak

The literal full unit and old-source squares commute with the original
clone map. Genuine pushout isomorphisms retain both complete original
legs. Thus any actual map with those SAME triangles is DK weak from
the actual original source-map weakness, without a model assumption.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.UnitGroupoidClone

variable {C D : Carrier.{u}} (F : C ⟶ D) (x : C)

/-- The SAME entire original two-label unit functor commutes with the actual full clone map. -/
theorem unitMap_map : unitMap C x ≫ map F x = unitMap D (F.obj x) := by
  apply EnrichedFunctor.ext SSet.{u}
    (F := unitMap C x ≫ map F x) (G := unitMap D (F.obj x))
    (fun a => by rcases a with ⟨a⟩; cases a <;> rfl)
  intro a b
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  cases a <;> cases b
  all_goals
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro p
    exact congrArg (fun f : (𝟙_ SSet.{u}) ⟶ (F.obj x ⟶[SSet.{u}] F.obj x) => f.app q p) (F.map_id x)

/-- Any SAME original map of genuine unit-groupoid point pushouts preserves actual DK weakness. -/
theorem unit_pushout_map_weak {P Q : Carrier.{u}}
    {u : unitDomain.{u} ⟶ P} {c : C ⟶ P} {v : unitDomain.{u} ⟶ Q} {d : D ⟶ Q}
    (sq : IsPushout unitPoint.{u} (BergnerObjects.select (C := C) x) u c)
    (sq' : IsPushout unitPoint.{u} (BergnerObjects.select (C := D) (F.obj x)) v d)
    (T : P ⟶ Q) (hu : u ≫ T = v) (hc : c ≫ T = F ≫ d)
    (hF : EnrichedDwyerKan.weakEquivalences F) : EnrichedDwyerKan.weakEquivalences T := by
  let e := (unit_isPushout C x).isoIsPushout _ _ sq
  let e' := (unit_isPushout D (F.obj x)).isoIsPushout _ _ sq'
  let L := e.inv ≫ map F x ≫ e'.hom
  have hl : u ≫ L = v := by
    calc
      u ≫ L = ((u ≫ e.inv) ≫ map F x) ≫ e'.hom := by simp only [L, Category.assoc]
      _ = (unitMap C x ≫ map F x) ≫ e'.hom :=
        congrArg (fun k => (k ≫ map F x) ≫ e'.hom) ((unit_isPushout C x).inl_isoIsPushout_inv _ _ sq)
      _ = unitMap D (F.obj x) ≫ e'.hom := congrArg (fun k => k ≫ e'.hom) (unitMap_map F x)
      _ = v := (unit_isPushout D (F.obj x)).inl_isoIsPushout_hom _ _ sq'
  have hr : c ≫ L = F ≫ d := by
    calc
      c ≫ L = ((c ≫ e.inv) ≫ map F x) ≫ e'.hom := by simp only [L, Category.assoc]
      _ = (inclusion C x ≫ map F x) ≫ e'.hom :=
        congrArg (fun k => (k ≫ map F x) ≫ e'.hom) ((unit_isPushout C x).inr_isoIsPushout_inv _ _ sq)
      _ = (F ≫ inclusion D (F.obj x)) ≫ e'.hom :=
        congrArg (fun k => k ≫ e'.hom) (inclusion_map F x)
      _ = F ≫ (inclusion D (F.obj x) ≫ e'.hom) := Category.assoc _ _ _
      _ = F ≫ d := congrArg (fun k => F ≫ k) ((unit_isPushout D (F.obj x)).inr_isoIsPushout_hom _ _ sq')
  have hL : L = T := sq.hom_ext (hl.trans hu.symm) (hr.trans hc.symm)
  have hw : EnrichedDwyerKan.weakEquivalences L :=
    EnrichedDwyerKan.weakEquivalences.comp_mem _ _
      (EnrichedDwyerKan.weakEquivalences.of_isIso e.inv)
      (EnrichedDwyerKan.weakEquivalences.comp_mem _ _ (map_weak F x hF)
        (EnrichedDwyerKan.weakEquivalences.of_isIso e'.hom))
  exact hL ▸ hw

end CategoryTheory.SimplicialEnrichment.UnitGroupoidClone
