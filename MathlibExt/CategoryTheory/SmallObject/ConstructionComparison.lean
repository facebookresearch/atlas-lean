/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.SmallObject.Construction
public import MathlibExt.CategoryTheory.SmallObject.FunctorObjIndex
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square

/-!
# Canonical comparison of one-step small-object attachments

The original whole generator labels, chosen coproducts and pushouts are
mapped through a full faithful colimit-preserving functor. Their universal
properties give the actual Arrow natural isomorphism, with original base,
unit, cells and right factors retained.

This uses Mathlib's small-object construction by Joël Riou (2024), its
full-faithful preimage API and native cofan/pushout universal properties.
No model or small-object eligibility condition is selected here.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe theta s vC vD uC uD
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.SmallObject

variable {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D]
    {I : Type s} [Small.{theta} I] {A B : I → C}
    (j : ∀ i, A i ⟶ B i) (F : C ⥤ D)
    [F.Full] [F.Faithful]
    [LocallySmall.{theta} C]
    [HasPushouts C] [HasPushouts D]
    [∀ {X S : C} (p : X ⟶ S),
      HasColimitsOfShape (Discrete (FunctorObjIndex j p)) C]
    [∀ {X S : D} (p : X ⟶ S),
      HasColimitsOfShape (Discrete (FunctorObjIndex (fun i => F.map (j i)) p)) D]
    [PreservesColimitsOfSize.{theta, theta} F]

/-- The actual chosen one-step attachment commutes with a full faithful
structural-colimit-preserving functor, retaining the original label family. -/
def functorMapIso :
    SmallObject.functor j ⋙ F.mapArrow ≅
      F.mapArrow ⋙ SmallObject.functor (fun i => F.map (j i)) := by
  classical
  -- Discrete(Shrink theta Q) is SmallCategory in BOTH universes theta.
  -- Transfer this preservation to the SAME original, unshrunk Q.
  letI (p : Arrow C) :
      PreservesColimitsOfShape (Discrete (FunctorObjIndex j p.hom)) F :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (equivShrink.{theta} (FunctorObjIndex j p.hom))).symm F
  letI : PreservesColimitsOfSize.{0, 0} F :=
    preservesSmallestColimits_of_preservesColimits F
  let jF := fun i => F.map (j i)
  let mappedCofan (p : Arrow C) (K : I → C) :
      Cofan (fun q : FunctorObjIndex jF (F.map p.hom) => F.obj (K q.i)) :=
    Cofan.mk (F.obj (∐ fun q : FunctorObjIndex j p.hom => K q.i))
      (fun q => F.map (Sigma.ι (fun q : FunctorObjIndex j p.hom => K q.i)
        ((FunctorObjIndex.equivMap j F p.hom).symm q)))
  have mappedCofanIsColimit (p : Arrow C) (K : I → C) :
      IsColimit (mappedCofan p K) := by
    exact (Cofan.isColimitEquivOfEquiv (FunctorObjIndex.equivMap j F p.hom).symm
      (Cofan.mk (F.obj (∐ fun q : FunctorObjIndex j p.hom => K q.i))
        (fun q => F.map (Sigma.ι (fun q : FunctorObjIndex j p.hom => K q.i) q)))).1
      (isColimitOfHasCoproductOfPreservesColimit F
        (fun q : FunctorObjIndex j p.hom => K q.i))
  let familyIso (p : Arrow C) (K : I → C) :
      F.obj (∐ fun q : FunctorObjIndex j p.hom => K q.i) ≅
        ∐ (fun q : FunctorObjIndex jF (F.map p.hom) => F.obj (K q.i)) :=
    (mappedCofanIsColimit p K).coconePointUniqueUpToIso (coproductIsCoproduct _)
  have familyIso_ι (p : Arrow C) (K : I → C) (q : FunctorObjIndex j p.hom) :
      F.map (Sigma.ι (fun q : FunctorObjIndex j p.hom => K q.i) q) ≫
        (familyIso p K).hom =
      Sigma.ι (fun q : FunctorObjIndex jF (F.map p.hom) => F.obj (K q.i)) (q.map F) := by
    have h := IsColimit.comp_coconePointUniqueUpToIso_hom
      (mappedCofanIsColimit p K) (coproductIsCoproduct _)
        (Discrete.mk (q.map F))
    have hi : Sigma.ι (fun q : FunctorObjIndex j p.hom => K q.i)
          ((FunctorObjIndex.equivMap j F p.hom).symm (q.map F)) =
        Sigma.ι (fun q : FunctorObjIndex j p.hom => K q.i) q := by
      congr 1
      simpa only [FunctorObjIndex.equivMap_apply] using
        (FunctorObjIndex.equivMap j F p.hom).symm_apply_apply q
    exact (congrArg (fun l => F.map l ≫ (familyIso p K).hom) hi).symm.trans h
  have familyIso_inv_ι (p : Arrow C) (K : I → C) (q : FunctorObjIndex j p.hom) :
      Sigma.ι (fun q : FunctorObjIndex jF (F.map p.hom) => F.obj (K q.i)) (q.map F) ≫
        (familyIso p K).inv =
      F.map (Sigma.ι (fun q : FunctorObjIndex j p.hom => K q.i) q) := by
    exact (Iso.comp_inv_eq (familyIso p K)).2 (familyIso_ι p K q).symm
  have mappedCoproduct_ext (p : Arrow C) (K : I → C) {Z : D}
      {a b : F.obj (∐ fun q : FunctorObjIndex j p.hom => K q.i) ⟶ Z}
      (h : ∀ q, F.map (Sigma.ι (fun q : FunctorObjIndex j p.hom => K q.i) q) ≫ a =
        F.map (Sigma.ι (fun q : FunctorObjIndex j p.hom => K q.i) q) ≫ b) : a = b :=
    (isColimitOfHasCoproductOfPreservesColimit F
      (fun q : FunctorObjIndex j p.hom => K q.i)).hom_ext (fun ⟨q⟩ => h q)
  have topComp (p : Arrow C) :
      (familyIso p A).hom ≫ functorObjTop jF (F.map p.hom) =
        F.map (functorObjTop j p.hom) := by
    apply mappedCoproduct_ext p A
    intro q
    rw [← Category.assoc, familyIso_ι]
    simp only [functorObjTop]
    rw [← F.map_comp]
    simp [FunctorObjIndex.map]
  have leftComp (p : Arrow C) :
      F.map (functorObjLeft j p.hom) ≫ (familyIso p B).hom =
        (familyIso p A).hom ≫ functorObjLeft jF (F.map p.hom) := by
    apply mappedCoproduct_ext p A
    intro q
    rw [← Category.assoc, ← F.map_comp]
    simp only [functorObjLeft, Sigma.ι_map, Functor.map_comp, Category.assoc]
    rw [familyIso_ι, ← Category.assoc, familyIso_ι]
    simp [FunctorObjIndex.map, jF]
  have projectionComp (p : Arrow C) :
      (familyIso p B).hom ≫ π'FunctorObj jF (F.map p.hom) =
        F.map (π'FunctorObj j p.hom) := by
    apply mappedCoproduct_ext p B
    intro q
    rw [← Category.assoc, familyIso_ι]
    simp [π'FunctorObj, ← F.map_comp, FunctorObjIndex.map]
  have mappedPushout (p : Arrow C) :
      IsPushout (functorObjTop jF (F.map p.hom)) (functorObjLeft jF (F.map p.hom))
        (F.map (ιFunctorObj j p.hom))
        ((familyIso p B).inv ≫ F.map (ρFunctorObj j p.hom)) := by
    apply ((functorObj_isPushout j p.hom).map F).of_iso
      (familyIso p A) (Iso.refl _) (familyIso p B) (Iso.refl _)
    · simpa using (topComp p).symm
    · exact leftComp p
    · simp
    · simp
  let χ (p : Arrow C) : F.obj (functorObj j p.hom) ≅ functorObj jF (F.map p.hom) :=
    (mappedPushout p).isoPushout
  have χ_unit (p : Arrow C) :
      F.map (ιFunctorObj j p.hom) ≫ (χ p).hom = ιFunctorObj jF (F.map p.hom) :=
    (mappedPushout p).inl_isoPushout_hom
  have χ_target (p : Arrow C) :
      F.map (ρFunctorObj j p.hom) ≫ (χ p).hom =
        (familyIso p B).hom ≫ ρFunctorObj jF (F.map p.hom) := by
    apply (cancel_epi (familyIso p B).inv).1
    simpa only [χ, Category.assoc, Iso.inv_hom_id_assoc] using
      (mappedPushout p).inr_isoPushout_hom
  have χ_cell (p : Arrow C) (q : FunctorObjIndex j p.hom) :
      F.map (Sigma.ι (functorObjTgtFamily j p.hom) q ≫ ρFunctorObj j p.hom) ≫
        (χ p).hom =
      Sigma.ι (functorObjTgtFamily jF (F.map p.hom)) (q.map F) ≫
        ρFunctorObj jF (F.map p.hom) := by
    rw [Functor.map_comp, Category.assoc, χ_target, ← Category.assoc, familyIso_ι]
    rfl
  have χ_factor (p : Arrow C) :
      (χ p).hom ≫ πFunctorObj jF (F.map p.hom) = F.map (πFunctorObj j p.hom) := by
    apply (mappedPushout p).hom_ext
    · rw [← Category.assoc, χ_unit]
      simp [← F.map_comp]
    · rw [← Category.assoc, (mappedPushout p).inr_isoPushout_hom]
      simp only [ρFunctorObj_π]
      rw [Category.assoc, ← F.map_comp, ρFunctorObj_π, ← projectionComp]
      simp
  have cellInjection (p : Arrow C) (q : FunctorObjIndex j p.hom) :
      Sigma.ι (functorObjTgtFamily jF (F.map p.hom)) (q.map F) ≫
        ((familyIso p B).inv ≫ F.map (ρFunctorObj j p.hom)) =
      F.map (Sigma.ι (functorObjTgtFamily j p.hom) q ≫ ρFunctorObj j p.hom) := by
    have h := congrArg (fun k => k ≫ F.map (ρFunctorObj j p.hom))
      (familyIso_inv_ι p B q)
    simpa only [jF, functorObjTgtFamily, FunctorObjIndex.map,
      Category.assoc, Functor.map_comp] using h
  have χ_naturality {p p' : Arrow C} (τ : p ⟶ p') :
      F.map (functorMap j τ) ≫ (χ p').hom =
        (χ p).hom ≫ functorMap jF (F.mapArrow.map τ) := by
    apply (mappedPushout p).hom_ext
    · have h := congrArg (fun k => F.map k ≫ (χ p').hom)
        (ιFunctorObj_naturality j (πX := p.hom) (πY := p'.hom) τ)
      simp only [Functor.map_comp, Category.assoc, χ_unit] at h
      exact h.trans (((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ functorMap jF (F.mapArrow.map τ)) (χ_unit p)).trans
          (ιFunctorObj_naturality jF (πX := F.map p.hom)
            (πY := F.map p'.hom) (F.mapArrow.map τ)))).symm)
    · apply (coproductIsCoproduct (functorObjTgtFamily jF (F.map p.hom))).hom_ext
      rintro ⟨r⟩
      obtain ⟨q, rfl⟩ := (FunctorObjIndex.equivMap j F p.hom).surjective r
      have hpoint :
          F.map (Sigma.ι (functorObjTgtFamily j p.hom) q ≫ ρFunctorObj j p.hom) ≫
              (F.map (functorMap j τ) ≫ (χ p').hom) =
            F.map (Sigma.ι (functorObjTgtFamily j p.hom) q ≫ ρFunctorObj j p.hom) ≫
              ((χ p).hom ≫ functorMap jF (F.mapArrow.map τ)) := by
        have hsource :
            (Sigma.ι (functorObjTgtFamily j p.hom) q ≫ ρFunctorObj j p.hom) ≫
                functorMap j τ =
              Sigma.ι (functorObjTgtFamily j p'.hom) (q.postcomp τ) ≫
                ρFunctorObj j p'.hom := by
          simpa [functorMap, FunctorObjIndex.postcomp] using
            ι_functorMapTgt_assoc j τ q.i q.t q.b q.w _ rfl _ rfl
              (ρFunctorObj j p'.hom)
        have htarget :
            (Sigma.ι (functorObjTgtFamily jF (F.map p.hom)) (q.map F) ≫
                ρFunctorObj jF (F.map p.hom)) ≫ functorMap jF (F.mapArrow.map τ) =
              Sigma.ι (functorObjTgtFamily jF (F.map p'.hom))
                ((q.map F).postcomp (F.mapArrow.map τ)) ≫
                  ρFunctorObj jF (F.map p'.hom) := by
          rcases q with ⟨i, t, b, w⟩
          simpa [functorMap, FunctorObjIndex.postcomp, FunctorObjIndex.map] using
            ι_functorMapTgt_assoc jF (F.mapArrow.map τ) i (F.map t) (F.map b)
              (by simpa only [Functor.map_comp] using F.congr_map w)
              _ rfl _ rfl (ρFunctorObj jF (F.map p'.hom))
        have hlabel :
            Sigma.ι (functorObjTgtFamily jF (F.map p'.hom)) ((q.postcomp τ).map F) ≫
                ρFunctorObj jF (F.map p'.hom) =
              Sigma.ι (functorObjTgtFamily jF (F.map p'.hom))
                ((q.map F).postcomp (F.mapArrow.map τ)) ≫
                  ρFunctorObj jF (F.map p'.hom) := by
          rcases q with ⟨i, t, b, w⟩
          congr 2
          exact FunctorObjIndex.map_postcomp ⟨i, t, b, w⟩ τ F
        have h := (congrArg (fun k => F.map k ≫ (χ p').hom) hsource).trans
          ((χ_cell p' (q.postcomp τ)).trans (hlabel.trans
            (htarget.symm.trans (congrArg
              (fun k => k ≫ functorMap jF (F.mapArrow.map τ)) (χ_cell p q)).symm)))
        simpa only [Functor.map_comp, Category.assoc] using h
      change Sigma.ι (functorObjTgtFamily jF (F.map p.hom)) (q.map F) ≫
          (((familyIso p B).inv ≫ F.map (ρFunctorObj j p.hom)) ≫
            (F.map (functorMap j τ) ≫ (χ p').hom)) =
        Sigma.ι (functorObjTgtFamily jF (F.map p.hom)) (q.map F) ≫
          (((familyIso p B).inv ≫ F.map (ρFunctorObj j p.hom)) ≫
            ((χ p).hom ≫ functorMap jF (F.mapArrow.map τ)))
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ (F.map (functorMap j τ) ≫ (χ p').hom))
          (cellInjection p q)).trans
          (hpoint.trans ((congrArg
            (fun k => k ≫ ((χ p).hom ≫ functorMap jF (F.mapArrow.map τ)))
            (cellInjection p q)).symm.trans (Category.assoc _ _ _))))
  refine NatIso.ofComponents
    (fun p => Arrow.isoMk' (F.map (πFunctorObj j p.hom))
      (πFunctorObj jF (F.map p.hom)) (χ p) (Iso.refl _) (by simpa using χ_factor p)) ?_
  intro p p' τ
  apply Arrow.hom_ext
  · exact χ_naturality τ
  · change F.map τ.right ≫ 𝟙 _ = 𝟙 _ ≫ F.map τ.right
    simp

/-- Both actual comparison components leave the original base unchanged. -/
theorem functorMapIso_right {X S : C} (p : X ⟶ S) :
    ((functorMapIso j F).app (Arrow.mk p)).hom.right = 𝟙 (F.obj S) ∧
    ((functorMapIso j F).app (Arrow.mk p)).inv.right = 𝟙 (F.obj S) :=
  ⟨rfl, rfl⟩

omit [HasPushouts C] [HasPushouts D] in
/-- Both directions for each original src-cofan injection.
The comparison term uses the mapped original cofan and the supplied coproduct. -/
theorem functorMapIso_src_cofan {X S : C} (p : X ⟶ S) :
  letI : PreservesColimitsOfShape (Discrete (FunctorObjIndex j p)) F :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (equivShrink.{theta} (FunctorObjIndex j p))).symm F
  let c : Cofan (fun r : FunctorObjIndex (fun i => F.map (j i)) (F.map p) =>
      F.obj (A r.i)) :=
    Cofan.mk (F.obj (∐ fun q : FunctorObjIndex j p => A q.i))
      (fun r => F.map (Sigma.ι (fun q : FunctorObjIndex j p => A q.i)
        ((FunctorObjIndex.equivMap j F p).symm r)))
  let hc : IsColimit c :=
    (Cofan.isColimitEquivOfEquiv (FunctorObjIndex.equivMap j F p).symm
      (Cofan.mk (F.obj (∐ fun q : FunctorObjIndex j p => A q.i))
        (fun q => F.map (Sigma.ι (fun q : FunctorObjIndex j p => A q.i) q)))).1
      (isColimitOfHasCoproductOfPreservesColimit F
        (fun q : FunctorObjIndex j p => A q.i))
  let v := hc.coconePointUniqueUpToIso (coproductIsCoproduct _)
  ∀ q : FunctorObjIndex j p,
    F.map (Sigma.ι (fun q : FunctorObjIndex j p => A q.i) q) ≫ v.hom =
      Sigma.ι (fun r : FunctorObjIndex (fun i => F.map (j i)) (F.map p) =>
        F.obj (A r.i)) (q.map F) ∧
    Sigma.ι (fun r : FunctorObjIndex (fun i => F.map (j i)) (F.map p) =>
        F.obj (A r.i)) (q.map F) ≫ v.inv =
      F.map (Sigma.ι (fun q : FunctorObjIndex j p => A q.i) q) := by
  let _ : PreservesColimitsOfShape (Discrete (FunctorObjIndex j p)) F :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (equivShrink.{theta} (FunctorObjIndex j p))).symm F
  let c : Cofan (fun r : FunctorObjIndex (fun i => F.map (j i)) (F.map p) =>
      F.obj (A r.i)) :=
    Cofan.mk (F.obj (∐ fun q : FunctorObjIndex j p => A q.i))
      (fun r => F.map (Sigma.ι (fun q : FunctorObjIndex j p => A q.i)
        ((FunctorObjIndex.equivMap j F p).symm r)))
  let hc : IsColimit c :=
    (Cofan.isColimitEquivOfEquiv (FunctorObjIndex.equivMap j F p).symm
      (Cofan.mk (F.obj (∐ fun q : FunctorObjIndex j p => A q.i))
        (fun q => F.map (Sigma.ι (fun q : FunctorObjIndex j p => A q.i) q)))).1
      (isColimitOfHasCoproductOfPreservesColimit F
        (fun q : FunctorObjIndex j p => A q.i))
  let v := hc.coconePointUniqueUpToIso (coproductIsCoproduct _)
  change ∀ q : FunctorObjIndex j p,
    F.map (Sigma.ι (fun q : FunctorObjIndex j p => A q.i) q) ≫ v.hom =
      Sigma.ι (fun r : FunctorObjIndex (fun i => F.map (j i)) (F.map p) =>
        F.obj (A r.i)) (q.map F) ∧
    Sigma.ι (fun r : FunctorObjIndex (fun i => F.map (j i)) (F.map p) =>
        F.obj (A r.i)) (q.map F) ≫ v.inv =
      F.map (Sigma.ι (fun q : FunctorObjIndex j p => A q.i) q)
  intro q
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom hc
    (coproductIsCoproduct (fun r : FunctorObjIndex (fun i => F.map (j i)) (F.map p) =>
      F.obj (A r.i))) (Discrete.mk (q.map F))
  have hi : Sigma.ι (fun q : FunctorObjIndex j p => A q.i)
      ((FunctorObjIndex.equivMap j F p).symm (q.map F)) =
    Sigma.ι (fun q : FunctorObjIndex j p => A q.i) q := by
    congr 1
    simpa only [FunctorObjIndex.equivMap_apply] using
      (FunctorObjIndex.equivMap j F p).symm_apply_apply q
  have hforward : F.map (Sigma.ι (fun q : FunctorObjIndex j p => A q.i) q) ≫
      v.hom = Sigma.ι (fun r : FunctorObjIndex (fun i => F.map (j i)) (F.map p) =>
        F.obj (A r.i)) (q.map F) :=
    (congrArg (fun k => F.map k ≫ v.hom) hi).symm.trans h
  exact ⟨hforward, (Iso.comp_inv_eq v).2 hforward.symm⟩

omit [HasPushouts C] [HasPushouts D] in
/-- Both directions for each original tgt-cofan injection.
The comparison term uses the mapped original cofan and the supplied coproduct. -/
theorem functorMapIso_tgt_cofan {X S : C} (p : X ⟶ S) :
  letI : PreservesColimitsOfShape (Discrete (FunctorObjIndex j p)) F :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (equivShrink.{theta} (FunctorObjIndex j p))).symm F
  let c : Cofan (fun r : FunctorObjIndex (fun i => F.map (j i)) (F.map p) =>
      F.obj (B r.i)) :=
    Cofan.mk (F.obj (∐ fun q : FunctorObjIndex j p => B q.i))
      (fun r => F.map (Sigma.ι (fun q : FunctorObjIndex j p => B q.i)
        ((FunctorObjIndex.equivMap j F p).symm r)))
  let hc : IsColimit c :=
    (Cofan.isColimitEquivOfEquiv (FunctorObjIndex.equivMap j F p).symm
      (Cofan.mk (F.obj (∐ fun q : FunctorObjIndex j p => B q.i))
        (fun q => F.map (Sigma.ι (fun q : FunctorObjIndex j p => B q.i) q)))).1
      (isColimitOfHasCoproductOfPreservesColimit F
        (fun q : FunctorObjIndex j p => B q.i))
  let v := hc.coconePointUniqueUpToIso (coproductIsCoproduct _)
  ∀ q : FunctorObjIndex j p,
    F.map (Sigma.ι (fun q : FunctorObjIndex j p => B q.i) q) ≫ v.hom =
      Sigma.ι (fun r : FunctorObjIndex (fun i => F.map (j i)) (F.map p) =>
        F.obj (B r.i)) (q.map F) ∧
    Sigma.ι (fun r : FunctorObjIndex (fun i => F.map (j i)) (F.map p) =>
        F.obj (B r.i)) (q.map F) ≫ v.inv =
      F.map (Sigma.ι (fun q : FunctorObjIndex j p => B q.i) q) := by
  let _ : PreservesColimitsOfShape (Discrete (FunctorObjIndex j p)) F :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (equivShrink.{theta} (FunctorObjIndex j p))).symm F
  let c : Cofan (fun r : FunctorObjIndex (fun i => F.map (j i)) (F.map p) =>
      F.obj (B r.i)) :=
    Cofan.mk (F.obj (∐ fun q : FunctorObjIndex j p => B q.i))
      (fun r => F.map (Sigma.ι (fun q : FunctorObjIndex j p => B q.i)
        ((FunctorObjIndex.equivMap j F p).symm r)))
  let hc : IsColimit c :=
    (Cofan.isColimitEquivOfEquiv (FunctorObjIndex.equivMap j F p).symm
      (Cofan.mk (F.obj (∐ fun q : FunctorObjIndex j p => B q.i))
        (fun q => F.map (Sigma.ι (fun q : FunctorObjIndex j p => B q.i) q)))).1
      (isColimitOfHasCoproductOfPreservesColimit F
        (fun q : FunctorObjIndex j p => B q.i))
  let v := hc.coconePointUniqueUpToIso (coproductIsCoproduct _)
  change ∀ q : FunctorObjIndex j p,
    F.map (Sigma.ι (fun q : FunctorObjIndex j p => B q.i) q) ≫ v.hom =
      Sigma.ι (fun r : FunctorObjIndex (fun i => F.map (j i)) (F.map p) =>
        F.obj (B r.i)) (q.map F) ∧
    Sigma.ι (fun r : FunctorObjIndex (fun i => F.map (j i)) (F.map p) =>
        F.obj (B r.i)) (q.map F) ≫ v.inv =
      F.map (Sigma.ι (fun q : FunctorObjIndex j p => B q.i) q)
  intro q
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom hc
    (coproductIsCoproduct (fun r : FunctorObjIndex (fun i => F.map (j i)) (F.map p) =>
      F.obj (B r.i))) (Discrete.mk (q.map F))
  have hi : Sigma.ι (fun q : FunctorObjIndex j p => B q.i)
      ((FunctorObjIndex.equivMap j F p).symm (q.map F)) =
    Sigma.ι (fun q : FunctorObjIndex j p => B q.i) q := by
    congr 1
    simpa only [FunctorObjIndex.equivMap_apply] using
      (FunctorObjIndex.equivMap j F p).symm_apply_apply q
  have hforward : F.map (Sigma.ι (fun q : FunctorObjIndex j p => B q.i) q) ≫
      v.hom = Sigma.ι (fun r : FunctorObjIndex (fun i => F.map (j i)) (F.map p) =>
        F.obj (B r.i)) (q.map F) :=
    (congrArg (fun k => F.map k ≫ v.hom) hi).symm.trans h
  exact ⟨hforward, (Iso.comp_inv_eq v).2 hforward.symm⟩

/-- Both right-factor equations for the actual original component. -/
theorem functorMapIso_factor {X S : C} (p : X ⟶ S) :
    ((functorMapIso j F).app (Arrow.mk p)).hom.left ≫
        πFunctorObj (fun i => F.map (j i)) (F.map p) = F.map (πFunctorObj j p) ∧
    ((functorMapIso j F).app (Arrow.mk p)).inv.left ≫ F.map (πFunctorObj j p) =
      πFunctorObj (fun i => F.map (j i)) (F.map p) := by
  constructor
  · have h := Arrow.w_mk (((functorMapIso j F).app (Arrow.mk p)).hom)
    change _ ≫ πFunctorObj (fun i => F.map (j i)) (F.map p) =
      F.map (πFunctorObj j p) ≫ _ at h
    rw [(functorMapIso_right j F p).1] at h
    exact h.trans (Category.comp_id _)
  · have h := Arrow.w_mk (((functorMapIso j F).app (Arrow.mk p)).inv)
    change _ ≫ F.map (πFunctorObj j p) =
      πFunctorObj (fun i => F.map (j i)) (F.map p) ≫ _ at h
    rw [(functorMapIso_right j F p).2] at h
    exact h.trans (Category.comp_id _)

/-- The canonical component carries the original unit to the chosen mapped unit. -/
theorem functorMapIso_unit_app {X S : C} (p : X ⟶ S) :
    F.map (ιFunctorObj j p) ≫ ((functorMapIso j F).app (Arrow.mk p)).hom.left =
      ιFunctorObj (fun i => F.map (j i)) (F.map p) := by
  classical
  dsimp [functorMapIso]
  exact IsPushout.inl_isoPushout_hom _

/-- The inverse component retains that same original unit. -/
theorem functorMapIso_unit_app_inv {X S : C} (p : X ⟶ S) :
    ιFunctorObj (fun i => F.map (j i)) (F.map p) ≫
        ((functorMapIso j F).app (Arrow.mk p)).inv.left = F.map (ιFunctorObj j p) := by
  let χ := Arrow.leftFunc.mapIso ((functorMapIso j F).app (Arrow.mk p))
  exact (Iso.comp_inv_eq χ).2 (functorMapIso_unit_app j F p).symm

/-- Compatibility of whole pointed units with the actual native unitors. -/
theorem functorMapIso_unit :
    (F.mapArrow.leftUnitor).inv ≫
        Functor.whiskerRight (SmallObject.ε j) F.mapArrow ≫ (functorMapIso j F).hom =
      (F.mapArrow.rightUnitor).inv ≫
        Functor.whiskerLeft F.mapArrow (SmallObject.ε (fun i => F.map (j i))) := by
  apply NatTrans.ext
  funext a
  rw [← Arrow.mk_eq a]
  simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_inv_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp]
  apply Arrow.hom_ext
  · simp only [Arrow.comp_left, Functor.mapArrow_map, ε_app]
    exact functorMapIso_unit_app j F a.hom
  · simp only [Arrow.comp_right, Functor.mapArrow_map, ε_app, Arrow.homMk_right]
    change F.map (𝟙 a.right) ≫ ((functorMapIso j F).app (Arrow.mk a.hom)).hom.right =
      𝟙 (F.obj a.right)
    rw [(functorMapIso_right j F a.hom).1]
    exact (Category.comp_id (F.map (𝟙 a.right))).trans (F.map_id a.right)

/-- Both target-pushout-leg equations use the actual mapped target-cofan term. -/
theorem functorMapIso_target_app {X S : C} (p : X ⟶ S) :
  letI : PreservesColimitsOfShape (Discrete (FunctorObjIndex j p)) F :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (equivShrink.{theta} (FunctorObjIndex j p))).symm F
  let c : Cofan (fun r : FunctorObjIndex (fun i => F.map (j i)) (F.map p) =>
      F.obj (B r.i)) :=
    Cofan.mk (F.obj (∐ fun q : FunctorObjIndex j p => B q.i))
      (fun r => F.map (Sigma.ι (fun q : FunctorObjIndex j p => B q.i)
        ((FunctorObjIndex.equivMap j F p).symm r)))
  let hc : IsColimit c :=
    (Cofan.isColimitEquivOfEquiv (FunctorObjIndex.equivMap j F p).symm
      (Cofan.mk (F.obj (∐ fun q : FunctorObjIndex j p => B q.i))
        (fun q => F.map (Sigma.ι (fun q : FunctorObjIndex j p => B q.i) q)))).1
      (isColimitOfHasCoproductOfPreservesColimit F
        (fun q : FunctorObjIndex j p => B q.i))
  let v := hc.coconePointUniqueUpToIso (coproductIsCoproduct _)
  F.map (ρFunctorObj j p) ≫ ((functorMapIso j F).app (Arrow.mk p)).hom.left =
      v.hom ≫ ρFunctorObj (fun i => F.map (j i)) (F.map p) ∧
    ρFunctorObj (fun i => F.map (j i)) (F.map p) ≫
        ((functorMapIso j F).app (Arrow.mk p)).inv.left = v.inv ≫ F.map (ρFunctorObj j p) := by
  let _ : PreservesColimitsOfShape (Discrete (FunctorObjIndex j p)) F :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (equivShrink.{theta} (FunctorObjIndex j p))).symm F
  let c : Cofan (fun r : FunctorObjIndex (fun i => F.map (j i)) (F.map p) =>
      F.obj (B r.i)) :=
    Cofan.mk (F.obj (∐ fun q : FunctorObjIndex j p => B q.i))
      (fun r => F.map (Sigma.ι (fun q : FunctorObjIndex j p => B q.i)
        ((FunctorObjIndex.equivMap j F p).symm r)))
  let hc : IsColimit c :=
    (Cofan.isColimitEquivOfEquiv (FunctorObjIndex.equivMap j F p).symm
      (Cofan.mk (F.obj (∐ fun q : FunctorObjIndex j p => B q.i))
        (fun q => F.map (Sigma.ι (fun q : FunctorObjIndex j p => B q.i) q)))).1
      (isColimitOfHasCoproductOfPreservesColimit F
        (fun q : FunctorObjIndex j p => B q.i))
  let v := hc.coconePointUniqueUpToIso (coproductIsCoproduct _)
  let χ := Arrow.leftFunc.mapIso ((functorMapIso j F).app (Arrow.mk p))
  change F.map (ρFunctorObj j p) ≫ χ.hom =
      v.hom ≫ ρFunctorObj (fun i => F.map (j i)) (F.map p) ∧
    ρFunctorObj (fun i => F.map (j i)) (F.map p) ≫ χ.inv = v.inv ≫ F.map (ρFunctorObj j p)
  have hinv : ρFunctorObj (fun i => F.map (j i)) (F.map p) ≫ χ.inv =
      v.inv ≫ F.map (ρFunctorObj j p) := by
    dsimp [χ, v, hc, c, functorMapIso]
    exact IsPushout.inr_isoPushout_inv _
  refine ⟨?_, hinv⟩
  have h := (Iso.comp_inv_eq χ).1 hinv
  exact (Iso.inv_comp_eq v).1 ((Category.assoc _ _ _).symm.trans h.symm)

/-- The canonical component retains the cell at each entire original label. -/
theorem functorMapIso_cell_app {X S : C} (p : X ⟶ S) (q : FunctorObjIndex j p) :
    F.map (Sigma.ι (functorObjTgtFamily j p) q ≫ ρFunctorObj j p) ≫
        ((functorMapIso j F).app (Arrow.mk p)).hom.left =
      Sigma.ι (functorObjTgtFamily (fun i => F.map (j i)) (F.map p)) (q.map F) ≫
        ρFunctorObj (fun i => F.map (j i)) (F.map p) := by
  let χ := Arrow.leftFunc.mapIso ((functorMapIso j F).app (Arrow.mk p))
  have htarget := (functorMapIso_target_app j F p).1
  have hcofan := ((functorMapIso_tgt_cofan j F p) q).1
  exact (congrArg (fun k => k ≫ χ.hom) (F.map_comp _ _)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k => F.map (Sigma.ι (functorObjTgtFamily j p) q) ≫ k)
        htarget).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ ρFunctorObj (fun i => F.map (j i)) (F.map p))
            hcofan))))

/-- The inverse comparison recovers the same original complete cell. -/
theorem functorMapIso_cell_app_inv {X S : C} (p : X ⟶ S) (q : FunctorObjIndex j p) :
    (Sigma.ι (functorObjTgtFamily (fun i => F.map (j i)) (F.map p)) (q.map F) ≫
        ρFunctorObj (fun i => F.map (j i)) (F.map p)) ≫
          ((functorMapIso j F).app (Arrow.mk p)).inv.left =
      F.map (Sigma.ι (functorObjTgtFamily j p) q ≫ ρFunctorObj j p) := by
  let χ := Arrow.leftFunc.mapIso ((functorMapIso j F).app (Arrow.mk p))
  exact (Iso.comp_inv_eq χ).2 (functorMapIso_cell_app j F p q).symm

end CategoryTheory.SmallObject
