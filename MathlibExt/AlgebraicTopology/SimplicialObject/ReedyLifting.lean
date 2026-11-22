/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Avocado
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyClasses
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Lifting between degreewise Reedy morphism properties

The degreewise lifting construction is specialized to simplicial objects and the natural-number
degree. All recursion and boundary helpers remain private; the public surface is the resulting
lifting implication.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MorphismProperty
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The four original simplicial diagrams and their full commutative lifting square. -/
structure LiftingData where
  /-- The original source diagram of the left map. -/
  A : SimplicialObject C
  /-- The original target diagram of the left map. -/
  B : SimplicialObject C
  /-- The original source diagram of the right map. -/
  E : SimplicialObject C
  /-- The original target diagram of the right map. -/
  F : SimplicialObject C
  /-- The original left simplicial map. -/
  i : A ⟶ B
  /-- The original right simplicial map. -/
  p : E ⟶ F
  /-- The original top simplicial map of the lifting square. -/
  u : A ⟶ E
  /-- The original bottom simplicial map of the lifting square. -/
  v : B ⟶ F
  w : u ≫ p = i ≫ v

/-- A complete natural lift on all original degrees below `n`. -/
structure PartialLift (d : LiftingData (C := C)) (n : ℕ) where
  /-- The actual component lift at each original lower degree. -/
  app : ∀ k : Fin n,
    d.B.obj (op ⦋k.1⦌) ⟶ d.E.obj (op ⦋k.1⦌)
  facLeft : ∀ k : Fin n,
    d.i.app (op ⦋k.1⦌) ≫ app k = d.u.app (op ⦋k.1⦌)
  facRight : ∀ k : Fin n,
    app k ≫ d.p.app (op ⦋k.1⦌) = d.v.app (op ⦋k.1⦌)
  naturality : ∀ {k l : Fin n} (θ : op ⦋k.1⦌ ⟶ op ⦋l.1⦌),
    d.B.map θ ≫ app l = app k ≫ d.E.map θ

namespace PartialLift

variable {d : LiftingData (C := C)} {n : ℕ}

private def empty (d : LiftingData (C := C)) : PartialLift d 0 where
  app k := Fin.elim0 k
  facLeft k := Fin.elim0 k
  facRight k := Fin.elim0 k
  naturality {k} := Fin.elim0 k

/-- The new component lift and its full compatibility with the supplied lower-degree lift. -/
structure ExtensionData (H : PartialLift d n) where
  /-- The actual new component lift at degree `n`. -/
  newApp : d.B.obj (op ⦋n⦌) ⟶ d.E.obj (op ⦋n⦌)
  facLeft : d.i.app (op ⦋n⦌) ≫ newApp = d.u.app (op ⦋n⦌)
  facRight : newApp ≫ d.p.app (op ⦋n⦌) = d.v.app (op ⦋n⦌)
  naturalityToNew : ∀ (k : Fin n) (θ : op ⦋k.1⦌ ⟶ op ⦋n⦌),
    d.B.map θ ≫ newApp = H.app k ≫ d.E.map θ
  naturalityFromNew : ∀ (k : Fin n) (θ : op ⦋n⦌ ⟶ op ⦋k.1⦌),
    d.B.map θ ≫ H.app k = newApp ≫ d.E.map θ
  naturalityNew : ∀ (θ : op ⦋n⦌ ⟶ op ⦋n⦌),
    d.B.map θ ≫ newApp = newApp ≫ d.E.map θ

private def extendApp (H : PartialLift d n) (e : ExtensionData H) (k : Fin (n + 1)) :
    d.B.obj (op ⦋k.1⦌) ⟶ d.E.obj (op ⦋k.1⦌) :=
  Fin.lastCases e.newApp (fun j ↦ H.app j) k

@[simp]
private theorem extendApp_last (H : PartialLift d n) (e : ExtensionData H) :
    extendApp H e (Fin.last n) = e.newApp :=
  Fin.lastCases_last

@[simp]
private theorem extendApp_castSucc (H : PartialLift d n) (e : ExtensionData H) (k : Fin n) :
    extendApp H e k.castSucc = H.app k :=
  Fin.lastCases_castSucc k

private def extend (H : PartialLift d n) (e : ExtensionData H) : PartialLift d (n + 1) where
  app := extendApp H e
  facLeft k := by
    refine Fin.lastCases
      (by simpa only [Fin.val_last, extendApp_last] using e.facLeft)
      (fun j => by
        simpa only [Fin.val_castSucc, extendApp_castSucc] using H.facLeft j) k
  facRight k := by
    refine Fin.lastCases
      (by simpa only [Fin.val_last, extendApp_last] using e.facRight)
      (fun j => by
        simpa only [Fin.val_castSucc, extendApp_castSucc] using H.facRight j) k
  naturality {k l} θ := by
    induction k using Fin.lastCases with
    | last =>
        induction l using Fin.lastCases with
        | last =>
            simpa only [Fin.val_last, extendApp_last] using e.naturalityNew θ
        | cast l =>
            simpa only [Fin.val_last, Fin.val_castSucc, extendApp_last,
              extendApp_castSucc] using e.naturalityFromNew l θ
    | cast k =>
        induction l using Fin.lastCases with
        | last =>
            simpa only [Fin.val_last, Fin.val_castSucc, extendApp_last,
              extendApp_castSucc] using e.naturalityToNew k θ
        | cast l =>
            simpa only [Fin.val_castSucc, extendApp_castSucc] using H.naturality θ

@[simp]
private theorem extend_app_castSucc (H : PartialLift d n) (e : ExtensionData H) (k : Fin n) :
    (H.extend e).app k.castSucc = H.app k :=
  extendApp_castSucc H e k

end PartialLift

private abbrev StepData (d : LiftingData (C := C)) :=
  ∀ (n : ℕ) (H : PartialLift d n), H.ExtensionData

private def stages (d : LiftingData (C := C)) (step : StepData d) :
    ∀ n : ℕ, PartialLift d n
  | 0 => PartialLift.empty d
  | n + 1 => (stages d step n).extend (step n (stages d step n))

@[simp]
private theorem stages_succ_app_castSucc (d : LiftingData (C := C))
    (step : StepData d) (n : ℕ) (k : Fin n) :
    (stages d step (n + 1)).app k.castSucc = (stages d step n).app k :=
  PartialLift.extend_app_castSucc _ _ k

private def globalApp (d : LiftingData (C := C)) (step : StepData d) (n : ℕ) :
    d.B.obj (op ⦋n⦌) ⟶ d.E.obj (op ⦋n⦌) :=
  (stages d step (n + 1)).app (Fin.last n)

private theorem stages_app_eq_global (d : LiftingData (C := C)) (step : StepData d)
    {k n : ℕ} (hk : k < n) :
    (stages d step n).app ⟨k, hk⟩ = globalApp d step k := by
  induction n with
  | zero => exact (Nat.not_lt_zero _ hk).elim
  | succ n ih =>
      by_cases hkn : k = n
      · subst k
        change (stages d step (n + 1)).app ⟨n, hk⟩ =
          (stages d step (n + 1)).app (Fin.last n)
        congr
      · have hk' : k < n := by omega
        change (stages d step (n + 1)).app (⟨k, hk'⟩ : Fin n).castSucc =
          globalApp d step k
        rw [stages_succ_app_castSucc]
        exact ih hk'

private theorem globalApp_facLeft (d : LiftingData (C := C)) (step : StepData d) (n : ℕ) :
    d.i.app (op ⦋n⦌) ≫ globalApp d step n = d.u.app (op ⦋n⦌) :=
  (stages d step (n + 1)).facLeft (Fin.last n)

private theorem globalApp_facRight (d : LiftingData (C := C)) (step : StepData d) (n : ℕ) :
    globalApp d step n ≫ d.p.app (op ⦋n⦌) = d.v.app (op ⦋n⦌) :=
  (stages d step (n + 1)).facRight (Fin.last n)

private theorem globalApp_naturality (d : LiftingData (C := C)) (step : StepData d)
    {k l : ℕ} (θ : op ⦋k⦌ ⟶ op ⦋l⦌) :
    d.B.map θ ≫ globalApp d step l = globalApp d step k ≫ d.E.map θ := by
  let N := max k l + 1
  have hk : k < N := by dsimp [N]; omega
  have hl : l < N := by dsimp [N]; omega
  have h := (stages d step N).naturality
    (k := (⟨k, hk⟩ : Fin N)) (l := (⟨l, hl⟩ : Fin N)) θ
  rw [stages_app_eq_global d step hk, stages_app_eq_global d step hl] at h
  exact h

private def globalNatTrans (d : LiftingData (C := C)) (step : StepData d) : d.B ⟶ d.E where
  app Δ := globalApp d step Δ.unop.len
  naturality {_ _} θ := globalApp_naturality d step θ

private theorem globalNatTrans_facLeft (d : LiftingData (C := C)) (step : StepData d) :
    d.i ≫ globalNatTrans d step = d.u := by
  ext Δ
  exact globalApp_facLeft d step Δ.unop.len

private theorem globalNatTrans_facRight (d : LiftingData (C := C)) (step : StepData d) :
    globalNatTrans d step ≫ d.p = d.v := by
  ext Δ
  exact globalApp_facRight d step Δ.unop.len

section LatchingBoundary

variable [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]
variable (d : LiftingData (C := C)) {n : ℕ} (H : PartialLift d n)

private def lowerLatchingCocone : Cocone (latchingDiagram d.B n) where
  pt := d.E.obj (op ⦋n⦌)
  ι :=
    { app := fun a =>
        H.app ⟨a.obj.left.unop.len, a.property.2⟩ ≫ d.E.map a.obj.hom
      naturality := by
        intro a b f
        change d.B.map f.hom.left ≫
            (H.app ⟨b.obj.left.unop.len, b.property.2⟩ ≫ d.E.map b.obj.hom) =
          (H.app ⟨a.obj.left.unop.len, a.property.2⟩ ≫ d.E.map a.obj.hom) ≫ 𝟙 _
        have hnat := H.naturality
          (k := ⟨a.obj.left.unop.len, a.property.2⟩)
          (l := ⟨b.obj.left.unop.len, b.property.2⟩) f.hom.left
        rw [Category.comp_id, ← Category.assoc, hnat]
        rw [Category.assoc, ← d.E.map_comp]
        apply congrArg (fun q => H.app ⟨a.obj.left.unop.len, a.property.2⟩ ≫ d.E.map q)
        simp }

private def lowerLatchingMap :
    latchingObject d.B n ⟶ d.E.obj (op ⦋n⦌) :=
  colimit.desc (latchingDiagram d.B n) (lowerLatchingCocone d H)

@[reassoc]
private theorem lowerLatchingMap_ι (a : latchingIndex n) :
    latchingι d.B n a ≫ lowerLatchingMap d H =
      H.app ⟨a.obj.left.unop.len, a.property.2⟩ ≫ d.E.map a.obj.hom := by
  apply colimit.ι_desc

set_option backward.isDefEq.respectTransparency false in
private theorem lowerLatching_compat :
    latchingMap d.A n ≫ d.u.app (op ⦋n⦌) =
      (latchingObjectFunctor n).map d.i ≫ lowerLatchingMap d H := by
  apply colimit.hom_ext
  intro a
  rw [← Category.assoc]
  erw [latchingMap_ι]
  rw [d.u.naturality]
  rw [← Category.assoc]
  erw [latchingObjectFunctor_map_ι]
  rw [Category.assoc, lowerLatchingMap_ι, ← Category.assoc]
  have hfac :
      d.i.app a.obj.left ≫ H.app ⟨a.obj.left.unop.len, a.property.2⟩ =
        d.u.app a.obj.left := by
    simpa using H.facLeft ⟨a.obj.left.unop.len, a.property.2⟩
  rw [hfac]
  simp only [Functor.id_obj]

section Pushouts

variable [HasPushouts C]

private def upperMap :
    relativeLatchingObject d.i n ⟶ d.E.obj (op ⦋n⦌) :=
  pushout.desc (d.u.app (op ⦋n⦌)) (lowerLatchingMap d H)
    (lowerLatching_compat d H)

@[reassoc]
private theorem upperMap_inl :
    pushout.inl (latchingMap d.A n) ((latchingObjectFunctor n).map d.i) ≫
        upperMap d H = d.u.app (op ⦋n⦌) := by
  apply pushout.inl_desc

@[reassoc]
private theorem upperMap_inr :
    pushout.inr (latchingMap d.A n) ((latchingObjectFunctor n).map d.i) ≫
        upperMap d H = lowerLatchingMap d H := by
  apply pushout.inr_desc

end Pushouts
end LatchingBoundary

section MatchingBoundary

variable [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]
variable (d : LiftingData (C := C)) {n : ℕ} (H : PartialLift d n)

private def lowerMatchingCone : Cone (matchingDiagram d.E n) where
  pt := d.B.obj (op ⦋n⦌)
  π :=
    { app := fun b =>
        d.B.map b.obj.hom ≫ H.app ⟨b.obj.right.unop.len, b.property.2⟩
      naturality := by
        intro a b f
        change 𝟙 _ ≫
            (d.B.map b.obj.hom ≫ H.app ⟨b.obj.right.unop.len, b.property.2⟩) =
          (d.B.map a.obj.hom ≫ H.app ⟨a.obj.right.unop.len, a.property.2⟩) ≫
            d.E.map f.hom.right
        have hnat := H.naturality
          (k := ⟨a.obj.right.unop.len, a.property.2⟩)
          (l := ⟨b.obj.right.unop.len, b.property.2⟩) f.hom.right
        rw [Category.id_comp, Category.assoc, ← hnat]
        rw [← Category.assoc, ← d.B.map_comp]
        apply congrArg (fun q => d.B.map q ≫ H.app ⟨b.obj.right.unop.len, b.property.2⟩)
        simpa using (StructuredArrow.w f.hom).symm }

private def lowerMatchingMap :
    d.B.obj (op ⦋n⦌) ⟶ matchingObject d.E n :=
  limit.lift (matchingDiagram d.E n) (lowerMatchingCone d H)

@[reassoc]
private theorem lowerMatchingMap_π (b : matchingIndex n) :
    lowerMatchingMap d H ≫ matchingπ d.E n b =
      d.B.map b.obj.hom ≫ H.app ⟨b.obj.right.unop.len, b.property.2⟩ := by
  apply limit.lift_π

set_option backward.isDefEq.respectTransparency false in
private theorem lowerMatching_compat :
    d.v.app (op ⦋n⦌) ≫ matchingMap d.F n =
      lowerMatchingMap d H ≫ (matchingObjectFunctor n).map d.p := by
  apply limit.hom_ext
  intro b
  rw [Category.assoc]
  erw [matchingMap_π]
  rw [Category.assoc]
  erw [matchingObjectFunctor_map_π]
  rw [← Category.assoc, lowerMatchingMap_π]
  have hfac :
      H.app ⟨b.obj.right.unop.len, b.property.2⟩ ≫ d.p.app b.obj.right =
        d.v.app b.obj.right := by
    simpa using H.facRight ⟨b.obj.right.unop.len, b.property.2⟩
  rw [Category.assoc, hfac]
  simp only [Functor.id_obj]
  exact (d.v.naturality b.obj.hom).symm

section Pullbacks

variable [HasPullbacks C]

private def lowerMap :
    d.B.obj (op ⦋n⦌) ⟶ relativeMatchingObject d.p n :=
  pullback.lift (d.v.app (op ⦋n⦌)) (lowerMatchingMap d H)
    (lowerMatching_compat d H)

@[reassoc]
private theorem lowerMap_fst :
    lowerMap d H ≫
        pullback.fst (matchingMap d.F n) ((matchingObjectFunctor n).map d.p) =
      d.v.app (op ⦋n⦌) := by
  apply pullback.lift_fst

@[reassoc]
private theorem lowerMap_snd :
    lowerMap d H ≫
        pullback.snd (matchingMap d.F n) ((matchingObjectFunctor n).map d.p) =
      lowerMatchingMap d H := by
  apply pullback.lift_snd

end Pullbacks
end MatchingBoundary

section DegreeStep

variable [HasPushouts C] [HasPullbacks C]
variable [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]
variable [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]
variable {P Q : MorphismProperty C}
variable (d : LiftingData (C := C)) {n : ℕ} (H : PartialLift d n)
variable (hi : reedyLeft P d.i) (hp : reedyRight Q d.p)
variable (hPQ : P ≤ Q.llp)

set_option backward.isDefEq.respectTransparency false in
private theorem mixedSquare_w :
    upperMap d H ≫ relativeMatchingMap d.p n =
      relativeLatchingMap d.i n ≫ lowerMap d H := by
  apply pullback.hom_ext
  · rw [Category.assoc, relativeMatchingMap_fst]
    rw [Category.assoc, lowerMap_fst]
    apply pushout.hom_ext
    · rw [upperMap_inl_assoc, relativeLatchingMap_inl_assoc]
      exact congrFun (congrArg NatTrans.app d.w) (op ⦋n⦌)
    · rw [upperMap_inr_assoc, relativeLatchingMap_inr_assoc]
      apply colimit.hom_ext
      intro a
      rw [← Category.assoc]
      erw [lowerLatchingMap_ι]
      rw [← Category.assoc]
      erw [latchingMap_ι]
      have hfac :
          H.app ⟨a.obj.left.unop.len, a.property.2⟩ ≫ d.p.app a.obj.left =
            d.v.app a.obj.left := by
        simpa using H.facRight ⟨a.obj.left.unop.len, a.property.2⟩
      rw [Category.assoc, d.p.naturality, ← Category.assoc, hfac]
      simpa only [Functor.id_obj] using (d.v.naturality a.obj.hom).symm
  · rw [Category.assoc, relativeMatchingMap_snd]
    rw [Category.assoc, lowerMap_snd]
    apply pushout.hom_ext
    · rw [upperMap_inl_assoc, relativeLatchingMap_inl_assoc]
      apply limit.hom_ext
      intro b
      rw [Category.assoc]
      erw [matchingMap_π]
      rw [Category.assoc]
      erw [lowerMatchingMap_π]
      have hfac :
          d.i.app b.obj.right ≫ H.app ⟨b.obj.right.unop.len, b.property.2⟩ =
            d.u.app b.obj.right := by
        simpa using H.facLeft ⟨b.obj.right.unop.len, b.property.2⟩
      rw [← Category.assoc, ← d.i.naturality]
      simp only [Functor.id_obj]
      rw [Category.assoc, hfac]
      simpa only [Functor.id_obj] using (d.u.naturality b.obj.hom).symm
    · rw [upperMap_inr_assoc, relativeLatchingMap_inr_assoc]
      apply colimit.hom_ext
      intro a
      apply limit.hom_ext
      intro b
      simp only [Category.assoc]
      erw [lowerLatchingMap_ι_assoc, matchingMap_π]
      erw [latchingMap_ι_assoc, lowerMatchingMap_π]
      rw [← d.E.map_comp]
      rw [← Category.assoc, ← d.B.map_comp]
      have hnat := H.naturality
        (k := ⟨a.obj.left.unop.len, a.property.2⟩)
        (l := ⟨b.obj.right.unop.len, b.property.2⟩)
        (a.obj.hom ≫ b.obj.hom)
      simpa only [Functor.id_obj] using hnat.symm

private theorem degreeSquare : CommSq (upperMap d H)
    (relativeLatchingMap d.i n) (relativeMatchingMap d.p n) (lowerMap d H) :=
  CommSq.mk (mixedSquare_w d H)

private noncomputable def degreeLiftStruct : (degreeSquare d H).LiftStruct := by
  let _ : HasLiftingProperty (relativeLatchingMap d.i n)
      (relativeMatchingMap d.p n) :=
    hPQ _ (hi n) _ (hp n)
  exact (inferInstance : (degreeSquare d H).HasLift).exists_lift.some

private noncomputable def degreeLift :
    d.B.obj (op ⦋n⦌) ⟶ d.E.obj (op ⦋n⦌) :=
  (degreeLiftStruct d H hi hp hPQ).l

private theorem degreeLift_facLeft :
    relativeLatchingMap d.i n ≫ degreeLift d H hi hp hPQ = upperMap d H :=
  (degreeLiftStruct d H hi hp hPQ).fac_left

private theorem degreeLift_facRight :
    degreeLift d H hi hp hPQ ≫ relativeMatchingMap d.p n = lowerMap d H :=
  (degreeLiftStruct d H hi hp hPQ).fac_right

set_option backward.isDefEq.respectTransparency false in
private theorem degreeLift_naturality_latching (a : latchingIndex n) :
    d.B.map a.obj.hom ≫ degreeLift d H hi hp hPQ =
      H.app ⟨a.obj.left.unop.len, a.property.2⟩ ≫ d.E.map a.obj.hom := by
  have h := congrArg
    (fun q => latchingι d.B n a ≫
      pushout.inr (latchingMap d.A n) ((latchingObjectFunctor n).map d.i) ≫ q)
    (degreeLift_facLeft d H hi hp hPQ)
  simpa only [Category.assoc, relativeLatchingMap_inr_assoc,
    latchingMap_ι_assoc, upperMap_inr_assoc, upperMap_inr,
    lowerLatchingMap_ι] using h

set_option backward.isDefEq.respectTransparency false in
private theorem degreeLift_naturality_matching (b : matchingIndex n) :
    d.B.map b.obj.hom ≫ H.app ⟨b.obj.right.unop.len, b.property.2⟩ =
      degreeLift d H hi hp hPQ ≫ d.E.map b.obj.hom := by
  have h := congrArg
    (fun q => q ≫
      pullback.snd (matchingMap d.F n) ((matchingObjectFunctor n).map d.p) ≫
        matchingπ d.E n b)
    (degreeLift_facRight d H hi hp hPQ)
  simpa only [Category.assoc, relativeMatchingMap_snd_assoc,
    matchingMap_π, lowerMap_snd_assoc, lowerMatchingMap_π] using h.symm

private def latchingIndexOfEpi (k : Fin n) (θ : op ⦋k.1⦌ ⟶ op ⦋n⦌)
    [Epi θ.unop] : latchingIndex n :=
  ⟨CostructuredArrow.mk θ, ⟨by simpa using (inferInstance : Epi θ.unop), k.2⟩⟩

private def matchingIndexOfMono (k : Fin n) (θ : op ⦋n⦌ ⟶ op ⦋k.1⦌)
    [Mono θ.unop] : matchingIndex n :=
  ⟨StructuredArrow.mk θ, ⟨by simpa using (inferInstance : Mono θ.unop), k.2⟩⟩

private theorem degreeLift_naturality_epi (k : Fin n)
    (θ : op ⦋k.1⦌ ⟶ op ⦋n⦌) [Epi θ.unop] :
    d.B.map θ ≫ degreeLift d H hi hp hPQ = H.app k ≫ d.E.map θ := by
  simpa [latchingIndexOfEpi] using
    degreeLift_naturality_latching d H hi hp hPQ (latchingIndexOfEpi k θ)

private theorem degreeLift_naturality_mono (k : Fin n)
    (θ : op ⦋n⦌ ⟶ op ⦋k.1⦌) [Mono θ.unop] :
    d.B.map θ ≫ H.app k = degreeLift d H hi hp hPQ ≫ d.E.map θ := by
  simpa [matchingIndexOfMono] using
    degreeLift_naturality_matching d H hi hp hPQ (matchingIndexOfMono k θ)

private theorem arbitrary_naturality_to_new (k : Fin n)
    (θ : op ⦋k.1⦌ ⟶ op ⦋n⦌) :
    d.B.map θ ≫ degreeLift d H hi hp hPQ = H.app k ≫ d.E.map θ := by
  let e := factorThruImage θ.unop
  let m := image.ι θ.unop
  have hdle : (image θ.unop).len ≤ k.1 := SimplexCategory.len_le_of_mono m
  have hd : (image θ.unop).len < n := hdle.trans_lt k.2
  let j : Fin n := ⟨(image θ.unop).len, hd⟩
  have hθ : m.op ≫ e.op = θ := by
    apply Quiver.Hom.unop_inj
    simp [e, m]
  have hm : d.B.map m.op ≫ H.app j = H.app k ≫ d.E.map m.op := by
    simpa only [Opposite.unop_op, SimplexCategory.mk_len] using
      H.naturality (k := k) (l := j) m.op
  have he : d.B.map e.op ≫ degreeLift d H hi hp hPQ =
      H.app j ≫ d.E.map e.op :=
    degreeLift_naturality_epi d H hi hp hPQ j e.op
  rw [← hθ, d.B.map_comp, d.E.map_comp]
  simp only [Category.assoc]
  rw [he, ← Category.assoc, hm]
  simp only [Category.assoc]

private theorem arbitrary_naturality_from_new (k : Fin n)
    (θ : op ⦋n⦌ ⟶ op ⦋k.1⦌) :
    d.B.map θ ≫ H.app k = degreeLift d H hi hp hPQ ≫ d.E.map θ := by
  let e := factorThruImage θ.unop
  let m := image.ι θ.unop
  have hdle : (image θ.unop).len ≤ k.1 := SimplexCategory.len_le_of_epi e
  have hd : (image θ.unop).len < n := hdle.trans_lt k.2
  let j : Fin n := ⟨(image θ.unop).len, hd⟩
  have hθ : m.op ≫ e.op = θ := by
    apply Quiver.Hom.unop_inj
    simp [e, m]
  have he : d.B.map e.op ≫ H.app k = H.app j ≫ d.E.map e.op := by
    simpa only [Opposite.unop_op, SimplexCategory.mk_len] using
      H.naturality (k := j) (l := k) e.op
  have hm : d.B.map m.op ≫ H.app j = degreeLift d H hi hp hPQ ≫ d.E.map m.op :=
    degreeLift_naturality_mono d H hi hp hPQ j m.op
  rw [← hθ, d.B.map_comp, d.E.map_comp]
  simp only [Category.assoc]
  rw [he, ← Category.assoc, hm]
  simp only [Category.assoc]

private theorem arbitrary_naturality_new (θ : op ⦋n⦌ ⟶ op ⦋n⦌) :
    d.B.map θ ≫ degreeLift d H hi hp hPQ =
      degreeLift d H hi hp hPQ ≫ d.E.map θ := by
  let e := factorThruImage θ.unop
  let m := image.ι θ.unop
  have hdle : (image θ.unop).len ≤ n := SimplexCategory.len_le_of_mono m
  by_cases hd : (image θ.unop).len < n
  · let j : Fin n := ⟨(image θ.unop).len, hd⟩
    have hθ : m.op ≫ e.op = θ := by
      apply Quiver.Hom.unop_inj
      simp [e, m]
    have he : d.B.map e.op ≫ degreeLift d H hi hp hPQ =
        H.app j ≫ d.E.map e.op :=
      degreeLift_naturality_epi d H hi hp hPQ j e.op
    have hm : d.B.map m.op ≫ H.app j =
        degreeLift d H hi hp hPQ ≫ d.E.map m.op :=
      degreeLift_naturality_mono d H hi hp hPQ j m.op
    rw [← hθ, d.B.map_comp, d.E.map_comp]
    simp only [Category.assoc]
    rw [he, ← Category.assoc, hm]
    simp only [Category.assoc]
  · have hlen : (image θ.unop).len = n :=
      le_antisymm hdle (Nat.le_of_not_gt hd)
    let _ : IsIso e :=
      (SimplexCategory.isIso_iff_of_epi e).2 (by simpa [e] using hlen.symm)
    let _ : IsIso m :=
      (SimplexCategory.isIso_iff_of_mono m).2 (by simpa [m] using hlen)
    let _ : IsIso θ.unop := by
      rw [← image.fac θ.unop]
      infer_instance
    have hθ : θ = 𝟙 _ := by
      apply Quiver.Hom.unop_inj
      simpa using SimplexCategory.eq_id_of_isIso θ.unop
    subst θ
    simp

private noncomputable def extensionData : H.ExtensionData where
  newApp := degreeLift d H hi hp hPQ
  facLeft := by
    have h := congrArg
      (fun q =>
        pushout.inl (latchingMap d.A n) ((latchingObjectFunctor n).map d.i) ≫ q)
      (degreeLift_facLeft d H hi hp hPQ)
    simpa only [Category.assoc, relativeLatchingMap_inl_assoc,
      relativeLatchingMap_inl, upperMap_inl] using h
  facRight := by
    have h := congrArg
      (fun q => q ≫
        pullback.fst (matchingMap d.F n) ((matchingObjectFunctor n).map d.p))
      (degreeLift_facRight d H hi hp hPQ)
    simpa only [Category.assoc, relativeMatchingMap_fst, lowerMap_fst] using h
  naturalityToNew := arbitrary_naturality_to_new d H hi hp hPQ
  naturalityFromNew := arbitrary_naturality_from_new d H hi hp hPQ
  naturalityNew := arbitrary_naturality_new d H hi hp hPQ

end DegreeStep

section Recursion

variable [HasPushouts C] [HasPullbacks C]
variable [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]
variable [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]
variable {P Q : MorphismProperty C}
variable (d : LiftingData (C := C))
variable (hi : reedyLeft P d.i) (hp : reedyRight Q d.p)
variable (hPQ : P ≤ Q.llp)

private noncomputable def stepData : StepData d :=
  fun _ H => extensionData d H hi hp hPQ

private noncomputable def globalLift : d.B ⟶ d.E :=
  globalNatTrans d (stepData d hi hp hPQ)

private theorem globalLift_facLeft : d.i ≫ globalLift d hi hp hPQ = d.u :=
  globalNatTrans_facLeft d (stepData d hi hp hPQ)

private theorem globalLift_facRight : globalLift d hi hp hPQ ≫ d.p = d.v :=
  globalNatTrans_facRight d (stepData d hi hp hPQ)

end Recursion

/-- Degreewise left Reedy maps lift against degreewise right Reedy maps whenever the
underlying morphism properties have the corresponding lifting relation. -/
theorem reedyLeft_le_llp_reedyRight (P Q : MorphismProperty C)
    [HasPushouts C] [HasPullbacks C]
    [∀ n : ℕ, HasColimitsOfShape (latchingIndex n) C]
    [∀ n : ℕ, HasLimitsOfShape (matchingIndex n) C]
    (hPQ : P ≤ Q.llp) :
    reedyLeft P ≤ (reedyRight Q).llp := by
  intro A B i hi E F p hp
  refine ⟨fun {u v} sq => ?_⟩
  let d : LiftingData (C := C) :=
    { A := A
      B := B
      E := E
      F := F
      i := i
      p := p
      u := u
      v := v
      w := sq.w }
  apply CommSq.HasLift.mk'
  exact
    { l := globalLift d hi hp hPQ
      fac_left := globalLift_facLeft d hi hp hPQ
      fac_right := globalLift_facRight d hi hp hPQ }

end CategoryTheory.SimplicialObject
