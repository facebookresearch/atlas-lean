/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The cofibrant cube lemma

A map between two pushout squares is a weak equivalence on the pushout
objects when it is a weak equivalence on all three span objects and the two
direct legs are cofibrations. The proof is the finite walking-span argument
of Hovey, *Model Categories*, Lemma 5.2.6: a compatible Brown factorization
of the whole span map replaces the missing general Reedy API.

Only the two common-source and two non-direct endpoint objects are explicitly
assumed cofibrant; cofibrancy of the direct-leg targets follows from the
cofibrations. The usual one-square gluing theorem is retained as a corollary.

This file installs no left-properness or cobase-change instance.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-! ## A finite Reedy pushout calculation -/

omit [ModelCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- The second cobase-change square in the finite walking-span calculation.
Both the latching object and the two span pushouts may be arbitrary chosen
pushouts. -/
private theorem reedySecond_isPushout
    {P₀ Q₀ P₁ Q₁ R₁ L T S : C}
    (u₀ : P₀ ⟶ Q₀) (aP : P₀ ⟶ P₁)
    (u₁ : P₁ ⟶ Q₁) (v₁ : P₁ ⟶ R₁)
    (aQ : Q₀ ⟶ Q₁)
    (lQ : Q₀ ⟶ L) (lP : P₁ ⟶ L)
    (lSq : IsPushout u₀ aP lQ lP)
    (lambda : L ⟶ Q₁)
    (hlQ : lQ ≫ lambda = aQ) (hlP : lP ≫ lambda = u₁)
    (inlT : Q₀ ⟶ T) (inrT : R₁ ⟶ T)
    (sqT : IsPushout u₀ (aP ≫ v₁) inlT inrT)
    (d : L ⟶ T) (hdQ : lQ ≫ d = inlT)
    (hdP : lP ≫ d = v₁ ≫ inrT)
    (inlS : Q₁ ⟶ S) (inrS : R₁ ⟶ S)
    (sqS : IsPushout u₁ v₁ inlS inrS)
    (t : T ⟶ S) (htQ : inlT ≫ t = aQ ≫ inlS)
    (htR : inrT ≫ t = inrS) :
    IsPushout d lambda t inlS := by
  have hcomm : d ≫ t = lambda ≫ inlS := by
    apply lSq.hom_ext
    · rw [← Category.assoc, hdQ, htQ, ← Category.assoc, hlQ]
    · rw [← Category.assoc, hdP, Category.assoc, htR,
        ← Category.assoc, hlP]
      exact sqS.w.symm
  refine
    { w := hcomm
      isColimit' := ⟨PushoutCocone.isColimitAux'
        (PushoutCocone.mk t inlS hcomm)
        (fun s => ?_)⟩ }
  have hcompat : u₁ ≫ s.inr = v₁ ≫ inrT ≫ s.inl := by
    have h := congrArg (fun q => lP ≫ q) s.condition
    have h' : (v₁ ≫ inrT) ≫ s.inl =
        (lP ≫ lambda) ≫ s.inr := by
      calc
        (v₁ ≫ inrT) ≫ s.inl = (lP ≫ d) ≫ s.inl := by rw [hdP]
        _ = lP ≫ d ≫ s.inl := Category.assoc _ _ _
        _ = lP ≫ lambda ≫ s.inr := h
        _ = (lP ≫ lambda) ≫ s.inr := (Category.assoc _ _ _).symm
    calc
      u₁ ≫ s.inr = (lP ≫ lambda) ≫ s.inr := by rw [hlP]
      _ = (v₁ ≫ inrT) ≫ s.inl := h'.symm
      _ = v₁ ≫ inrT ≫ s.inl := Category.assoc _ _ _
  let k : S ⟶ s.pt := sqS.desc s.inr (inrT ≫ s.inl) hcompat
  refine ⟨k, ?_, ?_, ?_⟩
  · change t ≫ k = s.inl
    apply sqT.hom_ext
    · have h := congrArg (fun q => lQ ≫ q) s.condition
      rw [← Category.assoc, hdQ, ← Category.assoc, hlQ] at h
      rw [← Category.assoc, htQ, Category.assoc, sqS.inl_desc]
      exact h.symm
    · calc
        inrT ≫ t ≫ k = (inrT ≫ t) ≫ k := (Category.assoc _ _ _).symm
        _ = inrS ≫ k := by rw [htR]
        _ = inrT ≫ s.inl := sqS.inr_desc _ _ _
  · change inlS ≫ k = s.inr
    exact sqS.inl_desc _ _ _
  · intro m hmT hmQ
    change S ⟶ s.pt at m
    change t ≫ m = s.inl at hmT
    change inlS ≫ m = s.inr at hmQ
    apply sqS.hom_ext
    · rw [sqS.inl_desc]
      exact hmQ
    · have h := congrArg
        (fun q => inrT ≫ q) hmT
      calc
        inrS ≫ m = (inrT ≫ t) ≫ m := by rw [htR]
        _ = inrT ≫ t ≫ m := Category.assoc _ _ _
        _ = inrT ≫ s.inl := h
        _ = inrS ≫ k := (sqS.inr_desc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Pushout sends the finite-Reedy trivial cofibrations used below to weak
equivalences. -/
private theorem weakEquivalence_pushoutMap_of_reedyTrivialCofibration
    {P₀ Q₀ R₀ P₁ Q₁ R₁ L : C}
    (u₀ : P₀ ⟶ Q₀) (v₀ : P₀ ⟶ R₀)
    (u₁ : P₁ ⟶ Q₁) (v₁ : P₁ ⟶ R₁)
    (aP : P₀ ⟶ P₁) (aQ : Q₀ ⟶ Q₁) (aR : R₀ ⟶ R₁)
    (hu : u₀ ≫ aQ = aP ≫ u₁)
    (hv : v₀ ≫ aR = aP ≫ v₁)
    (lQ : Q₀ ⟶ L) (lP : P₁ ⟶ L)
    (lSq : IsPushout u₀ aP lQ lP)
    (lambda : L ⟶ Q₁)
    (hlQ : lQ ≫ lambda = aQ) (hlP : lP ≫ lambda = u₁)
    [Cofibration aR] [WeakEquivalence aR]
    [Cofibration lambda] [WeakEquivalence lambda] :
    WeakEquivalence
      (pushout.map u₀ v₀ u₁ v₁ aQ aR aP hu hv) := by
  let T := pushout u₀ (aP ≫ v₁)
  let t₀ : pushout u₀ v₀ ⟶ T :=
    pushout.map u₀ v₀ u₀ (aP ≫ v₁) (𝟙 Q₀) aR (𝟙 P₀)
      (by simp) (by simpa using hv)
  let d : L ⟶ T := lSq.desc (pushout.inl _ _)
    (v₁ ≫ pushout.inr _ _) (by rw [← Category.assoc, pushout.condition])
  let t₁ : T ⟶ pushout u₁ v₁ :=
    pushout.map u₀ (aP ≫ v₁) u₁ v₁ aQ (𝟙 R₁) aP hu
      (by simp only [Category.comp_id])
  have ht₀sq : IsPushout
      (pushout.inr u₀ v₀) aR t₀ (pushout.inr u₀ (aP ≫ v₁)) := by
    have hTop := IsPushout.of_hasPushout u₀ v₀
    have hOuter : IsPushout u₀ (v₀ ≫ aR)
        (pushout.inl u₀ v₀ ≫ t₀) (pushout.inr u₀ (aP ≫ v₁)) := by
      rw [hv]
      have hleg : pushout.inl u₀ v₀ ≫ t₀ =
          pushout.inl u₀ (aP ≫ v₁) := by
        dsimp only [t₀, pushout.map]
        rw [pushout.inl_desc, Category.id_comp]
      rw [hleg]
      exact IsPushout.of_hasPushout u₀ (aP ≫ v₁)
    apply hOuter.of_top
    · dsimp only [t₀, pushout.map]
      simp only [pushout.inr_desc, Category.id_comp]
    · exact hTop
  have ht₁sq : IsPushout d lambda t₁ (pushout.inl u₁ v₁) := by
    have hdQ : lQ ≫ d = pushout.inl u₀ (aP ≫ v₁) := by
      exact lSq.inl_desc _ _ _
    have hdP : lP ≫ d = v₁ ≫ pushout.inr u₀ (aP ≫ v₁) := by
      exact lSq.inr_desc _ _ _
    have htQ : pushout.inl u₀ (aP ≫ v₁) ≫ t₁ =
        aQ ≫ pushout.inl u₁ v₁ := by
      dsimp only [t₁, pushout.map]
      rw [pushout.inl_desc]
    have htR : pushout.inr u₀ (aP ≫ v₁) ≫ t₁ =
        pushout.inr u₁ v₁ := by
      dsimp only [t₁, pushout.map]
      rw [pushout.inr_desc, Category.id_comp]
    exact reedySecond_isPushout u₀ aP u₁ v₁ aQ lQ lP lSq
      lambda hlQ hlP (pushout.inl _ _) (pushout.inr _ _)
      (IsPushout.of_hasPushout _ _) d hdQ hdP
      (pushout.inl _ _) (pushout.inr _ _)
      (IsPushout.of_hasPushout _ _) t₁ htQ htR
  let : WeakEquivalence t₀ := by
    rw [weakEquivalence_iff]
    exact ((trivialCofibrations C).of_isPushout ht₀sq
      (mem_trivialCofibrations aR)).2
  let : WeakEquivalence t₁ := by
    rw [weakEquivalence_iff]
    exact ((trivialCofibrations C).of_isPushout ht₁sq
      (mem_trivialCofibrations lambda)).2
  have ht₀Q : pushout.inl u₀ v₀ ≫ t₀ =
      pushout.inl u₀ (aP ≫ v₁) := by
    dsimp only [t₀, pushout.map]
    rw [pushout.inl_desc, Category.id_comp]
  have ht₀R : pushout.inr u₀ v₀ ≫ t₀ =
      aR ≫ pushout.inr u₀ (aP ≫ v₁) := by
    dsimp only [t₀, pushout.map]
    rw [pushout.inr_desc]
  have ht₁Q : pushout.inl u₀ (aP ≫ v₁) ≫ t₁ =
      aQ ≫ pushout.inl u₁ v₁ := by
    dsimp only [t₁, pushout.map]
    rw [pushout.inl_desc]
  have ht₁R : pushout.inr u₀ (aP ≫ v₁) ≫ t₁ =
      pushout.inr u₁ v₁ := by
    dsimp only [t₁, pushout.map]
    rw [pushout.inr_desc, Category.id_comp]
  have hcomp : t₀ ≫ t₁ =
      pushout.map u₀ v₀ u₁ v₁ aQ aR aP hu hv := by
    apply (IsPushout.of_hasPushout u₀ v₀).hom_ext
    · calc
        pushout.inl u₀ v₀ ≫ t₀ ≫ t₁ =
            (pushout.inl u₀ v₀ ≫ t₀) ≫ t₁ :=
          (Category.assoc _ _ _).symm
        _ = pushout.inl u₀ (aP ≫ v₁) ≫ t₁ := by rw [ht₀Q]
        _ = aQ ≫ pushout.inl u₁ v₁ := ht₁Q
        _ = pushout.inl u₀ v₀ ≫
            pushout.map u₀ v₀ u₁ v₁ aQ aR aP hu hv := by
          dsimp only [pushout.map]
          rw [pushout.inl_desc]
    · calc
        pushout.inr u₀ v₀ ≫ t₀ ≫ t₁ =
            (pushout.inr u₀ v₀ ≫ t₀) ≫ t₁ :=
          (Category.assoc _ _ _).symm
        _ = (aR ≫ pushout.inr u₀ (aP ≫ v₁)) ≫ t₁ := by rw [ht₀R]
        _ = aR ≫ pushout.inr u₀ (aP ≫ v₁) ≫ t₁ := Category.assoc _ _ _
        _ = aR ≫ pushout.inr u₁ v₁ := by rw [ht₁R]
        _ = pushout.inr u₀ v₀ ≫
            pushout.map u₀ v₀ u₁ v₁ aQ aR aP hu hv := by
          dsimp only [pushout.map]
          rw [pushout.inr_desc]
  rw [← hcomp]
  infer_instance

/-! ## Compatible Brown factorization of a map of spans -/

/-- The canonical map between pushouts of two spans is a weak equivalence
when the three vertical maps are weak equivalences, the two direct legs are
cofibrations, and the common-source and non-direct endpoint objects are
cofibrant. Neither non-direct leg is required to be a cofibration. -/
theorem weakEquivalence_pushoutMap_of_cofibrant
    {P₀ Q₀ R₀ P₁ Q₁ R₁ : C}
    {u₀ : P₀ ⟶ Q₀} {v₀ : P₀ ⟶ R₀}
    {u₁ : P₁ ⟶ Q₁} {v₁ : P₁ ⟶ R₁}
    {wP : P₀ ⟶ P₁} {wQ : Q₀ ⟶ Q₁} {wR : R₀ ⟶ R₁}
    (hu : u₀ ≫ wQ = wP ≫ u₁) (hv : v₀ ≫ wR = wP ≫ v₁)
    [Cofibration u₀] [Cofibration u₁]
    [WeakEquivalence wP] [WeakEquivalence wQ] [WeakEquivalence wR]
    [IsCofibrant P₀] [IsCofibrant P₁]
    [IsCofibrant R₀] [IsCofibrant R₁] :
    WeakEquivalence
      (pushout.map u₀ v₀ u₁ v₁ wQ wR wP hu hv) := by
  -- Brown data at the common object of the two spans.
  let dP := MorphismProperty.factorizationData
    (cofibrations C) (trivialFibrations C)
    (coprod.desc wP (𝟙 P₁) : P₀ ⨿ P₁ ⟶ P₁)
  let EP := dP.Z
  let aP : P₀ ⟶ EP := coprod.inl ≫ dP.i
  let sP : P₁ ⟶ EP := coprod.inr ≫ dP.i
  let pP : EP ⟶ P₁ := dP.p
  have haPp : aP ≫ pP = wP := by simp [aP, pP, dP]
  have hsPp : sP ≫ pP = 𝟙 P₁ := by simp [sP, pP, dP]
  let : Cofibration aP := by dsimp [aP]; infer_instance
  let : Cofibration sP := by dsimp [sP]; infer_instance
  let : WeakEquivalence aP :=
    weakEquivalence_of_postcomp_of_fac haPp
  let : WeakEquivalence sP :=
    weakEquivalence_of_postcomp_of_fac hsPp
  let : IsCofibrant EP := isCofibrant_of_cofibration aP
  -- Brown data at the non-direct/right object.
  let dR := MorphismProperty.factorizationData
    (cofibrations C) (trivialFibrations C)
    (coprod.desc wR (𝟙 R₁) : R₀ ⨿ R₁ ⟶ R₁)
  let ER := dR.Z
  let aR : R₀ ⟶ ER := coprod.inl ≫ dR.i
  let sR : R₁ ⟶ ER := coprod.inr ≫ dR.i
  let pR : ER ⟶ R₁ := dR.p
  have haRp : aR ≫ pR = wR := by simp [aR, pR, dR]
  have hsRp : sR ≫ pR = 𝟙 R₁ := by simp [sR, pR, dR]
  let : Cofibration aR := by dsimp [aR]; infer_instance
  let : Cofibration sR := by dsimp [sR]; infer_instance
  let : WeakEquivalence aR :=
    weakEquivalence_of_postcomp_of_fac haRp
  let : WeakEquivalence sR :=
    weakEquivalence_of_postcomp_of_fac hsRp
  let : IsCofibrant ER := isCofibrant_of_cofibration aR
  -- The non-direct span leg is selected by one lifting square. Using the
  -- combined coproduct cofibration makes both factor and section natural.
  let topR : P₀ ⨿ P₁ ⟶ ER :=
    coprod.desc (v₀ ≫ aR) (v₁ ≫ sR)
  let botR : EP ⟶ R₁ := pP ≫ v₁
  have hR : dP.i ≫ botR = topR ≫ pR := by
    apply BinaryCofan.IsColimit.hom_ext (colimit.isColimit (pair P₀ P₁))
    · have hfac := congrArg (fun q => coprod.inl ≫ q) dP.fac
      have hfac' : coprod.inl ≫ dP.i ≫ pP = wP := by
        simpa only [Category.assoc, coprod.inl_desc] using hfac
      calc
        coprod.inl ≫ dP.i ≫ botR =
            (coprod.inl ≫ dP.i ≫ pP) ≫ v₁ := by
          simp only [botR, Category.assoc]
        _ = wP ≫ v₁ := by rw [hfac']
        _ = v₀ ≫ wR := hv.symm
        _ = (v₀ ≫ aR) ≫ pR := by rw [Category.assoc, haRp]
        _ = (coprod.inl ≫ topR) ≫ pR := by
          apply congrArg (fun q => q ≫ pR)
          dsimp only [topR]
          exact (coprod.inl_desc _ _).symm
        _ = coprod.inl ≫ topR ≫ pR := Category.assoc _ _ _
    · have hfac := congrArg (fun q => coprod.inr ≫ q) dP.fac
      have hfac' : coprod.inr ≫ dP.i ≫ pP = 𝟙 P₁ := by
        simpa only [Category.assoc, coprod.inr_desc] using hfac
      calc
        coprod.inr ≫ dP.i ≫ botR =
            (coprod.inr ≫ dP.i ≫ pP) ≫ v₁ := by
          simp only [botR, Category.assoc]
        _ = v₁ := by rw [hfac', Category.id_comp]
        _ = (v₁ ≫ sR) ≫ pR := by
          rw [Category.assoc, hsRp, Category.comp_id]
        _ = (coprod.inr ≫ topR) ≫ pR := by
          apply congrArg (fun q => q ≫ pR)
          dsimp only [topR]
          exact (coprod.inr_desc _ _).symm
        _ = coprod.inr ≫ topR ≫ pR := Category.assoc _ _ _
  let sqR : CommSq topR dP.i pR botR := ⟨hR.symm⟩
  let : sqR.HasLift :=
    (inferInstance : HasLiftingProperty dP.i pR).sq_hasLift sqR
  let eRight : EP ⟶ ER := sqR.lift
  have haRight : aP ≫ eRight = v₀ ≫ aR := by
    dsimp only [aP, eRight]
    rw [Category.assoc, sqR.fac_left]
    dsimp only [topR]
    rw [coprod.inl_desc]
  have hsRight : sP ≫ eRight = v₁ ≫ sR := by
    dsimp only [sP, eRight]
    rw [Category.assoc, sqR.fac_left]
    dsimp only [topR]
    rw [coprod.inr_desc]
  have hpRight : eRight ≫ pR = pP ≫ v₁ := sqR.fac_right
  -- Double latching object for the direct/left span leg.
  let L₀ := pushout u₀ aP
  let q₀ : Q₀ ⟶ L₀ := pushout.inl u₀ aP
  let e₀ : EP ⟶ L₀ := pushout.inr u₀ aP
  let L := pushout (sP ≫ e₀) u₁
  let l₀ : L₀ ⟶ L := pushout.inl (sP ≫ e₀) u₁
  let q₁ : Q₁ ⟶ L := pushout.inr (sP ≫ e₀) u₁
  let eP : EP ⟶ L := e₀ ≫ l₀
  let m₀ : L₀ ⟶ Q₁ := pushout.desc wQ (pP ≫ u₁) (by
    simpa only [← Category.assoc, haPp] using hu)
  let m : L ⟶ Q₁ := pushout.desc m₀ (𝟙 Q₁) (by
    dsimp only [m₀, e₀]
    rw [Category.assoc, pushout.inr_desc, ← Category.assoc,
      hsPp, Category.id_comp, Category.comp_id])
  let dQ := MorphismProperty.factorizationData
    (cofibrations C) (trivialFibrations C) m
  let EQ := dQ.Z
  let lQ : L ⟶ EQ := dQ.i
  let pQ : EQ ⟶ Q₁ := dQ.p
  let eLeft : EP ⟶ EQ := eP ≫ lQ
  let aQ : Q₀ ⟶ EQ := q₀ ≫ l₀ ≫ lQ
  let sQ : Q₁ ⟶ EQ := q₁ ≫ lQ
  have heLeft : eLeft ≫ pQ = pP ≫ u₁ := by
    dsimp only [eLeft, eP, lQ, pQ]
    rw [Category.assoc, Category.assoc, dQ.fac]
    dsimp only [m]
    rw [pushout.inl_desc]
    dsimp only [m₀, e₀]
    rw [pushout.inr_desc]
  have haLeft : u₀ ≫ aQ = aP ≫ eLeft := by
    dsimp only [aQ, eLeft, eP, q₀, e₀]
    simpa only [Category.assoc] using congrArg
      (fun q => q ≫ l₀ ≫ lQ)
        (pushout.condition : u₀ ≫ q₀ = aP ≫ e₀)
  have hsLeft : u₁ ≫ sQ = sP ≫ eLeft := by
    dsimp only [sQ, eLeft, eP, e₀, q₁]
    simpa only [Category.assoc] using congrArg
      (fun q => q ≫ lQ)
        (pushout.condition : (sP ≫ e₀) ≫ l₀ = u₁ ≫ q₁).symm
  have haQp : aQ ≫ pQ = wQ := by
    dsimp only [aQ, lQ, pQ]
    rw [Category.assoc, Category.assoc, dQ.fac]
    dsimp only [m]
    rw [pushout.inl_desc]
    dsimp only [m₀, q₀]
    rw [pushout.inl_desc]
  have hsQp : sQ ≫ pQ = 𝟙 Q₁ := by
    dsimp only [sQ, lQ, pQ]
    rw [Category.assoc, dQ.fac]
    dsimp only [m, q₁]
    rw [pushout.inr_desc]
  let : Cofibration eLeft := by
    dsimp [eLeft, eP, e₀, l₀, lQ]
    infer_instance
  let : IsCofibrant EQ := isCofibrant_of_cofibration eLeft
  let : Cofibration aQ := by
    dsimp [aQ, q₀, l₀, lQ]
    infer_instance
  let : Cofibration sQ := by
    dsimp [sQ, q₁, lQ]
    infer_instance
  let : WeakEquivalence aQ :=
    weakEquivalence_of_postcomp_of_fac haQp
  let : WeakEquivalence sQ :=
    weakEquivalence_of_postcomp_of_fac hsQp
  -- Latching map of the factor `a`.
  let latchA : L₀ ⟶ EQ := l₀ ≫ lQ
  have hlatchAq : q₀ ≫ latchA = aQ := rfl
  have hlatchAe : e₀ ≫ latchA = eLeft := by
    dsimp only [latchA, eLeft, eP]
    exact (Category.assoc _ _ _).symm
  let : Cofibration latchA := by
    dsimp [latchA, l₀, lQ]
    infer_instance
  let : WeakEquivalence q₀ := by
    rw [weakEquivalence_iff]
    exact ((trivialCofibrations C).of_isPushout
      (IsPushout.of_hasPushout u₀ aP) (mem_trivialCofibrations aP)).2
  let : WeakEquivalence latchA := by
    have : WeakEquivalence (q₀ ≫ latchA) := by
      rw [hlatchAq]
      infer_instance
    exact weakEquivalence_of_precomp q₀ latchA
  -- Latching map of the section `s`; pushout associativity proves it is a
  -- cofibration without imposing a condition on the non-direct span leg.
  let Ls := pushout sP u₁
  let lsE : EP ⟶ Ls := pushout.inl sP u₁
  let lsQ : Q₁ ⟶ Ls := pushout.inr sP u₁
  let cLs : Ls ⟶ L := pushout.desc eP q₁ (by
    dsimp only [eP, e₀, l₀, q₁]
    rw [← Category.assoc]
    exact (pushout.condition : (sP ≫ pushout.inr u₀ aP) ≫
      pushout.inl (sP ≫ pushout.inr u₀ aP) u₁ =
        u₁ ≫ pushout.inr (sP ≫ pushout.inr u₀ aP) u₁))
  let latchS : Ls ⟶ EQ := cLs ≫ lQ
  have hlatchSQ : lsQ ≫ latchS = sQ := by
    dsimp only [lsQ, latchS, cLs, sQ, q₁]
    rw [← Category.assoc, pushout.inr_desc]
  have hlatchSE : lsE ≫ latchS = eLeft := by
    dsimp only [lsE, latchS, cLs, eLeft]
    rw [← Category.assoc, pushout.inl_desc]
  have hcLsSq : IsPushout e₀ lsE l₀ cLs := by
    let h := pushoutPushoutLeftIsPushout u₀ aP sP u₁
    exact IsPushout.of_isColimit h
  let : Cofibration cLs := by
    rw [cofibration_iff]
    exact (cofibrations C).of_isPushout hcLsSq.flip
      (mem_cofibrations e₀)
  let : Cofibration latchS := by
    dsimp [latchS]
    infer_instance
  let : WeakEquivalence lsQ := by
    rw [weakEquivalence_iff]
    exact ((trivialCofibrations C).of_isPushout
      (IsPushout.of_hasPushout sP u₁).flip
      (mem_trivialCofibrations sP)).2
  let : WeakEquivalence latchS := by
    have : WeakEquivalence (lsQ ≫ latchS) := by
      rw [hlatchSQ]
      infer_instance
    exact weakEquivalence_of_precomp lsQ latchS
  -- Pushout maps of the factor, section, and trivial-fibration part.
  let aS : pushout u₀ v₀ ⟶ pushout eLeft eRight :=
    pushout.map u₀ v₀ eLeft eRight aQ aR aP haLeft
      (by simpa using haRight.symm)
  let sS : pushout u₁ v₁ ⟶ pushout eLeft eRight :=
    pushout.map u₁ v₁ eLeft eRight sQ sR sP hsLeft hsRight.symm
  let pS : pushout eLeft eRight ⟶ pushout u₁ v₁ :=
    pushout.map eLeft eRight u₁ v₁ pQ pR pP heLeft hpRight
  let : WeakEquivalence aS := by
    exact weakEquivalence_pushoutMap_of_reedyTrivialCofibration
      u₀ v₀ eLeft eRight aP aQ aR haLeft (by simpa using haRight.symm)
      q₀ e₀ (IsPushout.of_hasPushout u₀ aP) latchA hlatchAq hlatchAe
  let : WeakEquivalence sS := by
    exact weakEquivalence_pushoutMap_of_reedyTrivialCofibration
      u₁ v₁ eLeft eRight sP sQ sR hsLeft hsRight.symm
      lsQ lsE (IsPushout.of_hasPushout sP u₁).flip
      latchS hlatchSQ hlatchSE
  have hsSpS : sS ≫ pS = 𝟙 (pushout u₁ v₁) := by
    apply (IsPushout.of_hasPushout u₁ v₁).hom_ext
    · calc
        pushout.inl u₁ v₁ ≫ sS ≫ pS =
            (pushout.inl u₁ v₁ ≫ sS) ≫ pS :=
          (Category.assoc _ _ _).symm
        _ = (sQ ≫ pushout.inl eLeft eRight) ≫ pS := by
          dsimp only [sS, pushout.map]
          rw [pushout.inl_desc]
        _ = sQ ≫ pushout.inl eLeft eRight ≫ pS := Category.assoc _ _ _
        _ = sQ ≫ pQ ≫ pushout.inl u₁ v₁ := by
          dsimp only [pS, pushout.map]
          rw [pushout.inl_desc]
        _ = (sQ ≫ pQ) ≫ pushout.inl u₁ v₁ :=
          (Category.assoc _ _ _).symm
        _ = pushout.inl u₁ v₁ := by rw [hsQp, Category.id_comp]
        _ = pushout.inl u₁ v₁ ≫ 𝟙 (pushout u₁ v₁) :=
          (Category.comp_id _).symm
    · calc
        pushout.inr u₁ v₁ ≫ sS ≫ pS =
            (pushout.inr u₁ v₁ ≫ sS) ≫ pS :=
          (Category.assoc _ _ _).symm
        _ = (sR ≫ pushout.inr eLeft eRight) ≫ pS := by
          dsimp only [sS, pushout.map]
          rw [pushout.inr_desc]
        _ = sR ≫ pushout.inr eLeft eRight ≫ pS := Category.assoc _ _ _
        _ = sR ≫ pR ≫ pushout.inr u₁ v₁ := by
          dsimp only [pS, pushout.map]
          rw [pushout.inr_desc]
        _ = (sR ≫ pR) ≫ pushout.inr u₁ v₁ :=
          (Category.assoc _ _ _).symm
        _ = pushout.inr u₁ v₁ := by rw [hsRp, Category.id_comp]
        _ = pushout.inr u₁ v₁ ≫ 𝟙 (pushout u₁ v₁) :=
          (Category.comp_id _).symm
  let : WeakEquivalence pS :=
    weakEquivalence_of_precomp_of_fac hsSpS
  let alphaS : pushout u₀ v₀ ⟶ pushout u₁ v₁ :=
    pushout.map u₀ v₀ u₁ v₁ wQ wR wP hu hv
  have haSpS : aS ≫ pS = alphaS := by
    apply (IsPushout.of_hasPushout u₀ v₀).hom_ext
    · calc
        pushout.inl u₀ v₀ ≫ aS ≫ pS =
            (pushout.inl u₀ v₀ ≫ aS) ≫ pS :=
          (Category.assoc _ _ _).symm
        _ = (aQ ≫ pushout.inl eLeft eRight) ≫ pS := by
          dsimp only [aS, pushout.map]
          rw [pushout.inl_desc]
        _ = aQ ≫ pushout.inl eLeft eRight ≫ pS := Category.assoc _ _ _
        _ = aQ ≫ pQ ≫ pushout.inl u₁ v₁ := by
          dsimp only [pS, pushout.map]
          rw [pushout.inl_desc]
        _ = (aQ ≫ pQ) ≫ pushout.inl u₁ v₁ :=
          (Category.assoc _ _ _).symm
        _ = wQ ≫ pushout.inl u₁ v₁ := by rw [haQp]
        _ = pushout.inl u₀ v₀ ≫ alphaS := by
          dsimp only [alphaS, pushout.map]
          rw [pushout.inl_desc]
    · calc
        pushout.inr u₀ v₀ ≫ aS ≫ pS =
            (pushout.inr u₀ v₀ ≫ aS) ≫ pS :=
          (Category.assoc _ _ _).symm
        _ = (aR ≫ pushout.inr eLeft eRight) ≫ pS := by
          dsimp only [aS, pushout.map]
          rw [pushout.inr_desc]
        _ = aR ≫ pushout.inr eLeft eRight ≫ pS := Category.assoc _ _ _
        _ = aR ≫ pR ≫ pushout.inr u₁ v₁ := by
          dsimp only [pS, pushout.map]
          rw [pushout.inr_desc]
        _ = (aR ≫ pR) ≫ pushout.inr u₁ v₁ :=
          (Category.assoc _ _ _).symm
        _ = wR ≫ pushout.inr u₁ v₁ := by rw [haRp]
        _ = pushout.inr u₀ v₀ ≫ alphaS := by
          dsimp only [alphaS, pushout.map]
          rw [pushout.inr_desc]
  let : WeakEquivalence alphaS := by
    rw [← haSpS]
    infer_instance
  exact inferInstance

/-- A map between two pushout squares is a weak equivalence on the pushout
objects when it is a weak equivalence on all three span objects and the two
direct legs are cofibrations. Only the common-source and non-direct endpoint
objects need explicit cofibrancy hypotheses. -/
theorem weakEquivalence_map_of_isPushouts_of_cofibrant
    {A B X P A' B' X' P' : C}
    {i : A ⟶ B} {g : A ⟶ X} {p : B ⟶ P} {q : X ⟶ P}
    {i' : A' ⟶ B'} {g' : A' ⟶ X'} {p' : B' ⟶ P'} {q' : X' ⟶ P'}
    (sq : IsPushout i g p q) (sq' : IsPushout i' g' p' q')
    {a : A ⟶ A'} {b : B ⟶ B'} {c : X ⟶ X'} {d : P ⟶ P'}
    (hi : i ≫ b = a ≫ i') (hg : g ≫ c = a ≫ g')
    (hp : p ≫ d = b ≫ p') (hq : q ≫ d = c ≫ q')
    [Cofibration i] [Cofibration i']
    [WeakEquivalence a] [WeakEquivalence b] [WeakEquivalence c]
    [IsCofibrant A] [IsCofibrant A'] [IsCofibrant X] [IsCofibrant X'] :
    WeakEquivalence d := by
  let h₀ := IsPushout.of_hasPushout i g
  let h₁ := IsPushout.of_hasPushout i' g'
  let m : pushout i g ⟶ pushout i' g' :=
    pushout.map i g i' g' b c a hi hg
  let : WeakEquivalence m :=
    weakEquivalence_pushoutMap_of_cofibrant hi hg
  let e₀ : pushout i g ≅ P := h₀.isoIsPushout _ _ sq
  let e₁ : pushout i' g' ≅ P' := h₁.isoIsPushout _ _ sq'
  have hd : e₀.inv ≫ m ≫ e₁.hom = d := by
    apply sq.hom_ext
    · calc
        p ≫ (e₀.inv ≫ m ≫ e₁.hom) =
            (p ≫ e₀.inv) ≫ m ≫ e₁.hom := by simp only [Category.assoc]
        _ = pushout.inl i g ≫ m ≫ e₁.hom := by
          rw [h₀.inl_isoIsPushout_inv]
        _ = (pushout.inl i g ≫ m) ≫ e₁.hom :=
          (Category.assoc _ _ _).symm
        _ = (b ≫ pushout.inl i' g') ≫ e₁.hom := by
          apply congrArg (fun z => z ≫ e₁.hom)
          dsimp only [m, pushout.map]
          exact pushout.inl_desc _ _ _
        _ = b ≫ pushout.inl i' g' ≫ e₁.hom := Category.assoc _ _ _
        _ = b ≫ p' := by rw [h₁.inl_isoIsPushout_hom]
        _ = p ≫ d := hp.symm
    · calc
        q ≫ (e₀.inv ≫ m ≫ e₁.hom) =
            (q ≫ e₀.inv) ≫ m ≫ e₁.hom := by simp only [Category.assoc]
        _ = pushout.inr i g ≫ m ≫ e₁.hom := by
          rw [h₀.inr_isoIsPushout_inv]
        _ = (pushout.inr i g ≫ m) ≫ e₁.hom :=
          (Category.assoc _ _ _).symm
        _ = (c ≫ pushout.inr i' g') ≫ e₁.hom := by
          apply congrArg (fun z => z ≫ e₁.hom)
          dsimp only [m, pushout.map]
          exact pushout.inr_desc _ _ _
        _ = c ≫ pushout.inr i' g' ≫ e₁.hom := Category.assoc _ _ _
        _ = c ≫ q' := by rw [h₁.inr_isoIsPushout_hom]
        _ = q ≫ d := hq.symm
  rw [← hd]
  infer_instance

/-- A pushout of a weak equivalence between cofibrant objects along a
cofibration is a weak equivalence. -/
theorem weakEquivalence_of_isPushout_of_cofibrant
    {A B X Y : C}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j)
    [Cofibration i] [WeakEquivalence f]
    [IsCofibrant A] [IsCofibrant X] :
    WeakEquivalence f' := by
  exact weakEquivalence_map_of_isPushouts_of_cofibrant
    (IsPushout.of_id_snd (f := i)) sq
    (a := 𝟙 A) (b := 𝟙 B) (c := f) (d := f')
    (by simp) (by simp) (by simp) sq.w

end HomotopicalAlgebra

end
