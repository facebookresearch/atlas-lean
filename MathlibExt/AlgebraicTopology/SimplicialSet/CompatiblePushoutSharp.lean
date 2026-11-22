/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CompatiblePushoutCartesianGeometry
public import MathlibExt.AlgebraicTopology.SimplicialSet.CompatiblePushoutReassociation
public import MathlibExt.AlgebraicTopology.SimplicialSet.CompatiblePushoutHCTransport
public import MathlibExt.AlgebraicTopology.SimplicialSet.PushoutEpiCover
public import MathlibExt.AlgebraicTopology.SimplicialSet.SharpCoproductClosure
public import MathlibExt.AlgebraicTopology.SimplicialSet.SharpPullbackClosure
public import MathlibExt.AlgebraicTopology.SimplicialSet.SharpEpiDescent
public import MathlibExt.AlgebraicTopology.SimplicialSet.SharpGluing
public import MathlibExt.AlgebraicTopology.SimplicialSet.MonoPushoutPullback

/-!
# Sharpness of compatible simplicial pushouts

Rezk’s compatible pushout theorem gives a sharp induced map of simplicial pushouts when the three component maps are sharp, the two input squares are homotopy cartesian, and the corresponding right legs of both spans are monic. Both output piece squares and both expressions for the intersection square are homotopy cartesian.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
open SSet.SharpComparisonDraft SSet.SharpCoproductClosure
namespace SSet.RezkCompatiblePushout

private theorem intersection_comm {X0 X1 P Y0 Y1 Q : SSet.{u}}
    (u0 : X0 ⟶ X1) (ix : X1 ⟶ P) (p0 : X0 ⟶ Y0)
    (p1 : X1 ⟶ Y1) (p : P ⟶ Q) (a : Y0 ⟶ Y1) (iy : Y1 ⟶ Q)
    (hu : u0 ≫ p1 = p0 ≫ a) (hi : ix ≫ p = p1 ≫ iy) :
    (u0 ≫ ix) ≫ p = p0 ≫ (a ≫ iy) := by
  calc
    (u0 ≫ ix) ≫ p = u0 ≫ (ix ≫ p) := Category.assoc _ _ _
    _ = u0 ≫ (p1 ≫ iy) := by rw [hi]
    _ = (u0 ≫ p1) ≫ iy := (Category.assoc _ _ _).symm
    _ = (p0 ≫ a) ≫ iy := by rw [hu]
    _ = p0 ≫ (a ≫ iy) := Category.assoc _ _ _

private abbrev result {X0 X1 X2 Y0 Y1 Y2 : SSet.{u}}
    (u0 : X0 ⟶ X1) (v0 : X0 ⟶ X2) (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2)
    (p0 : X0 ⟶ Y0) (p1 : X1 ⟶ Y1) (p2 : X2 ⟶ Y2)
    (hl : u0 ≫ p1 = p0 ≫ a) (hr : v0 ≫ p2 = p0 ≫ b) : Prop :=
  let p := pushout.map u0 v0 a b p1 p2 p0 hl hr
  Sharp p ∧
    WeakEquivalence (pullback.lift (pushout.inl u0 v0) p1 (by simp [p]) ≫
      comparison p (pushout.inl a b)) ∧
    WeakEquivalence (pullback.lift (pushout.inr u0 v0) p2 (by simp [p]) ≫
      comparison p (pushout.inr a b)) ∧
    WeakEquivalence (pullback.lift (u0 ≫ pushout.inl u0 v0) p0
      (intersection_comm u0 _ p0 p1 p a _ hl (by simp [p])) ≫
      comparison p (a ≫ pushout.inl a b))

private theorem actual_over_map {X0 X1 X2 Y0 Y1 Y2 P : SSet.{u}}
    (u0 : X0 ⟶ X1) (v0 : X0 ⟶ X2) (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2)
    (p0 : X0 ⟶ Y0) (p1 : X1 ⟶ Y1) (p2 : X2 ⟶ Y2)
    (hl : u0 ≫ p1 = p0 ≫ a) (hr : v0 ≫ p2 = p0 ≫ b)
    (e : pushout u0 v0 ⟶ P) (q : P ⟶ pushout a b)
    (h1 : pushout.inl u0 v0 ≫ e ≫ q = p1 ≫ pushout.inl a b)
    (h2 : pushout.inr u0 v0 ≫ e ≫ q = p2 ≫ pushout.inr a b) :
    e ≫ q = pushout.map u0 v0 a b p1 p2 p0 hl hr := by
  apply pushout.hom_ext
  · simpa only [pushout.map, pushout.inl_desc, Category.assoc] using h1
  · simpa only [pushout.map, pushout.inr_desc, Category.assoc] using h2

private theorem case_a {X0 X1 X2 Y0 Y1 Y2 : SSet.{u}}
    (u0 : X0 ⟶ X1) (v0 : X0 ⟶ X2) (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2)
    (p0 : X0 ⟶ Y0) (p1 : X1 ⟶ Y1) (p2 : X2 ⟶ Y2)
    (hl : u0 ≫ p1 = p0 ≫ a) (hr : v0 ≫ p2 = p0 ≫ b) [Mono b]
    (hp1 : Sharp p1) (hp2 : Sharp p2)
    (leftPB : IsPullback u0 p0 p1 a) (rightPB : IsPullback v0 p0 p2 b) :
    result u0 v0 a b p0 p1 p2 hl hr := by
  let p := pushout.map u0 v0 a b p1 p2 p0 hl hr
  let sl : CommSq (pushout.inl u0 v0) p1 p (pushout.inl a b) := ⟨by simp [p]⟩
  let sr : CommSq (pushout.inr u0 v0) p2 p (pushout.inr a b) := ⟨by simp [p]⟩
  have faces := strict_faces (IsPushout.of_hasPushout u0 v0)
    (IsPushout.of_hasPushout a b) leftPB rightPB sl sr
  have cover := coverSquare faces.1 faces.2.1
  let _ : Epi (coprod.desc (pushout.inl a b) (pushout.inr a b)) :=
    RezkPushoutCover.pushoutCover_epi a b
  have hp : Sharp p := SharpSaturation.sharp_of_epi_pullback cover
    (sharp_coprod_map p1 p2 hp1 hp2)
  exact ⟨hp, strictSquare_hc faces.1 hp,
    strictSquare_hc faces.2.1 hp, strictSquare_hc faces.2.2.1 hp⟩

private theorem case_b {X0 X1 X2 Y0 Y1 Y2 : SSet.{u}}
    (u0 : X0 ⟶ X1) (v0 : X0 ⟶ X2) (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2)
    (p0 : X0 ⟶ Y0) (p1 : X1 ⟶ Y1) (p2 : X2 ⟶ Y2)
    (hl : u0 ≫ p1 = p0 ≫ a) (hr : v0 ≫ p2 = p0 ≫ b)
    [Mono v0] [Mono b] (hp0 : Sharp p0) (hp1 : Sharp p1) (hp2 : Sharp p2)
    (leftHC : WeakEquivalence (pullback.lift u0 p0 hl ≫ comparison p1 a))
    (rightPB : IsPullback v0 p0 p2 b) :
    result u0 v0 a b p0 p1 p2 hl hr := by
  let Z0 := pullback p1 a
  let r : Z0 ⟶ X1 := pullback.fst p1 a
  let q0 : Z0 ⟶ Y0 := pullback.snd p1 a
  let ell : X0 ⟶ Z0 := pullback.lift u0 p0 hl
  have hell_r : ell ≫ r = u0 := pullback.lift_fst _ _ _
  have hell_q : ell ≫ q0 = p0 := pullback.lift_snd _ _ _
  have hell : WeakEquivalence ell :=
    (hc_iff_ordinaryLift_weak (CommSq.mk hl) hp1).mp leftHC
  have hq0 : Sharp q0 := SharpPullbackClosure.sharp_pullback_snd p1 a hp1
  let Z2 := pushout v0 ell
  let k : X2 ⟶ Z2 := pushout.inl v0 ell
  let j : Z0 ⟶ Z2 := pushout.inr v0 ell
  let q2 : Z2 ⟶ Y2 := pushout.desc p2 (q0 ≫ b) (by
    rw [← hell_q, Category.assoc] at hr
    exact hr)
  have hk : k ≫ q2 = p2 := pushout.inl_desc _ _ _
  have hj : j ≫ q2 = q0 ≫ b := pushout.inr_desc _ _ _
  have hp0' : Sharp (ell ≫ q0) := by rw [hell_q]; exact hp0
  have hp2' : Sharp (k ≫ q2) := by rw [hk]; exact hp2
  have hq2 : Sharp q2 := sharp_mono_gluing (IsPushout.of_hasPushout v0 ell)
    q0 q2 b hj.symm hell (Or.inl inferInstance) hq0 hp0' hp2'
  have hkWeak : WeakEquivalence k := weak_right_of_pushout_either_mono
    (IsPushout.of_hasPushout v0 ell) hell (Or.inl inferInstance)
  have outer : IsPullback v0 (ell ≫ q0) (k ≫ q2) b := by
    simpa only [hell_q, hk] using rightPB
  have newRight : IsPullback j q0 q2 b :=
    RezkMonoPushout.isPullback_tail (IsPushout.of_hasPushout v0 ell) (CommSq.mk hj) outer
  have newLeft : IsPullback r q0 p1 a := IsPullback.of_hasPullback p1 a
  have hl' : r ≫ p1 = q0 ≫ a := pullback.condition
  have hn := case_a r j a b q0 p1 q2 hl' hj hp1 hq2 newLeft newRight
  let p' := pushout.map r j a b p1 q2 q0 hl' hj
  let p := pushout.map u0 v0 a b p1 p2 p0 hl hr
  let E := caseBIso u0 v0 ell r hell_r
  have hE1 : pushout.inl u0 v0 ≫ E.hom = pushout.inl r j :=
    (caseB_iso_legs u0 v0 ell r hell_r).1
  have hE2 : pushout.inr u0 v0 ≫ E.hom = k ≫ pushout.inr r j :=
    (caseB_iso_legs u0 v0 ell r hell_r).2.1
  have hOver : E.hom ≫ p' = p := by
    apply actual_over_map u0 v0 a b p0 p1 p2 hl hr
    · rw [← Category.assoc, hE1]; simp [p']
    · rw [← Category.assoc, hE2, Category.assoc]
      simp only [p', pushout.map, pushout.inr_desc]
      exact (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ pushout.inr a b) hk)
  let EA : Arrow.mk p ≅ Arrow.mk p' := Arrow.isoMk E (Iso.refl _) (by simpa using hOver)
  have hp : Sharp p := (sharp_arrowIso_iff EA).mpr hn.1
  let oldL : CommSq (pushout.inl u0 v0) p1 p (pushout.inl a b) := ⟨by simp [p]⟩
  let newL : CommSq (pushout.inl r j) p1 p' (pushout.inl a b) := ⟨by simp [p']⟩
  have hc1 := (hc_weakSquare_iff oldL newL (𝟙 X1) E.hom (𝟙 Y1) (𝟙 (pushout a b))
    (by simpa using hE1) (by simp) (by simpa using hOver.symm) (by simp)
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mpr hn.2.1
  let oldR : CommSq (pushout.inr u0 v0) p2 p (pushout.inr a b) := ⟨by simp [p]⟩
  let newR : CommSq (pushout.inr r j) q2 p' (pushout.inr a b) := ⟨by simp [p']⟩
  have hc2 := (hc_weakSquare_iff oldR newR k E.hom (𝟙 Y2) (𝟙 (pushout a b))
    hE2 (by simpa using hk.symm) (by simpa using hOver.symm) (by simp)
    hkWeak (by infer_instance) (by infer_instance) (by infer_instance)).mpr hn.2.2.1
  let old0 : CommSq (u0 ≫ pushout.inl u0 v0) p0 p (a ≫ pushout.inl a b) :=
    ⟨intersection_comm u0 _ p0 p1 p a _ hl oldL.w⟩
  let new0 : CommSq (r ≫ pushout.inl r j) q0 p' (a ≫ pushout.inl a b) :=
    ⟨intersection_comm r _ q0 p1 p' a _ hl' newL.w⟩
  have hE0 : (u0 ≫ pushout.inl u0 v0) ≫ E.hom = ell ≫ (r ≫ pushout.inl r j) := by
    rw [Category.assoc, hE1, ← Category.assoc, hell_r]
  have hc0 := (hc_weakSquare_iff old0 new0 ell E.hom (𝟙 Y0) (𝟙 (pushout a b))
    hE0 (by simpa using hell_q.symm) (by simpa using hOver.symm) (by simp)
    hell (by infer_instance) (by infer_instance) (by infer_instance)).mpr hn.2.2.2
  exact ⟨hp, hc1, hc2, hc0⟩

private theorem case_c {X0 X1 X2 Y0 Y1 Y2 : SSet.{u}}
    (u0 : X0 ⟶ X1) (v0 : X0 ⟶ X2) (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2)
    (p0 : X0 ⟶ Y0) (p1 : X1 ⟶ Y1) (p2 : X2 ⟶ Y2)
    (hl : u0 ≫ p1 = p0 ≫ a) (hr : v0 ≫ p2 = p0 ≫ b)
    [Mono v0] [Mono b] (hp0 : Sharp p0) (hp1 : Sharp p1) (hp2 : Sharp p2)
    (leftHC : WeakEquivalence (pullback.lift u0 p0 hl ≫ comparison p1 a))
    (rightHC : WeakEquivalence (pullback.lift v0 p0 hr ≫ comparison p2 b)) :
    result u0 v0 a b p0 p1 p2 hl hr := by
  let Z0 := pullback p2 b
  let r2 : Z0 ⟶ X2 := pullback.fst p2 b
  let q0 : Z0 ⟶ Y0 := pullback.snd p2 b
  let ell : X0 ⟶ Z0 := pullback.lift v0 p0 hr
  have hell_r : ell ≫ r2 = v0 := pullback.lift_fst _ _ _
  have hell_q : ell ≫ q0 = p0 := pullback.lift_snd _ _ _
  have hell : WeakEquivalence ell :=
    (hc_iff_ordinaryLift_weak (CommSq.mk hr) hp2).mp rightHC
  let _ : Mono ell := mono_of_mono_fac hell_r
  let _ : Mono r2 := (IsPullback.of_hasPullback p2 b).mono_fst_of_mono
  have hq0 : Sharp q0 := SharpPullbackClosure.sharp_pullback_snd p2 b hp2
  let Z1 := pushout u0 ell
  let k : X1 ⟶ Z1 := pushout.inl u0 ell
  let j : Z0 ⟶ Z1 := pushout.inr u0 ell
  let q1 : Z1 ⟶ Y1 := pushout.desc p1 (q0 ≫ a) (by
    rw [← hell_q, Category.assoc] at hl
    exact hl)
  have hk : k ≫ q1 = p1 := pushout.inl_desc _ _ _
  have hj : j ≫ q1 = q0 ≫ a := pushout.inr_desc _ _ _
  have hp0' : Sharp (ell ≫ q0) := by rw [hell_q]; exact hp0
  have hp1' : Sharp (k ≫ q1) := by rw [hk]; exact hp1
  have hq1 : Sharp q1 := sharp_mono_gluing (IsPushout.of_hasPushout u0 ell)
    q0 q1 a hj.symm hell (Or.inr inferInstance) hq0 hp0' hp1'
  have hkWeak : WeakEquivalence k := weak_right_of_pushout_either_mono
    (IsPushout.of_hasPushout u0 ell) hell (Or.inr inferInstance)
  let originalLeft : CommSq u0 p0 p1 a := ⟨hl⟩
  let replacementLeft : CommSq j q0 q1 a := ⟨hj⟩
  have newLeftHC := (hc_weakSquare_iff originalLeft replacementLeft ell k (𝟙 Y0) (𝟙 Y1)
    (IsPushout.of_hasPushout u0 ell).w (by simpa using hell_q.symm)
    (by simpa using hk.symm) (by simp) hell hkWeak
    (by infer_instance) (by infer_instance)).mp leftHC
  have rightPB : IsPullback r2 q0 p2 b := IsPullback.of_hasPullback p2 b
  have hr' : r2 ≫ p2 = q0 ≫ b := pullback.condition
  have hn := case_b j r2 a b q0 q1 p2 hj hr' hq0 hq1 hp2 newLeftHC rightPB
  let p' := pushout.map j r2 a b q1 p2 q0 hj hr'
  let p := pushout.map u0 v0 a b p1 p2 p0 hl hr
  let E := caseCIso u0 v0 ell r2 hell_r
  have hE1 : pushout.inl u0 v0 ≫ E.hom = k ≫ pushout.inl j r2 :=
    (caseC_iso_legs u0 v0 ell r2 hell_r).1
  have hE2 : pushout.inr u0 v0 ≫ E.hom = pushout.inr j r2 :=
    (caseC_iso_legs u0 v0 ell r2 hell_r).2.1
  have hOver : E.hom ≫ p' = p := by
    apply actual_over_map u0 v0 a b p0 p1 p2 hl hr
    · rw [← Category.assoc, hE1, Category.assoc]
      simp only [p', pushout.map, pushout.inl_desc]
      exact (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ pushout.inl a b) hk)
    · rw [← Category.assoc, hE2]; simp [p']
  let EA : Arrow.mk p ≅ Arrow.mk p' := Arrow.isoMk E (Iso.refl _) (by simpa using hOver)
  have hp : Sharp p := (sharp_arrowIso_iff EA).mpr hn.1
  let oldL : CommSq (pushout.inl u0 v0) p1 p (pushout.inl a b) := ⟨by simp [p]⟩
  let newL : CommSq (pushout.inl j r2) q1 p' (pushout.inl a b) := ⟨by simp [p']⟩
  have hc1 := (hc_weakSquare_iff oldL newL k E.hom (𝟙 Y1) (𝟙 (pushout a b))
    hE1 (by simpa using hk.symm) (by simpa using hOver.symm) (by simp)
    hkWeak (by infer_instance) (by infer_instance) (by infer_instance)).mpr hn.2.1
  let oldR : CommSq (pushout.inr u0 v0) p2 p (pushout.inr a b) := ⟨by simp [p]⟩
  let newR : CommSq (pushout.inr j r2) p2 p' (pushout.inr a b) := ⟨by simp [p']⟩
  have hc2 := (hc_weakSquare_iff oldR newR (𝟙 X2) E.hom (𝟙 Y2) (𝟙 (pushout a b))
    (by simpa using hE2) (by simp) (by simpa using hOver.symm) (by simp)
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mpr hn.2.2.1
  let old0 : CommSq (u0 ≫ pushout.inl u0 v0) p0 p (a ≫ pushout.inl a b) :=
    ⟨intersection_comm u0 _ p0 p1 p a _ hl oldL.w⟩
  let new0 : CommSq (j ≫ pushout.inl j r2) q0 p' (a ≫ pushout.inl a b) :=
    ⟨intersection_comm j _ q0 q1 p' a _ hj newL.w⟩
  have hE0 : (u0 ≫ pushout.inl u0 v0) ≫ E.hom = ell ≫ (j ≫ pushout.inl j r2) := by
    rw [Category.assoc, hE1, ← Category.assoc, (IsPushout.of_hasPushout u0 ell).w,
      Category.assoc]
  have hc0 := (hc_weakSquare_iff old0 new0 ell E.hom (𝟙 Y0) (𝟙 (pushout a b))
    hE0 (by simpa using hell_q.symm) (by simpa using hOver.symm) (by simp)
    hell (by infer_instance) (by infer_instance) (by infer_instance)).mpr hn.2.2.2
  exact ⟨hp, hc1, hc2, hc0⟩

/-- Full Rezk8.1(2) on the original compatible spans: the actual pushout map
is sharp and all original pieces are homotopy cartesian, with both X0 paths. -/
theorem sharp_compatible_pushout {X0 X1 X2 Y0 Y1 Y2 : SSet.{u}}
    (u0 : X0 ⟶ X1) (v0 : X0 ⟶ X2) (a : Y0 ⟶ Y1) (b : Y0 ⟶ Y2)
    (p0 : X0 ⟶ Y0) (p1 : X1 ⟶ Y1) (p2 : X2 ⟶ Y2)
    (hl : u0 ≫ p1 = p0 ≫ a) (hr : v0 ≫ p2 = p0 ≫ b)
    [Mono v0] [Mono b] (hp0 : Sharp p0) (hp1 : Sharp p1) (hp2 : Sharp p2)
    (leftHC : WeakEquivalence (pullback.lift u0 p0 hl ≫ comparison p1 a))
    (rightHC : WeakEquivalence (pullback.lift v0 p0 hr ≫ comparison p2 b)) :
    let p := pushout.map u0 v0 a b p1 p2 p0 hl hr
    Sharp p ∧
      WeakEquivalence (pullback.lift (pushout.inl u0 v0) p1 (by simp [p]) ≫
        comparison p (pushout.inl a b)) ∧
      WeakEquivalence (pullback.lift (pushout.inr u0 v0) p2 (by simp [p]) ≫
        comparison p (pushout.inr a b)) ∧
      WeakEquivalence (pullback.lift (u0 ≫ pushout.inl u0 v0) p0
        (by
          simp only [p, Category.assoc, pushout.map, pushout.inl_desc]
          exact (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ pushout.inl a b) hl)) ≫
        comparison p (a ≫ pushout.inl a b)) ∧
      WeakEquivalence (pullback.lift (v0 ≫ pushout.inr u0 v0) p0
        (by
          simp only [p, Category.assoc, pushout.map, pushout.inr_desc]
          exact (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ pushout.inr a b) hr)) ≫
        comparison p (b ≫ pushout.inr a b)) := by
  have h := case_c u0 v0 a b p0 p1 p2 hl hr hp0 hp1 hp2 leftHC rightHC
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, ?_⟩
  have hpaths :
      (u0 ≫ pushout.inl u0 v0, a ≫ pushout.inl a b) =
        (v0 ≫ pushout.inr u0 v0, b ≫ pushout.inr a b) :=
    congrArg₂ Prod.mk (pushout.condition (f := u0) (g := v0))
      (pushout.condition (f := a) (g := b))
  let p := pushout.map u0 v0 a b p1 p2 p0 hl hr
  let C : (X0 ⟶ pushout u0 v0) × (Y0 ⟶ pushout a b) → Prop := fun ij =>
    ∀ w : ij.1 ≫ p = p0 ≫ ij.2,
      WeakEquivalence (pullback.lift ij.1 p0 w ≫ comparison p ij.2)
  have hleft : C (u0 ≫ pushout.inl u0 v0, a ≫ pushout.inl a b) := by
    intro w
    exact h.2.2.2
  have hright : C (v0 ≫ pushout.inr u0 v0, b ≫ pushout.inr a b) :=
    (congrArg C hpaths).mp hleft
  exact hright _

end SSet.RezkCompatiblePushout
