/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.MonoUnionSharpComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.SharpPullbackClosure

/-!
# Homotopy-cartesian comparison for a union

The union's actual incoming HC assertion from its three original pieces.

The target is the real pullback of the sharp ambient row along the union
inclusion. All three weak lifts come from the original piece HC assertions,
and actual nested pullback Isos preserve their full projections.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet.RezkUnionIncomingHC
open SharpComparisonDraft RezkCompatiblePushout

/-- The SAME union inclusion is HC from the three actual ambient piece
assertions and mono cell-side pushouts; no union HC or Sharp goal is supplied. -/
theorem incoming_of_three_original_pieces
    {X0 X1 X2 A Y0 Y1 Y2 B E F : SSet.{u}}
    {tX : X0 ⟶ X1} {iX : X0 ⟶ X2} {rX : X1 ⟶ A} {bX : X2 ⟶ A}
    {tY : Y0 ⟶ Y1} {iY : Y0 ⟶ Y2} {rY : Y1 ⟶ B} {bY : Y2 ⟶ B}
    (sx : IsPushout tX iX rX bX) (sy : IsPushout tY iY rY bY)
    (p0 : X0 ⟶ Y0) (p1 : X1 ⟶ Y1) (p2 : X2 ⟶ Y2) (p : A ⟶ B)
    (jX : A ⟶ E) (jY : B ⟶ F) (q : E ⟶ F)
    (hl : tX ≫ p1 = p0 ≫ tY) (hr : iX ≫ p2 = p0 ≫ iY)
    (hR : rX ≫ p = p1 ≫ rY) (hB : bX ≫ p = p2 ≫ bY)
    (whole : CommSq jX p q jY)
    (piece0 : CommSq ((tX ≫ rX) ≫ jX) p0 q ((tY ≫ rY) ≫ jY))
    (piece1 : CommSq (rX ≫ jX) p1 q (rY ≫ jY))
    (piece2 : CommSq (bX ≫ jX) p2 q (bY ≫ jY))
    [Mono iX] [Mono iY] (hq : Sharp q)
    (hc0 : WeakEquivalence (pullback.lift _ _ piece0.w ≫ comparison q _))
    (hc1 : WeakEquivalence (pullback.lift _ _ piece1.w ≫ comparison q _))
    (hc2 : WeakEquivalence (pullback.lift _ _ piece2.w ≫ comparison q _)) :
    WeakEquivalence (pullback.lift jX p whole.w ≫ comparison q jY) := by
  let Q : pullback q jY ⟶ B := pullback.snd q jY
  let delta : A ⟶ pullback q jY := pullback.lift jX p whole.w
  have hQ : Sharp Q := SharpPullbackClosure.sharp_pullback_snd q jY hq
  have h0 : ((tX ≫ rX) ≫ delta) ≫ Q = p0 ≫ (tY ≫ rY) := by
    calc
      ((tX ≫ rX) ≫ delta) ≫ Q = (tX ≫ rX) ≫ p := by
        rw [Category.assoc, show delta ≫ Q = p from pullback.lift_snd _ _ _]
      _ = tX ≫ (rX ≫ p) := Category.assoc _ _ _
      _ = tX ≫ (p1 ≫ rY) := by rw [hR]
      _ = (tX ≫ p1) ≫ rY := (Category.assoc _ _ _).symm
      _ = (p0 ≫ tY) ≫ rY := by rw [hl]
      _ = p0 ≫ (tY ≫ rY) := Category.assoc _ _ _
  have h1 : (rX ≫ delta) ≫ Q = p1 ≫ rY := by
    rw [Category.assoc, show delta ≫ Q = p from pullback.lift_snd _ _ _]
    exact hR
  have h2 : (bX ≫ delta) ≫ Q = p2 ≫ bY := by
    rw [Category.assoc, show delta ≫ Q = p from pullback.lift_snd _ _ _]
    exact hB
  have w0 : WeakEquivalence (pullback.lift ((tX ≫ rX) ≫ delta) p0 h0) := by
    have absolute : WeakEquivalence (pullback.lift _ _ piece0.w) :=
      (hc_iff_ordinaryLift_weak piece0 hq).mp hc0
    let e := SharpPullbackClosure.nestedPullbackIso q jY (tY ≫ rY)
    have fac : pullback.lift ((tX ≫ rX) ≫ delta) p0 h0 ≫ e.hom =
        pullback.lift ((tX ≫ rX) ≫ jX) p0 piece0.w := by
      apply pullback.hom_ext <;>
        simp [e, delta, Q, SharpPullbackClosure.nestedPullbackIso, Category.assoc]
    let : WeakEquivalence e.hom := by infer_instance
    have comp : WeakEquivalence (pullback.lift ((tX ≫ rX) ≫ delta) p0 h0 ≫ e.hom) := by
      rw [fac]
      exact absolute
    let := comp
    exact weakEquivalence_of_postcomp _ e.hom
  have w1 : WeakEquivalence (pullback.lift (rX ≫ delta) p1 h1) := by
    have absolute : WeakEquivalence (pullback.lift _ _ piece1.w) :=
      (hc_iff_ordinaryLift_weak piece1 hq).mp hc1
    let e := SharpPullbackClosure.nestedPullbackIso q jY rY
    have fac : pullback.lift (rX ≫ delta) p1 h1 ≫ e.hom =
        pullback.lift (rX ≫ jX) p1 piece1.w := by
      apply pullback.hom_ext <;>
        simp [e, delta, Q, SharpPullbackClosure.nestedPullbackIso, Category.assoc]
    let : WeakEquivalence e.hom := by infer_instance
    have comp : WeakEquivalence (pullback.lift (rX ≫ delta) p1 h1 ≫ e.hom) := by
      rw [fac]
      exact absolute
    let := comp
    exact weakEquivalence_of_postcomp _ e.hom
  have w2 : WeakEquivalence (pullback.lift (bX ≫ delta) p2 h2) := by
    have absolute : WeakEquivalence (pullback.lift _ _ piece2.w) :=
      (hc_iff_ordinaryLift_weak piece2 hq).mp hc2
    let e := SharpPullbackClosure.nestedPullbackIso q jY bY
    have fac : pullback.lift (bX ≫ delta) p2 h2 ≫ e.hom =
        pullback.lift (bX ≫ jX) p2 piece2.w := by
      apply pullback.hom_ext <;>
        simp [e, delta, Q, SharpPullbackClosure.nestedPullbackIso, Category.assoc]
    let : WeakEquivalence e.hom := by infer_instance
    have comp : WeakEquivalence (pullback.lift (bX ≫ delta) p2 h2 ≫ e.hom) := by
      rw [fac]
      exact absolute
    let := comp
    exact weakEquivalence_of_postcomp _ e.hom
  have hdelta : WeakEquivalence delta := by
    let : WeakEquivalence (pullback.lift ((tX ≫ rX) ≫ delta) p0 h0) := w0
    let : WeakEquivalence (pullback.lift (rX ≫ delta) p1 h1) := w1
    let : WeakEquivalence (pullback.lift (bX ≫ delta) p2 h2) := w2
    let : WeakEquivalence (comparison Q (tY ≫ rY)) := hQ _ _
    let : WeakEquivalence (comparison Q rY) := hQ _ _
    let : WeakEquivalence (comparison Q bY) := hQ _ _
    exact RezkMonoUnionHC.comparison_weak_after_mono_union sx sy Q delta
      p0 p1 p2 hl hr h0 h1 h2 hQ (by infer_instance) (by infer_instance) (by infer_instance)
  let : WeakEquivalence delta := hdelta
  let : WeakEquivalence (comparison q jY) := hq _ _
  change WeakEquivalence (delta ≫ comparison q jY)
  infer_instance

end SSet.RezkUnionIncomingHC
