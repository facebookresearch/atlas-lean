/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.PreimagePushout
import MathlibExt.AlgebraicTopology.SimplicialSet.CompatiblePushoutHCTransport
import MathlibExt.AlgebraicTopology.SimplicialSet.SharpGluing
import MathlibExt.AlgebraicTopology.ModelCategory.ProperSpanGluing

/-!
# The weak comparison after a mono union

Pull the actual base pushout back along its sharp ambient arrow. The
three source-piece HC comparisons give three ordinary weak maps. Proper
span gluing proves weakness of the SAME total comparison. The mono
hypotheses are the original union inclusions, not the comparison maps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet.RezkMonoUnionHC
open SharpComparisonDraft RezkCompatiblePushout

/-- The SAME union-to-total comparison is weak from its three original HC pieces. -/
theorem comparison_weak_after_mono_union
    {X0 X1 X2 A Y0 Y1 Y2 B E : SSet.{u}}
    {tX : X0 ⟶ X1} {iX : X0 ⟶ X2} {rX : X1 ⟶ A} {bX : X2 ⟶ A}
    {tY : Y0 ⟶ Y1} {iY : Y0 ⟶ Y2} {rY : Y1 ⟶ B} {bY : Y2 ⟶ B}
    (sourceSquare : IsPushout tX iX rX bX)
    (baseSquare : IsPushout tY iY rY bY)
    (q : E ⟶ B) (delta : A ⟶ E)
    (p0 : X0 ⟶ Y0) (p1 : X1 ⟶ Y1) (p2 : X2 ⟶ Y2)
    (hleft : tX ≫ p1 = p0 ≫ tY) (hright : iX ≫ p2 = p0 ≫ iY)
    (h0 : ((tX ≫ rX) ≫ delta) ≫ q = p0 ≫ (tY ≫ rY))
    (h1 : (rX ≫ delta) ≫ q = p1 ≫ rY)
    (h2 : (bX ≫ delta) ≫ q = p2 ≫ bY)
    [Mono iX] [Mono iY] (hq : Sharp q)
    (hc0 : WeakEquivalence (pullback.lift ((tX ≫ rX) ≫ delta) p0 h0 ≫
      comparison q (tY ≫ rY)))
    (hc1 : WeakEquivalence (pullback.lift (rX ≫ delta) p1 h1 ≫ comparison q rY))
    (hc2 : WeakEquivalence (pullback.lift (bX ≫ delta) p2 h2 ≫ comparison q bY)) :
    WeakEquivalence delta := by
  let a : X0 ⟶ pullback q (tY ≫ rY) :=
    pullback.lift ((tX ≫ rX) ≫ delta) p0 h0
  let b : X1 ⟶ pullback q rY := pullback.lift (rX ≫ delta) p1 h1
  let c : X2 ⟶ pullback q bY := pullback.lift (bX ≫ delta) p2 h2
  have ha : WeakEquivalence a :=
    (hc_iff_ordinaryLift_weak (CommSq.mk h0) hq).mp hc0
  have hb : WeakEquivalence b :=
    (hc_iff_ordinaryLift_weak (CommSq.mk h1) hq).mp hc1
  have hc : WeakEquivalence c :=
    (hc_iff_ordinaryLift_weak (CommSq.mk h2) hq).mp hc2
  let targetSquare := PreimagePushout.isPushout baseSquare q
  let top : pullback q (tY ≫ rY) ⟶ pullback q rY := PreimagePushout.boundaryToOld q
  let left : pullback q (tY ≫ rY) ⟶ pullback q bY :=
    PreimagePushout.boundaryToCell baseSquare q
  have htop : tX ≫ b = a ≫ top := by
    apply pullback.hom_ext
    · simp only [a, b, top, Category.assoc, pullback.lift_fst,
        PreimagePushout.boundaryToOld_fst]
    · calc
        (tX ≫ b) ≫ pullback.snd q rY = tX ≫ p1 := by
          dsimp only [b]
          rw [Category.assoc, pullback.lift_snd]
        _ = p0 ≫ tY := hleft
        _ = (a ≫ top) ≫ pullback.snd q rY := by
          dsimp only [a, top]
          rw [Category.assoc, PreimagePushout.boundaryToOld_snd,
            ← Category.assoc, pullback.lift_snd]
  have hcell : iX ≫ c = a ≫ left := by
    apply pullback.hom_ext
    · simpa only [a, c, left, Category.assoc, pullback.lift_fst,
        PreimagePushout.boundaryToCell_fst] using
        congrArg (fun z => z ≫ delta) sourceSquare.w.symm
    · calc
        (iX ≫ c) ≫ pullback.snd q bY = iX ≫ p2 := by
          dsimp only [c]
          rw [Category.assoc, pullback.lift_snd]
        _ = p0 ≫ iY := hright
        _ = (a ≫ left) ≫ pullback.snd q bY := by
          dsimp only [a, left]
          rw [Category.assoc, PreimagePushout.boundaryToCell_snd,
            ← Category.assoc, pullback.lift_snd]
  have hold : rX ≫ delta = b ≫ pullback.fst q rY := by
    dsimp only [b]
    exact (pullback.lift_fst _ _ _).symm
  have hnew : bX ≫ delta = c ≫ pullback.fst q bY := by
    dsimp only [c]
    exact (pullback.lift_fst _ _ _).symm
  let : Mono left := (PreimagePushout.boundaryToCell_isPullback baseSquare q).mono_fst_of_mono
  let : Cofibration iX := (SSet.modelCategoryQuillen.cofibration_iff iX).mpr inferInstance
  let : Cofibration left := (SSet.modelCategoryQuillen.cofibration_iff left).mpr inferInstance
  let : WeakEquivalence a := ha
  let : WeakEquivalence b := hb
  let : WeakEquivalence c := hc
  exact IsLeftProper.weakEquivalence_map_of_isPushouts_of_snd
    sourceSquare targetSquare htop hcell hold hnew

end SSet.RezkMonoUnionHC
