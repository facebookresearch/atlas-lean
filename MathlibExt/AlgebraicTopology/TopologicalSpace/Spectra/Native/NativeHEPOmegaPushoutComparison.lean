/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.ProperCospanGluing
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.DerivedLocalMapping
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.IndexCofibrantProperness
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHProper
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OmegaTestHomotopyCofiberClosure
import MathlibExt.Topology.Category.PointedCGWH.NativeMappingPushout
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.IndexKan.NativeStableIndexComparisons
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.IndexKan.SelectedRightKan

/-!
# Original Omega pushout comparisons with component q-cofibrations

This is the component q-cofibration intermediate for the actual symmetric and
orthogonal spectrum families. Both original caller spans and both complete
pushout-leg equations are retained, with arbitrary caller endpoints. The two
attaching maps are explicitly required to be componentwise q-cofibrations.

The actual native I construction supplies genuine cofibrant span replacements.
Pointwise scalar left properness makes their caller comparisons level weak.
Right properness of the actual mapping pullbacks then gives the original Omega
comparison. No stable model or weak-pushout outcome is supplied. The stronger
arbitrary based-HEP statement is a separate mathematical obligation.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.NativeOmegaWeakClosure
open PointedCGWH.Spectra.NativeIndexKanComposition
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed

namespace PointedCGWH.Spectra.NativeHEPOmegaPushoutComparison

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev C := EnrichedFunctorCat PointedCGWH.{u, v} I

attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private def callerComparison (D : WalkingSpan ⥤ C (I := I))
    (R : CofibrantSpanReplacement D) {Q P : C (I := I)}
    (lQ : R.Q.obj WalkingSpan.left ⟶ Q) (rQ : R.Q.obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout (R.Q.map WalkingSpan.Hom.fst) (R.Q.map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP) : Q ⟶ P :=
  sqQ.desc (R.counit.app WalkingSpan.left ≫ lP) (R.counit.app WalkingSpan.right ≫ rP) (by
    rw [← Category.assoc, R.counit.naturality WalkingSpan.Hom.fst,
      Category.assoc, sqP.w, ← Category.assoc,
      ← R.counit.naturality WalkingSpan.Hom.snd, Category.assoc])

private theorem callerComparison_left (D : WalkingSpan ⥤ C (I := I))
    (R : CofibrantSpanReplacement D) {Q P : C (I := I)}
    (lQ : R.Q.obj WalkingSpan.left ⟶ Q) (rQ : R.Q.obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout (R.Q.map WalkingSpan.Hom.fst) (R.Q.map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP) :
    lQ ≫ callerComparison D R lQ rQ sqQ lP rP sqP = R.counit.app WalkingSpan.left ≫ lP :=
  sqQ.inl_desc _ _ _

private theorem callerComparison_right (D : WalkingSpan ⥤ C (I := I))
    (R : CofibrantSpanReplacement D) {Q P : C (I := I)}
    (lQ : R.Q.obj WalkingSpan.left ⟶ Q) (rQ : R.Q.obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout (R.Q.map WalkingSpan.Hom.fst) (R.Q.map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP) :
    rQ ≫ callerComparison D R lQ rQ sqQ lP rP sqP = R.counit.app WalkingSpan.right ≫ rP :=
  sqQ.inr_desc _ _ _

private theorem callerComparison_levelWeak
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (D : WalkingSpan ⥤ C (I := I)) (R : CofibrantSpanReplacement D)
    {Q P : C (I := I)}
    (lQ : R.Q.obj WalkingSpan.left ⟶ Q) (rQ : R.Q.obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout (R.Q.map WalkingSpan.Hom.fst) (R.Q.map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP)
    (hi : ∀ a : I, Cofibration ((evaluation a).map (D.map WalkingSpan.Hom.fst))) :
    weakEquivalences (C (I := I)) (callerComparison D R lQ rQ sqQ lP rP sqP) := by
  apply (IndexCofibrantProperness.originalNativeLevelWeak_iff_evaluation _).mpr
  intro a
  let e := evaluation (V := PointedCGWH.{u, v}) a
  let _ : Cofibration (R.Q.map WalkingSpan.Hom.fst) := R.cofibration_fst
  let _ : Cofibration (e.map (R.Q.map WalkingSpan.Hom.fst)) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr
      (IndexCofibrantProperness.originalNativeCofibration_component_cofibration
        hHom _ (mem_cofibrations _) a)
  let _ : Cofibration (e.map (D.map WalkingSpan.Hom.fst)) := hi a
  have hCounit (j : WalkingSpan) : weakEquivalences PointedCGWH.{u, v} (e.map (R.counit.app j)) :=
    (IndexCofibrantProperness.originalNativeLevelWeak_iff_evaluation _).mp
      (R.counit_app_mem_trivialFibrations j).2 a
  let _ : WeakEquivalence (e.map (R.counit.app WalkingSpan.zero)) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (hCounit _)
  let _ : WeakEquivalence (e.map (R.counit.app WalkingSpan.left)) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (hCounit _)
  let _ : WeakEquivalence (e.map (R.counit.app WalkingSpan.right)) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (hCounit _)
  have hI := e.congr_map (R.counit.naturality WalkingSpan.Hom.fst)
  have hZ := e.congr_map (R.counit.naturality WalkingSpan.Hom.snd)
  have hX := e.congr_map (callerComparison_left D R lQ rQ sqQ lP rP sqP)
  have hP := e.congr_map (callerComparison_right D R lQ rQ sqQ lP rP sqP)
  simp only [Functor.map_comp] at hI hZ hX hP
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mp
    (IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst (sqQ.map e) (sqP.map e) hI hZ hX hP)

universe uC vC

omit B in
private theorem sourceFunctorPushout_weak
    {C₀ : Type uC} [Category.{vC} C₀] (S : C₀ᵒᵖ ⥤ PointedCGWH.{u, v})
    [PreservesLimitsOfShape WalkingCospan S]
    {A X Z P A' X' Z' P' : C₀}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (i' : A' ⟶ X') (z' : A' ⟶ Z') (kX' : X' ⟶ P') (kZ' : Z' ⟶ P')
    (sq : IsPushout i z kX kZ) (sq' : IsPushout i' z' kX' kZ')
    (a : A ⟶ A') (b : X ⟶ X') (c : Z ⟶ Z') (p : P ⟶ P')
    (hI : a ≫ i' = i ≫ b) (hZ : a ≫ z' = z ≫ c)
    (hX : b ≫ kX' = kX ≫ p) (hP : c ≫ kZ' = kZ ≫ p)
    [Fibration (S.map i.op)] [Fibration (S.map i'.op)]
    [WeakEquivalence (S.map a.op)] [WeakEquivalence (S.map b.op)]
    [WeakEquivalence (S.map c.op)] : WeakEquivalence (S.map p.op) := by
  have hMI := S.congr_map (congrArg Quiver.Hom.op hI)
  have hMZ := S.congr_map (congrArg Quiver.Hom.op hZ)
  have hMX := S.congr_map (congrArg Quiver.Hom.op hX)
  have hMP := S.congr_map (congrArg Quiver.Hom.op hP)
  simp only [op_comp, Functor.map_comp] at hMI hMZ hMX hMP
  exact IsRightProper.weakEquivalence_map_of_isPullbacks_of_fst
    (sq'.op.map S).flip (sq.op.map S).flip hMI hMZ hMX hMP

private theorem cofibrantPushout_omegaTests (s : NativeStabilizationFamily.{u, v} I L)
    {A X Z P A' X' Z' P' : C (I := I)}
    [IsCofibrant A] [IsCofibrant X] [IsCofibrant Z]
    [IsCofibrant A'] [IsCofibrant X'] [IsCofibrant Z']
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (i' : A' ⟶ X') (z' : A' ⟶ Z') (kX' : X' ⟶ P') (kZ' : Z' ⟶ P')
    (sq : IsPushout i z kX kZ) (sq' : IsPushout i' z' kX' kZ')
    [Cofibration i] [Cofibration i']
    (a : A ⟶ A') (b : X ⟶ X') (c : Z ⟶ Z') (p : P ⟶ P')
    (hI : a ≫ i' = i ≫ b) (hZ : a ≫ z' = z ≫ c)
    (hX : b ≫ kX' = kX ≫ p) (hP : c ≫ kZ' = kZ ≫ p)
    (ha : NativeK.omegaTests s a) (hb : NativeK.omegaTests s b)
    (hc : NativeK.omegaTests s c) : NativeK.omegaTests s p := by
  let _ : Cofibration kZ := (HomotopicalAlgebra.cofibration_iff _).mpr
    (MorphismProperty.of_isPushout sq.flip (mem_cofibrations i))
  let _ : Cofibration kZ' := (HomotopicalAlgebra.cofibration_iff _).mpr
    (MorphismProperty.of_isPushout sq'.flip (mem_cofibrations i'))
  let _ : IsCofibrant P := isCofibrant_of_cofibration kZ
  let _ : IsCofibrant P' := isCofibrant_of_cofibration kZ'
  apply DerivedLocalMapping.omegaTests_of_mappingPre_weak s p
  intro E hE
  let S := PointedCGWH.NativeMappingSourceFunctor.source E
  let _ : PreservesLimits S := PointedCGWH.NativeMappingSourcePreservation.source_preservesLimits E
  let _ : Fibration (S.map i.op) := (HomotopicalAlgebra.fibration_iff _).mpr
    (NativeK.mapSource_fibration i (mem_cofibrations i) E)
  let _ : Fibration (S.map i'.op) := (HomotopicalAlgebra.fibration_iff _).mpr
    (NativeK.mapSource_fibration i' (mem_cofibrations i') E)
  let _ : WeakEquivalence (S.map a.op) := (HomotopicalAlgebra.weakEquivalence_iff _).mpr
    (DerivedLocalMapping.mappingPre_weak_of_omegaTests s a ha E hE)
  let _ : WeakEquivalence (S.map b.op) := (HomotopicalAlgebra.weakEquivalence_iff _).mpr
    (DerivedLocalMapping.mappingPre_weak_of_omegaTests s b hb E hE)
  let _ : WeakEquivalence (S.map c.op) := (HomotopicalAlgebra.weakEquivalence_iff _).mpr
    (DerivedLocalMapping.mappingPre_weak_of_omegaTests s c hc E hE)
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mp
    (sourceFunctorPushout_weak S i z kX kZ i' z' kX' kZ' sq sq'
      a b c p hI hZ hX hP)

private theorem componentCofibrantPushout_omegaTests
    (s : NativeStabilizationFamily.{u, v} I L)
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    {A X Z P A' X' Z' P' : C (I := I)}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (i' : A' ⟶ X') (z' : A' ⟶ Z') (kX' : X' ⟶ P') (kZ' : Z' ⟶ P')
    (sq : IsPushout i z kX kZ) (sq' : IsPushout i' z' kX' kZ')
    (hi : ∀ a : I, Cofibration ((evaluation a).map i))
    (hi' : ∀ a : I, Cofibration ((evaluation a).map i'))
    (a : A ⟶ A') (b : X ⟶ X') (c : Z ⟶ Z') (p : P ⟶ P')
    (hI : a ≫ i' = i ≫ b) (hZ : a ≫ z' = z ≫ c)
    (hX : b ≫ kX' = kX ≫ p) (hP : c ≫ kZ' = kZ ≫ p)
    (ha : NativeK.omegaTests s a) (hb : NativeK.omegaTests s b)
    (hc : NativeK.omegaTests s c) : NativeK.omegaTests s p := by
  let D := span i z
  let F := span i' z'
  let α : D ⟶ F := spanHomMk a b c hI.symm hZ.symm
  let RD := originalCofibrantSpanReplacement (B := B) D
  let RF := originalCofibrantSpanReplacement (B := B) F
  let δ : RD.Q ⟶ RF.Q := (originalSpanFunctor (B := B)).map α
  let lD := pushout.inl (RD.Q.map WalkingSpan.Hom.fst) (RD.Q.map WalkingSpan.Hom.snd)
  let rD := pushout.inr (RD.Q.map WalkingSpan.Hom.fst) (RD.Q.map WalkingSpan.Hom.snd)
  let lF := pushout.inl (RF.Q.map WalkingSpan.Hom.fst) (RF.Q.map WalkingSpan.Hom.snd)
  let rF := pushout.inr (RF.Q.map WalkingSpan.Hom.fst) (RF.Q.map WalkingSpan.Hom.snd)
  let sqD := IsPushout.of_hasPushout (RD.Q.map WalkingSpan.Hom.fst) (RD.Q.map WalkingSpan.Hom.snd)
  let sqF := IsPushout.of_hasPushout (RF.Q.map WalkingSpan.Hom.fst) (RF.Q.map WalkingSpan.Hom.snd)
  let q := pushout.map (RD.Q.map WalkingSpan.Hom.fst) (RD.Q.map WalkingSpan.Hom.snd)
    (RF.Q.map WalkingSpan.Hom.fst) (RF.Q.map WalkingSpan.Hom.snd)
    (δ.app WalkingSpan.left) (δ.app WalkingSpan.right) (δ.app WalkingSpan.zero)
    (δ.naturality WalkingSpan.Hom.fst) (δ.naturality WalkingSpan.Hom.snd)
  have hL : lD ≫ q = δ.app WalkingSpan.left ≫ lF := by
    dsimp only [lD, q, pushout.map]
    rw [pushout.inl_desc]
  have hR : rD ≫ q = δ.app WalkingSpan.right ≫ rF := by
    dsimp only [rD, q, pushout.map]
    rw [pushout.inr_desc]
  have hNat (j : WalkingSpan) :
      δ.app j ≫ RF.counit.app j = RD.counit.app j ≫ α.app j :=
    congr_app ((originalSpanCounit (B := B)).naturality α) j
  have hα (j : WalkingSpan) : NativeK.omegaTests s (α.app j) := by
    rcases j with (_ | _ | _)
    · exact ha
    · exact hb
    · exact hc
  have hδ (j : WalkingSpan) : NativeK.omegaTests s (δ.app j) := by
    have hD := NativeK.levelWeak_le_omegaTests s _ (RD.counit_app_mem_trivialFibrations j).2
    have hF := NativeK.levelWeak_le_omegaTests s _ (RF.counit_app_mem_trivialFibrations j).2
    have h := (NativeK.omegaTests s).comp_mem _ _ hD (hα j)
    rw [← hNat j] at h
    exact (NativeK.omegaTests s).of_postcomp _ _ hF h
  let _ : IsCofibrant (RD.Q.obj WalkingSpan.zero) := RD.isCofibrant_zero
  let _ : Cofibration (RD.Q.map WalkingSpan.Hom.fst) := RD.cofibration_fst
  let _ : Cofibration (RD.Q.map WalkingSpan.Hom.snd) := RD.cofibration_snd
  let _ : IsCofibrant (RD.Q.obj WalkingSpan.left) := isCofibrant_of_cofibration (RD.Q.map WalkingSpan.Hom.fst)
  let _ : IsCofibrant (RD.Q.obj WalkingSpan.right) := isCofibrant_of_cofibration (RD.Q.map WalkingSpan.Hom.snd)
  let _ : IsCofibrant (RF.Q.obj WalkingSpan.zero) := RF.isCofibrant_zero
  let _ : Cofibration (RF.Q.map WalkingSpan.Hom.fst) := RF.cofibration_fst
  let _ : Cofibration (RF.Q.map WalkingSpan.Hom.snd) := RF.cofibration_snd
  let _ : IsCofibrant (RF.Q.obj WalkingSpan.left) := isCofibrant_of_cofibration (RF.Q.map WalkingSpan.Hom.fst)
  let _ : IsCofibrant (RF.Q.obj WalkingSpan.right) := isCofibrant_of_cofibration (RF.Q.map WalkingSpan.Hom.snd)
  have hq : NativeK.omegaTests s q :=
    cofibrantPushout_omegaTests s
      (RD.Q.map WalkingSpan.Hom.fst) (RD.Q.map WalkingSpan.Hom.snd) lD rD
      (RF.Q.map WalkingSpan.Hom.fst) (RF.Q.map WalkingSpan.Hom.snd) lF rF sqD sqF
      (δ.app WalkingSpan.zero) (δ.app WalkingSpan.left) (δ.app WalkingSpan.right) q
      (δ.naturality WalkingSpan.Hom.fst).symm (δ.naturality WalkingSpan.Hom.snd).symm
      hL.symm hR.symm (hδ _) (hδ _) (hδ _)
  let pD := callerComparison D RD lD rD sqD kX kZ sq
  let pF := callerComparison F RF lF rF sqF kX' kZ' sq'
  have hpD := NativeK.levelWeak_le_omegaTests s pD
    (callerComparison_levelWeak hHom D RD lD rD sqD kX kZ sq hi)
  have hpF := NativeK.levelWeak_le_omegaTests s pF
    (callerComparison_levelWeak hHom F RF lF rF sqF kX' kZ' sq' hi')
  have hDL := callerComparison_left D RD lD rD sqD kX kZ sq
  have hDR := callerComparison_right D RD lD rD sqD kX kZ sq
  have hFL := callerComparison_left F RF lF rF sqF kX' kZ' sq'
  have hFR := callerComparison_right F RF lF rF sqF kX' kZ' sq'
  have hWord : q ≫ pF = pD ≫ p := by
    apply sqD.hom_ext
    · calc
        lD ≫ (q ≫ pF) = (lD ≫ q) ≫ pF := (Category.assoc _ _ _).symm
        _ = (δ.app WalkingSpan.left ≫ lF) ≫ pF := by rw [hL]
        _ = δ.app WalkingSpan.left ≫ (lF ≫ pF) := Category.assoc _ _ _
        _ = δ.app WalkingSpan.left ≫ (RF.counit.app WalkingSpan.left ≫ kX') := by rw [hFL]
        _ = (δ.app WalkingSpan.left ≫ RF.counit.app WalkingSpan.left) ≫ kX' :=
          (Category.assoc _ _ _).symm
        _ = (RD.counit.app WalkingSpan.left ≫ b) ≫ kX' := by rw [hNat WalkingSpan.left]; rfl
        _ = RD.counit.app WalkingSpan.left ≫ (b ≫ kX') := Category.assoc _ _ _
        _ = RD.counit.app WalkingSpan.left ≫ (kX ≫ p) := by rw [hX]
        _ = (RD.counit.app WalkingSpan.left ≫ kX) ≫ p := (Category.assoc _ _ _).symm
        _ = (lD ≫ pD) ≫ p := by rw [← hDL]
        _ = lD ≫ (pD ≫ p) := Category.assoc _ _ _
    · calc
        rD ≫ (q ≫ pF) = (rD ≫ q) ≫ pF := (Category.assoc _ _ _).symm
        _ = (δ.app WalkingSpan.right ≫ rF) ≫ pF := by rw [hR]
        _ = δ.app WalkingSpan.right ≫ (rF ≫ pF) := Category.assoc _ _ _
        _ = δ.app WalkingSpan.right ≫ (RF.counit.app WalkingSpan.right ≫ kZ') := by rw [hFR]
        _ = (δ.app WalkingSpan.right ≫ RF.counit.app WalkingSpan.right) ≫ kZ' :=
          (Category.assoc _ _ _).symm
        _ = (RD.counit.app WalkingSpan.right ≫ c) ≫ kZ' := by rw [hNat WalkingSpan.right]; rfl
        _ = RD.counit.app WalkingSpan.right ≫ (c ≫ kZ') := Category.assoc _ _ _
        _ = RD.counit.app WalkingSpan.right ≫ (kZ ≫ p) := by rw [hP]
        _ = (RD.counit.app WalkingSpan.right ≫ kZ) ≫ p := (Category.assoc _ _ _).symm
        _ = (rD ≫ pD) ≫ p := by rw [← hDR]
        _ = rD ≫ (pD ≫ p) := Category.assoc _ _ _
  have h := (NativeK.omegaTests s).comp_mem _ _ hq hpF
  rw [hWord] at h
  exact (NativeK.omegaTests s).of_precomp _ _ hpD h

/-- The actual symmetric family has the full original two-span Omega comparison
when both attaching maps are componentwise q-cofibrations; endpoints are arbitrary. -/
theorem symmetric_componentCofibrantPushout_comparison_omegaTests
    {A X Z P A' X' Z' P' : Actual.SymmetricCarrier.{u, v}}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (i' : A' ⟶ X') (z' : A' ⟶ Z') (kX' : X' ⟶ P') (kZ' : Z' ⟶ P')
    (sq : IsPushout i z kX kZ) (sq' : IsPushout i' z' kX' kZ')
    (hi : ∀ a : PointedCGWH.SymmetricOperatorIndex.{u, v}, Cofibration ((evaluation a).map i))
    (hi' : ∀ a : PointedCGWH.SymmetricOperatorIndex.{u, v}, Cofibration ((evaluation a).map i'))
    (a : A ⟶ A') (b : X ⟶ X') (c : Z ⟶ Z') (p : P ⟶ P')
    (hI : a ≫ i' = i ≫ b) (hZ : a ≫ z' = z ≫ c)
    (hX : b ≫ kX' = kX ≫ p) (hP : c ≫ kZ' = kZ ≫ p)
    (ha : NativeK.omegaTests symmetricFamily a) (hb : NativeK.omegaTests symmetricFamily b)
    (hc : NativeK.omegaTests symmetricFamily c) : NativeK.omegaTests symmetricFamily p :=
  componentCofibrantPushout_omegaTests symmetricFamily
    PointedCGWH.SymmetricOperatorHom.nativeSymmetricOperatorHom_isCofibrant
    i z kX kZ i' z' kX' kZ' sq sq' hi hi' a b c p hI hZ hX hP ha hb hc

/-- The actual orthogonal family has the full original two-span Omega comparison
when both attaching maps are componentwise q-cofibrations; endpoints are arbitrary. -/
theorem orthogonal_componentCofibrantPushout_comparison_omegaTests
    {A X Z P A' X' Z' P' : Actual.OrthogonalCarrier.{u, v}}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (i' : A' ⟶ X') (z' : A' ⟶ Z') (kX' : X' ⟶ P') (kZ' : Z' ⟶ P')
    (sq : IsPushout i z kX kZ) (sq' : IsPushout i' z' kX' kZ')
    (hi : ∀ a : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}, Cofibration ((evaluation a).map i))
    (hi' : ∀ a : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}, Cofibration ((evaluation a).map i'))
    (a : A ⟶ A') (b : X ⟶ X') (c : Z ⟶ Z') (p : P ⟶ P')
    (hI : a ≫ i' = i ≫ b) (hZ : a ≫ z' = z ≫ c)
    (hX : b ≫ kX' = kX ≫ p) (hP : c ≫ kZ' = kZ ≫ p)
    (ha : NativeK.omegaTests orthogonalFamily a) (hb : NativeK.omegaTests orthogonalFamily b)
    (hc : NativeK.omegaTests orthogonalFamily c) : NativeK.omegaTests orthogonalFamily p :=
  componentCofibrantPushout_omegaTests orthogonalFamily
    PointedCGWH.Spectra.NativeStable.orthogonalHom_isCofibrant
    i z kX kZ i' z' kX' kZ' sq sq' hi hi' a b c p hI hZ hX hP ha hb hc

/-- Actual symmetric native cofibrations earn the required component geometry. -/
theorem symmetric_nativeCofibration_component {A X : Actual.SymmetricCarrier.{u, v}} (i : A ⟶ X)
    (hi : cofibrations Actual.SymmetricCarrier.{u, v} i) :
    ∀ a : PointedCGWH.SymmetricOperatorIndex.{u, v}, Cofibration ((evaluation a).map i) := by
  intro a
  exact (HomotopicalAlgebra.cofibration_iff _).mpr
    (IndexCofibrantProperness.originalNativeCofibration_component_cofibration
      PointedCGWH.SymmetricOperatorHom.nativeSymmetricOperatorHom_isCofibrant i hi a)

/-- Actual orthogonal native cofibrations earn the required component geometry. -/
theorem orthogonal_nativeCofibration_component {A X : Actual.OrthogonalCarrier.{u, v}} (i : A ⟶ X)
    (hi : cofibrations Actual.OrthogonalCarrier.{u, v} i) :
    ∀ a : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}, Cofibration ((evaluation a).map i) := by
  intro a
  exact (HomotopicalAlgebra.cofibration_iff _).mpr
    (IndexCofibrantProperness.originalNativeCofibration_component_cofibration
      PointedCGWH.Spectra.NativeStable.orthogonalHom_isCofibrant i hi a)

/-- The actual UP map of every native symmetric cofibration earns the full
component q-cofibration geometry through the original level Kan adjunction. -/
theorem symmetricOrthogonal_up_nativeCofibration_component
    {A X : Actual.SymmetricCarrier.{u, v}} (i : A ⟶ X)
    (hi : cofibrations Actual.SymmetricCarrier.{u, v} i) :
    ∀ a : PointedCGWH.SymmetricOperatorIndex.{u, v},
      Cofibration ((evaluation a).map
        ((symmetricOrthogonalLan ⋙ symmetricOrthogonalRestriction).map i)) := by
  let hQ := PointedCGWH.Spectra.Orthogonal.IndexKan.originalAdjunction_isQuillen
    CategoryTheory.Spectra.SpectrumIndexMaps.symmetricOrthogonalOperatorIndexFunctor
  have hLan : cofibrations Actual.OrthogonalCarrier.{u, v} (symmetricOrthogonalLan.map i) :=
    hQ.preservesCofibrations i hi
  intro a
  have h := orthogonal_nativeCofibration_component (symmetricOrthogonalLan.map i) hLan
    (CategoryTheory.Spectra.SpectrumIndexMaps.symmetricOrthogonalOperatorIndexFunctor.obj a)
  change Cofibration (component
    (restrictionMap CategoryTheory.Spectra.SpectrumIndexMaps.symmetricOrthogonalOperatorIndexFunctor
      (symmetricOrthogonalLan.map i)) a)
  rw [restrictionMap_component]
  exact h

/-- Every original native-cofibration unit pushout retains all unit Omega tests,
using the earned component geometry of both original UP span maps. -/
theorem symmetricOrthogonal_unit_nativeCofibrantPushout_omegaTests
    {A X Z P : Actual.SymmetricCarrier.{u, v}}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (sq : IsPushout i z kX kZ) (hi : cofibrations Actual.SymmetricCarrier.{u, v} i)
    (hA : NativeK.omegaTests symmetricFamily (symmetricOrthogonalAdjunction.unit.app A))
    (hX : NativeK.omegaTests symmetricFamily (symmetricOrthogonalAdjunction.unit.app X))
    (hZ : NativeK.omegaTests symmetricFamily (symmetricOrthogonalAdjunction.unit.app Z)) :
    NativeK.omegaTests symmetricFamily (symmetricOrthogonalAdjunction.unit.app P) := by
  let UP := symmetricOrthogonalLan.{u, v} ⋙ symmetricOrthogonalRestriction
  let _ : PreservesColimitsOfShape WalkingSpan symmetricOrthogonalLan.{u, v} :=
    symmetricOrthogonalAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  let hRan := PointedCGWH.Spectra.Orthogonal.IndexKan.originalRanAdjunction
    CategoryTheory.Spectra.SpectrumIndexMaps.symmetricOrthogonalOperatorIndexFunctor.{u, v}
  let _ : PreservesColimitsOfShape WalkingSpan symmetricOrthogonalRestriction.{u, v} :=
    hRan.leftAdjoint_preservesColimits.preservesColimitsOfShape
  let _ : PreservesColimitsOfShape WalkingSpan UP :=
    comp_preservesColimitsOfShape (F := symmetricOrthogonalLan) (G := symmetricOrthogonalRestriction)
  exact symmetric_componentCofibrantPushout_comparison_omegaTests
    i z kX kZ (UP.map i) (UP.map z) (UP.map kX) (UP.map kZ) sq (sq.map UP)
    (symmetric_nativeCofibration_component i hi)
    (symmetricOrthogonal_up_nativeCofibration_component i hi)
    (symmetricOrthogonalAdjunction.unit.app A) (symmetricOrthogonalAdjunction.unit.app X)
    (symmetricOrthogonalAdjunction.unit.app Z) (symmetricOrthogonalAdjunction.unit.app P)
    (symmetricOrthogonalAdjunction.unit.naturality i).symm
    (symmetricOrthogonalAdjunction.unit.naturality z).symm
    (symmetricOrthogonalAdjunction.unit.naturality kX).symm
    (symmetricOrthogonalAdjunction.unit.naturality kZ).symm hA hX hZ

end PointedCGWH.Spectra.NativeHEPOmegaPushoutComparison
