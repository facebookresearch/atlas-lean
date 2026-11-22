/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneFunctorCoreProducts

/-!
# Equivalence and replacement compatibility of native one-fold functor cores

Original source and target weak maps act through the same full functor maps.
The original and native common-core legs transfer their scalar weakness.
Full and normalized original replacement conventions are compared through
their actual units from the same literal zero core, without equating factors.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SSet.modelCategoryQuillen
open SimplicialPresheaf.InjectiveKan SimplicialPresheaf.OriginalLocalDerived

namespace SimplicialPresheaf.OrderedJFS.OneFunctor.Core

private local instance sourceLocallySmall : LocallySmall.{u} (FinitePowerSite.Source 1) :=
  @CategoryTheory.locallySmall_of_univLE _ _ UnivLE.zero

private def originalCommon :
    ConstantEvaluation.evaluation.{u} 1 ⟶
      oneDesignatedEquivalence.functor ⋙ SimplicialSpace.OnefoldCoreComparison.commonCore :=
  zeroEvaluationIso.hom ≫ Functor.whiskerLeft oneDesignatedEquivalence.functor
    SimplicialSpace.OnefoldCoreComparison.targetCoreLeg

private def nativeCommon :
    oneDesignatedEquivalence.{u}.functor ⋙ SimplicialSpace.OnefoldCoreComparison.nativeCore ⟶
      oneDesignatedEquivalence.functor ⋙ SimplicialSpace.OnefoldCoreComparison.commonCore :=
  Functor.whiskerLeft oneDesignatedEquivalence.functor
    SimplicialSpace.OnefoldCoreComparison.nativeCoreLeg

private theorem nativeWeak_of_zeroWeak {F G : Original.{u} 1} (f : F ⟶ G)
    (hF : isOriginalLocalFibrant family.{u} F) (hG : isOriginalLocalFibrant family.{u} G)
    (hf : SSet.realizationWeakEquivalences ((ConstantEvaluation.evaluation 1).map f)) :
    SSet.realizationWeakEquivalences
      (SimplicialSpace.OnefoldCoreComparison.nativeCore.map (oneDesignatedEquivalence.functor.map f)) := by
  have hOrigF : SSet.realizationWeakEquivalences (originalCommon.app F) :=
    SSet.realizationWeakEquivalences.comp_mem _ _
      (SSet.realizationWeakEquivalences.of_isIso (zeroEvaluationIso.hom.app F))
      (SimplicialSpace.OnefoldCoreComparison.targetCoreLeg_weak _
        ((one_locality_recognition F).2.2.mp hF))
  have hOrigG : SSet.realizationWeakEquivalences (originalCommon.app G) :=
    SSet.realizationWeakEquivalences.comp_mem _ _
      (SSet.realizationWeakEquivalences.of_isIso (zeroEvaluationIso.hom.app G))
      (SimplicialSpace.OnefoldCoreComparison.targetCoreLeg_weak _
        ((one_locality_recognition G).2.2.mp hG))
  have hNativeF : SSet.realizationWeakEquivalences (nativeCommon.app F) :=
    SimplicialSpace.OnefoldCoreComparison.nativeCoreLeg_weak _
      ((one_locality_recognition F).2.2.mp hF)
  have hNativeG : SSet.realizationWeakEquivalences (nativeCommon.app G) :=
    SimplicialSpace.OnefoldCoreComparison.nativeCoreLeg_weak _
      ((one_locality_recognition G).2.2.mp hG)
  have hc : SSet.realizationWeakEquivalences
      ((oneDesignatedEquivalence.functor ⋙ SimplicialSpace.OnefoldCoreComparison.commonCore).map f) := by
    apply SSet.realizationWeakEquivalences.of_precomp _ _ hOrigF
    rw [← originalCommon.naturality f]
    exact SSet.realizationWeakEquivalences.comp_mem _ _ hf hOrigG
  apply SSet.realizationWeakEquivalences.of_postcomp _ _ hNativeG
  change SSet.realizationWeakEquivalences
    ((oneDesignatedEquivalence.functor ⋙ SimplicialSpace.OnefoldCoreComparison.nativeCore).map f ≫
      nativeCommon.app G)
  rw [nativeCommon.naturality f]
  exact SSet.realizationWeakEquivalences.comp_mem _ _ hNativeF hc

/-- Original weak source maps retain their weak action on the actual native functor core. -/
theorem nativeSource_weak {A B : Original.{u} 1} (f : A ⟶ B)
    (hf : originalLocalEquivalences family.{u} f) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) :
    SSet.realizationWeakEquivalences
      (SimplicialSpace.OnefoldCoreComparison.nativeCore.map
        (oneDesignatedEquivalence.functor.map (sourceMap f Z))) := by
  have hw : SSet.realizationWeakEquivalences ((innerHomFunctor.{u}.map f.op).app Z) :=
    hf Z hZ
  have hRaw : SSet.realizationWeakEquivalences
      ((ConstantEvaluation.evaluation 1).map (sourceMap f Z)) := by
    apply SSet.realizationWeakEquivalences.of_postcomp _ _
      (SSet.realizationWeakEquivalences.of_isIso ((rawEndNatIso A).hom.app Z))
    rw [rawEndNatIso_source]
    exact SSet.realizationWeakEquivalences.comp_mem _ _
      (SSet.realizationWeakEquivalences.of_isIso ((rawEndNatIso B).hom.app Z)) hw
  exact nativeWeak_of_zeroWeak (sourceMap f Z) (object_localFibrant B Z hZ)
    (object_localFibrant A Z hZ) hRaw

/-- Original local weak target maps retain their weak action on the actual native functor core. -/
theorem nativeTarget_weak (A : Original.{u} 1) {Z V : Original.{u} 1} (g : Z ⟶ V)
    (hg : originalLocalEquivalences family.{u} g)
    (hZ : isOriginalLocalFibrant family.{u} Z) (hV : isOriginalLocalFibrant family.{u} V) :
    SSet.realizationWeakEquivalences ((nativeCoreFunctor A).map g) := by
  have hbase := (originalLocalEquivalence_iff_weakEquivalence_of_localFibrant family.{u}
    g hZ hV).mp hg
  have hw := innerHomPost_weak_of_weakEquivalence.{u} A g hbase hZ.1 hV.1
  have hRaw : SSet.realizationWeakEquivalences ((rawCoreFunctor A).map g) := by
    apply SSet.realizationWeakEquivalences.of_postcomp _ _
      (SSet.realizationWeakEquivalences.of_isIso ((rawEndNatIso A).hom.app V))
    rw [(rawEndNatIso A).hom.naturality g]
    exact SSet.realizationWeakEquivalences.comp_mem _ _
      (SSet.realizationWeakEquivalences.of_isIso ((rawEndNatIso A).hom.app Z)) hw
  exact nativeWeak_of_zeroWeak (targetMap A g) (object_localFibrant A Z hZ)
    (object_localFibrant A V hV) hRaw

/-- The full original replacement still uses its actual separate R factors. -/
abbrev fullCoreFunctor (A : Original.{u} 1) : Original.{u} 1 ⥤ SSet.{u} :=
  objectFunctor A ⋙ TransferredCoreReplacements.rReplacement (fullOriginalFamily.{u} 1)
    (ConstantEvaluation.zeroTuple 1)

/-- The full original unit is evaluated on the same whole functor object. -/
def fullCoreUnit (A : Original.{u} 1) : rawCoreFunctor A ⟶ fullCoreFunctor A :=
  Functor.whiskerLeft (objectFunctor A)
    (TransferredCoreReplacements.rUnit (fullOriginalFamily.{u} 1) (ConstantEvaluation.zeroTuple 1))

/-- Full-family replacement weakness is derived from the actual original normalized target. -/
theorem fullCoreUnit_weak (A Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z) :
    SSet.realizationWeakEquivalences ((fullCoreUnit A).app Z) := by
  have hFull : isOriginalLocalFibrant (fullOriginalFamily.{u} 1) Z :=
    (one_locality_recognition Z).2.1.mpr ((one_locality_recognition Z).1.mp hZ)
  exact (TransferredCoreReplacements.rUnit_trivialCofibration (fullOriginalFamily.{u} 1)
    (ConstantEvaluation.zeroTuple 1) (object A Z) (object_fullLocalFibrant A Z hFull)).2

/-- Full and normalized original core choices are compared by their two actual evaluated units. -/
def changeReplacementIso (A Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z) :
    scalarHo.obj ((coreFunctor A).obj Z) ≅ scalarHo.obj ((fullCoreFunctor A).obj Z) := by
  let _ : IsIso (scalarHo.map ((coreUnit A).app Z)) :=
    Localization.inverts scalarHo SSet.realizationWeakEquivalences _ (coreUnit_weak A Z hZ)
  let _ : IsIso (scalarHo.map ((fullCoreUnit A).app Z)) :=
    Localization.inverts scalarHo SSet.realizationWeakEquivalences _ (fullCoreUnit_weak A Z hZ)
  exact (asIso (scalarHo.map ((coreUnit A).app Z))).symm ≪≫
    asIso (scalarHo.map ((fullCoreUnit A).app Z))

/-- The replacement comparison keeps the literal original common-zero-core triangle. -/
theorem changeReplacementIso_triangle (A Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) :
    scalarHo.map ((coreUnit A).app Z) ≫ (changeReplacementIso A Z hZ).hom =
      scalarHo.map ((fullCoreUnit A).app Z) := by
  let _ : IsIso (scalarHo.map ((coreUnit A).app Z)) :=
    Localization.inverts scalarHo SSet.realizationWeakEquivalences _ (coreUnit_weak A Z hZ)
  change scalarHo.map ((coreUnit A).app Z) ≫
    (inv (scalarHo.map ((coreUnit A).app Z)) ≫ scalarHo.map ((fullCoreUnit A).app Z)) = _
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

/-- The original source Q-counit acts weakly on the native functor core, with no new factor choice. -/
theorem nativeQ_weak (A Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z) :
    SSet.realizationWeakEquivalences
      (SimplicialSpace.OnefoldCoreComparison.nativeCore.map
        (oneDesignatedEquivalence.functor.map (sourceMap ((localQCounit family.{u}).app A) Z))) :=
  nativeSource_weak _ (weakEquivalences_le_originalLocalEquivalences family.{u} _
    (localQCounit_baseTrivialFibration family.{u} A).2) Z hZ

/-- The original target R-unit retains its weak native-core action at a genuinely local source target. -/
theorem nativeR_weak (A Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z) :
    SSet.realizationWeakEquivalences ((nativeCoreFunctor A).map ((localRUnit family.{u}).app Z)) :=
  nativeTarget_weak A _ (localRUnit_localTrivialCofibration family.{u} Z).2 hZ
    (localR_isOriginalLocalFibrant family.{u} Z)

/-- The derived native-core triangle retains the original Q-counit's actual contravariant map. -/
theorem nativeMappingIso_q (A Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z) :
    scalarHo.map (SimplicialSpace.OnefoldCoreComparison.nativeCore.map
        (oneDesignatedEquivalence.functor.map (sourceMap ((localQCounit family.{u}).app A) Z))) ≫
          (nativeMappingIso ((localQ family.{u}).obj A) Z hZ).hom =
      (nativeMappingIso A Z hZ).hom ≫ scalarHo.map
        (localDerivedPrecomp family.{u} ((localQCounit family.{u}).app A) Z) :=
  nativeMappingIso_source ((localQCounit family.{u}).app A) Z hZ

/-- The derived native-core triangle retains the original R-unit's actual covariant map. -/
theorem nativeMappingIso_r (A Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z) :
    scalarHo.map ((nativeCoreFunctor A).map ((localRUnit family.{u}).app Z)) ≫
        (nativeMappingIso A ((localR family.{u}).obj Z)
          (localR_isOriginalLocalFibrant family.{u} Z)).hom =
      (nativeMappingIso A Z hZ).hom ≫
        scalarHo.map (localDerivedPostcomp family.{u} A ((localRUnit family.{u}).app Z)) :=
  nativeMappingIso_target A hZ (localR_isOriginalLocalFibrant family.{u} Z)
    ((localRUnit family.{u}).app Z)

/-- Full and normalized core replacements are natural on the same actual original target maps. -/
theorem changeReplacementIso_target (A : Original.{u} 1) {Z V : Original.{u} 1}
    (hZ : isOriginalLocalFibrant family.{u} Z) (hV : isOriginalLocalFibrant family.{u} V) (g : Z ⟶ V) :
    scalarHo.map ((coreFunctor A).map g) ≫ (changeReplacementIso A V hV).hom =
      (changeReplacementIso A Z hZ).hom ≫ scalarHo.map ((fullCoreFunctor A).map g) := by
  let _ : IsIso (scalarHo.map ((coreUnit A).app Z)) :=
    Localization.inverts scalarHo SSet.realizationWeakEquivalences _ (coreUnit_weak A Z hZ)
  apply (cancel_epi (scalarHo.map ((coreUnit A).app Z))).mp
  calc
    _ = scalarHo.map ((rawCoreFunctor A).map g) ≫ scalarHo.map ((fullCoreUnit A).app V) := by
      rw [← Category.assoc, ← scalarHo.map_comp, ← (coreUnit A).naturality g,
        scalarHo.map_comp, Category.assoc, changeReplacementIso_triangle A V hV]
    _ = scalarHo.map ((fullCoreUnit A).app Z) ≫ scalarHo.map ((fullCoreFunctor A).map g) := by
      rw [← scalarHo.map_comp, (fullCoreUnit A).naturality g, scalarHo.map_comp]
    _ = _ := by
      rw [← changeReplacementIso_triangle A Z hZ]
      simp only [Category.assoc]

/-- Full and normalized replacements retain the same original source-map square. -/
theorem changeReplacementIso_source {A B : Original.{u} 1} (f : A ⟶ B) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) :
    scalarHo.map ((TransferredCoreReplacements.rReplacement family.{u}
        (ConstantEvaluation.zeroTuple 1)).map (sourceMap f Z)) ≫ (changeReplacementIso A Z hZ).hom =
      (changeReplacementIso B Z hZ).hom ≫
        scalarHo.map ((TransferredCoreReplacements.rReplacement (fullOriginalFamily.{u} 1)
          (ConstantEvaluation.zeroTuple 1)).map (sourceMap f Z)) := by
  let _ : IsIso (scalarHo.map ((coreUnit B).app Z)) :=
    Localization.inverts scalarHo SSet.realizationWeakEquivalences _ (coreUnit_weak B Z hZ)
  have hf : (ConstantEvaluation.evaluation 1).map (sourceMap f Z) ≫ (fullCoreUnit A).app Z =
      (fullCoreUnit B).app Z ≫
        (TransferredCoreReplacements.rReplacement (fullOriginalFamily.{u} 1)
          (ConstantEvaluation.zeroTuple 1)).map (sourceMap f Z) :=
    (TransferredCoreReplacements.rUnit (fullOriginalFamily.{u} 1)
      (ConstantEvaluation.zeroTuple 1)).naturality (sourceMap f Z)
  apply (cancel_epi (scalarHo.map ((coreUnit B).app Z))).mp
  calc
    _ = scalarHo.map ((ConstantEvaluation.evaluation 1).map (sourceMap f Z)) ≫
        scalarHo.map ((fullCoreUnit A).app Z) := by
      rw [← Category.assoc, ← scalarHo.map_comp, ← coreUnit_source,
        scalarHo.map_comp, Category.assoc, changeReplacementIso_triangle A Z hZ]
    _ = scalarHo.map ((fullCoreUnit B).app Z) ≫
        scalarHo.map ((TransferredCoreReplacements.rReplacement (fullOriginalFamily.{u} 1)
          (ConstantEvaluation.zeroTuple 1)).map (sourceMap f Z)) := by
      rw [← scalarHo.map_comp, hf, scalarHo.map_comp]
    _ = _ := by
      rw [← changeReplacementIso_triangle B Z hZ]
      simp only [Category.assoc]

end SimplicialPresheaf.OrderedJFS.OneFunctor.Core
