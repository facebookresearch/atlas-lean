/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneFunctorCoreUniversal
import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalQuasicategoryCoreComparison

/-!
# The native quasicategory core of the original one-fold functor object

The actual first Joyal–Tierney right image of the complete functor presentation
has its native equivalence-edge core. The proved one-fold common-core cospan,
the checked new original zero comparison, and the actual Q/R end map identify
that core with the original derived scalar mapping object. The original
counit, Gamma unit, SOA replacement and common-core injections are retained.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial SSet.modelCategoryQuillen MonoidalCategory
open SimplicialPresheaf.InjectiveKan SimplicialPresheaf.OriginalLocalDerived

namespace SimplicialPresheaf.OrderedJFS.OneFunctor.Core

/-- The complete one-fold presentation is the image of the entire original functor object. -/
abbrev cssImage (A Z : Original.{u} 1) : SimplicialSpace.{u} :=
  oneDesignatedEquivalence.functor.obj (object A Z)

/-- Completeness is derived from the genuine original target predicate and power closure. -/
theorem cssImage_complete (A Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z) :
    SimplicialSpace.completeSegalSpaces (cssImage A Z) :=
  (one_locality_recognition (object A Z)).2.2.mp (object_localFibrant A Z hZ)

/-- The actual first-right-image equivalence-edge core of that full functor presentation. -/
abbrev nativeCoreFunctor (A : Original.{u} 1) : Original.{u} 1 ⥤ SSet.{u} :=
  objectFunctor A ⋙ oneDesignatedEquivalence.functor ⋙ SimplicialSpace.OnefoldCoreComparison.nativeCore

/-- Its original core is Kan by the actual first JT right-image theorem. -/
theorem nativeCore_isKan (A Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z) :
    SSet.KanComplex ((nativeCoreFunctor A).obj Z) :=
  SimplicialSpace.OnefoldCoreComparison.nativeCore_isKan _ (cssImage_complete A Z hZ)

/-- The common core retains the same completed pushout and original replacement maps. -/
abbrev nativeCommonFunctor (A : Original.{u} 1) : Original.{u} 1 ⥤ SSet.{u} :=
  objectFunctor A ⋙ oneDesignatedEquivalence.functor ⋙ SimplicialSpace.OnefoldCoreComparison.commonCore

/-- The original common-core object is the value of that same actual functor. -/
abbrev nativeCommonCore (A Z : Original.{u} 1) : SSet.{u} :=
  (nativeCommonFunctor A).obj Z

/-- The strict original zero/common-core leg is natural in every original target. -/
def rawNativeLeg (A : Original.{u} 1) : rawCoreFunctor A ⟶ nativeCommonFunctor A :=
  Functor.whiskerLeft (objectFunctor A) (zeroEvaluationIso.hom ≫
    Functor.whiskerLeft oneDesignatedEquivalence.functor
      SimplicialSpace.OnefoldCoreComparison.targetCoreLeg)

/-- The strict native core/common-core leg keeps its original Gamma map and is natural. -/
def nativeCoreLeg (A : Original.{u} 1) : nativeCoreFunctor A ⟶ nativeCommonFunctor A :=
  Functor.whiskerLeft (objectFunctor A ⋙ oneDesignatedEquivalence.functor)
    SimplicialSpace.OnefoldCoreComparison.nativeCoreLeg

/-- The original core leg uses the fixed zero comparison and the original target injection. -/
def rawToNativeCommon (A Z : Original.{u} 1) :
    (rawCoreFunctor A).obj Z ⟶ nativeCommonCore A Z :=
  (rawNativeLeg A).app Z

/-- The native equivalence-edge core leg retains the original Gamma/common-core construction. -/
def nativeToCommon (A Z : Original.{u} 1) :
    (nativeCoreFunctor A).obj Z ⟶ nativeCommonCore A Z :=
  (nativeCoreLeg A).app Z

/-- The original strict forward leg is weak from actual one-fold completeness. -/
theorem rawToNativeCommon_weak (A Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) :
    SSet.realizationWeakEquivalences (rawToNativeCommon A Z) :=
  SSet.realizationWeakEquivalences.comp_mem _ _
    (SSet.realizationWeakEquivalences.of_isIso (zeroEvaluationIso.hom.app (object A Z)))
    (SimplicialSpace.OnefoldCoreComparison.targetCoreLeg_weak _ (cssImage_complete A Z hZ))

/-- The native strict forward leg is weak by the actual same completed-pushout theorem. -/
theorem nativeToCommon_weak (A Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) :
    SSet.realizationWeakEquivalences (nativeToCommon A Z) :=
  SimplicialSpace.OnefoldCoreComparison.nativeCoreLeg_weak _ (cssImage_complete A Z hZ)

/-- Both original legs retain each original all-zero vertex of the entire functor object. -/
theorem original_vertex_square (A Z : Original.{u} 1)
    (x : ((rawCoreFunctor A).obj Z).obj (op ⦋0⦌)) :
    (rawToNativeCommon A Z).app (op ⦋0⦌) x =
      (nativeToCommon A Z).app (op ⦋0⦌)
        ⟨x, SSet.mem_core_obj_zero (X := SimplicialSpace.OnefoldCoreComparison.row.obj
          (cssImage A Z)) x⟩ :=
  SimplicialSpace.OnefoldCoreComparison.original_vertex_square (cssImage A Z) x

private def hoZeroIso (F : Original.{u} 1) (hF : isOriginalLocalFibrant family.{u} F) :
    scalarHo.obj ((ConstantEvaluation.evaluation 1).obj F) ≅
      SimplicialSpace.OnefoldCoreComparison.targetHo.obj
        ⟨oneDesignatedEquivalence.functor.obj F, (one_locality_recognition F).2.2.mp hF⟩ :=
  scalarHo.mapIso (zeroEvaluationIso.app F)

private def nativeObjectIso (F : Original.{u} 1) (hF : isOriginalLocalFibrant family.{u} F) :
    scalarHo.obj ((ConstantEvaluation.evaluation 1).obj F) ≅
      SimplicialSpace.OnefoldCoreComparison.nativeHo.obj
        ⟨oneDesignatedEquivalence.functor.obj F, (one_locality_recognition F).2.2.mp hF⟩ :=
  hoZeroIso F hF ≪≫ SimplicialSpace.OnefoldCoreComparison.coreHoIso.app
    ⟨oneDesignatedEquivalence.functor.obj F, (one_locality_recognition F).2.2.mp hF⟩

private theorem nativeObjectIso_triangle (F : Original.{u} 1)
    (hF : isOriginalLocalFibrant family.{u} F) :
    (nativeObjectIso F hF).hom ≫ SimplicialSpace.OnefoldCoreComparison.nativeHoLeg.app
        ⟨oneDesignatedEquivalence.functor.obj F, (one_locality_recognition F).2.2.mp hF⟩ =
      (hoZeroIso F hF).hom ≫ SimplicialSpace.OnefoldCoreComparison.targetHoLeg.app
        ⟨oneDesignatedEquivalence.functor.obj F, (one_locality_recognition F).2.2.mp hF⟩ := by
  let C : SimplicialSpace.OnefoldCoreComparison.CompleteTargets.{u} :=
    ⟨oneDesignatedEquivalence.functor.obj F, (one_locality_recognition F).2.2.mp hF⟩
  have hn := congrArg (fun t => t.app C)
    SimplicialSpace.OnefoldCoreComparison.coreHoIso_triangle
  simp only [NatTrans.comp_app] at hn
  change ((hoZeroIso F hF).hom ≫
      SimplicialSpace.OnefoldCoreComparison.coreHoIso.hom.app C) ≫
        SimplicialSpace.OnefoldCoreComparison.nativeHoLeg.app C =
      (hoZeroIso F hF).hom ≫ SimplicialSpace.OnefoldCoreComparison.targetHoLeg.app C
  rw [Category.assoc, hn]

/-- The original zero core and the actual native core are compared by the same original legs. -/
def nativeZeroIso (A Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z) :
    scalarHo.obj ((rawCoreFunctor A).obj Z) ≅ scalarHo.obj ((nativeCoreFunctor A).obj Z) :=
  nativeObjectIso (object A Z) (object_localFibrant A Z hZ)

/-- The original zero/core comparison retains both localized strict forward legs. -/
theorem nativeZeroIso_triangle (A Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) :
    (nativeZeroIso A Z hZ).hom ≫ scalarHo.map (nativeToCommon A Z) =
      scalarHo.map (rawToNativeCommon A Z) := by
  have h := nativeObjectIso_triangle (object A Z) (object_localFibrant A Z hZ)
  exact h.trans (scalarHo.map_comp (zeroEvaluationIso.hom.app (object A Z))
    (SimplicialSpace.OnefoldCoreComparison.targetCoreLeg.app (cssImage A Z))).symm

/-- The genuine native quasicategory core represents the actual original derived scalar end. -/
def nativeMappingIso (A Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z) :
    scalarHo.obj ((nativeCoreFunctor A).obj Z) ≅
      scalarHo.obj (((localDerivedEnd family.{u}).obj (op A)).obj Z) :=
  (nativeZeroIso A Z hZ).symm ≪≫ rawMappingIso A Z hZ

/-- This derived-end interpretation uses the same native zero/core comparison and forward end leg. -/
theorem nativeMappingIso_triangle (A Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) :
    (nativeZeroIso A Z hZ).hom ≫ (nativeMappingIso A Z hZ).hom =
      scalarHo.map ((derivedComparison A).app Z) := by
  change (nativeZeroIso A Z hZ).hom ≫
      ((nativeZeroIso A Z hZ).inv ≫ (rawMappingIso A Z hZ).hom) = _
  rw [Iso.hom_inv_id_assoc]
  rfl

/-- The universal core Hom interpretation retains the actual native-core derived-end comparison. -/
def nativeHomEquiv (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) :
    (scalarHo.obj K ⟶ scalarHo.obj ((nativeCoreFunctor A).obj Z)) ≃
      (scalarHo.obj K ⟶ scalarHo.obj (((localDerivedEnd family.{u}).obj (op A)).obj Z)) :=
  Iso.homCongr (Iso.refl _) (nativeMappingIso A Z hZ)


private def originalInput : LocalTargets.{u} ⥤ Original.{u} 1 :=
  (SimplicialPresheaf.CoreUniversalMapping.localObjectProperty family.{u}).ι

private def cssInput : LocalTargets.{u} ⥤ SimplicialSpace.OnefoldCoreComparison.CompleteTargets.{u} :=
  SimplicialSpace.completeSegalSpaces.lift
    (originalInput ⋙ oneDesignatedEquivalence.functor)
    (fun F => (one_locality_recognition F.obj).2.2.mp F.property)

private def nativeObjectNatIso :
    originalInput ⋙ ConstantEvaluation.evaluation.{u} 1 ⋙ scalarHo ≅
      originalInput ⋙ oneDesignatedEquivalence.functor ⋙
        SimplicialSpace.OnefoldCoreComparison.nativeCore ⋙ scalarHo :=
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft originalInput zeroEvaluationIso) scalarHo ≪≫
    Functor.isoWhiskerLeft cssInput SimplicialSpace.OnefoldCoreComparison.coreHoIso

private theorem nativeObjectIso_natural {F G : Original.{u} 1}
    (hF : isOriginalLocalFibrant family.{u} F) (hG : isOriginalLocalFibrant family.{u} G)
    (f : F ⟶ G) :
    scalarHo.map ((ConstantEvaluation.evaluation 1).map f) ≫ (nativeObjectIso G hG).hom =
      (nativeObjectIso F hF).hom ≫
        scalarHo.map (SimplicialSpace.OnefoldCoreComparison.nativeCore.map
          (oneDesignatedEquivalence.functor.map f)) :=
  nativeObjectNatIso.hom.naturality
    (show (⟨F, hF⟩ : LocalTargets.{u}) ⟶ ⟨G, hG⟩ from ObjectProperty.homMk f)

/-- The actual native zero/core comparison is natural on the original target maps. -/
theorem nativeZeroIso_target (A : Original.{u} 1) {Z V : Original.{u} 1}
    (hZ : isOriginalLocalFibrant family.{u} Z) (hV : isOriginalLocalFibrant family.{u} V)
    (g : Z ⟶ V) :
    scalarHo.map ((rawCoreFunctor A).map g) ≫ (nativeZeroIso A V hV).hom =
      (nativeZeroIso A Z hZ).hom ≫ scalarHo.map ((nativeCoreFunctor A).map g) :=
  nativeObjectIso_natural (object_localFibrant A Z hZ) (object_localFibrant A V hV)
    (targetMap A g)

/-- Native source contravariance retains the same original full functor map. -/
theorem nativeZeroIso_source {A B : Original.{u} 1} (f : A ⟶ B) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) :
    scalarHo.map ((ConstantEvaluation.evaluation 1).map (sourceMap f Z)) ≫
        (nativeZeroIso A Z hZ).hom =
      (nativeZeroIso B Z hZ).hom ≫
        scalarHo.map (SimplicialSpace.OnefoldCoreComparison.nativeCore.map
          (oneDesignatedEquivalence.functor.map (sourceMap f Z))) :=
  nativeObjectIso_natural (object_localFibrant B Z hZ) (object_localFibrant A Z hZ)
    (sourceMap f Z)

/-- Target naturality reads the literal all-zero component of the original full functor map. -/
theorem nativeZeroIso_target_app (A : Original.{u} 1) {Z V : Original.{u} 1}
    (hZ : isOriginalLocalFibrant family.{u} Z) (hV : isOriginalLocalFibrant family.{u} V)
    (g : Z ⟶ V) :
    scalarHo.map ((targetMap A g).app (op (ConstantEvaluation.zeroTuple 1))) ≫
        (nativeZeroIso A V hV).hom =
      (nativeZeroIso A Z hZ).hom ≫ scalarHo.map ((nativeCoreFunctor A).map g) :=
  nativeZeroIso_target A hZ hV g

/-- Source naturality reads the same literal original all-zero component. -/
theorem nativeZeroIso_source_app {A B : Original.{u} 1} (f : A ⟶ B) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) :
    scalarHo.map ((sourceMap f Z).app (op (ConstantEvaluation.zeroTuple 1))) ≫
        (nativeZeroIso A Z hZ).hom =
      (nativeZeroIso B Z hZ).hom ≫
        scalarHo.map (SimplicialSpace.OnefoldCoreComparison.nativeCore.map
          (oneDesignatedEquivalence.functor.map (sourceMap f Z))) :=
  nativeZeroIso_source f Z hZ

/-- The native-core derived-end comparison retains the actual original target and R maps. -/
theorem nativeMappingIso_target (A : Original.{u} 1) {Z V : Original.{u} 1}
    (hZ : isOriginalLocalFibrant family.{u} Z) (hV : isOriginalLocalFibrant family.{u} V)
    (g : Z ⟶ V) :
    scalarHo.map ((nativeCoreFunctor A).map g) ≫ (nativeMappingIso A V hV).hom =
      (nativeMappingIso A Z hZ).hom ≫ scalarHo.map (localDerivedPostcomp family.{u} A g) := by
  apply (cancel_epi (nativeZeroIso A Z hZ).hom).mp
  calc
    _ = scalarHo.map ((rawCoreFunctor A).map g) ≫
        scalarHo.map ((derivedComparison A).app V) := by
      rw [← Category.assoc, ← nativeZeroIso_target A hZ hV g, Category.assoc,
        nativeMappingIso_triangle A V hV]
    _ = scalarHo.map ((derivedComparison A).app Z) ≫
        scalarHo.map (localDerivedPostcomp family.{u} A g) := by
      rw [← scalarHo.map_comp, derivedComparison_target, scalarHo.map_comp]
    _ = _ := by
      rw [← nativeMappingIso_triangle A Z hZ]
      simp only [Category.assoc]

/-- The native comparison retains contravariance in the original source and its Q map. -/
theorem nativeMappingIso_source {A B : Original.{u} 1} (f : A ⟶ B) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) :
    scalarHo.map (SimplicialSpace.OnefoldCoreComparison.nativeCore.map
        (oneDesignatedEquivalence.functor.map (sourceMap f Z))) ≫
          (nativeMappingIso A Z hZ).hom =
      (nativeMappingIso B Z hZ).hom ≫ scalarHo.map (localDerivedPrecomp family.{u} f Z) := by
  apply (cancel_epi (nativeZeroIso B Z hZ).hom).mp
  calc
    _ = scalarHo.map ((ConstantEvaluation.evaluation 1).map (sourceMap f Z)) ≫
        scalarHo.map ((derivedComparison A).app Z) := by
      rw [← Category.assoc, ← nativeZeroIso_source f Z hZ, Category.assoc,
        nativeMappingIso_triangle A Z hZ]
    _ = scalarHo.map ((derivedComparison B).app Z) ≫
        scalarHo.map (localDerivedPrecomp family.{u} f Z) := by
      rw [← scalarHo.map_comp, derivedComparison_source, scalarHo.map_comp]
    _ = _ := by
      rw [← nativeMappingIso_triangle B Z hZ]
      simp only [Category.assoc]

/-- For every scalar source, the entire original functor object has this native-core universal Hom. -/
def nativeUniversalHomEquiv (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) :
    ((SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (groupoidal.obj K) ⟶
      (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (object A Z)) ≃
    (scalarHo.obj K ⟶ scalarHo.obj ((nativeCoreFunctor A).obj Z)) :=
  (SimplicialPresheaf.CoreDerivedAdjunction.homEquiv family.{u}
    (ConstantEvaluation.zeroIsTerminal 1) K (object A Z) (object_localFibrant A Z hZ)).trans
      (Iso.homCongr (Iso.refl _) (nativeZeroIso A Z hZ))

/-- The universal Hom function uses the original zero adjunct and the specified native core legs. -/
theorem nativeUniversalHomEquiv_apply (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z)
    (h : (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (groupoidal.obj K) ⟶
      (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (object A Z)) :
    nativeUniversalHomEquiv A K Z hZ h =
      SimplicialPresheaf.CoreDerivedAdjunction.homEquiv family.{u}
        (ConstantEvaluation.zeroIsTerminal 1) K (object A Z)
          (object_localFibrant A Z hZ) h ≫ (nativeZeroIso A Z hZ).hom := by
  change (𝟙 (scalarHo.obj K)) ≫ _ ≫ _ = _
  rw [Category.id_comp]

/-- The native universal function and the original Q/R universal function have the same Hom image. -/
theorem nativeUniversalHomEquiv_derived (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z)
    (h : (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (groupoidal.obj K) ⟶
      (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (object A Z)) :
    nativeUniversalHomEquiv A K Z hZ h ≫ (nativeMappingIso A Z hZ).hom = homEquiv A K Z hZ h := by
  rw [nativeUniversalHomEquiv_apply, homEquiv_apply, Category.assoc, nativeMappingIso_triangle]

/-- Every strict universal representative retains its actual baseline unit and zero evaluation. -/
theorem nativeUniversalHomEquiv_map (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) (g : groupoidal.obj K ⟶ object A Z) :
    nativeUniversalHomEquiv A K Z hZ
        ((SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).map g) =
      scalarHo.map (((BaselineConstantCoreComparison.unit.{u}
        (D := FinitePowerSite.Source 1)).app K).app (op (ConstantEvaluation.zeroTuple 1)) ≫
          g.app (op (ConstantEvaluation.zeroTuple 1))) ≫ (nativeZeroIso A Z hZ).hom := by
  rw [nativeUniversalHomEquiv_apply, SimplicialPresheaf.CoreDerivedAdjunction.homEquiv_map]

/-- The native universal function retains the same full original Cartesian transpose. -/
theorem nativeUniversalHomEquiv_currying (A : Original.{u} 1) (K : SSet.{u}) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) (f : A ⊗ groupoidal.obj K ⟶ Z) :
    nativeUniversalHomEquiv A K Z hZ
        ((SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).map (curry f)) =
      scalarHo.map (((BaselineConstantCoreComparison.unit.{u}
        (D := FinitePowerSite.Source 1)).app K).app (op (ConstantEvaluation.zeroTuple 1)) ≫
          (curry f).app (op (ConstantEvaluation.zeroTuple 1))) ≫ (nativeZeroIso A Z hZ).hom :=
  nativeUniversalHomEquiv_map A K Z hZ (curry f)

/-- Scalar source naturality uses the unchanged baseline groupoidal map. -/
theorem nativeUniversalHomEquiv_scalar (A : Original.{u} 1) {K L : SSet.{u}} (k : K ⟶ L)
    (Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z)
    (h : (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (groupoidal.obj L) ⟶
      (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (object A Z)) :
    nativeUniversalHomEquiv A K Z hZ
        ((SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).map (groupoidal.map k) ≫ h) =
      scalarHo.map k ≫ nativeUniversalHomEquiv A L Z hZ h := by
  rw [nativeUniversalHomEquiv_apply, SimplicialPresheaf.CoreDerivedAdjunction.homEquiv_source,
    nativeUniversalHomEquiv_apply, Category.assoc]

/-- The universal function is natural in the original full functor target map. -/
theorem nativeUniversalHomEquiv_target (A : Original.{u} 1) (K : SSet.{u}) {Z V : Original.{u} 1}
    (hZ : isOriginalLocalFibrant family.{u} Z) (hV : isOriginalLocalFibrant family.{u} V)
    (g : Z ⟶ V)
    (h : (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (groupoidal.obj K) ⟶
      (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (object A Z)) :
    nativeUniversalHomEquiv A K V hV
        (h ≫ (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).map (targetMap A g)) =
      nativeUniversalHomEquiv A K Z hZ h ≫ scalarHo.map ((nativeCoreFunctor A).map g) := by
  rw [nativeUniversalHomEquiv_apply, SimplicialPresheaf.CoreDerivedAdjunction.homEquiv_target
    family.{u} (ConstantEvaluation.zeroIsTerminal 1) K (object_localFibrant A Z hZ)
      (object_localFibrant A V hV) h (targetMap A g), nativeUniversalHomEquiv_apply,
    Category.assoc, nativeZeroIso_target_app A hZ hV g, ← Category.assoc]

/-- Universal source contravariance retains the same full original precomposition map. -/
theorem nativeUniversalHomEquiv_source {A B : Original.{u} 1} (f : A ⟶ B) (K : SSet.{u})
    (Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z)
    (h : (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (groupoidal.obj K) ⟶
      (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).obj (object B Z)) :
    nativeUniversalHomEquiv A K Z hZ
        (h ≫ (SimplicialPresheaf.CoreDerivedAdjunction.localHo family.{u}).map (sourceMap f Z)) =
      nativeUniversalHomEquiv B K Z hZ h ≫
        scalarHo.map (SimplicialSpace.OnefoldCoreComparison.nativeCore.map
          (oneDesignatedEquivalence.functor.map (sourceMap f Z))) := by
  rw [nativeUniversalHomEquiv_apply, SimplicialPresheaf.CoreDerivedAdjunction.homEquiv_target
    family.{u} (ConstantEvaluation.zeroIsTerminal 1) K (object_localFibrant B Z hZ)
      (object_localFibrant A Z hZ) h (sourceMap f Z), nativeUniversalHomEquiv_apply,
    Category.assoc, nativeZeroIso_source_app f Z hZ, ← Category.assoc]

end SimplicialPresheaf.OrderedJFS.OneFunctor.Core
