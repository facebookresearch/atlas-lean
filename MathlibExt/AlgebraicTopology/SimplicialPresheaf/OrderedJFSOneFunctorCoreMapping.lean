/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneFunctorScalarZero
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSConstantEvaluation
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.CoreUniversalMapping
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.CoreDerivedAdjunction

/-!
# The original one-fold functor core and its actual derived scalar end

The literal zero core of the transported functor object has two specified
forward maps: its original local replacement unit, and its scalar-end
comparison followed by the original source and target replacement maps.
Both are weak for a genuinely original-local-fibrant target. Their localized
comparison retains these same maps and the original Q/R choices.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
  HomotopicalAlgebra Opposite NatIso
open scoped Simplicial SSet.modelCategoryQuillen
open SimplicialPresheaf.InjectiveKan SimplicialPresheaf.OriginalLocalDerived

namespace SimplicialPresheaf.OrderedJFS.OneFunctor.Core

private local instance sourceLocallySmall : LocallySmall.{u} (FinitePowerSite.Source 1) :=
  @CategoryTheory.locallySmall_of_univLE _ _ UnivLE.zero

/-- The actual normalized original one-fold family, with its unchanged factor choices. -/
abbrev family := originalFamily.{u} 1

/-- The actual scalar Kan–Quillen localization. -/
abbrev scalarHo := SimplicialPresheaf.CoreDerivedAdjunction.scalarHo.{u}

/-- The ordinary all-zero evaluation and the designated Rezk zero row have the same values. -/
def zeroEvaluationIso : ConstantEvaluation.evaluation.{u} 1 ≅ OneFunctor.zero :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro A B f; rfl)

/-- The literal original zero core of the whole functor object. -/
abbrev rawCoreFunctor (A : Original.{u} 1) : Original.{u} 1 ⥤ SSet.{u} :=
  objectFunctor A ⋙ ConstantEvaluation.evaluation 1

/-- The checked new scalar-zero comparison, on the same original zero core. -/
def rawEndNatIso (A : Original.{u} 1) :
    rawCoreFunctor A ≅ innerHomFunctor.{u}.obj (op A) :=
  Functor.isoWhiskerLeft (objectFunctor A) zeroEvaluationIso ≪≫ zeroScalarNatIso A

/-- The actual chosen core uses the original local R and the original zero tuple. -/
abbrev coreFunctor (A : Original.{u} 1) : Original.{u} 1 ⥤ SSet.{u} :=
  objectFunctor A ⋙ TransferredCoreReplacements.rReplacement family.{u}
    (ConstantEvaluation.zeroTuple 1)

/-- The original evaluated replacement unit is the raw-to-replaced core map. -/
def coreUnit (A : Original.{u} 1) : rawCoreFunctor A ⟶ coreFunctor A :=
  Functor.whiskerLeft (objectFunctor A)
    (TransferredCoreReplacements.rUnit family.{u} (ConstantEvaluation.zeroTuple 1))

/-- Original target fibrancy makes the evaluated unit weak. -/
theorem coreUnit_weak (A Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z) :
    SSet.realizationWeakEquivalences ((coreUnit A).app Z) :=
  (TransferredCoreReplacements.rUnit_trivialCofibration family.{u}
    (ConstantEvaluation.zeroTuple 1) (object A Z) (object_localFibrant A Z hZ)).2

/-- The chosen core is Kan through the actual original R's global fibrancy. -/
theorem core_isKan (A Z : Original.{u} 1) : SSet.KanComplex ((coreFunctor A).obj Z) :=
  TransferredCoreReplacements.rReplacement_isKan family.{u}
    (ConstantEvaluation.zeroIsTerminal 1) (object A Z)

private def rawToR : innerHomFunctor.{u} (D := FinitePowerSite.Source 1) ⟶ rawAfterR.{u} family.{u} where
  app A :=
    { app Z := innerHomPost A.unop ((localRUnit family.{u}).app Z)
      naturality Z V g := by
        change (innerHomFunctor.{u}.obj A).map g ≫
            (innerHomFunctor.{u}.obj A).map ((localRUnit family.{u}).app V) =
          (innerHomFunctor.{u}.obj A).map ((localRUnit family.{u}).app Z) ≫
            (innerHomFunctor.{u}.obj A).map ((localR family.{u}).map g)
        rw [← (innerHomFunctor.{u}.obj A).map_comp, ← (innerHomFunctor.{u}.obj A).map_comp]
        apply congrArg (innerHomFunctor.{u}.obj A).map
        simpa only [Functor.id_map] using (localRUnit family.{u}).naturality g }
  naturality A B f := by
    apply NatTrans.ext
    funext Z
    exact ((innerHomFunctor.{u}.map f).naturality ((localRUnit family.{u}).app Z)).symm

/-- The native raw end uses the same target R-unit and source Q-counit. -/
def rawToDerived : innerHomFunctor.{u} (D := FinitePowerSite.Source 1) ⟶ localDerivedEnd family.{u} :=
  rawToR ≫ localEndSpan family.{u}

/-- Both actual replacement legs occur in their original order. -/
theorem rawToDerived_app (A Z : Original.{u} 1) :
    (rawToDerived.app (op A)).app Z =
      innerHomPost A ((localRUnit family.{u}).app Z) ≫
        innerHomPre ((localQCounit family.{u}).app A) ((localR family.{u}).obj Z) := rfl

/-- Raw-to-derived weakness uses actual local Whitehead and baseline mapping invariance. -/
theorem rawToDerived_weak (A Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z) :
    SSet.realizationWeakEquivalences ((rawToDerived.app (op A)).app Z) := by
  have hR := localR_isOriginalLocalFibrant family.{u} Z
  have hr := localRUnit_localTrivialCofibration family.{u} Z
  have hbase := (originalLocalEquivalence_iff_weakEquivalence_of_localFibrant family.{u}
    ((localRUnit family.{u}).app Z) hZ hR).mp hr.2
  have hpost := (rawMappingInvariance.{u} (FinitePowerSite.Source 1)).2.2.2.2.2.2
    A ((localRUnit family.{u}).app Z) hbase hZ.1 hR.1
  have hpre := (localEndSpans_weak family.{u} A Z).1
  exact SSet.realizationWeakEquivalences.comp_mem _ _ hpost hpre

/-- The actual functor core maps to the actual Q/R-derived scalar mapping model. -/
def derivedComparison (A : Original.{u} 1) :
    rawCoreFunctor A ⟶ (localDerivedEnd family.{u}).obj (op A) :=
  (rawEndNatIso A).hom ≫ rawToDerived.app (op A)

/-- The second forward leg of the core/derived-end span is weak. -/
theorem derivedComparison_weak (A Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z) :
    SSet.realizationWeakEquivalences ((derivedComparison A).app Z) :=
  SSet.realizationWeakEquivalences.comp_mem _ _
    (SSet.realizationWeakEquivalences.of_isIso ((rawEndNatIso A).hom.app Z))
    (rawToDerived_weak A Z hZ)

/-- The derived scalar end retains the same actual Q/R data and is Kan. -/
theorem derivedEnd_isKan (A Z : Original.{u} 1) :
    SSet.KanComplex (((localDerivedEnd family.{u}).obj (op A)).obj Z) :=
  localDerivedEnd_isKan family.{u} A Z

/-- The category of genuine original-local-fibrant targets. -/
abbrev LocalTargets := SimplicialPresheaf.CoreUniversalMapping.LocalTargets family.{u}

private def input : LocalTargets.{u} ⥤ Original.{u} 1 :=
  (SimplicialPresheaf.CoreUniversalMapping.localObjectProperty family.{u}).ι

private def localizedUnit (A : Original.{u} 1) :
    input ⋙ rawCoreFunctor A ⋙ scalarHo ⟶ input ⋙ coreFunctor A ⋙ scalarHo :=
  Functor.whiskerLeft input (Functor.whiskerRight (coreUnit A) scalarHo)

private def localizedComparison (A : Original.{u} 1) :
    input ⋙ rawCoreFunctor A ⋙ scalarHo ⟶
      input ⋙ (localDerivedEnd family.{u}).obj (op A) ⋙ scalarHo :=
  Functor.whiskerLeft input (Functor.whiskerRight (derivedComparison A) scalarHo)

private theorem localizedUnit_isIso (A : Original.{u} 1) : IsIso (localizedUnit A) := by
  let _ : ∀ Z, IsIso ((localizedUnit A).app Z) := fun Z => by
    change IsIso (scalarHo.map ((coreUnit A).app Z.obj))
    exact Localization.inverts scalarHo SSet.realizationWeakEquivalences _
      (coreUnit_weak A Z.obj Z.property)
  exact NatIso.isIso_of_isIso_app _

private theorem localizedComparison_isIso (A : Original.{u} 1) :
    IsIso (localizedComparison A) := by
  let _ : ∀ Z, IsIso ((localizedComparison A).app Z) := fun Z => by
    change IsIso (scalarHo.map ((derivedComparison A).app Z.obj))
    exact Localization.inverts scalarHo SSet.realizationWeakEquivalences _
      (derivedComparison_weak A Z.obj Z.property)
  exact NatIso.isIso_of_isIso_app _

/-- Localize precisely the two actual weak legs of the one-fold functor-core span. -/
def mappingNatIso (A : Original.{u} 1) :
    input ⋙ coreFunctor A ⋙ scalarHo ≅
      input ⋙ (localDerivedEnd family.{u}).obj (op A) ⋙ scalarHo := by
  let _ := localizedUnit_isIso A
  let _ := localizedComparison_isIso A
  exact (asIso (localizedUnit A)).symm ≪≫ asIso (localizedComparison A)

/-- The localized comparison keeps the raw core's exact forward triangle. -/
theorem mappingNatIso_triangle (A : Original.{u} 1) :
    localizedUnit A ≫ (mappingNatIso A).hom = localizedComparison A := by
  let _ := localizedUnit_isIso A
  change localizedUnit A ≫ (inv (localizedUnit A) ≫ localizedComparison A) = _
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

/-- The computed original functor core represents the original derived scalar mapping object. -/
def mappingIso (A Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z) :
    scalarHo.obj ((coreFunctor A).obj Z) ≅
      scalarHo.obj (((localDerivedEnd family.{u}).obj (op A)).obj Z) :=
  (mappingNatIso A).app ⟨Z, hZ⟩

/-- Its triangle retains the two original strict forward maps. -/
theorem mappingIso_triangle (A Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z) :
    scalarHo.map ((coreUnit A).app Z) ≫ (mappingIso A Z hZ).hom =
      scalarHo.map ((derivedComparison A).app Z) :=
  congrArg (fun t => t.app ⟨Z, hZ⟩) (mappingNatIso_triangle A)


/-- The literal core/end comparison keeps the original contravariant source action. -/
theorem rawEndNatIso_source {A B : Original.{u} 1} (f : A ⟶ B) (Z : Original.{u} 1) :
    (ConstantEvaluation.evaluation 1).map (sourceMap f Z) ≫ (rawEndNatIso A).hom.app Z =
      (rawEndNatIso B).hom.app Z ≫ (innerHomFunctor.{u}.map f.op).app Z := by
  change (ConstantEvaluation.evaluation 1).map (sourceMap f Z) ≫
      zeroEvaluationIso.hom.app (object A Z) ≫ (zeroScalarIso A Z).hom =
    (zeroEvaluationIso.hom.app (object B Z) ≫ (zeroScalarIso B Z).hom) ≫ innerHomPre f Z
  rw [← Category.assoc, zeroEvaluationIso.hom.naturality, Category.assoc, zeroScalarIso_source]
  simp only [Category.assoc]

/-- The raw-to-derived end comparison retains the actual Q source map. -/
theorem rawToDerived_source {A B : Original.{u} 1} (f : A ⟶ B) (Z : Original.{u} 1) :
    (innerHomFunctor.{u}.map f.op).app Z ≫ (rawToDerived.app (op A)).app Z =
      (rawToDerived.app (op B)).app Z ≫ localDerivedPrecomp family.{u} f Z :=
  NatTrans.congr_app (rawToDerived.naturality f.op) Z

/-- The functor-core comparison has the same original contravariant map and derived Q action. -/
theorem derivedComparison_source {A B : Original.{u} 1} (f : A ⟶ B)
    (Z : Original.{u} 1) :
    (ConstantEvaluation.evaluation 1).map (sourceMap f Z) ≫ (derivedComparison A).app Z =
      (derivedComparison B).app Z ≫ localDerivedPrecomp family.{u} f Z := by
  change (ConstantEvaluation.evaluation 1).map (sourceMap f Z) ≫
      ((rawEndNatIso A).hom.app Z ≫ (rawToDerived.app (op A)).app Z) =
    ((rawEndNatIso B).hom.app Z ≫ (rawToDerived.app (op B)).app Z) ≫
      localDerivedPrecomp family.{u} f Z
  rw [← Category.assoc, rawEndNatIso_source, Category.assoc, rawToDerived_source]
  simp only [Category.assoc]

/-- Evaluation and the original R-unit retain the same source-map square. -/
theorem coreUnit_source {A B : Original.{u} 1} (f : A ⟶ B) (Z : Original.{u} 1) :
    (ConstantEvaluation.evaluation 1).map (sourceMap f Z) ≫ (coreUnit A).app Z =
      (coreUnit B).app Z ≫
        (TransferredCoreReplacements.rReplacement family.{u}
          (ConstantEvaluation.zeroTuple 1)).map (sourceMap f Z) :=
  (TransferredCoreReplacements.rUnit family.{u}
    (ConstantEvaluation.zeroTuple 1)).naturality (sourceMap f Z)

/-- The two actual forward maps commute with every original target map. -/
theorem derivedComparison_target (A : Original.{u} 1) {Z V : Original.{u} 1} (g : Z ⟶ V) :
    (rawCoreFunctor A).map g ≫ (derivedComparison A).app V =
      (derivedComparison A).app Z ≫ localDerivedPostcomp family.{u} A g :=
  (derivedComparison A).naturality g

/-- Target naturality reads the same original zero component of the full functor map. -/
theorem derivedComparison_target_app (A : Original.{u} 1) {Z V : Original.{u} 1} (g : Z ⟶ V) :
    (targetMap A g).app (op (ConstantEvaluation.zeroTuple 1)) ≫ (derivedComparison A).app V =
      (derivedComparison A).app Z ≫ localDerivedPostcomp family.{u} A g :=
  derivedComparison_target A g

/-- Source naturality reads the same original zero component of the full contravariant map. -/
theorem derivedComparison_source_app {A B : Original.{u} 1} (f : A ⟶ B)
    (Z : Original.{u} 1) :
    (sourceMap f Z).app (op (ConstantEvaluation.zeroTuple 1)) ≫ (derivedComparison A).app Z =
      (derivedComparison B).app Z ≫ localDerivedPrecomp family.{u} f Z :=
  derivedComparison_source f Z

/-- On a fibrant target, the actual forward core/end leg is invertible after scalar localization. -/
def rawMappingIso (A Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z) :
    scalarHo.obj ((rawCoreFunctor A).obj Z) ≅
      scalarHo.obj (((localDerivedEnd family.{u}).obj (op A)).obj Z) := by
  let _ : IsIso (scalarHo.map ((derivedComparison A).app Z)) :=
    Localization.inverts scalarHo SSet.realizationWeakEquivalences _
      (derivedComparison_weak A Z hZ)
  exact asIso (scalarHo.map ((derivedComparison A).app Z))

/-- The localized comparison is natural in the original target. -/
theorem mappingIso_target (A : Original.{u} 1) {Z V : Original.{u} 1}
    (hZ : isOriginalLocalFibrant family.{u} Z) (hV : isOriginalLocalFibrant family.{u} V)
    (g : Z ⟶ V) :
    scalarHo.map ((coreFunctor A).map g) ≫ (mappingIso A V hV).hom =
      (mappingIso A Z hZ).hom ≫ scalarHo.map (localDerivedPostcomp family.{u} A g) :=
  (mappingNatIso A).hom.naturality
    (show (⟨Z, hZ⟩ : LocalTargets.{u}) ⟶ ⟨V, hV⟩ from ObjectProperty.homMk g)

/-- The localized comparison retains contravariance in every original source. -/
theorem mappingIso_source {A B : Original.{u} 1} (f : A ⟶ B) (Z : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) :
    scalarHo.map ((TransferredCoreReplacements.rReplacement family.{u}
      (ConstantEvaluation.zeroTuple 1)).map (sourceMap f Z)) ≫ (mappingIso A Z hZ).hom =
      (mappingIso B Z hZ).hom ≫ scalarHo.map (localDerivedPrecomp family.{u} f Z) := by
  let _ : IsIso (scalarHo.map ((coreUnit B).app Z)) :=
    Localization.inverts scalarHo SSet.realizationWeakEquivalences _ (coreUnit_weak B Z hZ)
  apply (cancel_epi (scalarHo.map ((coreUnit B).app Z))).mp
  calc
    _ = scalarHo.map ((ConstantEvaluation.evaluation 1).map (sourceMap f Z)) ≫
        scalarHo.map ((coreUnit A).app Z) ≫ (mappingIso A Z hZ).hom := by
      rw [← Category.assoc, ← scalarHo.map_comp, ← coreUnit_source,
        scalarHo.map_comp, Category.assoc]
    _ = scalarHo.map ((ConstantEvaluation.evaluation 1).map (sourceMap f Z)) ≫
        scalarHo.map ((derivedComparison A).app Z) := by rw [mappingIso_triangle A Z hZ]
    _ = scalarHo.map ((derivedComparison B).app Z) ≫
        scalarHo.map (localDerivedPrecomp family.{u} f Z) := by
      rw [← scalarHo.map_comp, derivedComparison_source, scalarHo.map_comp]
    _ = _ := by rw [← mappingIso_triangle B Z hZ]; simp only [Category.assoc]

end SimplicialPresheaf.OrderedJFS.OneFunctor.Core
