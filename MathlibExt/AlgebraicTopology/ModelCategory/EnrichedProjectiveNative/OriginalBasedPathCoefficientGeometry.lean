/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.OriginalBasedPathGeometry
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOriginalFiberComparisonBoundary

/-!
# Original fiber and cofiber geometry on enriched native diagrams

The index is an arbitrary category enriched over the actual pointed CGWH
coefficient category. Every construction uses the original native I replacement,
I cone and I suspension, at the caller's realized-generator bottom. The published
coefficient disk maximum is reused with its actual selected time-one point.
No stable model or Omega hypothesis is part of this geometry.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.DiskMaximumGeometry
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.OriginalFiberCofiberGeometry

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

variable {J : Type} [EnrichedCategory PointedCGWH.{u, v} J]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] Native.modelCategory Native.allObjectsFibrant
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

private abbrev Carrier := EnrichedFunctorCat PointedCGWH.{u, v} J
private abbrev H := toHomotopyCategory (Carrier (J := J))
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := J)
private abbrev S := OriginalISuspension.suspension (B := B) (I := J)

variable (a : ∀ F : Arrow (Carrier (J := J)),
  PullbackCone F.hom (Diagrams.zeroTo F.right)) (ha : ∀ F, IsLimit (a F))

private abbrev P := OrdinaryHoChosenFiberMaps.fibrantFibrationProperty (C := Carrier (J := J))

/-- The entire original two-projection fiber functor on every native level fibration. -/
abbrev fiberFunctor : Eligible (J := J) ⥤ Carrier (J := J) :=
  P.ι ⋙ Diagrams.FiberGeometry.chosenFiberFunctor a ha

/-- The original suspended comparison uses the same full native Q-cofiber map. -/
abbrev suspendedComparison (F : Eligible (J := J)) :
    H.obj (S.obj (Q.obj (a F.obj).pt)) ⟶
      H.obj ((CofiberNullity.cofiberQ (B := B) (I := J)).obj F.obj) :=
  (OriginalFiberComparison.nativeFibrationComparison (B := B) a ha).app F

/-- The same full native comparison is natural on every original level-fibration arrow. -/
theorem suspendedComparison_naturality {F G : Eligible (J := J)} (m : F ⟶ G) :
    H.map (S.map (Q.map (Diagrams.FiberGeometry.chosenFiberMap m.hom
      (a F.obj) (a G.obj) (ha G.obj)))) ≫ suspendedComparison a ha G =
      suspendedComparison a ha F ≫ H.map ((CofiberNullity.cofiberQ (B := B)).map m.hom) :=
  (OriginalFiberComparison.nativeFibrationComparison (B := B) a ha).naturality m

/-- The original Q boundary is the original Q suspension of the complete fiber projection. -/
theorem suspendedComparison_boundary (F : Eligible (J := J)) :
    suspendedComparison a ha F ≫ H.map (OriginalFiberComparison.originalQCofiberBoundary
      (B := B) F.obj) = H.map (S.map (Q.map (a F.obj).fst)) := by
  change (OriginalFiberComparison.nativeFibrationComparison (B := B) a ha).app F ≫ _ = _
  rw [OriginalFiberComparison.nativeFibrationComparison_app]
  exact OriginalFiberComparison.originalFibrationComparison_boundary (B := B) a ha F


namespace NativeBasedPathGeometry

open CategoryTheory.EnrichedFunctorCat MonoidalCategory
open scoped MonoidalClosed
private abbrev disk := PointedCGWH.diskOne.{u, v}
private abbrev L := EnrichedFunctorCat.tensorLeft (A := J) disk.{u, v}
private abbrev adj := ScalarLeibniz.adjunction (A := J) disk.{u, v}

namespace PathCoefficientGeometry

open LoopFiberUniversalProperty

private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := J)

/-- The actual disk boundary of a cofibrant source is a native projective cofibration. -/
theorem scalarBoundary_cofibration (A : (Carrier (J := J))) [IsCofibrant A] :
    Cofibration (scalarBoundary A) := by
  let u : A ⟶ tensorLeftObject (𝟙_ PointedCGWH.{u, v}) A := (scalarUnitIso A).inv
  let d : tensorLeftObject (𝟙_ PointedCGWH.{u, v}) A ⟶
      tensorLeftObject PointedCGWH.diskOne A := scalarTensorMap diskFreeEndpoint A
  have hu : cofibrations (Carrier (J := J)) u := (cofibration_iff _).mp inferInstance
  have hd : cofibrations (Carrier (J := J)) d :=
    PointedCGWH.EnrichedIntervalCylinderModel.scalarTensorMap_cofibration
      diskFreeEndpoint A ((cofibration_iff _).mp diskFreeEndpoint_cofibration)
  exact (cofibration_iff _).mpr ((cofibrations (Carrier (J := J))).comp_mem u d hu hd)


/-- Both actual Q-path endpoint components give the original counit Arrow over the identity base. -/
def basedPathCounitArrow (Y : (Carrier (J := J))) :
    basedPathArrowFunctor.obj Y ⟶ basedPathUnresolvedArrowFunctor.obj Y :=
  Arrow.homMk (ε.app (basedPath.obj Y)) (𝟙 Y)
    ((basedPathQEndpoint_app Y).symm.trans (Category.comp_id _).symm)

/-- The entire original Q counit is natural on both path Arrow components. -/
def basedPathCounitNatTrans : basedPathArrowFunctor (J := J) ⟶
    basedPathUnresolvedArrowFunctor (J := J) where
  app Y := basedPathCounitArrow Y
  naturality X Y f := by
    apply Arrow.hom_ext
    · exact ε.naturality (basedPath.map f)
    · exact (Category.comp_id f).trans (Category.id_comp f).symm

/-- The original two-projection map transports the caller's actual Q-path fiber. -/
def basedPathFiberCounit (Y : (Carrier (J := J))) :
    (a (basedPathArrowFunctor.obj Y)).pt ⟶
      (a (basedPathUnresolvedArrowFunctor.obj Y)).pt :=
  Diagrams.FiberGeometry.chosenFiberMap (basedPathCounitArrow Y)
    (a (basedPathArrowFunctor.obj Y)) (a (basedPathUnresolvedArrowFunctor.obj Y))
    (ha (basedPathUnresolvedArrowFunctor.obj Y))

/-- The complete first projection retains the actual original Q-path counit. -/
theorem basedPathFiberCounit_fst (Y : (Carrier (J := J))) :
    basedPathFiberCounit a ha Y ≫ (a (basedPathUnresolvedArrowFunctor.obj Y)).fst =
      (a (basedPathArrowFunctor.obj Y)).fst ≫ ε.app (basedPath.obj Y) :=
  Diagrams.FiberGeometry.chosenFiberMap_fst _ _ _ _

/-- The full chosen zero projection is unchanged under the actual weak Arrow. -/
theorem basedPathFiberCounit_snd (Y : (Carrier (J := J))) :
    basedPathFiberCounit a ha Y ≫ (a (basedPathUnresolvedArrowFunctor.obj Y)).snd =
      (a (basedPathArrowFunctor.obj Y)).snd :=
  Diagrams.FiberGeometry.chosenFiberMap_snd _ _ _ _

/-- The whole caller-chosen fiber counit is induced by the actual full natural Arrow counit. -/
def basedPathFiberCounitNatTrans :
    basedPathArrowFunctor ⋙ Diagrams.FiberGeometry.chosenFiberFunctor a ha ⟶
      basedPathUnresolvedArrowFunctor ⋙ Diagrams.FiberGeometry.chosenFiberFunctor a ha :=
  Functor.whiskerRight basedPathCounitNatTrans
    (Diagrams.FiberGeometry.chosenFiberFunctor a ha)

/-- Actual native fibration fibers preserve the weakness of both original counit Arrow endpoints. -/
theorem basedPathFiberCounit_weak (Y : (Carrier (J := J))) :
    weakEquivalences (Carrier (J := J)) (basedPathFiberCounit a ha Y) := by
  let _ : MorphismProperty.HasFunctorialFactorization
      (trivialCofibrations (Carrier (J := J))) (fibrations (Carrier (J := J))) :=
    (HomotopicalAlgebra.EnrichedProjective.Native.functorialFactorizations
      (B := B) (A := J)).2
  let _ : Fibration (basedPathArrowFunctor.obj Y).hom := basedPathQEndpoint_fibration Y
  let _ : Fibration (basedPathUnresolvedArrowFunctor.obj Y).hom :=
    basedPathEndpoint_fibration Y
  let _ : WeakEquivalence (basedPathCounitArrow Y).left :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (basedPath.obj Y))
  let _ : WeakEquivalence (basedPathCounitArrow Y).right := by
    change WeakEquivalence (𝟙 Y)
    infer_instance
  rw [basedPathFiberCounit, OriginalFiberComparison.chosenFiberMap_eq_generic a ha]
  exact OrdinaryHoChosenFiberCofiberComparison.originalChosenMap_weak
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero a ha (basedPathCounitArrow Y)

/-- The coefficient source is the actual original cofibrant replacement of the native loop. -/
abbrev qLoopSource (Y : (Carrier (J := J))) : (Carrier (J := J)) :=
  Q.obj (scalarLoop.obj Y)

/-- The actual loop inclusion is lifted through the unchanged original Q-path trivial fibration. -/
theorem qLoopPathLiftSquare (Y : (Carrier (J := J))) :
    CommSq (Diagrams.zeroTo (basedPathQ.obj Y)) (Diagrams.zeroTo (qLoopSource Y))
      (ε.app (basedPath.obj Y))
      (ε.app (scalarLoop.obj Y) ≫ loopInclusion Y) :=
  ⟨Diagrams.zeroDiagramIsInitial.hom_ext _ _⟩

private instance qLoopPathLiftSquare_hasLift (Y : (Carrier (J := J))) :
    (qLoopPathLiftSquare Y).HasLift := by
  let hA : IsCofibrant (qLoopSource Y) :=
    Replacement.isCofibrant_cofibrantReplacement (B := B) (A := J)
      (scalarLoop.obj Y)
  have hi : cofibrations (Carrier (J := J)) (Diagrams.zeroTo (qLoopSource Y)) :=
    (HomotopicalAlgebra.cofibration_iff _).mp
      ((isCofibrant_iff_of_isInitial _ Diagrams.zeroDiagramIsInitial).mp hA)
  have hp : trivialFibrations (Carrier (J := J)) (ε.app (basedPath.obj Y)) :=
    Replacement.cofibrantReplacementCounit_mem_trivialFibrations
      (B := B) (A := J) (basedPath.obj Y)
  exact (MorphismProperty.hasLiftingProperty_of_wfs
    (Diagrams.zeroTo (qLoopSource Y)) (ε.app (basedPath.obj Y)) hi hp).sq_hasLift _

/-- This is the genuine CM4 lift of the actual original Q-loop inclusion. -/
def qLoopPathLift (Y : (Carrier (J := J))) : qLoopSource Y ⟶ basedPathQ.obj Y :=
  (qLoopPathLiftSquare Y).lift

/-- Its original counit projection is the entire same sphere-quotient loop map. -/
theorem qLoopPathLift_counit (Y : (Carrier (J := J))) :
    qLoopPathLift Y ≫ ε.app (basedPath.obj Y) =
      ε.app (scalarLoop.obj Y) ≫ loopInclusion Y :=
  (qLoopPathLiftSquare Y).fac_right

/-- The whole lifted coefficient lies over the original zero endpoint. -/
theorem qLoopPathLift_endpoint (Y : (Carrier (J := J))) :
    qLoopPathLift Y ≫ basedPathQEndpoint.app Y =
      Diagrams.toZero (qLoopSource Y) ≫ Diagrams.zeroTo Y := by
  rw [basedPathQEndpoint_app, ← Category.assoc, qLoopPathLift_counit,
    Category.assoc, loopInclusion_endpoint, ← Category.assoc]
  exact congrArg (· ≫ Diagrams.zeroTo Y) (Diagrams.zeroDiagramIsTerminal.hom_ext _ _)

/-- Both actual cone legs construct a coefficient in every caller-chosen Q-path fiber. -/
def qLoopPathFiberMap (Y : (Carrier (J := J))) :
    qLoopSource Y ⟶ (a (basedPathArrowFunctor.obj Y)).pt :=
  (ha (basedPathArrowFunctor.obj Y)).lift
    (PullbackCone.mk (qLoopPathLift Y) (Diagrams.toZero (qLoopSource Y))
      (qLoopPathLift_endpoint Y))

/-- Its first projection is the complete actual Q-path lift. -/
theorem qLoopPathFiberMap_fst (Y : (Carrier (J := J))) :
    qLoopPathFiberMap a ha Y ≫ (a (basedPathArrowFunctor.obj Y)).fst = qLoopPathLift Y :=
  (ha (basedPathArrowFunctor.obj Y)).fac _ WalkingCospan.left

/-- Its second projection is the original coefficient zero map. -/
theorem qLoopPathFiberMap_snd (Y : (Carrier (J := J))) :
    qLoopPathFiberMap a ha Y ≫ (a (basedPathArrowFunctor.obj Y)).snd =
      Diagrams.toZero (qLoopSource Y) :=
  (ha (basedPathArrowFunctor.obj Y)).fac _ WalkingCospan.right

/--
The actual weak fiber counit recovers the same Q-loop counit through the strict loop limit Iso.
-/
theorem qLoopPathFiberMap_counit (Y : (Carrier (J := J))) :
    qLoopPathFiberMap a ha Y ≫ basedPathFiberCounit a ha Y =
      ε.app (scalarLoop.obj Y) ≫ (chosenLoopFiberIso a ha Y).hom := by
  apply PullbackCone.IsLimit.hom_ext (ha (basedPathUnresolvedArrowFunctor.obj Y))
  · let p : (a (basedPathArrowFunctor.obj Y)).pt ⟶ basedPathQ.obj Y :=
      (a (basedPathArrowFunctor.obj Y)).fst
    let e : basedPathQ.obj Y ⟶ basedPath.obj Y := ε.app (basedPath.obj Y)
    let c : scalarLoop.obj Y ⟶ (a (basedPathUnresolvedArrowFunctor.obj Y)).pt :=
      (chosenLoopFiberIso a ha Y).hom
    let z : qLoopSource Y ⟶ scalarLoop.obj Y := ε.app (scalarLoop.obj Y)
    let i : scalarLoop.obj Y ⟶ basedPath.obj Y := loopInclusion Y
    let q : qLoopSource Y ⟶ (a (basedPathArrowFunctor.obj Y)).pt := qLoopPathFiberMap a ha Y
    let b : (a (basedPathArrowFunctor.obj Y)).pt ⟶ (a (basedPathUnresolvedArrowFunctor.obj Y)).pt :=
      basedPathFiberCounit a ha Y
    let p' : (a (basedPathUnresolvedArrowFunctor.obj Y)).pt ⟶ basedPath.obj Y :=
      (a (basedPathUnresolvedArrowFunctor.obj Y)).fst
    let l : qLoopSource Y ⟶ basedPathQ.obj Y := qLoopPathLift Y
    have h₁ : b ≫ p' = p ≫ e := basedPathFiberCounit_fst a ha Y
    have h₂ : q ≫ p = l := qLoopPathFiberMap_fst a ha Y
    have h₃ : c ≫ p' = i := chosenLoopFiberIso_hom_fst a ha Y
    have h₄ : l ≫ e = z ≫ i := qLoopPathLift_counit Y
    exact (Category.assoc q b p').trans
      ((congrArg (q ≫ ·) h₁).trans
        ((Category.assoc q p e).symm.trans
          ((congrArg (· ≫ e) h₂).trans
            (h₄.trans ((congrArg (z ≫ ·) h₃).symm.trans (Category.assoc z c p').symm)))))
  · exact Diagrams.zeroDiagramIsTerminal.hom_ext _ _


/-- The coefficient is weak by the actual strict loop limit and original weak chosen-fiber maps. -/
theorem qLoopPathFiberMap_weak (Y : (Carrier (J := J))) :
    weakEquivalences (Carrier (J := J)) (qLoopPathFiberMap a ha Y) := by
  apply (weakEquivalences (Carrier (J := J))).of_postcomp _ _
    (basedPathFiberCounit_weak a ha Y)
  rw [qLoopPathFiberMap_counit]
  exact (weakEquivalences (Carrier (J := J))).comp_mem _ _
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences
      (scalarLoop.obj Y))
    (mem_weakEquivalences (chosenLoopFiberIso a ha Y).hom)

/-- Restrict the true native disk-maximum contraction along the actual Q-loop inclusion. -/
def qLoopDiskPath (Y : (Carrier (J := J))) : L.obj (qLoopSource Y) ⟶ basedPath.obj Y :=
  L.map (ε.app (scalarLoop.obj Y) ≫ loopInclusion Y) ≫
    basedPathContraction Y

/-- Its full native time-zero source is the original Q-loop inclusion word. -/
theorem qLoopDiskPath_source (Y : (Carrier (J := J))) :
    scalarBoundary (qLoopSource Y) ≫ qLoopDiskPath Y =
      ε.app (scalarLoop.obj Y) ≫ loopInclusion Y := by
  rw [qLoopDiskPath, ← Category.assoc, ← scalarBoundary_naturality,
    Category.assoc, basedPathContraction_source, Category.comp_id]

/-- Its original endpoint is the actual sphere quotient followed by the entire scalar Q counit. -/
theorem qLoopDiskPath_endpoint (Y : (Carrier (J := J))) :
    qLoopDiskPath Y ≫ basedPathEndpoint.app Y =
      scalarTensorMap ScalarSphereSuspension.quotient (qLoopSource Y) ≫
        (scalarSuspension.map (ε.app (scalarLoop.obj Y)) ≫
          scalarCounit.app Y) := by
  rw [qLoopDiskPath, Category.assoc, basedPathContraction_endpoint]
  have hD : ScalarLeibniz.unadjunct disk (qLoopSource Y) Y
      (ε.app (scalarLoop.obj Y) ≫ loopInclusion Y) =
    L.map (ε.app (scalarLoop.obj Y) ≫ loopInclusion Y) ≫ adj.counit.app Y := by
    change ScalarLeibniz.unadjunct (A := J) disk (qLoopSource Y) Y
      (ε.app (scalarLoop.obj Y) ≫ loopInclusion Y) =
      ((ScalarLeibniz.adjunction (A := J) disk).homEquiv _ _).symm
        (ε.app (scalarLoop.obj Y) ≫ loopInclusion Y)
    rw [ScalarLeibniz.adjunction, Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  have hS : ScalarLeibniz.unadjunct PointedCGWH.sphereOne (qLoopSource Y) Y
      (ε.app (scalarLoop.obj Y)) =
    scalarSuspension.map (ε.app (scalarLoop.obj Y)) ≫
      scalarCounit.app Y := by
    change ScalarLeibniz.unadjunct (A := J) PointedCGWH.sphereOne (qLoopSource Y) Y
      (ε.app (scalarLoop.obj Y)) =
      ((ScalarLeibniz.adjunction (A := J) PointedCGWH.sphereOne).homEquiv _ _).symm
        (ε.app (scalarLoop.obj Y))
    rw [ScalarLeibniz.adjunction, Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  exact hD.symm.trans ((loop_unadjunct (ε.app (scalarLoop.obj Y))).trans
    (congrArg (scalarTensorMap ScalarSphereSuspension.quotient (qLoopSource Y) ≫ ·) hS))

/-- The actual disk contraction and loop lift form the original relative CM4 square. -/
theorem qLoopDiskLiftSquare (Y : (Carrier (J := J))) :
    CommSq (qLoopPathLift Y) (scalarBoundary (qLoopSource Y))
      (ε.app (basedPath.obj Y)) (qLoopDiskPath Y) :=
  ⟨(qLoopPathLift_counit Y).trans (qLoopDiskPath_source Y).symm⟩

private instance qLoopDiskLiftSquare_hasLift (Y : (Carrier (J := J))) :
    (qLoopDiskLiftSquare Y).HasLift := by
  let _ : IsCofibrant (qLoopSource Y) :=
    Replacement.isCofibrant_cofibrantReplacement (B := B) (A := J)
      (scalarLoop.obj Y)
  have hi : cofibrations (Carrier (J := J)) (scalarBoundary (qLoopSource Y)) :=
    (HomotopicalAlgebra.cofibration_iff _).mp (scalarBoundary_cofibration _)
  have hp : trivialFibrations (Carrier (J := J)) (ε.app (basedPath.obj Y)) :=
    Replacement.cofibrantReplacementCounit_mem_trivialFibrations
      (B := B) (A := J) (basedPath.obj Y)
  exact (MorphismProperty.hasLiftingProperty_of_wfs
    (scalarBoundary (qLoopSource Y)) (ε.app (basedPath.obj Y)) hi hp).sq_hasLift _

/-- CM4 lifts the true full disk contraction through the actual original path Q counit. -/
def qLoopDiskLift (Y : (Carrier (J := J))) : L.obj (qLoopSource Y) ⟶ basedPathQ.obj Y :=
  (qLoopDiskLiftSquare Y).lift

/-- Its full scalar source is the same actual chosen Q-loop lift. -/
theorem qLoopDiskLift_source (Y : (Carrier (J := J))) :
    scalarBoundary (qLoopSource Y) ≫ qLoopDiskLift Y = qLoopPathLift Y :=
  (qLoopDiskLiftSquare Y).fac_left

/-- Its complete original Q counit projection is exactly the genuine restricted contraction. -/
theorem qLoopDiskLift_counit (Y : (Carrier (J := J))) :
    qLoopDiskLift Y ≫ ε.app (basedPath.obj Y) = qLoopDiskPath Y :=
  (qLoopDiskLiftSquare Y).fac_right

/-- The whole actual lifted disk lies over the original quotient and full scalar Q counit. -/
theorem qLoopDiskLift_endpoint (Y : (Carrier (J := J))) :
    qLoopDiskLift Y ≫ basedPathQEndpoint.app Y =
      scalarTensorMap ScalarSphereSuspension.quotient (qLoopSource Y) ≫
        (scalarSuspension.map (ε.app (scalarLoop.obj Y)) ≫
          scalarCounit.app Y) := by
  rw [basedPathQEndpoint_app, ← Category.assoc, qLoopDiskLift_counit]
  exact qLoopDiskPath_endpoint Y

omit B in
/-- The original I-cone scalar source retains the same ordered native boundary and unit maps. -/
theorem originalScalarBoundary_eq (A : (Carrier (J := J))) :
    ConeLiftGeometry.scalarBoundary A = scalarBoundary A := by
  change ((scalarUnitIso A).inv ≫
      scalarTensorMap diskBoundarySourceIso.hom A) ≫
      scalarTensorMap PointedCGWH.diskBoundary A =
    (scalarUnitIso A).inv ≫ scalarTensorMap
      (diskBoundarySourceIso.hom ≫ PointedCGWH.diskBoundary) A
  rw [Category.assoc, ← scalarTensorMap_comp]

private instance qLoopSource_isCofibrant (Y : (Carrier (J := J))) :
    IsCofibrant (qLoopSource Y) :=
  Replacement.isCofibrant_cofibrantReplacement (B := B) (A := J)
    (scalarLoop.obj Y)

private abbrev cone := OriginalICone.cone (B := B) (I := J)
private abbrev iota := OriginalICone.inclusion (B := B) (I := J)
private abbrev suspensionCone (A : (Carrier (J := J))) :=
  OriginalISuspensionCofibrantComparison.originalSuspensionCocone (B := B) A

/-- The specific original I-suspension coefficient retains the complete actual scalar Q counit. -/
def pathConeTarget (F : Eligible (J := J)) : S.obj (qLoopSource F.obj.right) ⟶ F.obj.right :=
  ConeLiftGeometry.coneToScalarSuspension (qLoopSource F.obj.right) ≫
    (scalarSuspension.map (ε.app (scalarLoop.obj F.obj.right)) ≫
      scalarCounit.app F.obj.right)

/-- The true disk lift is composed with the actual whole identity-base Serre lift and I-cone map. -/
def pathConeLift (F : Eligible (J := J)) : cone.obj (qLoopSource F.obj.right) ⟶ F.obj.left :=
  ConeLiftGeometry.coneToScalarDisk (qLoopSource F.obj.right) ≫
    qLoopDiskLift F.obj.right ≫ identityBaseSerreLift F

/--
The complete original I source is precisely the actual Q-loop path lift followed by Serre lift.
-/
theorem pathConeLift_source (F : Eligible (J := J)) :
    iota.app (qLoopSource F.obj.right) ≫ pathConeLift F =
      qLoopPathLift F.obj.right ≫ identityBaseSerreLift F := by
  calc
    _ = (iota.app (qLoopSource F.obj.right) ≫
          ConeLiftGeometry.coneToScalarDisk (qLoopSource F.obj.right)) ≫
        qLoopDiskLift F.obj.right ≫ identityBaseSerreLift F := by
      simp only [pathConeLift, Category.assoc]
    _ = scalarBoundary (qLoopSource F.obj.right) ≫
        qLoopDiskLift F.obj.right ≫ identityBaseSerreLift F := by
      rw [ConeLiftGeometry.coneToScalarDisk_source, originalScalarBoundary_eq]
    _ = _ := by rw [← Category.assoc, qLoopDiskLift_source]

/-- The whole original I-cone lift lies over the same original scalar-Q target coefficient. -/
theorem pathConeLift_over (F : Eligible (J := J)) :
    pathConeLift F ≫ F.obj.hom =
      (suspensionCone (qLoopSource F.obj.right)).inl ≫ pathConeTarget F := by
  let A := qLoopSource F.obj.right
  let k : (OriginalICone.cone (B := B)).obj A ⟶ tensorLeftObject PointedCGWH.diskOne A :=
    ConeLiftGeometry.coneToScalarDisk A
  let d : tensorLeftObject PointedCGWH.diskOne A ⟶ scalarSuspension.obj A :=
    scalarTensorMap ScalarSphereSuspension.quotient A
  let t : scalarSuspension.obj A ⟶ F.obj.right :=
    scalarSuspension.map (ε.app (scalarLoop.obj F.obj.right)) ≫ scalarCounit.app F.obj.right
  let l : (OriginalICone.cone (B := B)).obj A ⟶ S.obj A := (suspensionCone A).inl
  have h : l ≫ ConeLiftGeometry.coneToScalarSuspension A = k ≫ d :=
    ConeLiftGeometry.coneToScalarSuspension_cone A
  let g : tensorLeftObject PointedCGWH.diskOne A ⟶ basedPathQ.obj F.obj.right :=
    qLoopDiskLift F.obj.right
  let h' : basedPathQ.obj F.obj.right ⟶ F.obj.left := identityBaseSerreLift F
  let e : basedPathQ.obj F.obj.right ⟶ F.obj.right := basedPathQEndpoint.app F.obj.right
  have hLift : h' ≫ F.obj.hom = e := identityBaseSerreLift_over F
  have hDisk : g ≫ e = d ≫ t := qLoopDiskLift_endpoint F.obj.right
  have hOver : pathConeLift F ≫ F.obj.hom = k ≫ (d ≫ t) := by
    change (k ≫ (g ≫ h')) ≫ F.obj.hom = _
    exact (Category.assoc k (g ≫ h') F.obj.hom).trans
      ((congrArg (k ≫ ·) ((Category.assoc g h' F.obj.hom).trans
        (congrArg (g ≫ ·) hLift))).trans (congrArg (k ≫ ·) hDisk))
  exact hOver.trans ((Category.assoc k d t).symm.trans
    ((congrArg (· ≫ t) h.symm).trans
      (Category.assoc l (ConeLiftGeometry.coneToScalarSuspension A) t)))


/-- The actual full identity-base Arrow carries the same original Q-loop fiber coefficient. -/
def pathFiberMap (F : Eligible (J := J)) : qLoopSource F.obj.right ⟶ (a F.obj).pt :=
  qLoopPathFiberMap a ha F.obj.right ≫
    Diagrams.FiberGeometry.chosenFiberMap (identityBaseSerreLiftArrow F)
      (a (basedPathArrowFunctor.obj F.obj.right)) (a F.obj) (ha F.obj)

/--
The first caller projection is exactly the original source restriction of that specific I lift.
-/
theorem pathFiberMap_fst (F : Eligible (J := J)) :
    pathFiberMap a ha F ≫ (a F.obj).fst =
      iota.app (qLoopSource F.obj.right) ≫ pathConeLift F := by
  rw [pathFiberMap, Category.assoc, Diagrams.FiberGeometry.chosenFiberMap_fst,
    ← Category.assoc, qLoopPathFiberMap_fst]
  exact (pathConeLift_source F).symm

/-- The same full caller fiber zero leg retains the actual source zero map. -/
theorem pathFiberMap_snd (F : Eligible (J := J)) :
    pathFiberMap a ha F ≫ (a F.obj).snd = Diagrams.toZero (qLoopSource F.obj.right) := by
  rw [pathFiberMap, Category.assoc, Diagrams.FiberGeometry.chosenFiberMap_snd,
    qLoopPathFiberMap_snd]

/-- The specific original fiber coefficient is lifted through its unchanged actual Q counit. -/
theorem pathQFiberLiftSquare (F : Eligible (J := J)) :
    CommSq (Diagrams.zeroTo (Q.obj (a F.obj).pt)) (Diagrams.zeroTo (qLoopSource F.obj.right))
      (ε.app (a F.obj).pt) (pathFiberMap a ha F) :=
  ⟨Diagrams.zeroDiagramIsInitial.hom_ext _ _⟩

private instance pathQFiberLiftSquare_hasLift (F : Eligible (J := J)) :
    (pathQFiberLiftSquare a ha F).HasLift := by
  have hi : cofibrations (Carrier (J := J)) (Diagrams.zeroTo (qLoopSource F.obj.right)) :=
    (HomotopicalAlgebra.cofibration_iff _).mp
      ((isCofibrant_iff_of_isInitial _ Diagrams.zeroDiagramIsInitial).mp inferInstance)
  have hp : trivialFibrations (Carrier (J := J)) (ε.app (a F.obj).pt) :=
    Replacement.cofibrantReplacementCounit_mem_trivialFibrations
      (B := B) (A := J) (a F.obj).pt
  exact (MorphismProperty.hasLiftingProperty_of_wfs
    (Diagrams.zeroTo (qLoopSource F.obj.right)) (ε.app (a F.obj).pt) hi hp).sq_hasLift _

/--
This Q-fiber coefficient is constructed from the actual path lift, not a different Serre lift.
-/
def pathQFiberMap (F : Eligible (J := J)) : qLoopSource F.obj.right ⟶ Q.obj (a F.obj).pt :=
  (pathQFiberLiftSquare a ha F).lift

/-- Its complete original counit recovers precisely the same path-derived fiber coefficient. -/
theorem pathQFiberMap_counit (F : Eligible (J := J)) :
    pathQFiberMap a ha F ≫ ε.app (a F.obj).pt = pathFiberMap a ha F :=
  (pathQFiberLiftSquare a ha F).fac_right

/-- Both original source and projection equations retain the specific path-derived I-cone lift. -/
theorem pathQFiberMap_counit_fst (F : Eligible (J := J)) :
    pathQFiberMap a ha F ≫ ε.app (a F.obj).pt ≫ (a F.obj).fst =
      iota.app (qLoopSource F.obj.right) ≫ pathConeLift F := by
  rw [← Category.assoc, pathQFiberMap_counit, pathFiberMap_fst]

/-- A contractible original total object makes the actual whole identity-base Serre lift weak. -/
theorem identityBaseSerreLift_weak (F : Eligible (J := J))
    (hF : weakEquivalences (Carrier (J := J)) (Diagrams.toZero F.obj.left)) :
    weakEquivalences (Carrier (J := J)) (identityBaseSerreLift F) := by
  apply (weakEquivalences (Carrier (J := J))).of_postcomp _ _ hF
  have h : identityBaseSerreLift F ≫ Diagrams.toZero F.obj.left =
      Diagrams.toZero (basedPathQ.obj F.obj.right) :=
    Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  rw [h]
  exact basedPathQCollapse_weak F.obj.right

/-- Actual native weak Arrow maps and the strict loop limit prove weakness of this coefficient. -/
theorem pathFiberMap_weak (F : Eligible (J := J))
    (hF : weakEquivalences (Carrier (J := J)) (Diagrams.toZero F.obj.left)) :
    weakEquivalences (Carrier (J := J)) (pathFiberMap a ha F) := by
  let _ : MorphismProperty.HasFunctorialFactorization
      (trivialCofibrations (Carrier (J := J))) (fibrations (Carrier (J := J))) :=
    (HomotopicalAlgebra.EnrichedProjective.Native.functorialFactorizations
      (B := B) (A := J)).2
  let _ : Fibration (basedPathArrowFunctor.obj F.obj.right).hom :=
    basedPathQEndpoint_fibration F.obj.right
  let _ : Fibration F.obj.hom := F.property.1
  let _ : WeakEquivalence (identityBaseSerreLiftArrow F).left :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (identityBaseSerreLift_weak F hF)
  let _ : WeakEquivalence (identityBaseSerreLiftArrow F).right := by
    change WeakEquivalence (𝟙 F.obj.right)
    infer_instance
  have hFiber : weakEquivalences (Carrier (J := J))
      (Diagrams.FiberGeometry.chosenFiberMap (identityBaseSerreLiftArrow F)
        (a (basedPathArrowFunctor.obj F.obj.right)) (a F.obj) (ha F.obj)) := by
    rw [OriginalFiberComparison.chosenFiberMap_eq_generic a ha]
    exact OrdinaryHoChosenFiberCofiberComparison.originalChosenMap_weak
      Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero a ha (identityBaseSerreLiftArrow F)
  exact (weakEquivalences (Carrier (J := J))).comp_mem _ _
    (qLoopPathFiberMap_weak a ha F.obj.right) hFiber

/-- The genuine original counit lift preserves weakness of the same path-derived coefficient. -/
theorem pathQFiberMap_weak (F : Eligible (J := J))
    (hF : weakEquivalences (Carrier (J := J)) (Diagrams.toZero F.obj.left)) :
    weakEquivalences (Carrier (J := J)) (pathQFiberMap a ha F) := by
  apply (weakEquivalences (Carrier (J := J))).of_postcomp _ _
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (a F.obj).pt)
  rw [pathQFiberMap_counit]
  exact pathFiberMap_weak a ha F hF

/--
The actual two-cone homotopy compares this specific path coefficient and complete target word.
-/
theorem pathQFiberMap_comparison_ho (F : Eligible (J := J)) :
    H.map (S.map (pathQFiberMap a ha F)) ≫ H.map (ConeLiftGeometry.rawQFiberComparison a F.obj) =
      H.map (pathConeTarget F) ≫ H.map (OriginalISuspension.cocone (B := B) F.obj).inr :=
  ConeLiftGeometry.coneCoefficient_comparison_ho_of_lift a F.obj
    (qLoopSource F.obj.right) (pathConeTarget F) (pathConeLift F) (pathConeLift_over F)
    (pathQFiberMap a ha F) (pathQFiberMap_counit_fst a ha F)

/-- Contractibility of the actual original source makes its I-cone inclusion weak. -/
theorem originalConeInclusion_weak (X : (Carrier (J := J)))
    (hX : weakEquivalences (Carrier (J := J)) (Diagrams.toZero X)) :
    weakEquivalences (Carrier (J := J)) (iota.app X) := by
  apply (weakEquivalences (Carrier (J := J))).of_postcomp _ _
    (OriginalICone.contraction_trivialFibration X).2
  have h : iota.app X ≫ (OriginalICone.contraction (B := B)).app X = Diagrams.toZero X :=
    Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  rw [h]
  exact hX

/--
The original plain cofiber inclusion is weak by the actual cone pushout and source contraction.
-/
theorem originalPlainCofiberInclusion_weak (F : Arrow (Carrier (J := J)))
    (hX : weakEquivalences (Carrier (J := J)) (Diagrams.toZero F.left)) :
    weakEquivalences (Carrier (J := J)) (OriginalISuspension.cocone (B := B) F).inr :=
  ((trivialCofibrations (Carrier (J := J))).of_isPushout
    (IsPushout.of_isColimit (OriginalISuspension.coconeIsColimit (B := B) F)).flip
    ⟨OriginalICone.inclusion_cofibration F.left, originalConeInclusion_weak F.left hX⟩).2

/-- The actual original source Q counit preserves the same full weak collapse. -/
theorem qSourceCollapse_weak (X : (Carrier (J := J)))
    (hX : weakEquivalences (Carrier (J := J)) (Diagrams.toZero X)) :
    weakEquivalences (Carrier (J := J)) (Diagrams.toZero (Q.obj X)) := by
  have h : ε.app X ≫ Diagrams.toZero X = Diagrams.toZero (Q.obj X) :=
    Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  exact h ▸ (weakEquivalences (Carrier (J := J))).comp_mem _ _
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences X) hX

/-- The full original Q/corner resolution remains in the genuine native all-fibration category. -/
def resolvedFibrationFunctor : Eligible (J := J) ⥤ Eligible (J := J) :=
  P.lift (P.ι ⋙ OriginalFiberComparison.resolution (B := B) (I := J)) (fun F => by
    refine ⟨?_, HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant _⟩
    let _ : Fibration F.obj.hom := F.property.1
    exact OrdinaryHoChosenFiberCofiberComparison.ArrowResolution.resolvedMap_fibration Q ε
      Replacement.cofibrantReplacementCounit_mem_trivialFibrations F.obj)

/-- The full resolved original Arrow has exactly the original Q/corner source and target maps. -/
theorem resolvedFibrationFunctor_obj (F : Eligible (J := J)) :
    (resolvedFibrationFunctor.obj F).obj =
      (OriginalFiberComparison.resolution (B := B) (I := J)).obj F.obj := rfl

/-- The same complete original resolution retains the original target Q object. -/
theorem resolvedFibrationFunctor_target (F : Eligible (J := J)) :
    (resolvedFibrationFunctor.obj F).obj.right = Q.obj F.obj.right := rfl

/--
The actual source corner counits transport the original total contraction to its whole resolution.
-/
theorem resolvedFibration_total_weak (F : Eligible (J := J))
    (hF : weakEquivalences (Carrier (J := J)) (Diagrams.toZero F.obj.left)) :
    weakEquivalences (Carrier (J := J))
      (Diagrams.toZero (resolvedFibrationFunctor.obj F).obj.left) := by
  let r := (OriginalFiberComparison.resolutionToOriginal (B := B) (I := J)).app F.obj
  have hr : weakEquivalences (Carrier (J := J)) r.left :=
    (OrdinaryHoChosenFiberCofiberComparison.ArrowResolution.toOriginal_trivialFibrations Q ε
      Replacement.cofibrantReplacementCounit_mem_trivialFibrations F.obj).1.2
  have h : r.left ≫ Diagrams.toZero F.obj.left =
      Diagrams.toZero (resolvedFibrationFunctor.obj F).obj.left :=
    Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  exact h ▸ (weakEquivalences (Carrier (J := J))).comp_mem _ _ hr hF

/--
The universal path family is resolved by the actual original full Arrow Q/corner construction.
-/
def resolvedPathFibrationFunctor : (Carrier (J := J)) ⥤ Eligible (J := J) :=
  basedPathFibrationFunctor ⋙ resolvedFibrationFunctor

/-- Every actual resolved path total remains weakly contractible on the original native carrier. -/
theorem resolvedPath_total_weak (Y : (Carrier (J := J))) :
    weakEquivalences (Carrier (J := J))
      (Diagrams.toZero (resolvedPathFibrationFunctor.obj Y).obj.left) :=
  resolvedFibration_total_weak (basedPathFibrationFunctor.obj Y) (basedPathQCollapse_weak Y)

private theorem originalConeCollapseWeak (X : (Carrier (J := J))) :
    weakEquivalences (Carrier (J := J))
      (OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        (cone.obj X)) := by
  have h : (OriginalICone.contraction (B := B)).app X =
      OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        (cone.obj X) := Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  exact h ▸ (OriginalICone.contraction_trivialFibration X).2

private abbrev genericResolvedFiberSuspensionIso :=
  OrdinaryHoChosenFiberHomSequence.OriginalJoin.resolvedQFiberSuspensionHoIso
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero a ha Q ε
    Replacement.isCofibrant_cofibrantReplacement
    Replacement.cofibrantReplacementCounit_mem_trivialFibrations cone iota
    (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B))
    (fun X _ => OriginalICone.inclusion_cofibration X)
    (fun X _ => originalConeCollapseWeak X)

/--
Paste the actual whole original fiber and cofiber resolution Isos before taking integer classes.
-/
theorem suspendedComparison_resolution_equation (F : Eligible (J := J)) :
    (OriginalFiberComparison.originalResolvedQFiberSuspensionHoIso (B := B) a ha).hom.app F ≫
      suspendedComparison a ha F ≫
        (OriginalFiberComparison.QCofiberToResolutionHoIso (B := B) (I := J)).hom.app F.obj =
      H.map (ConeLiftGeometry.rawQFiberComparison a
        ((OriginalFiberComparison.resolution (B := B) (I := J)).obj F.obj)) := by
  have hE :
      (OriginalFiberComparison.originalResolvedQFiberSuspensionHoIso (B := B) a ha).hom.app F =
        (genericResolvedFiberSuspensionIso a ha).hom.app F := by
    rw [OriginalFiberComparison.originalResolvedQFiberSuspensionHoIso_hom]
    exact congrArg (fun m => H.map (S.map (Q.map m)))
      (OriginalFiberComparison.chosenFiberMap_eq_generic a ha
        ((OriginalFiberComparison.resolutionToOriginal (B := B) (I := J)).app F.obj))
  rw [hE]
  have hβ : suspendedComparison a ha F =
      (OriginalFiberComparison.originalFibrationComparison (B := B) (I := J) a ha).app F :=
    OriginalFiberComparison.nativeFibrationComparison_app (B := B) (I := J) a ha F
  refine (congrArg (fun m => (genericResolvedFiberSuspensionIso a ha).hom.app F ≫ m ≫
    (OriginalFiberComparison.QCofiberToResolutionHoIso (B := B) (I := J)).hom.app F.obj)
    hβ).trans ?_
  exact OrdinaryHoChosenFiberHomSequence.OriginalJoin.originalSuspendedFiberToQCofiber_equation
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero a ha Q ε
    Replacement.isCofibrant_cofibrantReplacement
    Replacement.cofibrantReplacementCounit_mem_trivialFibrations cone iota
    (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B))
    (fun X _ => OriginalICone.inclusion_cofibration X)
    (fun X _ => originalConeCollapseWeak X) F

end PathCoefficientGeometry

end NativeBasedPathGeometry

namespace FiberChoiceGeometry

private abbrev P := OrdinaryHoChosenFiberMaps.fibrantFibrationProperty (C := (Carrier (J := J)))
private abbrev cone := OriginalICone.cone (B := B) (I := J)
private abbrev iota := OriginalICone.inclusion (B := B) (I := J)
private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := J)

variable (b : ∀ F : Arrow (Carrier (J := J)), PullbackCone F.hom (Diagrams.zeroTo F.right))
  (hb : ∀ F, IsLimit (b F))

/--
Both original caller limit families are compared by their actual whole pullback universal
properties.
-/
abbrev fiberChoiceIso (F : Arrow (Carrier (J := J))) : (a F).pt ≅ (b F).pt :=
  OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero a ha b hb F

/-- The complete original native fiber family retains the actual natural caller-choice Iso. -/
def fiberChoiceNatIso : fiberFunctor a ha ≅ fiberFunctor b hb :=
  Functor.isoWhiskerLeft P.ι
    ((OriginalFiberComparison.chosenFiberFunctorNatIso a ha).symm ≪≫
      OrdinaryHoChosenFiberMaps.choiceNatIso Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        a ha b hb ≪≫ OriginalFiberComparison.chosenFiberFunctorNatIso b hb)

/-- Every forward source component is the same actual original two-projection choice Iso. -/
theorem fiberChoiceNatIso_hom_app (F : Eligible (J := J)) :
    (fiberChoiceNatIso a ha b hb).hom.app F = (fiberChoiceIso a ha b hb F.obj).hom := by
  simp only [fiberChoiceNatIso, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, NatTrans.comp_app, OriginalFiberComparison.chosenFiberFunctorNatIso,
    NatIso.ofComponents, Iso.refl_hom, Iso.refl_inv]
  change 𝟙 _ ≫ (fiberChoiceIso a ha b hb F.obj).hom ≫ 𝟙 _ =
    (fiberChoiceIso a ha b hb F.obj).hom
  simp only [Category.id_comp, Category.comp_id]

omit B in
/--
Both original fiber projection functions are retained under this exact caller-choice source map.
-/
theorem fiberChoiceIso_projections (F : Arrow (Carrier (J := J))) :
    (fiberChoiceIso a ha b hb F).hom ≫ (b F).fst = (a F).fst ∧
      (fiberChoiceIso a ha b hb F).hom ≫ (b F).snd = (a F).snd :=
  ⟨OrdinaryHoChosenFiberMaps.choiceIso_hom_fst _ _ _ _ _ _ F,
    OrdinaryHoChosenFiberMaps.choiceIso_hom_snd _ _ _ _ _ _ F⟩

/-- The same original Q/I comparison is natural in every independent caller fiber choice. -/
theorem suspendedComparison_choice (F : Eligible (J := J)) :
    H.map (S.map (Q.map (fiberChoiceIso a ha b hb F.obj).hom)) ≫ suspendedComparison b hb F =
      suspendedComparison a ha F := by
  have hA : suspendedComparison a ha F =
      (OriginalFiberComparison.originalFibrationComparison (B := B) (I := J) a ha).app F :=
    OriginalFiberComparison.nativeFibrationComparison_app (B := B) (I := J) a ha F
  have hB : suspendedComparison b hb F =
      (OriginalFiberComparison.originalFibrationComparison (B := B) (I := J) b hb).app F :=
    OriginalFiberComparison.nativeFibrationComparison_app (B := B) (I := J) b hb F
  refine (congrArg (H.map (S.map (Q.map (fiberChoiceIso a ha b hb F.obj).hom)) ≫ ·) hB).trans ?_
  refine (OrdinaryHoChosenFiberHomSequence.OriginalJoin.originalSuspendedFiberToQCofiber_choice
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero a ha Q ε
    Replacement.isCofibrant_cofibrantReplacement
    Replacement.cofibrantReplacementCounit_mem_trivialFibrations cone iota
    (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B))
    (fun X _ => OriginalICone.inclusion_cofibration X)
    (fun X _ => NativeBasedPathGeometry.PathCoefficientGeometry.originalConeCollapseWeak X)
    b hb F).trans hA.symm

omit B in
/-- Both whole original inverse source-choice functions keep the actual two projections. -/
theorem fiberChoiceIso_inverse_projections (F : Arrow (Carrier (J := J))) :
    (fiberChoiceIso a ha b hb F).inv ≫ (a F).fst = (b F).fst ∧
    (fiberChoiceIso a ha b hb F).inv ≫ (a F).snd = (b F).snd :=
  ⟨OrdinaryHoChosenFiberMaps.choiceIso_inv_fst _ _ _ _ _ _ F,
    OrdinaryHoChosenFiberMaps.choiceIso_inv_snd _ _ _ _ _ _ F⟩

/-- The inverse whole fiber-choice map preserves the complete original Q/suspension comparison. -/
theorem suspendedComparison_choice_inverse (F : Eligible (J := J)) :
    H.map (S.map (Q.map (fiberChoiceIso a ha b hb F.obj).inv)) ≫
      suspendedComparison a ha F = suspendedComparison b hb F := by
  let e : H.obj (S.obj (Q.obj (a F.obj).pt)) ≅ H.obj (S.obj (Q.obj (b F.obj).pt)) :=
    H.mapIso (S.mapIso (Q.mapIso (fiberChoiceIso a ha b hb F.obj)))
  have h : e.hom ≫ suspendedComparison b hb F = suspendedComparison a ha F :=
    suspendedComparison_choice a ha b hb F
  exact (congrArg (e.inv ≫ ·) h).symm.trans
    ((Category.assoc e.inv e.hom (suspendedComparison b hb F)).symm.trans
      ((congrArg (· ≫ suspendedComparison b hb F) e.inv_hom_id).trans (Category.id_comp _)))


end FiberChoiceGeometry

end HomotopicalAlgebra.EnrichedProjective.Native.OriginalFiberCofiberGeometry
