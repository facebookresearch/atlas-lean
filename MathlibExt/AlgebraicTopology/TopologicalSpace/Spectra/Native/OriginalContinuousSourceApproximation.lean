/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OmegaTestTransfiniteClosure
import MathlibExt.CategoryTheory.SmallObject.ContinuousApproximation
import MathlibExt.AlgebraicTopology.ModelCategory.ContinuousCofibrationColimit

/-!
# Original continuous source approximations

The stage functors retain the original input diagram and every natural
transformation. Bottom and successor maps use the actual original I
factorization at the caller's realized cardinal and bottom. Limit stages use
the colimit of the complete preceding approximation diagram. Weak counit
conclusions require the original input to be genuinely continuous with its
actual HEP transitions; no weak conclusion for a discontinuous input is claimed.
-/

set_option autoImplicit false
noncomputable section
universe u v w uC vC


namespace PointedCGWH.Spectra.OriginalContinuousSourceApproximation

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native HomotopicalAlgebra.EnrichedProjective
open CategoryTheory.EnrichedFunctorCat CategoryTheory.SmallObject.SuccStruct
open scoped CGWH.modelCategory MonoidalClosed

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev C := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- The original complete successor input arrow uses the full previous counit
and the next stage of the caller's unchanged input functor. -/
def originalSuccessorInput (F : J ⥤ C (I := I)) {j : J} (Q : Set.Iic j ⥤ C (I := I))
    (p : Q ⟶ (Set.initialSegIic j).monotone.functor ⋙ F) : Arrow (C (I := I)) :=
  Arrow.mk (p.app ⟨j, le_rfl⟩ ≫ F.map (homOfLE (Order.le_succ j)))

/-- The full successor approximation is the actual original I intermediate object. -/
def originalSuccessorObject (F : J ⥤ C (I := I)) {j : J} (Q : Set.Iic j ⥤ C (I := I))
    (p : Q ⟶ (Set.initialSegIic j).monotone.functor ⋙ F) : C (I := I) :=
  (Native.cofibrantFactorizationData (B := B)).Z.obj (originalSuccessorInput F Q p)

/-- The successor arrow is the same original I factor map from the complete previous source. -/
def originalSuccessorInclusion (F : J ⥤ C (I := I)) {j : J} (Q : Set.Iic j ⥤ C (I := I))
    (p : Q ⟶ (Set.initialSegIic j).monotone.functor ⋙ F) :
    Q.obj ⟨j, le_rfl⟩ ⟶ originalSuccessorObject (B := B) F Q p :=
  (Native.cofibrantFactorizationData (B := B)).i.app (originalSuccessorInput F Q p)

/-- The successor counit is the same entire original I right factor. -/
def originalSuccessorProjection (F : J ⥤ C (I := I)) {j : J} (Q : Set.Iic j ⥤ C (I := I))
    (p : Q ⟶ (Set.initialSegIic j).monotone.functor ⋙ F) :
    originalSuccessorObject (B := B) F Q p ⟶ F.obj (Order.succ j) :=
  (Native.cofibrantFactorizationData (B := B)).p.app (originalSuccessorInput F Q p)

omit [OrderBot J] [WellFoundedLT J] in
/-- The actual successor factors the entire previous-counit/input-stage composite. -/
theorem originalSuccessor_factor (F : J ⥤ C (I := I)) {j : J} (Q : Set.Iic j ⥤ C (I := I))
    (p : Q ⟶ (Set.initialSegIic j).monotone.functor ⋙ F) :
    originalSuccessorInclusion (B := B) F Q p ≫ originalSuccessorProjection (B := B) F Q p =
      p.app ⟨j, le_rfl⟩ ≫ F.map (homOfLE (Order.le_succ j)) :=
  (Native.cofibrantFactorizationData (B := B)).fac_app

/-- The exact previous approximation and counit form a full original arrow diagram. -/
def originalArrowPrefix (F : J ⥤ C (I := I)) {j : J} (Q : Set.Iic j ⥤ C (I := I))
    (p : Q ⟶ (Set.initialSegIic j).monotone.functor ⋙ F) :
    Set.Iic j ⥤ Arrow (C (I := I)) where
  obj k := Arrow.mk (p.app k)
  map f := Arrow.homMk (Q.map f) (F.map
    ((Set.initialSegIic j).monotone.functor.map f)) (p.naturality f)
  map_id k := by
    apply Arrow.hom_ext
    · exact Q.map_id k
    · simp
  map_comp f g := by
    apply Arrow.hom_ext
    · exact Q.map_comp f g
    · simp

/-- The full original successor square retains both factor maps and the actual input stage. -/
def originalSuccessorArrow (F : J ⥤ C (I := I)) {j : J} (Q : Set.Iic j ⥤ C (I := I))
    (p : Q ⟶ (Set.initialSegIic j).monotone.functor ⋙ F) :
    (originalArrowPrefix F Q p).obj ⟨j, le_rfl⟩ ⟶
      Arrow.mk (originalSuccessorProjection (B := B) F Q p) :=
  Arrow.homMk (originalSuccessorInclusion (B := B) F Q p)
    (F.map (homOfLE (Order.le_succ j))) (originalSuccessor_factor (B := B) F Q p)

/-- The complete next prefix is an actual arrow-diagram extension using the original I square. -/
def originalSuccessorArrowPrefix (F : J ⥤ C (I := I)) {j : J} (hj : ¬IsMax j)
    (Q : Set.Iic j ⥤ C (I := I))
    (p : Q ⟶ (Set.initialSegIic j).monotone.functor ⋙ F) :
    Set.Iic (Order.succ j) ⥤ Arrow (C (I := I)) :=
  extendToSucc hj (originalArrowPrefix F Q p) (originalSuccessorArrow (B := B) F Q p)

omit [OrderBot J] [WellFoundedLT J] in
/-- The full successor target diagram is literally the original restricted F, on every map. -/
theorem originalSuccessorArrowPrefix_target (F : J ⥤ C (I := I)) {j : J} (hj : ¬IsMax j)
    (Q : Set.Iic j ⥤ C (I := I))
    (p : Q ⟶ (Set.initialSegIic j).monotone.functor ⋙ F) :
    originalSuccessorArrowPrefix (B := B) F hj Q p ⋙ Arrow.rightFunc =
      (Set.initialSegIic (Order.succ j)).monotone.functor ⋙ F := by
  rw [originalSuccessorArrowPrefix, extendToSucc_comp]
  change extendToSucc hj ((Set.initialSegIic j).monotone.functor ⋙ F)
    (F.map (homOfLE (Order.le_succ j))) = _
  exact extendToSucc_original_eq hj F

end PointedCGWH.Spectra.OriginalContinuousSourceApproximation
namespace PointedCGWH.Spectra.OriginalContinuousSourceApproximation

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native HomotopicalAlgebra.EnrichedProjective
open CategoryTheory.EnrichedFunctorCat CategoryTheory.SmallObject.SuccStruct
open scoped CGWH.modelCategory MonoidalClosed

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev D := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- The actual complete source approximation diagram of the original successor prefix. -/
def originalSuccessorSourcePrefix (F : J ⥤ D (I := I)) {j : J} (hj : ¬IsMax j)
    (Q : Set.Iic j ⥤ D (I := I))
    (p : Q ⟶ (Set.initialSegIic j).monotone.functor ⋙ F) :
    Set.Iic (Order.succ j) ⥤ D (I := I) :=
  originalSuccessorArrowPrefix (B := B) F hj Q p ⋙ Arrow.leftFunc

/-- The whole actual original successor counit retains every target-stage map. -/
def originalSuccessorCounit (F : J ⥤ D (I := I)) {j : J} (hj : ¬IsMax j)
    (Q : Set.Iic j ⥤ D (I := I))
    (p : Q ⟶ (Set.initialSegIic j).monotone.functor ⋙ F) :
    originalSuccessorSourcePrefix (B := B) F hj Q p ⟶
      (Set.initialSegIic (Order.succ j)).monotone.functor ⋙ F :=
  Functor.whiskerLeft (originalSuccessorArrowPrefix (B := B) F hj Q p) Arrow.leftToRight ≫
    eqToHom (originalSuccessorArrowPrefix_target (B := B) F hj Q p)

omit [OrderBot J] [WellFoundedLT J] in
/-- The next source prefix retains the actual predecessor Q on the complete old interval. -/
theorem originalSuccessorSourcePrefix_restrict (F : J ⥤ D (I := I)) {j : J} (hj : ¬IsMax j)
    (Q : Set.Iic j ⥤ D (I := I))
    (p : Q ⟶ (Set.initialSegIic j).monotone.functor ⋙ F) :
    SmallObject.restrictionLE (originalSuccessorSourcePrefix (B := B) F hj Q p)
      (Order.le_succ j) = Q := by
  change SmallObject.restrictionLE (originalSuccessorArrowPrefix (B := B) F hj Q p)
    (Order.le_succ j) ⋙ Arrow.leftFunc = Q
  rw [originalSuccessorArrowPrefix, extendToSucc_restrict_eq]
  rfl

omit [OrderBot J] [WellFoundedLT J] in
/-- Every original successor inclusion is genuinely a cofibration by the same I factory. -/
theorem originalSuccessorInclusion_cofibration (F : J ⥤ D (I := I)) {j : J}
    (Q : Set.Iic j ⥤ D (I := I))
    (p : Q ⟶ (Set.initialSegIic j).monotone.functor ⋙ F) :
    cofibrations (D (I := I)) (originalSuccessorInclusion (B := B) F Q p) :=
  (Native.cofibrantFactorizationData (B := B)).hi _

omit [OrderBot J] [WellFoundedLT J] in
/-- Every original successor right factor is the actual original trivial fibration. -/
theorem originalSuccessorProjection_trivialFibration (F : J ⥤ D (I := I)) {j : J}
    (Q : Set.Iic j ⥤ D (I := I))
    (p : Q ⟶ (Set.initialSegIic j).monotone.functor ⋙ F) :
    trivialFibrations (D (I := I)) (originalSuccessorProjection (B := B) F Q p) :=
  (Native.cofibrantFactorizationData (B := B)).hp _

end PointedCGWH.Spectra.OriginalContinuousSourceApproximation
namespace PointedCGWH.Spectra.OriginalContinuousSourceApproximation

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native HomotopicalAlgebra.EnrichedProjective
open CategoryTheory.EnrichedFunctorCat CategoryTheory.SmallObject.SuccStruct
open scoped CGWH.modelCategory MonoidalClosed

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev NativeC := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- The full actual limit input arrow diagram retains the original strict interval and
the entire source counit on all preceding stages. -/
def originalLimitArrowDiagram (F : J ⥤ NativeC (I := I)) (m : J)
    (Q : Set.Iio m ⥤ NativeC (I := I))
    (p : Q ⟶ (Set.principalSegIio m).monotone.functor ⋙ F) :
    Set.Iio m ⥤ Arrow (NativeC (I := I)) where
  obj k := Arrow.mk (p.app k)
  map f := Arrow.homMk (Q.map f)
    (F.map ((Set.principalSegIio m).monotone.functor.map f)) (p.naturality f)
  map_id k := by
    apply Arrow.hom_ext
    · exact Q.map_id k
    · simp
  map_comp f g := by
    apply Arrow.hom_ext
    · exact Q.map_comp f g
    · simp

/-- The actual original limit target cocone is the principal-segment cocone of F itself. -/
def originalLimitArrowCocone (F : J ⥤ NativeC (I := I)) (m : J)
    (Q : Set.Iio m ⥤ NativeC (I := I))
    (p : Q ⟶ (Set.principalSegIio m).monotone.functor ⋙ F) [HasColimit Q] :
    Cocone (originalLimitArrowDiagram F m Q p) :=
  Comma.coconeOfPreserves (originalLimitArrowDiagram F m Q p)
    (colimit.isColimit Q) ((Set.principalSegIio m).cocone F)

/-- The same complete original colimit map is the limit-stage counit. -/
def originalLimitProjection (F : J ⥤ NativeC (I := I)) (m : J)
    (Q : Set.Iio m ⥤ NativeC (I := I))
    (p : Q ⟶ (Set.principalSegIio m).monotone.functor ⋙ F) [HasColimit Q] :
    colimit Q ⟶ F.obj m :=
  (originalLimitArrowCocone F m Q p).pt.hom

omit B [OrderBot J] [SuccOrder J] [WellFoundedLT J] in
/-- Every actual source colimit leg retains the full original limit counit square. -/
theorem originalLimitProjection_ι (F : J ⥤ NativeC (I := I)) (m : J)
    (Q : Set.Iio m ⥤ NativeC (I := I))
    (p : Q ⟶ (Set.principalSegIio m).monotone.functor ⋙ F) [HasColimit Q]
    (j : Set.Iio m) :
    colimit.ι Q j ≫ originalLimitProjection F m Q p =
      p.app j ≫ F.map (homOfLE j.2.le) :=
  ((originalLimitArrowCocone F m Q p).ι.app j).w

/-- Genuine continuity of the original input supplies the actual full arrow colimit.
No continuity or weak counit outcome is given as an input for Q. -/
def originalLimitArrowCoconeIsColimit (F : J ⥤ NativeC (I := I)) [F.IsWellOrderContinuous]
    (m : J) (hm : Order.IsSuccLimit m) (Q : Set.Iio m ⥤ NativeC (I := I))
    (p : Q ⟶ (Set.principalSegIio m).monotone.functor ⋙ F) [HasColimit Q] :
    IsColimit (originalLimitArrowCocone F m Q p) :=
  Comma.coconeOfPreservesIsColimit (originalLimitArrowDiagram F m Q p)
    (colimit.isColimit Q) (F.isColimitOfIsWellOrderContinuous m hm)

/-- Extend the same complete original limit arrow cocone to its full closed interval. -/
def originalLimitArrowPrefix (F : J ⥤ NativeC (I := I)) (m : J)
    (Q : Set.Iio m ⥤ NativeC (I := I))
    (p : Q ⟶ (Set.principalSegIio m).monotone.functor ⋙ F) [HasColimit Q] :
    Set.Iic m ⥤ Arrow (NativeC (I := I)) :=
  ofCocone (originalLimitArrowCocone F m Q p)

/-- The complete source limit cocone has the original chosen colimit source and every leg. -/
def originalLimitSourceCocone (F : J ⥤ NativeC (I := I)) (m : J)
    (Q : Set.Iio m ⥤ NativeC (I := I))
    (p : Q ⟶ (Set.principalSegIio m).monotone.functor ⋙ F) [HasColimit Q] :
    Cocone Q :=
  Arrow.leftFunc.mapCocone (originalLimitArrowCocone F m Q p)

/-- The actual preceding source is colimiting for every original input, without an input
continuity hypothesis or a desired weak counit field. -/
def originalLimitSourceCoconeIsColimit (F : J ⥤ NativeC (I := I)) (m : J)
    (Q : Set.Iio m ⥤ NativeC (I := I))
    (p : Q ⟶ (Set.principalSegIio m).monotone.functor ⋙ F) [HasColimit Q] :
    IsColimit (originalLimitSourceCocone F m Q p) :=
  colimit.isColimit Q

/-- The full closed-interval source diagram extends the actual preceding colimit. -/
def originalLimitSourcePrefix (F : J ⥤ NativeC (I := I)) (m : J)
    (Q : Set.Iio m ⥤ NativeC (I := I))
    (p : Q ⟶ (Set.principalSegIio m).monotone.functor ⋙ F) [HasColimit Q] :
    Set.Iic m ⥤ NativeC (I := I) :=
  originalLimitArrowPrefix F m Q p ⋙ Arrow.leftFunc

end PointedCGWH.Spectra.OriginalContinuousSourceApproximation
namespace PointedCGWH.Spectra.OriginalContinuousSourceApproximation

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native HomotopicalAlgebra.EnrichedProjective
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev E := EnrichedFunctorCat PointedCGWH.{u, v} I
private abbrev Inputs := J ⥤ E (I := I)

/-- Every original input-stage object and map, as a complete functor on all F and α. -/
def originalInputStages : J ⥤ (Inputs (I := I) (J := J) ⥤ E (I := I)) :=
  CategoryTheory.evaluation J (E (I := I))

/-- The zeroth full source functor uses the same original Q on every actual bottom stage. -/
def originalBottomSource : Inputs (I := I) (J := J) ⥤ E (I := I) :=
  (originalInputStages (I := I) (J := J)).obj ⊥ ⋙
    Replacement.cofibrantReplacement (B := B)

/-- The entire bottom counit is the original I counit natural transformation. -/
def originalBottomCounit : originalBottomSource (B := B) (I := I) (J := J) ⟶
    (originalInputStages (I := I) (J := J)).obj ⊥ :=
  Functor.whiskerLeft ((originalInputStages (I := I) (J := J)).obj ⊥)
    (Replacement.cofibrantReplacementCounit (B := B))

/-- The original same-I factory acts on whole source/target functors pointwise,
retaining every α square before evaluating any particular input. -/
def originalWholeInputFactorization :
    MorphismProperty.FunctorialFactorizationData
      ((cofibrations (E (I := I))).functorCategory (Inputs (I := I) (J := J)))
      ((trivialFibrations (E (I := I))).functorCategory (Inputs (I := I) (J := J))) :=
  (Native.cofibrantFactorizationData (B := B)).functorCategory (Inputs (I := I) (J := J))

end PointedCGWH.Spectra.OriginalContinuousSourceApproximation


namespace PointedCGWH.Spectra.OriginalContinuousSourceApproximation

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native HomotopicalAlgebra.EnrichedProjective
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev NativeDiagram := EnrichedFunctorCat PointedCGWH.{u, v} I
private abbrev AllInputs := J ⥤ NativeDiagram (I := I)

private instance nativeAllInputColimits :
    HasColimitsOfSize.{v, v} (AllInputs (I := I) (J := J) ⥤ NativeDiagram (I := I)) := by
  let : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := Native.nativeColimits
  infer_instance

/-- The complete all-input original approximation Arrow diagram uses the exact original
bottom Q/ε and the same original I functorial factory. -/
def wholeOriginalArrowDiagram :
    J ⥤ Arrow (AllInputs (I := I) (J := J) ⥤ NativeDiagram (I := I)) :=
  CategoryTheory.OriginalContinuousApproximation.fullDiagram
    (originalInputStages (I := I) (J := J))
    (Arrow.mk (originalBottomCounit (B := B) (I := I) (J := J)))
    (originalWholeInputFactorization (B := B) (I := I) (J := J)) rfl

/-- The entire original source approximation is a full all-input stage functor. -/
def wholeOriginalSource :
    J ⥤ (AllInputs (I := I) (J := J) ⥤ NativeDiagram (I := I)) :=
  wholeOriginalArrowDiagram (B := B) (I := I) (J := J) ⋙ Arrow.leftFunc

/-- The complete original target diagram remains the input evaluation stage functor. -/
theorem wholeOriginalArrowDiagram_target :
    wholeOriginalArrowDiagram (B := B) (I := I) (J := J) ⋙ Arrow.rightFunc =
      originalInputStages (I := I) (J := J) :=
  CategoryTheory.OriginalContinuousApproximation.fullDiagram_target _ _ _ _

/-- The full original counit retains every stage and every input natural transformation. -/
def wholeOriginalCounit : wholeOriginalSource (B := B) (I := I) (J := J) ⟶
    originalInputStages (I := I) (J := J) :=
  Functor.whiskerLeft (wholeOriginalArrowDiagram (B := B) (I := I) (J := J))
      Arrow.leftToRight ≫ eqToHom (wholeOriginalArrowDiagram_target (B := B))

/-- The approximation of a particular original F is evaluation of the same complete
all-input source functor, retaining every original ordinal transition. -/
def source (F : J ⥤ NativeDiagram (I := I)) : J ⥤ NativeDiagram (I := I) :=
  wholeOriginalSource (B := B) (I := I) (J := J) ⋙
    (CategoryTheory.evaluation (AllInputs (I := I) (J := J)) (NativeDiagram (I := I))).obj F

/-- The counit at a caller F is the actual component of that same original whole counit. -/
def counit (F : J ⥤ NativeDiagram (I := I)) : source (B := B) F ⟶ F :=
  Functor.whiskerRight (wholeOriginalCounit (B := B) (I := I) (J := J))
    ((CategoryTheory.evaluation (AllInputs (I := I) (J := J)) (NativeDiagram (I := I))).obj F)

end PointedCGWH.Spectra.OriginalContinuousSourceApproximation

namespace PointedCGWH.Spectra.OriginalContinuousSourceApproximation

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native HomotopicalAlgebra.EnrichedProjective
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev ND := EnrichedFunctorCat PointedCGWH.{u, v} I
private abbrev InputCategory := J ⥤ ND (I := I)

/-- The complete all-input source functor is genuinely continuous through its actual
preceding source colimits, with no continuity hypothesis on caller F. -/
theorem wholeOriginalSource_continuous :
    (wholeOriginalSource (B := B) (I := I) (J := J)).IsWellOrderContinuous :=
  CategoryTheory.OriginalContinuousApproximation.sourceDiagram_continuous _ _ _ _

/-- Actual evaluation of the full source functor retains every original limit cocone. -/
def sourceLimitIsColimit (F : J ⥤ ND (I := I)) (m : J) (hm : Order.IsSuccLimit m) :
    IsColimit ((Set.principalSegIio m).cocone (source (B := B) F)) := by
  let Q := wholeOriginalSource (B := B) (I := I) (J := J)
  let : Q.IsWellOrderContinuous := wholeOriginalSource_continuous (B := B)
  let : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := Native.nativeColimits
  let U := (CategoryTheory.evaluation (InputCategory (I := I) (J := J)) (ND (I := I))).obj F
  exact isColimitOfPreserves U (Q.isColimitOfIsWellOrderContinuous m hm)

/-- The actual original source approximation of every F is genuinely continuous. -/
theorem source_continuous (F : J ⥤ ND (I := I)) : (source (B := B) F).IsWellOrderContinuous :=
  { nonempty_isColimit m hm := ⟨sourceLimitIsColimit F m hm⟩ }

end PointedCGWH.Spectra.OriginalContinuousSourceApproximation
namespace PointedCGWH.Spectra.OriginalContinuousSourceApproximation

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native HomotopicalAlgebra.EnrichedProjective
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev NativeC0 := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- The source map of every original α is the whole all-input approximation functor map. -/
def sourceMap {F G : J ⥤ NativeC0 (I := I)} (α : F ⟶ G) :
    source (B := B) F ⟶ source (B := B) G where
  app j := ((wholeOriginalSource (B := B) (I := I) (J := J)).obj j).map α
  naturality _i _j f := ((wholeOriginalSource (B := B) (I := I) (J := J)).map f).naturality α |>.symm

/-- Every complete original α counit square remains natural on the unchanged F/G. -/
theorem counit_naturality {F G : J ⥤ NativeC0 (I := I)} (α : F ⟶ G) :
    sourceMap (B := B) α ≫ counit (B := B) G = counit (B := B) F ≫ α := by
  apply NatTrans.ext
  funext j
  exact ((wholeOriginalCounit (B := B) (I := I) (J := J)).app j).naturality α

end PointedCGWH.Spectra.OriginalContinuousSourceApproximation

namespace PointedCGWH.Spectra.OriginalContinuousSourceApproximation

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native HomotopicalAlgebra.EnrichedProjective
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev NativeCar := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- Every full all-input source successor is in the actual original pointwise cofibration class. -/
theorem wholeOriginalSource_successor (j : J) (hj : ¬IsMax j) :
    (cofibrations (NativeCar (I := I))).functorCategory (J ⥤ NativeCar (I := I))
      ((wholeOriginalSource (B := B) (I := I) (J := J)).map (homOfLE (Order.le_succ j))) :=
  CategoryTheory.OriginalContinuousApproximation.sourceDiagram_successor_mem _ _ _ _ j hj

/-- The actual original successor source map at every caller F is an I-cofibration. -/
theorem source_successor_cofibration (F : J ⥤ NativeCar (I := I)) (j : J) (hj : ¬IsMax j) :
    cofibrations (NativeCar (I := I)) ((source (B := B) F).map (homOfLE (Order.le_succ j))) :=
  wholeOriginalSource_successor (B := B) j hj F

/-- The actual bottom source keeps the entire original I-Q source of F_bot. -/
theorem source_bottom (F : J ⥤ NativeCar (I := I)) :
    (source (B := B) F).obj ⊥ =
      (Replacement.cofibrantReplacement (B := B)).obj (F.obj ⊥) := by
  have h := CategoryTheory.OriginalContinuousApproximation.fullDiagram_bottom
    (originalInputStages (I := I) (J := J))
    (Arrow.mk (originalBottomCounit (B := B) (I := I) (J := J)))
    (originalWholeInputFactorization (B := B) (I := I) (J := J)) rfl
  exact congrArg (fun p : Arrow ((J ⥤ NativeCar (I := I)) ⥤ NativeCar (I := I)) =>
    p.left.obj F) h

end PointedCGWH.Spectra.OriginalContinuousSourceApproximation

namespace PointedCGWH.Spectra.OriginalContinuousSourceApproximation

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native HomotopicalAlgebra.EnrichedProjective
open CategoryTheory.EnrichedFunctorCat CategoryTheory.MorphismProperty
open scoped CGWH.modelCategory MonoidalClosed

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev ActualNative := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- The real original bottom source is cofibrant without any hypothesis on the caller F. -/
theorem source_bottom_cofibrant (F : J ⥤ ActualNative (I := I)) :
    IsCofibrant ((source (B := B) F).obj ⊥) := by
  rw [source_bottom]
  exact Replacement.isCofibrant_cofibrantReplacement (B := B) (F.obj ⊥)

/-- Every actual source transition, including those crossing genuine limits, is an
original model cofibration on the same complete source diagram. -/
theorem source_map_cofibration (F : J ⥤ ActualNative (I := I)) {i j : J} (f : i ⟶ j) :
    cofibrations (ActualNative (I := I)) ((source (B := B) F).map f) := by
  let Q := source (B := B) F
  let : Q.IsWellOrderContinuous := source_continuous F
  let : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := Native.nativeColimits
  let : (cofibrations (ActualNative (I := I))).IsStableUnderTransfiniteComposition.{v} := by
    rw [← trivialFibrations_llp]
    infer_instance
  let witness : (cofibrations (ActualNative (I := I))).TransfiniteCompositionOfShape J
      (colimit.ι Q ⊥) :=
    { F := Q
      isoBot := Iso.refl (Q.obj ⊥)
      incl := (colimit.cocone Q).ι
      isColimit := colimit.isColimit Q
      fac := Category.id_comp _
      map_mem := source_successor_cofibration F }
  exact witness.mem_map f

/-- Every original approximation source stage is genuinely cofibrant. -/
theorem source_stage_cofibrant (F : J ⥤ ActualNative (I := I)) (j : J) :
    IsCofibrant ((source (B := B) F).obj j) := by
  let : IsCofibrant ((source (B := B) F).obj ⊥) := source_bottom_cofibrant F
  let : Cofibration ((source (B := B) F).map (homOfLE bot_le : ⊥ ⟶ j)) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr (source_map_cofibration F (homOfLE bot_le))
  exact isCofibrant_of_cofibration ((source (B := B) F).map (homOfLE bot_le : ⊥ ⟶ j))

end PointedCGWH.Spectra.OriginalContinuousSourceApproximation

namespace PointedCGWH.Spectra.OriginalContinuousSourceApproximation

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native HomotopicalAlgebra.EnrichedProjective
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.Spectra.Orthogonal.OriginalIClosedHomotopyExtension
open scoped CGWH.modelCategory MonoidalClosed

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev OriginalNative := EnrichedFunctorCat PointedCGWH.{u, v} I

omit B in
/-- The original free-I closure lies in the genuine native HEP lifting class on every
actual index, by the same original free-I HEP suppliers and full LLP closure. -/
theorem originalNativeILeft_le_HEP :
    (HomotopicalAlgebra.EnrichedProjective.generators (A := I)
      PointedCGWH.realizedBoundaryInclusions.{u, v}).rlp.llp ≤
        PointedCGWH.EnrichedBasedHomotopyExtension.property := by
  let P : MorphismProperty (OriginalNative (I := I)) :=
    HomotopicalAlgebra.EnrichedProjective.generators PointedCGWH.realizedBoundaryInclusions
  let T := cotensorEndpointFamily.{u, v} (I := I)
  have h : P ≤ T.llp := by
    rw [← nativeHEP_eq_llp]
    exact originalFreeI_le_nativeHEP
  have hRight : T ≤ P.rlp := (MorphismProperty.le_llp_iff_le_rlp P T).mp h
  rw [nativeHEP_eq_llp]
  exact MorphismProperty.antitone_llp hRight

/-- The original source approximation has genuine native HEP successors by the original
I construction; no HEP condition on F is needed to construct this source. -/
theorem source_successor_HEP (F : J ⥤ OriginalNative (I := I)) (j : J) (hj : ¬IsMax j) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property
      ((source (B := B) F).map (homOfLE (Order.le_succ j))) := by
  have h := source_successor_cofibration (B := B) F j hj
  rw [Native.cofibrations_eq] at h
  exact originalNativeILeft_le_HEP _ h

end PointedCGWH.Spectra.OriginalContinuousSourceApproximation

namespace PointedCGWH.Spectra.OriginalContinuousSourceApproximation

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native HomotopicalAlgebra.EnrichedProjective
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev DNative := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- The original actual successor counit is trivial fibrant for every F without caller
source cofibrancy or continuity assumptions. -/
theorem counit_successor_trivialFibration (F : J ⥤ DNative (I := I)) (j : J) (hj : ¬IsMax j) :
    trivialFibrations (DNative (I := I)) ((counit (B := B) F).app (Order.succ j)) := by
  have h := CategoryTheory.OriginalContinuousApproximation.sourceCounit_successor_mem
    (originalInputStages (I := I) (J := J))
    (Arrow.mk (originalBottomCounit (B := B) (I := I) (J := J)))
    (originalWholeInputFactorization (B := B) (I := I) (J := J)) rfl j hj
  exact h F

/-- The original bottom counit Arrow is the exact original I-Q counit at F_bot. -/
theorem counit_bottom_arrow (F : J ⥤ DNative (I := I)) :
    Arrow.mk ((counit (B := B) F).app ⊥) =
      Arrow.mk ((Replacement.cofibrantReplacementCounit (B := B)).app (F.obj ⊥)) := by
  have h := CategoryTheory.OriginalContinuousApproximation.fullDiagram_bottom
    (originalInputStages (I := I) (J := J))
    (Arrow.mk (originalBottomCounit (B := B) (I := I) (J := J)))
    (originalWholeInputFactorization (B := B) (I := I) (J := J)) rfl
  have h0 : Arrow.mk ((wholeOriginalCounit (B := B) (I := I) (J := J)).app ⊥) =
      (wholeOriginalArrowDiagram (B := B) (I := I) (J := J)).obj ⊥ := by
    change Arrow.mk ((CategoryTheory.OriginalContinuousApproximation.sourceCounit
      (originalInputStages (I := I) (J := J))
      (Arrow.mk (originalBottomCounit (B := B) (I := I) (J := J)))
      (originalWholeInputFactorization (B := B) (I := I) (J := J)) rfl).app ⊥) = _
    rw [CategoryTheory.OriginalContinuousApproximation.sourceCounit_app]
    exact Arrow.arrow_mk_comp_eqToHom _ _
  exact congrArg (fun a : Arrow ((J ⥤ DNative (I := I)) ⥤ DNative (I := I)) =>
    ((CategoryTheory.evaluation (J ⥤ DNative (I := I)) (DNative (I := I))).obj F).mapArrow.obj a)
    (h0.trans h)

end PointedCGWH.Spectra.OriginalContinuousSourceApproximation

namespace PointedCGWH.Spectra.OriginalContinuousSourceApproximation

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native HomotopicalAlgebra.EnrichedProjective
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.Spectra.NativeOmegaWeakClosure
open scoped CGWH.modelCategory MonoidalClosed

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev NativeSpace := EnrichedFunctorCat PointedCGWH.{u, v} I

omit B in
private theorem map_le_of_target_eq {D : Type uC} [Category.{vC} D]
    {K : Type w} [Preorder K] (F : K ⥤ D) {i j k : K} (hij : i ≤ j) (hik : i ≤ k)
    (e : j = k) : Arrow.mk (F.map (homOfLE hij)) = Arrow.mk (F.map (homOfLE hik)) := by
  cases e
  rfl

/-- Every original source counit is level weak for an actual continuous native HEP diagram.
No desired weak counit is a premise at a limit and no q-cofibrancy of F is required. -/
theorem counit_levelWeak (F : J ⥤ NativeSpace (I := I)) [F.IsWellOrderContinuous]
    (hF : ∀ j : J, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j)))) (j : J) :
    weakEquivalences (NativeSpace (I := I)) ((counit (B := B) F).app j) := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl : j = ⊥ := by simpa using hj
    rw [← (weakEquivalences (NativeSpace (I := I))).arrow_mk_mem_toSet_iff,
      counit_bottom_arrow, (weakEquivalences (NativeSpace (I := I))).arrow_mk_mem_toSet_iff]
    exact Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) (F.obj ⊥)
  | succ j hj _ih => exact (counit_successor_trivialFibration (B := B) F j hj).2
  | isSuccLimit m hm ih =>
    let Q := source (B := B) F
    let : Q.IsWellOrderContinuous := source_continuous F
    let R := (Set.principalSegIio m).monotone.functor
    let : (R ⋙ Q).IsWellOrderContinuous :=
      inferInstanceAs
        (((Set.principalSegIio m : Set.Iio m ≤i J)).monotone.functor ⋙ Q).IsWellOrderContinuous
    let : (R ⋙ F).IsWellOrderContinuous :=
      inferInstanceAs
        (((Set.principalSegIio m : Set.Iio m ≤i J)).monotone.functor ⋙ F).IsWellOrderContinuous
    let : Nonempty (Set.Iio m) := ⟨⟨⊥, hm.bot_lt⟩⟩
    let : OrderBot (Set.Iio m) :=
      { bot := ⟨⊥, hm.bot_lt⟩
        bot_le := fun k => show (⊥ : J) ≤ k.1 from bot_le }
    let qC : Cocone (R ⋙ Q) := (Set.principalSegIio m).cocone Q
    let fC : Cocone (R ⋙ F) := (Set.principalSegIio m).cocone F
    have hQSucc : ∀ k : Set.Iio m, ¬IsMax k →
        PointedCGWH.EnrichedBasedHomotopyExtension.property
          ((R ⋙ Q).map (homOfLE (Order.le_succ k))) := by
      intro k hk
      have hks : Order.succ k.1 < m := (Order.IsSuccLimit.succ_lt_iff hm).mpr k.2
      have hkm : ¬IsMax k.1 := not_isMax_of_lt k.2
      have he : (Order.succ k).1 = Order.succ k.1 := coe_succ_of_mem hks
      have hArrow : Arrow.mk ((R ⋙ Q).map (homOfLE (Order.le_succ k))) =
          Arrow.mk (Q.map (homOfLE (Order.le_succ k.1))) := by
        exact map_le_of_target_eq Q (leOfHom (R.map (homOfLE (Order.le_succ k))))
          (Order.le_succ k.1) he
      rw [← PointedCGWH.EnrichedBasedHomotopyExtension.property.arrow_mk_mem_toSet_iff,
        hArrow, PointedCGWH.EnrichedBasedHomotopyExtension.property.arrow_mk_mem_toSet_iff]
      exact source_successor_HEP (B := B) F k.1 hkm
    have hFSucc : ∀ k : Set.Iio m, ¬IsMax k →
        PointedCGWH.EnrichedBasedHomotopyExtension.property
          ((R ⋙ F).map (homOfLE (Order.le_succ k))) := by
      intro k hk
      have hkm : ¬IsMax k.1 := not_isMax_of_lt k.2
      have hks : Order.succ k.1 < m := (Order.IsSuccLimit.succ_lt_iff hm).mpr k.2
      have he : (Order.succ k).1 = Order.succ k.1 := coe_succ_of_mem hks
      have hArrow : Arrow.mk ((R ⋙ F).map (homOfLE (Order.le_succ k))) =
          Arrow.mk (F.map (homOfLE (Order.le_succ k.1))) := by
        exact map_le_of_target_eq F (leOfHom (R.map (homOfLE (Order.le_succ k))))
          (Order.le_succ k.1) he
      rw [← PointedCGWH.EnrichedBasedHomotopyExtension.property.arrow_mk_mem_toSet_iff,
        hArrow, PointedCGWH.EnrichedBasedHomotopyExtension.property.arrow_mk_mem_toSet_iff]
      exact hF k.1 hkm
    exact originalHEPOrdinal_levelWeak_comparison qC fC
      (sourceLimitIsColimit F m hm) (F.isColimitOfIsWellOrderContinuous m hm)
      hQSucc hFSucc (Functor.whiskerLeft R (counit (B := B) F))
      (fun k => ih k.1 k.2) ((counit (B := B) F).app m)
      (fun k => (counit (B := B) F).naturality (homOfLE k.2.le))

end PointedCGWH.Spectra.OriginalContinuousSourceApproximation
namespace PointedCGWH.Spectra.OriginalContinuousSourceApproximation

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native HomotopicalAlgebra.EnrichedProjective
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.Spectra.NativeOmegaWeakClosure
open scoped CGWH.modelCategory MonoidalClosed

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev OriginalC := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- The actual source counit cocone keeps the caller's same endpoint and every original leg. -/
def sourceComparisonCocone (F : J ⥤ OriginalC (I := I)) (c : Cocone F) :
    Cocone (source (B := B) F) :=
  (Cocone.precompose (counit (B := B) F)).obj c

/-- The exact chosen source colimit has its actual full original counit comparison. -/
def sourceColimitComparison (F : J ⥤ OriginalC (I := I)) (c : Cocone F)
    (q : Cocone (source (B := B) F)) (hq : IsColimit q) : q.pt ⟶ c.pt :=
  hq.desc (sourceComparisonCocone F c)

/-- Every source-colimit leg retains the complete original counit/caller-cocone square. -/
theorem sourceColimitComparison_ι (F : J ⥤ OriginalC (I := I)) (c : Cocone F)
    (q : Cocone (source (B := B) F)) (hq : IsColimit q) (j : J) :
    q.ι.app j ≫ sourceColimitComparison F c q hq = (counit (B := B) F).app j ≫ c.ι.app j :=
  hq.fac (sourceComparisonCocone F c) j

/-- The same caller-colimit comparison is level weak for original continuous HEP input F.
All original source/target cocones, their IsColimit data and full leg maps are retained. -/
theorem sourceColimitComparison_levelWeak (F : J ⥤ OriginalC (I := I)) [F.IsWellOrderContinuous]
    (hF : ∀ j : J, ¬IsMax j → PointedCGWH.EnrichedBasedHomotopyExtension.property
      (F.map (homOfLE (Order.le_succ j))))
    (c : Cocone F) (hc : IsColimit c)
    (q : Cocone (source (B := B) F)) (hq : IsColimit q) :
    weakEquivalences (OriginalC (I := I)) (sourceColimitComparison F c q hq) := by
  let : (source (B := B) F).IsWellOrderContinuous := source_continuous F
  exact originalHEPOrdinal_levelWeak_comparison q c hq hc
    (source_successor_HEP F) hF (counit (B := B) F) (counit_levelWeak F hF)
    (sourceColimitComparison F c q hq) (sourceColimitComparison_ι F c q hq)

end PointedCGWH.Spectra.OriginalContinuousSourceApproximation
