/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.ChosenFiberHom
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOriginalFiberComparisonBoundary

/-!
# The actual original orthogonal boundary gives the same fiber restriction

The original Q-cofiber boundary and inverse integer suspension Hom
function construct the actual boundary test in every degree. The proved
original comparison boundary identity then identifies its transferred
test with the caller's unchanged first fiber projection. Every entire
source and target action and the same ordinary null classes are retained.
No comparison-test bijectivity or stable model is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.ChosenFiberBoundaryTests

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry
open PointedCGWH.Spectra.Orthogonal.IntegerTargetTests
open PointedCGWH.Spectra.Orthogonal.NegativeHomTests
open PointedCGWH.Spectra.Orthogonal.ChosenFiberHomTests

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := O.{u, v})
private abbrev S := OriginalISuspension.suspension (B := B) (I := O.{u, v})
private abbrev CQ := NativeK.CofiberNullity.cofiberQ (B := B) (I := O.{u, v})

namespace General

variable {P : ObjectProperty (Arrow C.{u, v})}
  (hP : P ≤ ChosenFiberHomTests.fibrantFibrationProperty.{u, v} (B := B))

open PointedCGWH.Spectra.Orthogonal.ChosenFiberHomTests.General

/-- The unchanged original Q-cofiber boundary is the same actual source map. -/
abbrev boundary (F : P.FullSubcategory) : CQ.obj F.obj ⟶ S.obj (Q.obj F.obj.left) :=
  NativeK.OriginalFiberComparison.originalQCofiberBoundary (B := B) F.obj

/-- The actual original boundary and inverse suspension Hom function
retain the same source spectrum in every integer degree. -/
def boundaryTest (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v}) (hE : omegaProperty E) :
    ChosenFiberHomTests.General.totalHom (q + 1) F E → ChosenFiberHomTests.General.cofiberHom q F E :=
  fun g => H.map (boundary F) ≫ (shiftHomEquiv q F.obj.left E hE).symm g

variable (a : ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
  (ha : ∀ F, IsLimit (a F))

/-- The same actual suspended-fiber comparison recovers the unchanged
original Q-suspension of the caller's first projection. -/
theorem comparison_boundary (F : P.FullSubcategory) :
    ChosenFiberHomTests.General.comparison (hP := hP) a ha F ≫ H.map (boundary F) = H.map (S.map (Q.map (a
      F.obj).fst)) :=
  OriginalFiberCofiberGeometry.suspendedComparison_boundary (B := B) (J := O.{u, v})
    a ha (ChosenFiberHomTests.General.asFibrantFibration hP F)

/-- The transferred original integer boundary function is exactly the
caller fiber's unchanged original first projection test. -/
theorem boundaryTest_fiberRestriction (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.totalHom (q + 1) F E) :
    ChosenFiberHomTests.General.comparisonTest (hP := hP) a ha q F E hE (boundaryTest q F E hE g) =
      ChosenFiberHomTests.General.fiberRestriction a (q + 1) F E g := by
  have h : ChosenFiberHomTests.General.comparison (hP := hP) a ha F ≫
      (H.map (boundary F) ≫ (shiftHomEquiv q F.obj.left E hE).symm g) =
    H.map (S.map (Q.map (a F.obj).fst)) ≫ (shiftHomEquiv q F.obj.left E hE).symm g :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ (shiftHomEquiv q F.obj.left E hE).symm g)
        (comparison_boundary (hP := hP) a ha F))
  change shiftHomEquiv q (a F.obj).pt E hE
      (ChosenFiberHomTests.General.comparison (hP := hP) a ha F ≫
        (H.map (boundary F) ≫ (shiftHomEquiv q F.obj.left E hE).symm g)) =
    H.map (a F.obj).fst ≫ g
  rw [h, shiftHomEquiv_source q (a F.obj).fst E hE, Equiv.apply_symm_apply]

/-- Every complete original source Arrow square acts on the same
boundary and original inverse integer suspension function. -/
theorem boundaryTest_source (q : ℤ) {F G : P.FullSubcategory} (f : F ⟶ G)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.totalHom (q + 1) G E) :
    boundaryTest q F E hE (ChosenFiberHomTests.General.totalSource (q + 1) f E g) =
      ChosenFiberHomTests.General.cofiberSource q f E (boundaryTest q G E hE g) := by
  have hn : CQ.map f.hom ≫ boundary G =
      boundary F ≫ S.map (Q.map f.hom.left) :=
    NativeK.OriginalFiberComparison.originalQCofiberBoundary_naturality (B := B) f.hom
  have h := H.congr_map hn
  simp only [Functor.map_comp] at h
  change H.map (boundary F) ≫ (shiftHomEquiv q F.obj.left E hE).symm (H.map f.hom.left ≫ g) =
    H.map (CQ.map f.hom) ≫ (H.map (boundary G) ≫ (shiftHomEquiv q G.obj.left E hE).symm g)
  rw [shiftHomEquiv_symm_source q f.hom.left E hE]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (shiftHomEquiv q G.obj.left E hE).symm g) h.symm).trans
      (Category.assoc _ _ _))

/-- Every full original target map retains the same integer boundary test. -/
theorem boundaryTest_target (q : ℤ) (F : P.FullSubcategory) {E E' : C.{u, v}} (t : E ⟶ E')
    (hE : omegaProperty E) (hE' : omegaProperty E') (g : ChosenFiberHomTests.General.totalHom (q + 1) F E) :
    boundaryTest q F E' hE' (g ≫ H.map ((integerTarget (q + 1)).map t)) =
      ChosenFiberHomTests.General.cofiberTarget q F t (boundaryTest q F E hE g) := by
  change H.map (boundary F) ≫ (shiftHomEquiv q F.obj.left E' hE').symm
      (g ≫ H.map ((integerTarget (q + 1)).map t)) =
    (H.map (boundary F) ≫ (shiftHomEquiv q F.obj.left E hE).symm g) ≫
      H.map ((integerTarget q).map t)
  rw [shiftHomEquiv_symm_target q F.obj.left t hE hE']
  exact (Category.assoc _ _ _).symm

/-- The original boundary test retains its actual original null class in every degree. -/
theorem boundaryTest_null (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v})
    (hE : omegaProperty E) :
    boundaryTest q F E hE
        (OrdinaryHoCofiberKernel.nullHom F.obj.left ((integerTarget (q + 1)).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj) ((integerTarget q).obj E) := by
  change H.map (boundary F) ≫ (shiftHomEquiv q F.obj.left E hE).symm
      (OrdinaryHoCofiberKernel.nullHom F.obj.left ((integerTarget (q + 1)).obj E)) = _
  rw [shiftHomEquiv_symm_null]
  exact OrdinaryHoCofiberKernel.precomp_nullHom (boundary F)

variable (b : ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
  (hb : ∀ F, IsLimit (b F))

/-- Both complete caller choice functions retain the same transferred
original boundary and unchanged first projection. -/
theorem boundaryTest_choice (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v})
    (hE : omegaProperty E) (g : ChosenFiberHomTests.General.totalHom (q + 1) F E) :
    ChosenFiberHomTests.General.choiceHomEquiv a ha b hb (q + 1) F E
        (ChosenFiberHomTests.General.comparisonTest (hP := hP) b hb q F E hE (boundaryTest q F E hE g)) =
      ChosenFiberHomTests.General.fiberRestriction a (q + 1) F E g := by
  rw [ChosenFiberHomTests.General.comparisonTest_choice (hP := hP), boundaryTest_fiberRestriction (hP := hP)]

/-- The same actual inverse caller choice retains the original
boundary and unchanged first fiber projection as well. -/
theorem boundaryTest_choice_inverse (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v})
    (hE : omegaProperty E) (g : ChosenFiberHomTests.General.totalHom (q + 1) F E) :
    (ChosenFiberHomTests.General.choiceHomEquiv a ha b hb (q + 1) F E).symm
        (ChosenFiberHomTests.General.comparisonTest (hP := hP) a ha q F E hE (boundaryTest q F E hE g)) =
      ChosenFiberHomTests.General.fiberRestriction b (q + 1) F E g := by
  rw [ChosenFiberHomTests.General.comparisonTest_choice_inverse (hP := hP), boundaryTest_fiberRestriction (hP := hP)]

end General

/-- The unchanged original Q-cofiber boundary is the same actual source map. -/
abbrev boundary (F : rightArrows.{u, v}) : CQ.obj F.obj ⟶ S.obj (Q.obj F.obj.left) :=
  General.boundary
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (F := F)

/-- The actual original boundary and inverse suspension Hom function
retain the same source spectrum in every integer degree. -/
def boundaryTest (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v}) (hE : omegaProperty E) :
    totalHom (q + 1) F E → cofiberHom q F E :=
  General.boundaryTest
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)

variable (a : ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
  (ha : ∀ F, IsLimit (a F))

/-- The same actual suspended-fiber comparison recovers the unchanged
original Q-suspension of the caller's first projection. -/
theorem comparison_boundary (F : rightArrows.{u, v}) :
    comparison a ha F ≫ H.map (boundary F) = H.map (S.map (Q.map (a F.obj).fst)) :=
  General.comparison_boundary
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (a := a)
    (ha := ha)
    (F := F)

/-- The transferred original integer boundary function is exactly the
caller fiber's unchanged original first projection test. -/
theorem boundaryTest_fiberRestriction (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) (g : totalHom (q + 1) F E) :
    comparisonTest a ha q F E hE (boundaryTest q F E hE g) =
      fiberRestriction a (q + 1) F E g :=
  General.boundaryTest_fiberRestriction
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

/-- Every complete original source Arrow square acts on the same
boundary and original inverse integer suspension function. -/
theorem boundaryTest_source (q : ℤ) {F G : rightArrows.{u, v}} (f : F ⟶ G)
    (E : C.{u, v}) (hE : omegaProperty E) (g : totalHom (q + 1) G E) :
    boundaryTest q F E hE (totalSource (q + 1) f E g) =
      cofiberSource q f E (boundaryTest q G E hE g) :=
  General.boundaryTest_source
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (G := G)
    (f := f)
    (E := E)
    (hE := hE)
    (g := g)

/-- Every full original target map retains the same integer boundary test. -/
theorem boundaryTest_target (q : ℤ) (F : rightArrows.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E')
    (hE : omegaProperty E) (hE' : omegaProperty E') (g : totalHom (q + 1) F E) :
    boundaryTest q F E' hE' (g ≫ H.map ((integerTarget (q + 1)).map t)) =
      cofiberTarget q F t (boundaryTest q F E hE g) :=
  General.boundaryTest_target
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (E := E)
    (E' := E')
    (t := t)
    (hE := hE)
    (hE' := hE')
    (g := g)

/-- The original boundary test retains its actual original null class in every degree. -/
theorem boundaryTest_null (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v})
    (hE : omegaProperty E) :
    boundaryTest q F E hE
        (OrdinaryHoCofiberKernel.nullHom F.obj.left ((integerTarget (q + 1)).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj) ((integerTarget q).obj E) :=
  General.boundaryTest_null
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)

variable (b : ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
  (hb : ∀ F, IsLimit (b F))

/-- Both complete caller choice functions retain the same transferred
original boundary and unchanged first projection. -/
theorem boundaryTest_choice (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v})
    (hE : omegaProperty E) (g : totalHom (q + 1) F E) :
    choiceHomEquiv a ha b hb (q + 1) F E
        (comparisonTest b hb q F E hE (boundaryTest q F E hE g)) =
      fiberRestriction a (q + 1) F E g :=
  General.boundaryTest_choice
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

/-- The same actual inverse caller choice retains the original
boundary and unchanged first fiber projection as well. -/
theorem boundaryTest_choice_inverse (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v})
    (hE : omegaProperty E) (g : totalHom (q + 1) F E) :
    (choiceHomEquiv a ha b hb (q + 1) F E).symm
        (comparisonTest a ha q F E hE (boundaryTest q F E hE g)) =
      fiberRestriction b (q + 1) F E g :=
  General.boundaryTest_choice_inverse
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

end PointedCGWH.Spectra.Orthogonal.ChosenFiberBoundaryTests
