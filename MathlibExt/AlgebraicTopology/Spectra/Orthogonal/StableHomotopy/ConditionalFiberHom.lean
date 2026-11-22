/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.FiberInclusionImage

/-!
# Conditional inverse of the actual orthogonal fiber comparison tests

The explicit premise is Hom bijectivity of the unchanged original
suspended-fiber comparison. It retains every caller limit family, full
paired K-right arrow and actual native Omega target. The premise does
not supply a model, replacement, class equation or new comparison map.

The equivalences below have exactly the already proved comparison test
as their forward function. Their inverses retain every original source,
target and caller choice map. The genuine comparison theorem is still
needed before these conditional helpers give unconditional fiber tests.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.ConditionalFiberHom

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.IntegerTargetTests
open PointedCGWH.Spectra.Orthogonal.NegativeHomTests
open PointedCGWH.Spectra.Orthogonal.ChosenFiberHomTests
open PointedCGWH.Spectra.Orthogonal.ChosenFiberBoundaryTests

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}
private abbrev FiberChoices :=
  ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev CQ := NativeK.CofiberNullity.cofiberQ (B := B) (I := O.{u, v})

namespace General

variable {P : ObjectProperty (Arrow C.{u, v})}
  (hP : P ≤ ChosenFiberHomTests.fibrantFibrationProperty.{u, v} (B := B))

open PointedCGWH.Spectra.Orthogonal.ChosenFiberHomTests.General
open PointedCGWH.Spectra.Orthogonal.ChosenFiberBoundaryTests.General
open PointedCGWH.Spectra.Orthogonal.FiberInclusionImage.General

/-- Exactly the pending original comparison Hom theorem, on every
actual caller limit family and every full native K-right arrow. -/
def ComparisonHomBijections : Prop :=
  ∀ (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))
    (F : P.FullSubcategory) (E : C.{u, v}), omegaProperty E →
      Function.Bijective
        (fun g : H.obj (CQ.obj F.obj) ⟶ H.obj E => ChosenFiberHomTests.General.comparison (hP := hP) a ha F ≫ g)

variable (hComparison : ComparisonHomBijections.{u, v} (hP := hP) (B := B))
  (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))

/-- Every integer target is tested by the same original comparison. -/
theorem comparisonPrecomposition_bijective
    (hComparison : ComparisonHomBijections.{u, v} (hP := hP) (B := B))
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F)) (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) :
    Function.Bijective (ChosenFiberHomTests.General.comparisonPrecomposition (hP := hP) a ha q F E) :=
  hComparison a ha F ((integerTarget q).obj E) (integerTarget_isOmega q E hE)

/-- The actual original test becomes an equivalence using precisely
its original comparison and the proved integer suspension equivalence. -/
def cofiberToFiberHomEquiv (hComparison : ComparisonHomBijections.{u, v} (hP := hP) (B := B))
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F)) (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) :
    ChosenFiberHomTests.General.cofiberHom q F E ≃ ChosenFiberHomTests.General.fiberHom a (q + 1) F E :=
  (Equiv.ofBijective (ChosenFiberHomTests.General.comparisonPrecomposition (hP := hP) a ha q F E)
    (comparisonPrecomposition_bijective (hP := hP) hComparison a ha q F E hE)).trans
      (shiftHomEquiv q (a F.obj).pt E hE)

/-- The whole forward function is the unchanged original comparison test. -/
theorem cofiberToFiberHomEquiv_apply (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.cofiberHom q F E) :
    cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE g =
      ChosenFiberHomTests.General.comparisonTest (hP := hP) a ha q F E hE g := rfl

/-- The full comparison test is bijective in every integer degree. -/
theorem comparisonTest_bijective (hComparison : ComparisonHomBijections.{u, v} (hP := hP) (B := B))
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F)) (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) :
    Function.Bijective (ChosenFiberHomTests.General.comparisonTest (hP := hP) a ha q F E hE) :=
  (cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE).bijective

/-- The inverse is the unique original cofiber preimage of the same test. -/
theorem cofiberToFiberHomEquiv_symm_spec (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.fiberHom a (q + 1) F E) :
    ChosenFiberHomTests.General.comparisonTest (hP := hP) a ha q F E hE
        ((cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE).symm g) = g :=
  (cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE).apply_symm_apply g

/-- The same inverse recovers every original cofiber test. -/
theorem cofiberToFiberHomEquiv_symm_comparisonTest (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.cofiberHom q F E) :
    (cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE).symm
        (ChosenFiberHomTests.General.comparisonTest (hP := hP) a ha q F E hE g) = g :=
  (cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE).symm_apply_apply g

/-- The complete forward function preserves the actual original null class. -/
theorem cofiberToFiberHomEquiv_null (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) :
    cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE
        (OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj) ((integerTarget q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((integerTarget (q + 1)).obj E) :=
  ChosenFiberHomTests.General.comparisonTest_null (hP := hP) a ha q F E hE

/-- The complete inverse preserves the same original null class. -/
theorem cofiberToFiberHomEquiv_symm_null (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) :
    (cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE).symm
        (OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((integerTarget (q + 1)).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj) ((integerTarget q).obj E) := by
  apply (cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE).injective
  rw [Equiv.apply_symm_apply, cofiberToFiberHomEquiv_null (hP := hP)]

/-- Every complete original K-right source square retains its actual Hom function. -/
theorem cofiberToFiberHomEquiv_source (q : ℤ) {F G : P.FullSubcategory} (f : F ⟶ G)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.cofiberHom q G E) :
    cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE (ChosenFiberHomTests.General.cofiberSource q f E g) =
      ChosenFiberHomTests.General.fiberSource a ha (q + 1) f E
        (cofiberToFiberHomEquiv (hP := hP) hComparison a ha q G E hE g) :=
  ChosenFiberHomTests.General.comparisonTest_source (hP := hP) a ha q f E hE g

/-- Its full inverse retains the same original chosen-fiber source map. -/
theorem cofiberToFiberHomEquiv_symm_source (q : ℤ) {F G : P.FullSubcategory} (f : F ⟶ G)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.fiberHom a (q + 1) G E) :
    (cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE).symm
        (ChosenFiberHomTests.General.fiberSource a ha (q + 1) f E g) =
      ChosenFiberHomTests.General.cofiberSource q f E ((cofiberToFiberHomEquiv (hP := hP) hComparison a ha q G E
        hE).symm g) := by
  apply (cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE).injective
  rw [Equiv.apply_symm_apply, cofiberToFiberHomEquiv_source (hP := hP), Equiv.apply_symm_apply]

/-- Every actual integer target map retains the entire forward comparison square. -/
theorem cofiberToFiberHomEquiv_target (q : ℤ) (F : P.FullSubcategory)
    {E E' : C.{u, v}} (t : E ⟶ E') (hE : omegaProperty E) (hE' : omegaProperty E')
    (g : ChosenFiberHomTests.General.cofiberHom q F E) :
    cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E' hE' (ChosenFiberHomTests.General.cofiberTarget q F t g) =
      ChosenFiberHomTests.General.fiberTarget a (q + 1) F t (cofiberToFiberHomEquiv (hP := hP) hComparison a ha
        q F E hE g) :=
  ChosenFiberHomTests.General.comparisonTest_target (hP := hP) a ha q F t hE hE' g

/-- The inverse retains both complete original integer target functor actions. -/
theorem cofiberToFiberHomEquiv_symm_target (q : ℤ) (F : P.FullSubcategory)
    {E E' : C.{u, v}} (t : E ⟶ E') (hE : omegaProperty E) (hE' : omegaProperty E')
    (g : ChosenFiberHomTests.General.fiberHom a (q + 1) F E) :
    (cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E' hE').symm
        (ChosenFiberHomTests.General.fiberTarget a (q + 1) F t g) =
      ChosenFiberHomTests.General.cofiberTarget q F t ((cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E
        hE).symm g) := by
  apply (cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E' hE').injective
  rw [Equiv.apply_symm_apply,
    cofiberToFiberHomEquiv_target (hP := hP) hComparison a ha q F t hE hE', Equiv.apply_symm_apply]

/-- The actual original boundary is sent to the unchanged caller first projection. -/
theorem cofiberToFiberHomEquiv_boundaryTest (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.totalHom (q + 1) F E) :
    cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE (ChosenFiberBoundaryTests.General.boundaryTest q
      F E hE g) =
      ChosenFiberHomTests.General.fiberRestriction a (q + 1) F E g :=
  ChosenFiberBoundaryTests.General.boundaryTest_fiberRestriction (hP := hP) a ha q F E hE g

/-- Its same inverse recovers the unchanged original cofiber boundary test. -/
theorem cofiberToFiberHomEquiv_symm_fiberRestriction (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.totalHom (q + 1) F E) :
    (cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE).symm
        (ChosenFiberHomTests.General.fiberRestriction a (q + 1) F E g) =
          ChosenFiberBoundaryTests.General.boundaryTest q F E hE g := by
  rw [← cofiberToFiberHomEquiv_boundaryTest (hP := hP) hComparison a ha q F E hE g,
    Equiv.symm_apply_apply]

variable (b : FiberChoices.{u, v}) (hb : ∀ F, IsLimit (b F))

/-- Both complete caller fiber choices retain the same original forward comparison. -/
theorem cofiberToFiberHomEquiv_choice (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.cofiberHom q F E) :
    ChosenFiberHomTests.General.choiceHomEquiv a ha b hb (q + 1) F E
        (cofiberToFiberHomEquiv (hP := hP) hComparison b hb q F E hE g) =
      cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE g :=
  ChosenFiberHomTests.General.comparisonTest_choice (hP := hP) a ha b hb q F E hE g

/-- The full inverse retains the original forward caller choice Hom function. -/
theorem cofiberToFiberHomEquiv_symm_choice (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.fiberHom b (q + 1) F E) :
    (cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE).symm
        (ChosenFiberHomTests.General.choiceHomEquiv a ha b hb (q + 1) F E g) =
      (cofiberToFiberHomEquiv (hP := hP) hComparison b hb q F E hE).symm g := by
  apply (cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE).injective
  rw [Equiv.apply_symm_apply, ← cofiberToFiberHomEquiv_choice (hP := hP) hComparison a ha b hb,
    Equiv.apply_symm_apply]

/-- The same forward comparison retains the actual inverse caller fiber choice map. -/
theorem cofiberToFiberHomEquiv_choice_inverse (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.cofiberHom q F E) :
    (ChosenFiberHomTests.General.choiceHomEquiv a ha b hb (q + 1) F E).symm
        (cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE g) =
      cofiberToFiberHomEquiv (hP := hP) hComparison b hb q F E hE g :=
  ChosenFiberHomTests.General.comparisonTest_choice_inverse (hP := hP) a ha b hb q F E hE g

/-- The inverse comparison also retains the full inverse caller fiber choice function. -/
theorem cofiberToFiberHomEquiv_symm_choice_inverse (q : ℤ) (F : P.FullSubcategory)
    (E : C.{u, v}) (hE : omegaProperty E) (g : ChosenFiberHomTests.General.fiberHom a (q + 1) F E) :
    (cofiberToFiberHomEquiv (hP := hP) hComparison b hb q F E hE).symm
        ((ChosenFiberHomTests.General.choiceHomEquiv a ha b hb (q + 1) F E).symm g) =
      (cofiberToFiberHomEquiv (hP := hP) hComparison a ha q F E hE).symm g := by
  apply (cofiberToFiberHomEquiv (hP := hP) hComparison b hb q F E hE).injective
  rw [Equiv.apply_symm_apply,
    ← cofiberToFiberHomEquiv_choice_inverse (hP := hP) hComparison a ha b hb, Equiv.apply_symm_apply]

end General

/-- Exactly the pending original comparison Hom theorem, on every
actual caller limit family and every full native K-right arrow. -/
def ComparisonHomBijections : Prop :=
  General.ComparisonHomBijections
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)

variable (hComparison : ComparisonHomBijections.{u, v} (B := B))
  (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F))

/-- Every integer target is tested by the same original comparison. -/
theorem comparisonPrecomposition_bijective
    (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F)) (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) :
    Function.Bijective (comparisonPrecomposition a ha q F E) :=
  General.comparisonPrecomposition_bijective
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)

/-- The actual original test becomes an equivalence using precisely
its original comparison and the proved integer suspension equivalence. -/
def cofiberToFiberHomEquiv (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F)) (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) :
    cofiberHom q F E ≃ fiberHom a (q + 1) F E :=
  General.cofiberToFiberHomEquiv
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)

/-- The whole forward function is the unchanged original comparison test. -/
theorem cofiberToFiberHomEquiv_apply (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) (g : cofiberHom q F E) :
    cofiberToFiberHomEquiv hComparison a ha q F E hE g =
      comparisonTest a ha q F E hE g :=
  General.cofiberToFiberHomEquiv_apply
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

/-- The full comparison test is bijective in every integer degree. -/
theorem comparisonTest_bijective (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F)) (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) :
    Function.Bijective (comparisonTest a ha q F E hE) :=
  General.comparisonTest_bijective
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)

/-- The inverse is the unique original cofiber preimage of the same test. -/
theorem cofiberToFiberHomEquiv_symm_spec (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) (g : fiberHom a (q + 1) F E) :
    comparisonTest a ha q F E hE
        ((cofiberToFiberHomEquiv hComparison a ha q F E hE).symm g) = g :=
  General.cofiberToFiberHomEquiv_symm_spec
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

/-- The same inverse recovers every original cofiber test. -/
theorem cofiberToFiberHomEquiv_symm_comparisonTest (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) (g : cofiberHom q F E) :
    (cofiberToFiberHomEquiv hComparison a ha q F E hE).symm
        (comparisonTest a ha q F E hE g) = g :=
  General.cofiberToFiberHomEquiv_symm_comparisonTest
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

/-- The complete forward function preserves the actual original null class. -/
theorem cofiberToFiberHomEquiv_null (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) :
    cofiberToFiberHomEquiv hComparison a ha q F E hE
        (OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj) ((integerTarget q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((integerTarget (q + 1)).obj E) :=
  General.cofiberToFiberHomEquiv_null
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)

/-- The complete inverse preserves the same original null class. -/
theorem cofiberToFiberHomEquiv_symm_null (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) :
    (cofiberToFiberHomEquiv hComparison a ha q F E hE).symm
        (OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((integerTarget (q + 1)).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj) ((integerTarget q).obj E) :=
  General.cofiberToFiberHomEquiv_symm_null
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)

/-- Every complete original K-right source square retains its actual Hom function. -/
theorem cofiberToFiberHomEquiv_source (q : ℤ) {F G : rightArrows.{u, v}} (f : F ⟶ G)
    (E : C.{u, v}) (hE : omegaProperty E) (g : cofiberHom q G E) :
    cofiberToFiberHomEquiv hComparison a ha q F E hE (cofiberSource q f E g) =
      fiberSource a ha (q + 1) f E
        (cofiberToFiberHomEquiv hComparison a ha q G E hE g) :=
  General.cofiberToFiberHomEquiv_source
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (G := G)
    (f := f)
    (E := E)
    (hE := hE)
    (g := g)

/-- Its full inverse retains the same original chosen-fiber source map. -/
theorem cofiberToFiberHomEquiv_symm_source (q : ℤ) {F G : rightArrows.{u, v}} (f : F ⟶ G)
    (E : C.{u, v}) (hE : omegaProperty E) (g : fiberHom a (q + 1) G E) :
    (cofiberToFiberHomEquiv hComparison a ha q F E hE).symm
        (fiberSource a ha (q + 1) f E g) =
      cofiberSource q f E ((cofiberToFiberHomEquiv hComparison a ha q G E hE).symm g) :=
  General.cofiberToFiberHomEquiv_symm_source
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (G := G)
    (f := f)
    (E := E)
    (hE := hE)
    (g := g)

/-- Every actual integer target map retains the entire forward comparison square. -/
theorem cofiberToFiberHomEquiv_target (q : ℤ) (F : rightArrows.{u, v})
    {E E' : C.{u, v}} (t : E ⟶ E') (hE : omegaProperty E) (hE' : omegaProperty E')
    (g : cofiberHom q F E) :
    cofiberToFiberHomEquiv hComparison a ha q F E' hE' (cofiberTarget q F t g) =
      fiberTarget a (q + 1) F t (cofiberToFiberHomEquiv hComparison a ha q F E hE g) :=
  General.cofiberToFiberHomEquiv_target
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (E' := E')
    (t := t)
    (hE := hE)
    (hE' := hE')
    (g := g)

/-- The inverse retains both complete original integer target functor actions. -/
theorem cofiberToFiberHomEquiv_symm_target (q : ℤ) (F : rightArrows.{u, v})
    {E E' : C.{u, v}} (t : E ⟶ E') (hE : omegaProperty E) (hE' : omegaProperty E')
    (g : fiberHom a (q + 1) F E) :
    (cofiberToFiberHomEquiv hComparison a ha q F E' hE').symm
        (fiberTarget a (q + 1) F t g) =
      cofiberTarget q F t ((cofiberToFiberHomEquiv hComparison a ha q F E hE).symm g) :=
  General.cofiberToFiberHomEquiv_symm_target
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (E' := E')
    (t := t)
    (hE := hE)
    (hE' := hE')
    (g := g)

/-- The actual original boundary is sent to the unchanged caller first projection. -/
theorem cofiberToFiberHomEquiv_boundaryTest (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) (g : totalHom (q + 1) F E) :
    cofiberToFiberHomEquiv hComparison a ha q F E hE (boundaryTest q F E hE g) =
      fiberRestriction a (q + 1) F E g :=
  General.cofiberToFiberHomEquiv_boundaryTest
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

/-- Its same inverse recovers the unchanged original cofiber boundary test. -/
theorem cofiberToFiberHomEquiv_symm_fiberRestriction (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) (g : totalHom (q + 1) F E) :
    (cofiberToFiberHomEquiv hComparison a ha q F E hE).symm
        (fiberRestriction a (q + 1) F E g) = boundaryTest q F E hE g :=
  General.cofiberToFiberHomEquiv_symm_fiberRestriction
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

variable (b : FiberChoices.{u, v}) (hb : ∀ F, IsLimit (b F))

/-- Both complete caller fiber choices retain the same original forward comparison. -/
theorem cofiberToFiberHomEquiv_choice (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) (g : cofiberHom q F E) :
    choiceHomEquiv a ha b hb (q + 1) F E
        (cofiberToFiberHomEquiv hComparison b hb q F E hE g) =
      cofiberToFiberHomEquiv hComparison a ha q F E hE g :=
  General.cofiberToFiberHomEquiv_choice
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

/-- The full inverse retains the original forward caller choice Hom function. -/
theorem cofiberToFiberHomEquiv_symm_choice (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) (g : fiberHom b (q + 1) F E) :
    (cofiberToFiberHomEquiv hComparison a ha q F E hE).symm
        (choiceHomEquiv a ha b hb (q + 1) F E g) =
      (cofiberToFiberHomEquiv hComparison b hb q F E hE).symm g :=
  General.cofiberToFiberHomEquiv_symm_choice
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

/-- The same forward comparison retains the actual inverse caller fiber choice map. -/
theorem cofiberToFiberHomEquiv_choice_inverse (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) (g : cofiberHom q F E) :
    (choiceHomEquiv a ha b hb (q + 1) F E).symm
        (cofiberToFiberHomEquiv hComparison a ha q F E hE g) =
      cofiberToFiberHomEquiv hComparison b hb q F E hE g :=
  General.cofiberToFiberHomEquiv_choice_inverse
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

/-- The inverse comparison also retains the full inverse caller fiber choice function. -/
theorem cofiberToFiberHomEquiv_symm_choice_inverse (q : ℤ) (F : rightArrows.{u, v})
    (E : C.{u, v}) (hE : omegaProperty E) (g : fiberHom a (q + 1) F E) :
    (cofiberToFiberHomEquiv hComparison b hb q F E hE).symm
        ((choiceHomEquiv a ha b hb (q + 1) F E).symm g) =
      (cofiberToFiberHomEquiv hComparison a ha q F E hE).symm g :=
  General.cofiberToFiberHomEquiv_symm_choice_inverse
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (hComparison := hComparison)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

end PointedCGWH.Spectra.Orthogonal.ConditionalFiberHom
