/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.ChosenFiberExactness

/-!
# Every original integer degree of the orthogonal chosen fiber sequence

The original diagonal connecting maps are normalized into the same original
integer group functors. Both source normalization maps are retained, and the
target is the caller's unchanged chosen fiber group. This constructs the
actual consecutive integer connecting map and its three exact positions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.IntegerFiberSequence

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
  OrthogonalIntegerHomotopy
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerColimitNormalization
open PointedCGWH.Spectra.Orthogonal.ChosenFiberTests

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The original next positive index has exactly the next integer degree,
with the same original canonical starting level. -/
theorem successor_degree (q : ℤ) :
    integerDegree (integerTailLevel q) (integerTailPositiveIndex q + 1) = q + 1 := by
  have h := integerDegree_canonical q
  simp only [integerDegree] at h ⊢
  omega

/-- Both full original normalization functions compare the next diagonal
source to its exact original integer group functor. -/
def successorComparison (q : ℤ) :
    diagonalPiFunctor.{u, v} (integerTailLevel q) (integerTailPositiveIndex q + 1) ≅
      integerPiFunctor (q + 1) :=
  integerComparisonNatIso (integerTailLevel q) (integerTailPositiveIndex q + 1) ≪≫
    eqToIso (congrArg integerPiFunctor (successor_degree q))

/-- Every original native Arrow retains the complete forward degree comparison. -/
theorem successorComparison_hom_naturality (q : ℤ)
    {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    (diagonalPiFunctor (integerTailLevel q) (integerTailPositiveIndex q + 1)).map f ≫
        (successorComparison q).hom.app Y =
      (successorComparison q).hom.app X ≫ (integerPiFunctor (q + 1)).map f :=
  (successorComparison q).hom.naturality f

/-- Every original native Arrow retains the same full inverse comparison. -/
theorem successorComparison_inv_naturality (q : ℤ)
    {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    (integerPiFunctor (q + 1)).map f ≫ (successorComparison q).inv.app Y =
      (successorComparison q).inv.app X ≫
        (diagonalPiFunctor (integerTailLevel q) (integerTailPositiveIndex q + 1)).map f :=
  (successorComparison q).inv.naturality f

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

variable {X Y : OrthogonalCarrier.{u, v}} (p : X ⟶ Y)
  (c : PullbackCone p (Diagrams.zeroTo Y)) (hc : IsLimit c)
  (hp : (NativeK.generators orthogonalFamily).rlp p)

/-- The actual connecting morphism keeps the original next-degree
normalization and the original looped diagonal connecting map. -/
def connectingMap (q : ℤ) :
    (integerPiFunctor (q + 1)).obj Y ⟶ (integerPiFunctor q).obj c.pt :=
  (successorComparison q).inv.app Y ≫
    diagonalConnecting p c hc hp (integerTailLevel q) (integerTailPositiveIndex q)

/-- The forward normalization reconstructs the whole original diagonal
connecting function at every integer degree. -/
theorem connectingMap_reconstruction (q : ℤ) :
    (successorComparison q).hom.app Y ≫ connectingMap p c hc hp q =
      diagonalConnecting p c hc hp (integerTailLevel q) (integerTailPositiveIndex q) := by
  rw [connectingMap, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

omit B in
/-- The inverse normalization retains the original next-degree total
projection and its same original source map. -/
theorem projection_comparison (q : ℤ) :
    (integerPiFunctor (q + 1)).map p ≫ (successorComparison q).inv.app Y =
      (successorComparison q).inv.app X ≫
        (diagonalPiFunctor (integerTailLevel q) (integerTailPositiveIndex q + 1)).map p :=
  successorComparison_inv_naturality q p

include hc hp in
/-- Every integer group of the original total spectrum has its unchanged
chosen-fiber inclusion and original projection as an exact pair. -/
theorem exact_at_total (q : ℤ) :
    Function.MulExact ((integerPiFunctor q).map c.fst).hom
      ((integerPiFunctor q).map p).hom :=
  diagonal_exact_at_total p c hc hp (integerTailLevel q) (integerTailPositiveIndex q)

/-- Every original integer fiber group has the actual next-degree
connecting function and the unchanged total projection as an exact pair. -/
theorem exact_at_fiber (q : ℤ) :
    Function.MulExact (connectingMap p c hc hp q).hom
      ((integerPiFunctor q).map c.fst).hom := by
  let m := integerTailLevel q
  let k := integerTailPositiveIndex q
  apply GrpCat.mulExact_of_iso_ladder ((successorComparison q).app Y).symm
    (Iso.refl _) (Iso.refl _) (connectingMap p c hc hp q)
    ((integerPiFunctor q).map c.fst) (diagonalConnecting p c hc hp m k)
    ((diagonalPiFunctor m k).map c.fst)
  · change connectingMap p c hc hp q ≫ 𝟙 _ =
      (successorComparison q).inv.app Y ≫ diagonalConnecting p c hc hp m k
    rw [Category.comp_id]
    rfl
  · change (integerPiFunctor q).map c.fst ≫ 𝟙 _ =
      𝟙 _ ≫ (diagonalPiFunctor m k).map c.fst
    rw [Category.comp_id, Category.id_comp]
    rfl
  · exact diagonal_exact_at_fiber p c hc hp m k

/-- Every original next-degree base group retains its full original
projection and the same integer connecting map as an exact pair. -/
theorem exact_at_base (q : ℤ) :
    Function.MulExact ((integerPiFunctor (q + 1)).map p).hom
      (connectingMap p c hc hp q).hom := by
  let m := integerTailLevel q
  let k := integerTailPositiveIndex q
  apply GrpCat.mulExact_of_iso_ladder ((successorComparison q).app X).symm
    ((successorComparison q).app Y).symm (Iso.refl _)
    ((integerPiFunctor (q + 1)).map p) (connectingMap p c hc hp q)
    ((diagonalPiFunctor m (k + 1)).map p) (diagonalConnecting p c hc hp m k)
  · exact projection_comparison p q
  · change connectingMap p c hc hp q ≫ 𝟙 _ =
      (successorComparison q).inv.app Y ≫ diagonalConnecting p c hc hp m k
    rw [Category.comp_id]
    rfl
  · exact diagonal_exact_at_base p c hc hp m k

end PointedCGWH.Spectra.Orthogonal.IntegerFiberSequence
