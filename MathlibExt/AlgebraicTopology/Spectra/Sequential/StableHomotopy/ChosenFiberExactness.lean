/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.StableHomotopy.ChosenFiberLevelSequence
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.IntegerStablePi
import MathlibExt.Algebra.Category.Grp.FilteredColimitExactness

/-!
# The original integer stable homotopy maps of a chosen sequential fiber

The three diagrams are the existing varying-degree diagrams of the actual
fiber, total spectrum and base spectrum. Their maps are induced by the
original chosen total projection and original spectrum map. The original
level Serre exactness passes to the same chosen group quotient colimits.

This proves exactness at the total spectrum in every integer degree. The
connecting maps and the other two stable exact pairs require the full
ordered loop comparison and are separate results.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy

open CategoryTheory.SequentialSpectrum.EnrichedIndex (degree)
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams (zeroTo)
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The original changing-degree maps of a chosen fiber sequence are stagewise exact. -/
theorem chosenFiberDiagonal_exact_at_total
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y)
    (c : PullbackCone p (zeroTo Y)) (hc : IsLimit c)
    (hp : ∀ n : ℕ, fibrations PointedCGWH.{u, v} (levelMap p n))
    (m k n : ℕ) :
    Function.MulExact (((diagonalDiagramFunctor m k).map c.fst).app n).hom
      (((diagonalDiagramFunctor m k).map p).app n).hom := by
  change Function.MulExact
    (PointedCGWH.piNPositiveMap (k + n) (levelMap c.fst (m + n))).hom
    (PointedCGWH.piNPositiveMap (k + n) (levelMap p (m + n))).hom
  rw [show ⇑(PointedCGWH.piNPositiveMap (k + n) (levelMap c.fst (m + n))).hom =
      PointedCGWH.piNMap (k + n + 1) (levelMap c.fst (m + n)) from
    funext (PointedCGWH.piNPositiveMap_apply (k + n) (levelMap c.fst (m + n))),
    show ⇑(PointedCGWH.piNPositiveMap (k + n) (levelMap p (m + n))).hom =
      PointedCGWH.piNMap (k + n + 1) (levelMap p (m + n)) from
    funext (PointedCGWH.piNPositiveMap_apply (k + n) (levelMap p (m + n)))]
  exact chosenFiberLevelPositiveExact_at_total p c hc
    (degree PointedCGWH.sphereOne (m + n)) (hp (m + n)) (k + n)

/-- The unchanged original diagonal quotient maps are exact at the total quotient. -/
theorem chosenFiberDiagonalColimit_exact_at_total
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y)
    (c : PullbackCone p (zeroTo Y)) (hc : IsLimit c)
    (hp : ∀ n : ℕ, fibrations PointedCGWH.{u, v} (levelMap p n)) (m k : ℕ) :
    Function.MulExact
      (GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m k).map c.fst)).hom
      (GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m k).map p)).hom :=
  GrpCat.FilteredColimits.colimitMap_mulExact _ _
    (chosenFiberDiagonal_exact_at_total p c hc hp m k)

/-- Every actual integer stable homotopy sequence is exact at its original total spectrum. -/
theorem integerStablePi_chosenFiber_exact_at_total
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y)
    (c : PullbackCone p (zeroTo Y)) (hc : IsLimit c)
    (hp : ∀ n : ℕ, fibrations PointedCGWH.{u, v} (levelMap p n)) (q : ℤ) :
    Function.MulExact ((integerStablePiFunctor q).map c.fst).hom
      ((integerStablePiFunctor q).map p).hom :=
  chosenFiberDiagonalColimit_exact_at_total p c hc hp
    (integerTailLevel q) (integerTailPositiveIndex q)

end PointedCGWH.SequentialSpectrum.StableHomotopy
