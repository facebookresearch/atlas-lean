/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.CotensorPointMap
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SphereOperatorCategory

/-!
# Underlying sequences of symmetric cotensors

Cotensoring a native symmetric spectrum by a pointed space acts on its underlying symmetric
sequence through the internal Hom functor. Every sequence map is the image under that
internal Hom functor of the original sequence map.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace NativeOmegaPreparation.NativeSymmetricCotensorSequence
/-- The finite-bijection index category used by the symmetric sequence construction. -/
abbrev I := Operad.SmallFinBijGroupoid
attribute [local instance] CategoryTheory.Operad.SmallFinBijGroupoid.instMonoidalCategory
  CategoryTheory.Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

/-- Every original symmetric-sequence index arrow of the actual native cotensor is the unchanged
internal-Hom map of that same original full unit-coefficient operator arrow. -/
theorem map
    (E : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v})
    (M : PointedCGWH.{u, v}) {n k : I} (f : n ⟶ k) :
    ((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj (cotensorObject M E)).functor.map f =
      (ihom M).map (((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj E).functor.map f) := by
  let R := PointedCGWH.copowerRestriction.{u, v, 0} I
  let p : (𝟙_ PointedCGWH.{u, v}) ⟶
      (PointedCGWH.symmetricOperatorObj.{u, v} n ⟶[PointedCGWH.{u, v}]
        PointedCGWH.symmetricOperatorObj.{u, v} k) :=
    PointedCGWH.basedDiscreteIncl.{u, v, 0} (n ⟶ k) f ≫
      PointedCGWH.symmetricIndexInclusion.{u, v}.map (R.obj n) (R.obj k)
  change (eHomEquiv PointedCGWH.{u, v}).symm
      (p ≫ (EnrichedFunctor.cotensor M E.toEnrichedFunctor).map
        (PointedCGWH.symmetricOperatorObj.{u, v} n) (PointedCGWH.symmetricOperatorObj.{u, v} k)) =
    (ihom M).map ((eHomEquiv PointedCGWH.{u, v}).symm
      (p ≫ E.toEnrichedFunctor.map (PointedCGWH.symmetricOperatorObj.{u, v} n)
        (PointedCGWH.symmetricOperatorObj.{u, v} k)))
  exact CotensorPointMap.map M E.toEnrichedFunctor
    (PointedCGWH.symmetricOperatorObj.{u, v} n) (PointedCGWH.symmetricOperatorObj.{u, v} k) p

end NativeOmegaPreparation.NativeSymmetricCotensorSequence
