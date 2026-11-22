/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.FiniteCoproductIntegerPi

/-!
# The actual finite coproduct-to-product integer stable equivalence

The original diagonal/zero comparison from the actual finite coproduct
to the same chosen finite product induces an Iso in every integer degree.
The entire forward map is identified with the proved original finite
coproduct coordinate equivalence through the actual product comparison.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.FiniteAdditivityGeometry

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.FiniteProductGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.FiniteCoproductIntegerPiGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  Diagrams.nativeHasZeroObject HasZeroObject.zeroMorphismsOfZeroObject

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {n : ℕ} (X : Fin n → PointedCGWH.SequentialSpectrum.{u, v}) [HasProduct X]

/-- The actual finite diagonal/zero comparison is the original tuple of whole coproduct coordinate maps. -/
def comparison : (∐ X) ⟶ ∏ᶜ X :=
  Pi.lift (fun i => FiniteCoproductIntegerPiGeometry.coordinate X i)

omit B in
/-- Every original product projection of the full comparison is the same original coproduct coordinate. -/
theorem comparison_projection (i : Fin n) :
    comparison X ≫ Pi.π X i = FiniteCoproductIntegerPiGeometry.coordinate X i := Pi.lift_comp_π _ _

/-- The whole original integer map is the finite coproduct coordinate Iso followed by the product Iso inverse. -/
def integerComparisonIso (q : ℤ) (hX : ∀ i, IsCofibrant (X i)) :
    (integerStablePiFunctor q).obj (∐ X) ≅ (integerStablePiFunctor q).obj (∏ᶜ X) := by
  let e : (integerStablePiFunctor q).obj (∐ X) ≅
      GrpCat.of (∀ i, (integerStablePiFunctor q).obj (X i)) :=
    (FiniteCoproductIntegerPiGeometry.equiv (B := B) q n X hX).toGrpIso
  exact e ≪≫ (PointedCGWH.SequentialSpectrum.MappingTelescope.FiniteProductGeometry.comparisonIso X q).symm

private theorem integerComparisonIso_cancel (q : ℤ) (hX : ∀ i, IsCofibrant (X i)) :
    (integerComparisonIso X q hX).hom ≫
      (PointedCGWH.SequentialSpectrum.MappingTelescope.FiniteProductGeometry.comparisonIso X q).hom =
    (show (integerStablePiFunctor q).obj (∐ X) ≅
      GrpCat.of (∀ i, (integerStablePiFunctor q).obj (X i)) from
        (FiniteCoproductIntegerPiGeometry.equiv (B := B) q n X hX).toGrpIso).hom := by
  simp only [integerComparisonIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The complete original comparison Iso hom is exactly the map of the actual diagonal/zero spectrum comparison. -/
theorem integerComparisonIso_hom (q : ℤ) (hX : ∀ i, IsCofibrant (X i)) :
    (integerComparisonIso X q hX).hom = (integerStablePiFunctor q).map (comparison X) := by
  apply (cancel_mono (PointedCGWH.SequentialSpectrum.MappingTelescope.FiniteProductGeometry.comparisonIso X q).hom).mp
  rw [integerComparisonIso_cancel]
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro z
  funext i
  have he := FiniteCoproductIntegerPiGeometry.equiv_coordinate (B := B) q n X hX z i
  have hp := ConcreteCategory.congr_hom
    ((integerStablePiFunctor q).congr_map (comparison_projection X i)) z
  have hm := ConcreteCategory.congr_hom
    ((integerStablePiFunctor q).map_comp (comparison X) (Pi.π X i)) z
  have hc := congrArg (fun f => f.hom (((integerStablePiFunctor q).map (comparison X)).hom z) i)
    (PointedCGWH.SequentialSpectrum.MappingTelescope.FiniteProductGeometry.comparisonIso_hom X q)
  exact he.trans (hp.symm.trans (hm.trans hc.symm))

/-- The same actual finite coproduct-to-product map preserves every original integer stable-pi group. -/
theorem comparison_integerPiStar (hX : ∀ i, IsCofibrant (X i)) : integerPiStarEquivalences (comparison X) := by
  rw [integerPiStarEquivalences_iff]
  intro q
  exact (integerComparisonIso_hom X q hX) ▸ (integerComparisonIso X q hX).isIso_hom

end PointedCGWH.SequentialSpectrum.StableHomotopy.FiniteAdditivityGeometry
