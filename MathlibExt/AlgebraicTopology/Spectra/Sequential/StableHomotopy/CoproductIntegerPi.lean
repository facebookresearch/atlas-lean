/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Algebra.Group.SplitCoordinateExactness
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.CoproductQCofiber
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.CofiberIntegerExactness

/-!
# Actual integer stable-pi splitting of an original binary coproduct

The original cofiber inclusion becomes the same original right projection
after the proved weak Q-cofiber collapse. Its exact integer kernel is
therefore the original left-summand image. The two original sections and
projections give the full coordinate group isomorphism.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.CoproductIntegerPiGeometry

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiHoGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.CoproductCofiberGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberIntegerSequence
open PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberConnectingIntegerPiGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.ISuspensionIntegerPiGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberIntegerExactnessGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
private abbrev Index := PointedCGWH.Spectra.Sequential.Index.{u, v}
private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := Index)
variable (X Y : PointedCGWH.SequentialSpectrum.{u, v})

/-- The original right projection is the original zero/identity coproduct map. -/
def rightProjection : X ⨿ Y ⟶ Y := coprod.desc (Diagrams.toZero X ≫ Diagrams.zeroTo Y) (𝟙 Y)

/-- The actual integer group map of the proved original Q-cofiber collapse. -/
def collapseMap (q : ℤ) :
    (integerStablePiFunctor q).obj ((cofiber (B := B)).obj (arrow X Y)) ⟶
      (integerStablePiFunctor q).obj Y :=
  (integerStablePiFunctor q).map (CoproductQCofiberGeometry.collapse (B := B) X Y)

/-- The same original Q-cofiber collapse induces an Iso in every integer degree. -/
theorem collapseMap_isIso [IsCofibrant X] [IsCofibrant Y] (q : ℤ) : IsIso (collapseMap X Y q) :=
  integerStablePiFunctor_invertsLevelWeak q _
    (CoproductQCofiberGeometry.collapse_weak (B := B) X Y).mem

/-- The whole original integer cofiber inclusion/collapse word is exactly the original right projection map. -/
theorem inclusion_collapseMap (q : ℤ) :
    inclusionInteger (B := B) q (arrow X Y) ≫ collapseMap X Y q =
      (integerStablePiFunctor q).map (rightProjection X Y) := by
  rw [inclusionInteger_formula, qCounitHoIso_integer_inverse]
  have h := (integerStablePiFunctor q).congr_map (CoproductQCofiberGeometry.inclusion_collapse (B := B) X Y)
  have hcomp := (integerStablePiFunctor q).map_comp
    (inclusion (B := B) (arrow X Y)) (CoproductQCofiberGeometry.collapse (B := B) X Y)
  have hright := (integerStablePiFunctor q).map_comp (ε.app (X ⨿ Y)) (rightProjection X Y)
  have hc : (integerStablePiFunctor q).map (ε.app (X ⨿ Y)) = (qCounitIntegerNatIso q).hom.app (X ⨿ Y) :=
    (qCounitIntegerNatIso_hom_app q (X ⨿ Y)).symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (qCounitIntegerNatIso q).inv.app (X ⨿ Y) ≫ f)
      (hcomp.symm.trans (h.trans hright))).trans
      ((congrArg (fun f => (qCounitIntegerNatIso q).inv.app (X ⨿ Y) ≫ f ≫
        (integerStablePiFunctor q).map (rightProjection X Y)) hc).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun f => f ≫ (integerStablePiFunctor q).map (rightProjection X Y))
            ((qCounitIntegerNatIso q).app (X ⨿ Y)).inv_hom_id).trans (Category.id_comp _)))))

end PointedCGWH.SequentialSpectrum.StableHomotopy.CoproductIntegerPiGeometry
