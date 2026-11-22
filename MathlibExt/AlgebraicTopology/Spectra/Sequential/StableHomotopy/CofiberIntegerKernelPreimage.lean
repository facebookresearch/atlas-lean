/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.ScalarCofiberIntegerPreimage
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.CofiberKernelRepresentatives

/-!
# Every original integer cofiber kernel class has an original source preimage

The actual strict sphere representative is lifted after the original I
suspension, normalized to its scalar unit class, and transported through
the full signed integer suspension isomorphism. The original Q counits
then give a preimage on the unchanged source and target homotopy objects.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberKernelRepresentatives

open HomotopicalAlgebra.EnrichedProjective.Native
open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiHoGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberIntegerSequence
open PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberSphereLift
open PointedCGWH.SuspensionReflectionGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
private abbrev Index := PointedCGWH.Spectra.Sequential.Index.{u, v}
private abbrev H := toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := Index)

/-- Every kernel element of the full original target-to-cofiber map lies in the source image. -/
theorem original_inclusion_kernel_preimage
    (q : ℤ) (F : Arrow PointedCGWH.SequentialSpectrum.{u, v})
    (x : (integerStablePiHoFunctor q).obj (H.obj F.right))
    (hx : (inclusionInteger q F).hom x = 1) :
    ∃ y : (integerStablePiHoFunctor q).obj (H.obj F.left),
      ((integerStablePiHoFunctor q).map (H.map F.hom)).hom y = x := by
  obtain ⟨n, a, g, k, ha, hg, hk⟩ := original_inclusion_kernel_suspended_lift q F x hx
  let m := integerTailLevel q
  let t := integerTailPositiveIndex q
  let b := suspendedCoefficientClass F (m + n) (t + n + 1)
    (qSuspendedCoefficient F (m + n) (t + n + 1) k)
  have hb := suspendedCoefficientClass_map_eq_suspension F (m + n) (t + n + 1) a g hg
    (qSuspendedCoefficient F (m + n) (t + n + 1) k)
    (qSuspendedCoefficient_map F (m + n) (t + n + 1) g k hk)
  have hb' : ((levelCubeGroupFunctor (m + n) ((t + n) + 1)).map
      (SuspensionGeometry.suspension.map (Q.map F.hom))).hom b =
    ((spaceSuspensionGroupMap (t + n)).app
      (PointedCGWH.SequentialSpectrum.level (Q.obj F.right) (m + n))).hom a := by
    change (PointedCGWH.piNPositiveMap ((t + n) + 1)
      (PointedCGWH.SequentialSpectrum.levelMap
        (SuspensionGeometry.suspension.map (Q.map F.hom)) (m + n))).hom b = _
    rw [PointedCGWH.piNPositiveMap_apply]
    exact hb.trans (spaceSuspensionGroupMap_eq_class (t + n)
      (PointedCGWH.SequentialSpectrum.level (Q.obj F.right) (m + n)) a).symm
  obtain ⟨c, hc⟩ := stageForward_image_of_space_lift n m t (Q.map F.hom) a b hb'
  obtain ⟨y, hy⟩ := integerPiMap_image_of_signed_stage q n (Q.map F.hom) a c hc
  let P := integerStablePiHoFunctor q
  let eX := qCounitHoIso (B := B) F.left
  let eY := qCounitHoIso (B := B) F.right
  have hn : P.map (H.map (Q.map F.hom)) ≫ P.map eY.hom =
      P.map eX.hom ≫ P.map (H.map F.hom) :=
    (P.map_comp _ _).symm.trans
      ((P.congr_map (qCounitHoIso_naturality (B := B) F.hom)).trans (P.map_comp _ _))
  have hn' := congrArg (fun f => f.hom y) hn
  have hQ : (P.map (H.map (Q.map F.hom))).hom y = (P.map eY.inv).hom x := by
    rw [integerStablePiHoFunctor_map]
    exact hy.trans ha
  have hInv := congrArg (fun f => f.hom x) (P.mapIso eY).inv_hom_id
  refine ⟨(P.map eX.hom).hom y, ?_⟩
  calc
    _ = (P.map eY.hom).hom ((P.map (H.map (Q.map F.hom))).hom y) := hn'.symm
    _ = (P.map eY.hom).hom ((P.map eY.inv).hom x) := congrArg (P.map eY.hom).hom hQ
    _ = x := hInv

end PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberKernelRepresentatives
