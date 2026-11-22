/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Algebra.Category.Grp.FilteredKernelRepresentatives
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.CofiberSphereLift

/-!
# Original integer kernel representatives and suspended sphere lifts

Every kernel class of the actual Q-cofiber target inclusion is represented
at an original positive diagonal stage. Filtered-colimit equality moves it
to a later stage with literal null cube image. The native sphere
correspondence and original I-cone construction supply a strict sphere
map and its actual suspended lift. The inverse original Q counit retains
the input class from the original target.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory
namespace PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberKernelRepresentatives
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiHoGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberIntegerSequence
open PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberSphereLift
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
private abbrev Index := PointedCGWH.Spectra.Sequential.Index.{u, v}
private abbrev H := toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := Index)
private abbrev S := OriginalISuspension.suspension (B := B) (I := Index)

/-- Each original integer kernel class has a later representative with null level image. -/
theorem inclusion_kernel_level_representative
    (q : ℤ) (F : Arrow PointedCGWH.SequentialSpectrum.{u, v})
    (x : (integerStablePiFunctor q).obj (Q.obj F.right))
    (hx : ((integerStablePiFunctor q).map (inclusion F)).hom x = 1) :
    ∃ (n : ℕ) (a : PointedCGWH.piN (integerTailPositiveIndex q + n + 1)
        (PointedCGWH.SequentialSpectrum.level (Q.obj F.right) (integerTailLevel q + n))),
      (integerStablePiLeg q (Q.obj F.right) n).hom a = x ∧
      PointedCGWH.piNMap (integerTailPositiveIndex q + n + 1)
        (PointedCGWH.SequentialSpectrum.levelMap (inclusion F) (integerTailLevel q + n)) a =
          PointedCGWH.SphereHom.nullCube (integerTailPositiveIndex q + n + 1)
            (PointedCGWH.SequentialSpectrum.level (cofiber.obj F) (integerTailLevel q + n)) := by
  let D := (integerDiagonalDiagramFunctor q).obj (Q.obj F.right)
  let E := (integerDiagonalDiagramFunctor q).obj (cofiber.obj F)
  let α : D ⟶ E := (integerDiagonalDiagramFunctor q).map (inclusion F)
  have hx' : (GrpCat.FilteredColimits.colimitMap α).hom x = 1 := hx
  obtain ⟨n, m, h, a, ha, hn⟩ :=
    GrpCat.FilteredColimits.colimitMap_kernel_representative α x hx'
  let b := D.map (homOfLE h) a
  refine ⟨m, b, ?_, ?_⟩
  · change (GrpCat.FilteredColimits.colimitCocone D).ι.app m (D.map (homOfLE h) a) = x
    have hleg := ConcreteCategory.congr_hom
      ((GrpCat.FilteredColimits.colimitCocone D).ι.naturality (homOfLE h)) a
    exact hleg.trans ha
  · have hnat := ConcreteCategory.congr_hom (α.naturality (homOfLE h)) a
    have hb : α.app m b = 1 := hnat.trans hn
    change (((diagonalDiagramFunctor (integerTailLevel q) (integerTailPositiveIndex q)).map
      (inclusion F)).app m).hom b = 1 at hb
    have hb' : PointedCGWH.piNMap (integerTailPositiveIndex q + m + 1)
        (PointedCGWH.SequentialSpectrum.levelMap (inclusion F) (integerTailLevel q + m)) b =
          (1 : (PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + m)).obj
            (PointedCGWH.SequentialSpectrum.level (cofiber.obj F) (integerTailLevel q + m))) := by
      exact (diagonalDiagramFunctor_map_apply (integerTailLevel q)
        (integerTailPositiveIndex q) (inclusion F) m b).symm.trans hb
    exact hb'.trans (PointedCGWH.SphereHom.nullCube_eq_one
      (integerTailPositiveIndex q + m)
      (PointedCGWH.SequentialSpectrum.level (cofiber.obj F) (integerTailLevel q + m))).symm

/-- The inverse Q counit sends an original target kernel class to the same level lift. -/
theorem original_inclusion_kernel_level_representative
    (q : ℤ) (F : Arrow PointedCGWH.SequentialSpectrum.{u, v})
    (x : (integerStablePiHoFunctor q).obj (H.obj F.right))
    (hx : (inclusionInteger q F).hom x = 1) :
    ∃ (n : ℕ) (a : PointedCGWH.piN (integerTailPositiveIndex q + n + 1)
        (PointedCGWH.SequentialSpectrum.level (Q.obj F.right) (integerTailLevel q + n))),
      (integerStablePiLeg q (Q.obj F.right) n).hom a =
        ((integerStablePiHoFunctor q).map (qCounitHoIso F.right).inv).hom x ∧
      PointedCGWH.piNMap (integerTailPositiveIndex q + n + 1)
        (PointedCGWH.SequentialSpectrum.levelMap (inclusion F) (integerTailLevel q + n)) a =
          PointedCGWH.SphereHom.nullCube (integerTailPositiveIndex q + n + 1)
            (PointedCGWH.SequentialSpectrum.level (cofiber.obj F) (integerTailLevel q + n)) := by
  have hx' : ((integerStablePiFunctor q).map (inclusion F)).hom
      (((integerStablePiHoFunctor q).map (qCounitHoIso F.right).inv).hom x) = 1 := by
    exact (ConcreteCategory.congr_hom (inclusionInteger_formula q F) x).symm.trans hx
  exact inclusion_kernel_level_representative q F
    (((integerStablePiHoFunctor q).map (qCounitHoIso F.right).inv).hom x) hx'

/-- A kernel class has an original strict sphere map and suspended coefficient lift. -/
theorem original_inclusion_kernel_suspended_lift
    (q : ℤ) (F : Arrow PointedCGWH.SequentialSpectrum.{u, v})
    (x : (integerStablePiHoFunctor q).obj (H.obj F.right))
    (hx : (inclusionInteger q F).hom x = 1) :
    ∃ (n : ℕ) (a : PointedCGWH.piN (integerTailPositiveIndex q + n + 1)
        (PointedCGWH.SequentialSpectrum.level (Q.obj F.right) (integerTailLevel q + n)))
      (g : sphereSource (integerTailLevel q + n) (integerTailPositiveIndex q + n + 1) ⟶
        Q.obj F.right)
      (k : H.obj (S.obj (sphereSource (integerTailLevel q + n)
        (integerTailPositiveIndex q + n + 1))) ⟶ H.obj (S.obj (Q.obj F.left))),
      (integerStablePiLeg q (Q.obj F.right) n).hom a =
        ((integerStablePiHoFunctor q).map (qCounitHoIso F.right).inv).hom x ∧
      H.map g = levelSphereClass (integerTailLevel q + n)
        (integerTailPositiveIndex q + n + 1) (Q.obj F.right) a ∧
      k ≫ H.map (S.map (Q.map F.hom)) = H.map (S.map g) := by
  obtain ⟨n, a, ha, hnull⟩ := original_inclusion_kernel_level_representative q F x hx
  obtain ⟨g, hg, hgn⟩ := levelSphereClass_null_representative F
    (integerTailLevel q + n) (integerTailPositiveIndex q + n + 1) a hnull
  obtain ⟨k, hk⟩ := sphereSuspendedLift_of_null F
    (integerTailLevel q + n) (integerTailPositiveIndex q + n + 1) g hgn
  exact ⟨n, a, g, k, ha, hg, hk⟩

end PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberKernelRepresentatives
