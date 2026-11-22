/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.NativeLoopWeakDetection
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.OmegaInputs

/-!
# Actual native level-weak recognition between original Omega spectra

Both original Omega hypotheses and the full adjoint structure square give
level weakness from the genuine all-loop-component positive detector.
The Type and Group map functions retain the original native pi maps.
The existing canonical native component-weak theorem is reused.
No arbitrary-input telescope Omega, stable model or integer/Ω identification
is asserted by this home.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.OmegaLevelWeakGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope
open PointedCGWH.SequentialSpectrum.OrderedLoop
open PointedCGWH.NativeLoopWeakDetectionGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The SAME original CGWH class inherits its genuine three directions from original TopCat. -/
theorem originalCGWHWeak_hasTwoOutOfThree :
    CGWH.weakHomotopyEquivalences.{u, v}.HasTwoOutOfThreeProperty := by
  rw [CGWH.weakHomotopyEquivalences_eq_inverseImage]
  infer_instance

/-- The ENTIRE original positive Group map has the SAME actual literal-degree Type function. -/
theorem positiveGroupMap_underlying (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (forget GrpCat).map ((piNPositiveFunctor n).map f) = (piNFunctor (n + 1)).map f := by
  apply ConcreteCategory.hom_ext
  intro a
  exact piNPositiveMap_apply n f a

/-- BOTH full original Group and Type maps have the SAME actual isomorphism condition. -/
theorem positiveGroupMap_isIso_iff_type (n : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    IsIso ((piNPositiveFunctor n).map f) ↔ IsIso ((piNFunctor (n + 1)).map f) :=
  (isIso_iff_of_reflects_iso ((piNPositiveFunctor n).map f) (forget GrpCat)).symm.trans
    (congrArg IsIso (positiveGroupMap_underlying n f)).to_iff

/-- The whole genuine positive Group Iso condition is the actual original pi-map bijection. -/
theorem positiveGroupMap_isIso_iff_bijective (n : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    IsIso ((piNPositiveFunctor n).map f) ↔ Function.Bijective (piNMap (n + 1) f) :=
  (positiveGroupMap_isIso_iff_type n f).trans (CategoryTheory.isIso_iff_bijective _)

/-- BOTH original Omega adjoints and their ENTIRE original square give actual loop recognition. -/
theorem omegaLevelMap_weak_iff_loop_next
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hX : X.IsOmega) (hY : Y.IsOmega) (m : ℕ) :
    CGWH.weakHomotopyEquivalences (PointedCGWH.SequentialSpectrum.levelMap f m).right ↔
      CGWH.weakHomotopyEquivalences
        (PointedCGWH.loop.map (PointedCGWH.SequentialSpectrum.levelMap f (m + 1))).right := by
  let W := CGWH.weakHomotopyEquivalences.{u, v}
  let _ : W.HasTwoOutOfThreeProperty := originalCGWHWeak_hasTwoOutOfThree
  let a := (PointedCGWH.SequentialSpectrum.adjointStructureMap X m).right
  let b := (PointedCGWH.SequentialSpectrum.adjointStructureMap Y m).right
  let l := (PointedCGWH.SequentialSpectrum.levelMap f m).right
  let r := (PointedCGWH.loop.map (PointedCGWH.SequentialSpectrum.levelMap f (m + 1))).right
  have h : l ≫ b = a ≫ r := pointedToCGWH.congr_map
    (PointedCGWH.SequentialSpectrum.adjointStructureMap_naturality f m)
  constructor
  · intro hl
    exact W.of_precomp (W' := W) a r (hX m) (h ▸ W.comp_mem l b hl (hY m))
  · intro hr
    exact W.of_postcomp (W' := W) l b (hY m) (h.symm ▸ W.comp_mem a r (hX m) hr)

/-- Actual original Omega level weakness is detected by ALL selected positive next-level maps. -/
theorem omegaLevelMap_weak_iff_positive_bijective
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hX : X.IsOmega) (hY : Y.IsOmega) (m : ℕ) :
    CGWH.weakHomotopyEquivalences (PointedCGWH.SequentialSpectrum.levelMap f m).right ↔
      ∀ n : ℕ, Function.Bijective
        (piNMap (n + 1) (PointedCGWH.SequentialSpectrum.levelMap f (m + 1))) :=
  (omegaLevelMap_weak_iff_loop_next f hX hY m).trans (nativeLoopMap_weak_iff_based _)

/-- The ENTIRE original Type-Iso test recognizes the SAME native Omega level weak map. -/
theorem omegaLevelMap_weak_iff_positiveType_isIso
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hX : X.IsOmega) (hY : Y.IsOmega) (m : ℕ) :
    CGWH.weakHomotopyEquivalences (PointedCGWH.SequentialSpectrum.levelMap f m).right ↔
      ∀ n : ℕ, IsIso ((piNFunctor (n + 1)).map
        (PointedCGWH.SequentialSpectrum.levelMap f (m + 1))) := by
  apply (omegaLevelMap_weak_iff_positive_bijective f hX hY m).trans
  exact forall_congr' (fun n => (CategoryTheory.isIso_iff_bijective _).symm)

/-- The ENTIRE original genuine Group-Iso test recognizes the SAME native Omega level weak map. -/
theorem omegaLevelMap_weak_iff_positiveGroup_isIso
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hX : X.IsOmega) (hY : Y.IsOmega) (m : ℕ) :
    CGWH.weakHomotopyEquivalences (PointedCGWH.SequentialSpectrum.levelMap f m).right ↔
      ∀ n : ℕ, IsIso ((piNPositiveFunctor n).map
        (PointedCGWH.SequentialSpectrum.levelMap f (m + 1))) := by
  apply (omegaLevelMap_weak_iff_positiveType_isIso f hX hY m).trans
  exact forall_congr' (fun n => (positiveGroupMap_isIso_iff_type n _).symm)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- BOTH entire original Omega models have their SAME complete positive Type-map recognition. -/
theorem omegaMap_modelWeak_iff_positiveType_isIso
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hX : X.IsOmega) (hY : Y.IsOmega) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f ↔
      ∀ m n : ℕ, IsIso ((piNFunctor (n + 1)).map
        (PointedCGWH.SequentialSpectrum.levelMap f (m + 1))) :=
  (PointedCGWH.SequentialSpectrum.MappingTelescope.levelWeak_iff_components f).trans
    (forall_congr' (fun m => omegaLevelMap_weak_iff_positiveType_isIso f hX hY m))

/-- BOTH entire original Omega models have their SAME genuine positive Group-map recognition. -/
theorem omegaMap_modelWeak_iff_positiveGroup_isIso
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hX : X.IsOmega) (hY : Y.IsOmega) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f ↔
      ∀ m n : ℕ, IsIso ((piNPositiveFunctor n).map
        (PointedCGWH.SequentialSpectrum.levelMap f (m + 1))) :=
  (PointedCGWH.SequentialSpectrum.MappingTelescope.levelWeak_iff_components f).trans
    (forall_congr' (fun m => omegaLevelMap_weak_iff_positiveGroup_isIso f hX hY m))

end PointedCGWH.SequentialSpectrum.OmegaLevelWeakGeometry
