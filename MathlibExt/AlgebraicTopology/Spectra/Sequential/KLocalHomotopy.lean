/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.KSmallObject
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKLocalHomotopy
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.LevelFibrancy
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyPrecompositionLifting
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Path

/-!
# Actual native K-local products, paths and homotopy Hom

All statements use the literal original K right class and actual native
model. Its constructed local objects are closed under native products and
good level path objects. Actual K-left maps between cofibrant objects give
a bijection on Ho(level) Hom into those local objects. Identification with
the original Omega predicate and stable-model admission remain separate.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat PointedCGWH.EnrichedFunctorMapping
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.SequentialSpectrum.StableK

open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- Every original native level trivial fibration is in the full constructed K right class. -/
theorem levelTrivialFibrations_le_right : trivialFibrations PointedCGWH.SequentialSpectrum.{u, v} ≤
    generators.rlp := by
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.levelTrivialFibrations_le_right.{u, v} StabilizationKAdapter.family.{u, v}

/-- Locality pulls back through the actual original native level trivial fibrations. -/
theorem local_of_levelTrivialFibration {X Y : PointedCGWH.SequentialSpectrum.{u, v}}
    (p : X ⟶ Y) (hp : trivialFibrations PointedCGWH.SequentialSpectrum.{u, v} p)
    (hY : generators.rlp (toZero Y)) : generators.rlp (toZero X) := by
  simp only [← StabilizationKAdapter.generators_eq] at *
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.local_of_levelTrivialFibration.{u, v} StabilizationKAdapter.family.{u, v} p hp hY

/-- An actual K-local target makes each original cylinder source mapping arrow trivial fibrant. -/
theorem mappingSource_trivial_of_local (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v})
    (hX : generators.rlp (toZero X)) :
    trivialFibrations PointedCGWH.{u, v}
      (EnrichedFunctorCat.WeightedEndVariance.pre (stabilizationCylinderSource n) X) := by
  have hX' : (NativeK.generators.{u, v} StabilizationKAdapter.family.{u, v}).rlp (toZero X) := by
    simpa only [StabilizationKAdapter.generators_eq] using hX
  have h := NativeK.mappingSource_trivial_of_local.{u, v}
    StabilizationKAdapter.family.{u, v} n X hX'
  have he := congrFun (StabilizationKAdapter.cylinderMappingSource_function_eq n) X
  have hp := congrArg
    (fun f : Arrow PointedCGWH.{u, v} => trivialFibrations PointedCGWH.{u, v} f.hom) he
  exact hp.mp h

/-- A level fibration between the actual constructed local objects has all original K lifting. -/
theorem levelFibration_between_local_mem_right
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y)
    (hp : fibrations PointedCGWH.SequentialSpectrum.{u, v} p)
    (hX : generators.rlp (toZero X)) (hY : generators.rlp (toZero Y)) : generators.rlp p := by
  simp only [← StabilizationKAdapter.generators_eq] at *
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.levelFibration_between_local_mem_right.{u, v}
      StabilizationKAdapter.family.{u, v} p hp hX hY

omit B in
/-- The actual original native product of two constructed local objects is local. -/
theorem product_local (X Y : PointedCGWH.SequentialSpectrum.{u, v})
    (hX : generators.rlp (toZero X)) (hY : generators.rlp (toZero Y)) :
    generators.rlp (toZero (X ⨯ Y)) := by
  simp only [← StabilizationKAdapter.generators_eq] at *
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.product_local.{u, v} StabilizationKAdapter.family.{u, v} X Y hX hY

/-- Every actual good level path object of a constructed local target is local. -/
theorem goodPath_local (Z : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : generators.rlp (toZero Z)) (P : PathObject Z) [P.IsGood] :
    generators.rlp (toZero P.P) := by
  simp only [← StabilizationKAdapter.generators_eq] at *
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.goodPath_local.{u, v} StabilizationKAdapter.family.{u, v} Z hZ P

/-- Its same original joint path projection has the full original K right lifting. -/
theorem goodPath_projection_mem_right (Z : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : generators.rlp (toZero Z)) (P : PathObject Z) [P.IsGood] : generators.rlp P.p := by
  simp only [← StabilizationKAdapter.generators_eq] at *
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.goodPath_projection_mem_right.{u, v} StabilizationKAdapter.family.{u, v} Z hZ P

omit B in
/-- A constructed local object's actual map to the chosen native terminal remains K-right. -/
theorem chosenTerminal_mem_right (Z : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : generators.rlp (toZero Z)) : generators.rlp (terminal.from Z) := by
  simp only [← StabilizationKAdapter.generators_eq] at *
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.chosenTerminal_mem_right.{u, v} StabilizationKAdapter.family.{u, v} Z hZ

/-- Original K-left maps induce a bijection of actual native Ho(level) Hom into local targets. -/
theorem left_Ho_precomp_bijective
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) (hf : generators.rlp.llp f)
    [IsCofibrant X] (Z : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : generators.rlp (toZero Z)) (P : PathObject Z) [P.IsGood] :
    Function.Bijective (fun g : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Y ⟶
        (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z =>
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map f ≫ g) := by
  simp only [← StabilizationKAdapter.generators_eq] at *
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.left_Ho_precomp_bijective.{u, v} StabilizationKAdapter.family.{u, v} f hf Z hZ P

/-- The actual original J/κ/B path functor stays in the constructed K-local objects. -/
theorem originalPath_local (Z : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : generators.rlp (toZero Z)) :
    generators.rlp (toZero ((HomotopicalAlgebra.EnrichedProjective.Native.Path.pathFunctor
      (B := B)).obj Z)) := by
  simp only [← StabilizationKAdapter.generators_eq] at *
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.originalPath_local.{u, v} StabilizationKAdapter.family.{u, v} Z hZ

/-- Its SAME original J joint endpoint map has every literal K lifting property. -/
theorem originalPath_endpoints_mem_right (Z : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : generators.rlp (toZero Z)) :
    generators.rlp ((HomotopicalAlgebra.EnrichedProjective.Native.Path.endpoints
      (B := B)).app Z) := by
  simp only [← StabilizationKAdapter.generators_eq] at *
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.originalPath_endpoints_mem_right.{u, v} StabilizationKAdapter.family.{u, v} Z hZ

/-- Actual original K-left maps and original J path give the native Ho(level) Hom bijection. -/
theorem left_Ho_precomp_bijective_originalPath
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) (hf : generators.rlp.llp f)
    [IsCofibrant X] (Z : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : generators.rlp (toZero Z)) :
    Function.Bijective (fun g : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Y ⟶
        (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z =>
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map f ≫ g) := by
  simp only [← StabilizationKAdapter.generators_eq] at *
  simpa only [StabilizationKAdapter.generators_eq] using
    NativeK.left_Ho_precomp_bijective_originalPath.{u, v}
      StabilizationKAdapter.family.{u, v} f hf Z hZ

end PointedCGWH.SequentialSpectrum.StableK
