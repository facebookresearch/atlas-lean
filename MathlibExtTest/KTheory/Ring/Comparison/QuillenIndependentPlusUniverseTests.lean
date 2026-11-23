/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Ring.Comparison.QuillenIndependentPlusUniverse

noncomputable section

open AlgebraicKTheory.QuillenPlus.UniverseAssembly
open TopologicalSpace
open scoped ContinuousMap

universe uR uM uObj uHom uNative uProbe

attribute [local instance]
  AlgebraicKTheory.QuillenPlus.UniverseAssembly.targetSpaceTopology

example (R : Type uR) [Ring R] :
    transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R
        (sourcePoint.{uR, uM, uObj, uHom, uNative} R) =
      targetPoint.{uR, uM, uObj, uHom, uNative} R ∧
    transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R
        (targetPoint.{uR, uM, uObj, uHom, uNative} R) =
      sourcePoint.{uR, uM, uObj, uHom, uNative} R :=
  ⟨transportedForward_point R, transportedInverse_point R⟩

example (R : Type uR) [Ring R] :
    Nonempty (ContinuousMap.HomotopyRel
      ((transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R).comp
        (transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R))
      (ContinuousMap.id (sourceSpace.{uR, uM, uObj, uHom, uNative} R))
      {sourcePoint.{uR, uM, uObj, uHom, uNative} R}) ∧
    Nonempty (ContinuousMap.HomotopyRel
      ((transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R).comp
        (transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R))
      (ContinuousMap.id (targetSpace.{uR, uM, uObj, uHom, uNative} R))
      {targetPoint.{uR, uM, uObj, uHom, uNative} R}) :=
  ⟨⟨transportedLeftHomotopyRel R⟩, ⟨transportedRightHomotopyRel R⟩⟩

/-- Objects, Hom types and native carriers are independently larger than the module level. -/
example (R : Type) [Ring R] :
    Nonempty (ContinuousMap.HomotopyRel
      ((transportedInverse.{0, 1, 3, 5, 7, 2} R).comp
        (transportedForward.{0, 1, 3, 5, 7, 2} R))
      (ContinuousMap.id (sourceSpace.{0, 1, 3, 5, 7} R))
      {sourcePoint.{0, 1, 3, 5, 7} R}) :=
  ⟨transportedLeftHomotopyRel.{0, 1, 3, 5, 7, 2} R⟩

/-- The core probe changes while the actual native carrier stays fixed. -/
example (R : Type) [Ring R] :
    Nonempty (ContinuousMap.HomotopyRel
      ((transportedForward.{0, 1, 3, 5, 7, 9} R).comp
        (transportedInverse.{0, 1, 3, 5, 7, 9} R))
      (ContinuousMap.id (targetSpace.{0, 1, 3, 5, 7} R))
      {targetPoint.{0, 1, 3, 5, 7} R}) :=
  ⟨transportedRightHomotopyRel.{0, 1, 3, 5, 7, 9} R⟩

example (R : Type uR) [Ring R]
    (x : sourceSpace.{uR, uM, uObj, uHom, uNative} R) :
    (transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R x).1 =
      AlgebraicKTheory.OriginalQK0UniverseLiftCompatibility.nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R x :=
  transportedForward_first_eq_canonicalK0 R x

example (R : Type uR) [Ring R] (k : AlgebraicKTheory.RingK0 R) :
    ∃ x : sourceSpace.{uR, uM, uObj, uHom, uNative} R,
      (transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R x).1 = k :=
  transportedForward_every_class R k

example (R : Type uR) [Ring R] :
    ∃ e : sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R ≃ₕ
        targetSpace.{uR, uM, uObj, uHom, uNative} R,
      e.toFun = transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R ∧
      e.invFun = transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R ∧
      e.toFun (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) = targetPoint.{uR, uM, uObj, uHom, uNative} R ∧
      e.invFun (targetPoint.{uR, uM, uObj, uHom, uNative} R) = sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R ∧
      Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun)
        (ContinuousMap.id (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R))
        {sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R}) ∧
      Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun)
        (ContinuousMap.id (targetSpace.{uR, uM, uObj, uHom, uNative} R)) {targetPoint.{uR, uM, uObj, uHom, uNative} R}) ∧
      ∀ x, (e.toFun x).1 =
        AlgebraicKTheory.OriginalQK0UniverseLiftCompatibility.nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R x := by
  letI : TopologicalSpace (targetSpace.{uR, uM, uObj, uHom, uNative} R) :=
    targetSpaceTopology.{uR, uM, uObj, uHom, uNative} R
  obtain ⟨_, _, e, hf, hg, _, _, hL, _, hK, _, _⟩ :=
    AlgebraicKTheory.QuillenPlus.quillenIndependentPlusEquivalence_allUniverses_canonicalK0_exists.{uR, uM, uObj, uHom, uNative, uProbe} R
  have hProbePoint :
      sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R =
        sourcePoint.{uR, uM, uObj, uHom, uNative} R :=
    sourcePointWithProbe_eq.{uR, uM, uObj, uHom, uNative, uProbe} R
  have hNamedQ :
      e.toFun (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) =
        targetPoint.{uR, uM, uObj, uHom, uNative} R := by
    rw [hf]
    exact (congrArg (transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R)
      hProbePoint).trans
      (transportedForward_point.{uR, uM, uObj, uHom, uNative, uProbe} R)
  have hNamedT :
      e.invFun (targetPoint.{uR, uM, uObj, uHom, uNative} R) =
        sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R := by
    rw [hg]
    exact (transportedInverse_point.{uR, uM, uObj, uHom, uNative, uProbe} R).trans
      hProbePoint.symm
  have hComposition : e.toFun.comp e.invFun =
      (transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R).comp
        (transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R) :=
    congrArg₂
      (fun (f : C(sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R,
          targetSpace.{uR, uM, uObj, uHom, uNative} R))
        (g : C(targetSpace.{uR, uM, uObj, uHom, uNative} R,
          sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)) =>
        f.comp g) hf hg
  have hNamedR : Nonempty (ContinuousMap.HomotopyRel
      (e.toFun.comp e.invFun)
      (ContinuousMap.id (targetSpace.{uR, uM, uObj, uHom, uNative} R))
      {targetPoint.{uR, uM, uObj, uHom, uNative} R}) :=
    ⟨(transportedRightHomotopyRel.{uR, uM, uObj, uHom, uNative, uProbe} R).cast
      hComposition.symm rfl⟩
  exact ⟨e, hf, hg, hNamedQ, hNamedT, hL, hNamedR, hK⟩

/-- Object/Hom/native carrier parameters are distinct; probe is genuine CGWH data. -/
example (R : Type) [Ring R] :
    let X : CGWH.{2, 7} := sourceRealizationBundle.{0, 1, 3, 5, 7, 2} R
    UCompactlyGeneratedSpace.{2} X ∧ UWeakHausdorffSpace.{2} X := by
  obtain ⟨hCG, hWH, _⟩ :=
    AlgebraicKTheory.QuillenPlus.quillenIndependentPlusEquivalence_allUniverses_canonicalK0_exists.{0, 1, 3, 5, 7, 2} R
  exact ⟨hCG, hWH⟩

/-- Changing the actual compact probe does not change the native carrier seven. -/
example (R : Type) [Ring R] :
    let X : CGWH.{9, 7} := sourceRealizationBundle.{0, 1, 3, 5, 7, 9} R
    UCompactlyGeneratedSpace.{9} X ∧ UWeakHausdorffSpace.{9} X := by
  obtain ⟨hCG, hWH, _⟩ :=
    AlgebraicKTheory.QuillenPlus.quillenIndependentPlusEquivalence_allUniverses_canonicalK0_exists.{0, 1, 3, 5, 7, 9} R
  exact ⟨hCG, hWH⟩

#check @transportedForward
#print axioms transportedForward
#check @transportedInverse
#print axioms transportedInverse
#check @transportedLeftHomotopyRel
#print axioms transportedLeftHomotopyRel
#check @transportedRightHomotopyRel
#print axioms transportedRightHomotopyRel
#check @transportedForward_first_eq_coreK0
#print axioms transportedForward_first_eq_coreK0
#check @transportedForward_first_eq_canonicalK0
#print axioms transportedForward_first_eq_canonicalK0
#check @transportedForward_every_class
#print axioms transportedForward_every_class
#check @AlgebraicKTheory.QuillenPlus.quillenIndependentPlusEquivalence_allUniverses_canonicalK0_exists
#print axioms AlgebraicKTheory.QuillenPlus.quillenIndependentPlusEquivalence_allUniverses_canonicalK0_exists

end
