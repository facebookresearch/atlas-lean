/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.Comparison.QuillenIndependentPlusUniverse
public import MathlibExt.KTheory.Exact.Quillen.KSpaceHomotopyGroups
public import MathlibExt.Topology.Homotopy.HomotopyGroupLoopShift
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import MathlibExt.Topology.Homotopy.BasedHomotopyGroupEquivalence

/-!
# Homotopy groups of the same independently constructed Quillen plus

The zeroth comparison retains every fixed original `RingK0` class. Its
value is the independent Q/S component evaluator of the actual lifted
projective category, composed with the literal native-carrier descent.
The accepted six-universe comparison identifies that value with the first
coordinate of its actual global forward map.

The native source is the raw loop space of the genuine compact-probe
Quillen realization, at its original constant loop. No equivalence,
component label, CW model or based comparison is supplied by a caller.
-/

noncomputable section

open CategoryTheory
open scoped ContinuousMap

universe uR uM uObj uHom uNative uProbe uX uY

namespace AlgebraicKTheory.QuillenPlus

open UniverseAssembly

attribute [local instance]
  OriginalQK0UniverseLiftCompatibility.categoryUniverseSymmFunctorAdditive
  OriginalQK0UniverseLiftCompatibility.categoryUniverseSymmInverseAdditive
  OriginalQK0UniverseLiftCompatibility.categoryUniverseSymmFunctorIsExact
  OriginalQK0UniverseLiftCompatibility.categoryUniverseSymmInverseIsExact

private def componentMap
    {X : Type uX} {Y : Type uY}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    ZerothHomotopy X → ZerothHomotopy Y :=
  ZerothHomotopy.lift (fun x => ZerothHomotopy.mk (f x))
    (fun {_ _} p => ZerothHomotopy.sound (p.map f.continuous))

private def componentEquivOfStrictInverse
    {X : Type uX} {Y : Type uY}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(Y, X))
    (hLeft : g.comp f = ContinuousMap.id X)
    (hRight : f.comp g = ContinuousMap.id Y) :
    ZerothHomotopy X ≃ ZerothHomotopy Y where
  toFun := componentMap f
  invFun := componentMap g
  left_inv c := by
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
    change ZerothHomotopy.mk (g (f x)) = ZerothHomotopy.mk x
    exact congrArg ZerothHomotopy.mk (ContinuousMap.congr_fun hLeft x)
  right_inv c := by
    obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective c
    change ZerothHomotopy.mk (f (g y)) = ZerothHomotopy.mk y
    exact congrArg ZerothHomotopy.mk (ContinuousMap.congr_fun hRight y)

/-- All components of the actual six-universe Quillen source correspond to
the fixed original `RingK0`, through the independent category evaluator.
The compact-probe parameter remains part of the actual source bundle. -/
public def quillenIndependentPlusComponentsEquiv (R : Type uR) [Ring R] :
    ZerothHomotopy
      (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) ≃
        RingK0 R :=
  (componentEquivOfStrictInverse
      (QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R)
      (QuillenUniverseLift.rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R)
      (QuillenUniverseLift.rawNativeCarrierUp_comp_down.{uR, uM, uObj, uHom, uNative} R)
      (QuillenUniverseLift.rawNativeCarrierDown_comp_up.{uR, uM, uObj, uHom, uNative} R)).trans
    ((OriginalQK0UniverseLiftCompatibility.originalComponentsEquivK0
        (FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R)).trans
      (OriginalQK0UniverseLiftCompatibility.categoryK0Equiv.{uR, uM, uObj, uHom} R).toEquiv)

private theorem componentsEquivComputed (R : Type uR) [Ring R]
    (p : sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) :
    quillenIndependentPlusComponentsEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R
        (ZerothHomotopy.mk p) =
      OriginalQK0UniverseLiftCompatibility.nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R p := by
  change (OriginalQK0UniverseLiftCompatibility.categoryK0Equiv.{uR, uM, uObj, uHom} R)
    ((OriginalQK0UniverseLiftCompatibility.originalComponentsEquivK0
      (FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R))
      (ZerothHomotopy.mk
        (QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R p))) = _
  rw [OriginalQK0UniverseLiftCompatibility.originalComponentsEquivK0_apply]
  rw [OriginalQK0UniverseLiftCompatibility.categoryK0Equiv_apply.{uR, uM, uObj, uHom} R]
  change RingK0.projectiveUniverseEquiv.{uR, uM} R
    (K0.equivOfEquivalence
      (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R).symm
      (OriginalQK0Comparison.canonicalLoopComponentsK0
        (C := FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R)
        (ZerothHomotopy.mk
          (QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R p)))) = _
  exact (OriginalQK0UniverseLiftCompatibility.nativeLoopFixedK0_formula.{uR, uM, uObj, uHom, uNative} R p).symm

/-- The zeroth comparison has the original independent Q/S value on every
raw source loop, including all components and non-generator loops. -/
public theorem quillenIndependentPlusComponentsEquiv_mk (R : Type uR) [Ring R]
    (p : sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) :
    quillenIndependentPlusComponentsEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R
        (ZerothHomotopy.mk p) =
      OriginalQK0UniverseLiftCompatibility.nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R p :=
  componentsEquivComputed.{uR, uM, uObj, uHom, uNative, uProbe} R p

/-- The component comparison is exactly the first coordinate of the accepted
literal global Quillen/core/plus forward composition. -/
public theorem quillenIndependentPlusComponentsEquiv_forward (R : Type uR) [Ring R]
    (p : sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) :
    quillenIndependentPlusComponentsEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R
        (ZerothHomotopy.mk p) =
      (transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R p).1 :=
  (quillenIndependentPlusComponentsEquiv_mk.{uR, uM, uObj, uHom, uNative, uProbe} R p).trans
    (transportedForward_first_eq_canonicalK0.{uR, uM, uObj, uHom, uNative, uProbe} R p).symm

/-- The degree-zero cube-based homotopy set uses the same fixed original
`RingK0` comparison at the actual constant loop of the probe bundle. -/
public def quillenIndependentPlusPiZeroEquiv (R : Type uR) [Ring R] :
    HomotopyGroup.Pi 0
      (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
      (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) ≃ RingK0 R :=
  (HomotopyGroup.pi0EquivZerothHomotopy
    (X := sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
    (x := sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)).trans
      (quillenIndependentPlusComponentsEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R)

private theorem piZeroEquivComputed (R : Type uR) [Ring R]
    (p : sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) :
    quillenIndependentPlusPiZeroEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R
      ((HomotopyGroup.pi0EquivZerothHomotopy
        (X := sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (x := sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)).symm
          (ZerothHomotopy.mk p)) =
      OriginalQK0UniverseLiftCompatibility.nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R p := by
  change quillenIndependentPlusComponentsEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R
    ((HomotopyGroup.pi0EquivZerothHomotopy
      (X := sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
      (x := sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R))
      ((HomotopyGroup.pi0EquivZerothHomotopy
        (X := sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (x := sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)).symm
          (ZerothHomotopy.mk p))) = _
  rw [Equiv.apply_symm_apply]
  exact quillenIndependentPlusComponentsEquiv_mk.{uR, uM, uObj, uHom, uNative, uProbe} R p

/-- Every actual raw loop represents its original independent fixed K0
class under the degree-zero comparison. -/
public theorem quillenIndependentPlusPiZeroEquiv_loop (R : Type uR) [Ring R]
    (p : sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) :
    quillenIndependentPlusPiZeroEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R
      ((HomotopyGroup.pi0EquivZerothHomotopy
        (X := sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (x := sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)).symm
          (ZerothHomotopy.mk p)) =
      OriginalQK0UniverseLiftCompatibility.nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R p :=
  piZeroEquivComputed.{uR, uM, uObj, uHom, uNative, uProbe} R p

/-- The actual native constant loop retains the original zero K0 class. -/
public theorem quillenIndependentPlusComponentsEquiv_constant (R : Type uR) [Ring R] :
    quillenIndependentPlusComponentsEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R
      (ZerothHomotopy.mk
        (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)) = 0 :=
  (quillenIndependentPlusComponentsEquiv_mk.{uR, uM, uObj, uHom, uNative, uProbe} R _).trans
    ((congrArg
      (OriginalQK0UniverseLiftCompatibility.nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R)
      (sourcePointWithProbe_eq.{uR, uM, uObj, uHom, uNative, uProbe} R)).trans
        (OriginalQK0UniverseLiftCompatibility.nativeLoopFixedK0_constant.{uR, uM, uObj, uHom, uNative} R))

/-- The actual based forward map to the same lifted independent plus target.
Its first step is the accepted literal global forward composition; only
then is the fixed K0 coordinate projected away. -/
public def quillenIndependentPlusForwardProjection (R : Type uR) [Ring R] :
    C(sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R,
      plusSpace.{uR, uM, uObj, uHom, uNative} R) := by
  letI : TopologicalSpace (RingK0 R) := (RingK0.discreteSpace R).str
  letI : TopologicalSpace (targetSpace.{uR, uM, uObj, uHom, uNative} R) :=
    targetSpaceTopology.{uR, uM, uObj, uHom, uNative} R
  let pr : C(targetSpace.{uR, uM, uObj, uHom, uNative} R,
      plusSpace.{uR, uM, uObj, uHom, uNative} R) :=
    ContinuousMap.snd
  exact pr.comp (transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R)

private theorem forwardProjectionComputed (R : Type uR) [Ring R]
    (p : sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) :
    quillenIndependentPlusForwardProjection.{uR, uM, uObj, uHom, uNative, uProbe} R p =
      (transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R p).2 := by
  rfl

/-- The projection uses the literal second coordinate of the accepted map. -/
public theorem quillenIndependentPlusForwardProjection_apply (R : Type uR) [Ring R]
    (p : sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) :
    quillenIndependentPlusForwardProjection.{uR, uM, uObj, uHom, uNative, uProbe} R p =
      (transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R p).2 :=
  forwardProjectionComputed.{uR, uM, uObj, uHom, uNative, uProbe} R p

/-- The actual return map first inserts the fixed zero K0 coordinate,
then uses the accepted literal global inverse composition. This is not
asserted to invert projection on every component of the source space. -/
public def quillenIndependentPlusInverseSection (R : Type uR) [Ring R] :
    C(plusSpace.{uR, uM, uObj, uHom, uNative} R,
      sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) := by
  letI : TopologicalSpace (RingK0 R) := (RingK0.discreteSpace R).str
  letI : TopologicalSpace (targetSpace.{uR, uM, uObj, uHom, uNative} R) :=
    targetSpaceTopology.{uR, uM, uObj, uHom, uNative} R
  let sec : C(plusSpace.{uR, uM, uObj, uHom, uNative} R,
      targetSpace.{uR, uM, uObj, uHom, uNative} R) :=
    (ContinuousMap.const (plusSpace.{uR, uM, uObj, uHom, uNative} R)
      (0 : RingK0 R)).prodMk (ContinuousMap.id _)
  exact (transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R).comp sec

private theorem inverseSectionComputed (R : Type uR) [Ring R]
    (b : plusSpace.{uR, uM, uObj, uHom, uNative} R) :
    quillenIndependentPlusInverseSection.{uR, uM, uObj, uHom, uNative, uProbe} R b =
      transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R ((0 : RingK0 R), b) := by
  rfl

/-- The return map is the same global inverse at the actual zero-labelled point. -/
public theorem quillenIndependentPlusInverseSection_apply (R : Type uR) [Ring R]
    (b : plusSpace.{uR, uM, uObj, uHom, uNative} R) :
    quillenIndependentPlusInverseSection.{uR, uM, uObj, uHom, uNative, uProbe} R b =
      transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R ((0 : RingK0 R), b) :=
  inverseSectionComputed.{uR, uM, uObj, uHom, uNative, uProbe} R b

private theorem forwardProjectionPointComputed (R : Type uR) [Ring R] :
    quillenIndependentPlusForwardProjection.{uR, uM, uObj, uHom, uNative, uProbe} R
      (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) =
        plusPoint.{uR, uM, uObj, uHom, uNative} R := by
  letI : TopologicalSpace (targetSpace.{uR, uM, uObj, uHom, uNative} R) :=
    targetSpaceTopology.{uR, uM, uObj, uHom, uNative} R
  obtain ⟨_, _, e, hf, _, hq, _, _, _, _, _, _⟩ :=
    quillenIndependentPlusEquivalence_allUniverses_canonicalK0_exists.{uR, uM, uObj, uHom, uNative, uProbe} R
  have hPair : transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R
      (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) =
      ((0 : RingK0 R), plusPoint.{uR, uM, uObj, uHom, uNative} R) :=
    (congrArg (fun f : C(sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R,
        targetSpace.{uR, uM, uObj, uHom, uNative} R) =>
      f (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)) hf).symm.trans hq
  exact (quillenIndependentPlusForwardProjection_apply.{uR, uM, uObj, uHom, uNative, uProbe} R _).trans
    (congrArg Prod.snd hPair)

/-- The original native constant loop maps to the same lifted cell point. -/
public theorem quillenIndependentPlusForwardProjection_point (R : Type uR) [Ring R] :
    quillenIndependentPlusForwardProjection.{uR, uM, uObj, uHom, uNative, uProbe} R
      (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) =
        plusPoint.{uR, uM, uObj, uHom, uNative} R :=
  forwardProjectionPointComputed.{uR, uM, uObj, uHom, uNative, uProbe} R

private theorem inverseSectionPointComputed (R : Type uR) [Ring R] :
    quillenIndependentPlusInverseSection.{uR, uM, uObj, uHom, uNative, uProbe} R
      (plusPoint.{uR, uM, uObj, uHom, uNative} R) =
        sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R := by
  letI : TopologicalSpace (targetSpace.{uR, uM, uObj, uHom, uNative} R) :=
    targetSpaceTopology.{uR, uM, uObj, uHom, uNative} R
  obtain ⟨_, _, e, _, hg, _, ht, _, _, _, _, _⟩ :=
    quillenIndependentPlusEquivalence_allUniverses_canonicalK0_exists.{uR, uM, uObj, uHom, uNative, uProbe} R
  have hPair : transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R
      ((0 : RingK0 R), plusPoint.{uR, uM, uObj, uHom, uNative} R) =
      sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R :=
    (congrArg (fun g : C(targetSpace.{uR, uM, uObj, uHom, uNative} R,
        sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) =>
      g ((0 : RingK0 R), plusPoint.{uR, uM, uObj, uHom, uNative} R)) hg).symm.trans ht
  exact (quillenIndependentPlusInverseSection_apply.{uR, uM, uObj, uHom, uNative, uProbe} R _).trans hPair

/-- The same lifted cell point returns to the original native constant loop. -/
public theorem quillenIndependentPlusInverseSection_point (R : Type uR) [Ring R] :
    quillenIndependentPlusInverseSection.{uR, uM, uObj, uHom, uNative, uProbe} R
      (plusPoint.{uR, uM, uObj, uHom, uNative} R) =
        sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R :=
  inverseSectionPointComputed.{uR, uM, uObj, uHom, uNative, uProbe} R

private theorem positiveMapCongr
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (n : ℕ) (f g : C(X, Y))
    (hf : f x = y) (hg : g x = y) (hfg : f = g) :
    HomotopyGroup.mapHomOfEq f hf n = HomotopyGroup.mapHomOfEq g hg n := by
  cases hfg
  rfl

private theorem positiveComparisonData_nonempty (R : Type uR) [Ring R] (n : ℕ) : Nonempty
    { i : HomotopyGroup.Pi (n + 1)
        (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) ≃*
        HomotopyGroup.Pi (n + 1)
          (plusSpace.{uR, uM, uObj, uHom, uNative} R)
          (plusPoint.{uR, uM, uObj, uHom, uNative} R) //
      (∀ a, i a = HomotopyGroup.mapHomOfEq
        (quillenIndependentPlusForwardProjection.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (quillenIndependentPlusForwardProjection_point.{uR, uM, uObj, uHom, uNative, uProbe} R) n a) ∧
      ∀ a, i.symm a = HomotopyGroup.mapHomOfEq
        (quillenIndependentPlusInverseSection.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (quillenIndependentPlusInverseSection_point.{uR, uM, uObj, uHom, uNative, uProbe} R) n a } := by
  letI : TopologicalSpace (RingK0 R) := (RingK0.discreteSpace R).str
  letI : DiscreteTopology (RingK0 R) := ⟨rfl⟩
  letI : TopologicalSpace (targetSpace.{uR, uM, uObj, uHom, uNative} R) :=
    targetSpaceTopology.{uR, uM, uObj, uHom, uNative} R
  obtain ⟨_, _, e, hf, hg, hq, ht, ⟨L⟩, ⟨S⟩, _, _, _⟩ :=
    quillenIndependentPlusEquivalence_allUniverses_canonicalK0_exists.{uR, uM, uObj, uHom, uNative, uProbe} R
  let E := HomotopyGroup.mulEquivOfBasedInverse n e.toFun e.invFun hq ht L S
  let D := HomotopyGroup.discreteProductSndMulEquiv n (0 : RingK0 R)
    (plusPoint.{uR, uM, uObj, uHom, uNative} R)
  let pr : C(targetSpace.{uR, uM, uObj, uHom, uNative} R,
      plusSpace.{uR, uM, uObj, uHom, uNative} R) := ContinuousMap.snd
  let sec : C(plusSpace.{uR, uM, uObj, uHom, uNative} R,
      targetSpace.{uR, uM, uObj, uHom, uNative} R) :=
    (ContinuousMap.const (plusSpace.{uR, uM, uObj, uHom, uNative} R)
      (0 : RingK0 R)).prodMk (ContinuousMap.id _)
  refine ⟨⟨E.trans D, ?_, ?_⟩⟩
  · intro a
    change D (E a) = _
    rw [HomotopyGroup.discreteProductSndMulEquiv_apply,
      HomotopyGroup.mulEquivOfBasedInverse_apply]
    have hPoint : (pr.comp e.toFun)
        (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) =
        plusPoint.{uR, uM, uObj, uHom, uNative} R := congrArg Prod.snd hq
    have hMaps : pr.comp e.toFun =
        quillenIndependentPlusForwardProjection.{uR, uM, uObj, uHom, uNative, uProbe} R := by
      apply ContinuousMap.ext
      intro p
      change (e.toFun p).2 = _
      exact (congrArg Prod.snd (ContinuousMap.congr_fun hf p)).trans
        (quillenIndependentPlusForwardProjection_apply.{uR, uM, uObj, uHom, uNative, uProbe} R p).symm
    have hSame := positiveMapCongr n (pr.comp e.toFun)
      (quillenIndependentPlusForwardProjection.{uR, uM, uObj, uHom, uNative, uProbe} R)
      hPoint (quillenIndependentPlusForwardProjection_point.{uR, uM, uObj, uHom, uNative, uProbe} R) hMaps
    exact (HomotopyGroup.mapHomOfEq_comp e.toFun pr hq rfl hPoint n a).symm.trans
      (congrArg (fun m => m a) hSame)
  · intro a
    change E.symm (D.symm a) = _
    have hSec : sec (plusPoint.{uR, uM, uObj, uHom, uNative} R) =
        ((0 : RingK0 R), plusPoint.{uR, uM, uObj, uHom, uNative} R) := rfl
    have hD : D.symm a = HomotopyGroup.mapHomOfEq
        (X := plusSpace.{uR, uM, uObj, uHom, uNative} R)
        (Y := targetSpace.{uR, uM, uObj, uHom, uNative} R)
        (x := plusPoint.{uR, uM, uObj, uHom, uNative} R)
        (y := ((0 : RingK0 R), plusPoint.{uR, uM, uObj, uHom, uNative} R))
        sec hSec n a := by
      exact HomotopyGroup.discreteProductSndMulEquiv_symm_apply n (0 : RingK0 R)
        (plusPoint.{uR, uM, uObj, uHom, uNative} R) a
    have hE : E.symm (HomotopyGroup.mapHomOfEq
        (X := plusSpace.{uR, uM, uObj, uHom, uNative} R)
        (Y := targetSpace.{uR, uM, uObj, uHom, uNative} R)
        (x := plusPoint.{uR, uM, uObj, uHom, uNative} R)
        (y := ((0 : RingK0 R), plusPoint.{uR, uM, uObj, uHom, uNative} R))
        sec hSec n a) = HomotopyGroup.mapHomOfEq
          (X := targetSpace.{uR, uM, uObj, uHom, uNative} R)
          (Y := sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
          (x := ((0 : RingK0 R), plusPoint.{uR, uM, uObj, uHom, uNative} R))
          (y := sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
          e.invFun ht n (HomotopyGroup.mapHomOfEq
            (X := plusSpace.{uR, uM, uObj, uHom, uNative} R)
            (Y := targetSpace.{uR, uM, uObj, uHom, uNative} R)
            (x := plusPoint.{uR, uM, uObj, uHom, uNative} R)
            (y := ((0 : RingK0 R), plusPoint.{uR, uM, uObj, uHom, uNative} R))
            sec hSec n a) := by
      exact HomotopyGroup.mulEquivOfBasedInverse_symm_apply n e.toFun e.invFun hq ht L S
        (HomotopyGroup.mapHomOfEq
          (X := plusSpace.{uR, uM, uObj, uHom, uNative} R)
          (Y := targetSpace.{uR, uM, uObj, uHom, uNative} R)
          (x := plusPoint.{uR, uM, uObj, uHom, uNative} R)
          (y := ((0 : RingK0 R), plusPoint.{uR, uM, uObj, uHom, uNative} R))
          sec hSec n a)
    have hPoint : (e.invFun.comp sec)
        (plusPoint.{uR, uM, uObj, uHom, uNative} R) =
        sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R :=
      (congrArg e.invFun hSec).trans ht
    have hMaps : e.invFun.comp sec =
        quillenIndependentPlusInverseSection.{uR, uM, uObj, uHom, uNative, uProbe} R := by
      apply ContinuousMap.ext
      intro b
      change e.invFun ((0 : RingK0 R), b) = _
      exact (ContinuousMap.congr_fun hg ((0 : RingK0 R), b)).trans
        (quillenIndependentPlusInverseSection_apply.{uR, uM, uObj, uHom, uNative, uProbe} R b).symm
    have hSame := positiveMapCongr n (e.invFun.comp sec)
      (quillenIndependentPlusInverseSection.{uR, uM, uObj, uHom, uNative, uProbe} R)
      hPoint (quillenIndependentPlusInverseSection_point.{uR, uM, uObj, uHom, uNative, uProbe} R) hMaps
    have hComp := HomotopyGroup.mapHomOfEq_comp
      (X := plusSpace.{uR, uM, uObj, uHom, uNative} R)
      (Y := targetSpace.{uR, uM, uObj, uHom, uNative} R)
      (Z := sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
      (x := plusPoint.{uR, uM, uObj, uHom, uNative} R)
      (y := ((0 : RingK0 R), plusPoint.{uR, uM, uObj, uHom, uNative} R))
      (z := sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
      sec e.invFun hSec ht hPoint n a
    have hFinal : HomotopyGroup.mapHomOfEq (e.invFun.comp sec) hPoint n a =
        HomotopyGroup.mapHomOfEq
          (quillenIndependentPlusInverseSection.{uR, uM, uObj, uHom, uNative, uProbe} R)
          (quillenIndependentPlusInverseSection_point.{uR, uM, uObj, uHom, uNative, uProbe} R) n a :=
      congrArg (fun m : HomotopyGroup.Pi (n + 1)
          (plusSpace.{uR, uM, uObj, uHom, uNative} R)
          (plusPoint.{uR, uM, uObj, uHom, uNative} R) →ₙ*
          HomotopyGroup.Pi (n + 1)
            (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
            (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) => m a) hSame
    exact (congrArg E.symm hD).trans (hE.trans (hComp.symm.trans hFinal))

private def positiveComparisonData (R : Type uR) [Ring R] (n : ℕ) :
    { i : HomotopyGroup.Pi (n + 1)
        (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) ≃*
        HomotopyGroup.Pi (n + 1)
          (plusSpace.{uR, uM, uObj, uHom, uNative} R)
          (plusPoint.{uR, uM, uObj, uHom, uNative} R) //
      (∀ a, i a = HomotopyGroup.mapHomOfEq
        (quillenIndependentPlusForwardProjection.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (quillenIndependentPlusForwardProjection_point.{uR, uM, uObj, uHom, uNative, uProbe} R) n a) ∧
      ∀ a, i.symm a = HomotopyGroup.mapHomOfEq
        (quillenIndependentPlusInverseSection.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (quillenIndependentPlusInverseSection_point.{uR, uM, uObj, uHom, uNative, uProbe} R) n a } :=
  Classical.choice (positiveComparisonData_nonempty.{uR, uM, uObj, uHom, uNative, uProbe} R n)

/-- Positive homotopy groups of the full six-universe Quillen K-space are
those of the same independently constructed plus at its original lifted point.
The full accepted Q-to-K0×plus comparison is used before projecting the
fixed discrete factor; no whole-space equivalence with the connected plus
alone is asserted. -/
public def quillenIndependentPlusPositiveHomotopyEquiv (R : Type uR) [Ring R] (n : ℕ) :
    HomotopyGroup.Pi (n + 1)
      (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
      (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) ≃*
      HomotopyGroup.Pi (n + 1)
        (plusSpace.{uR, uM, uObj, uHom, uNative} R)
        (plusPoint.{uR, uM, uObj, uHom, uNative} R) :=
  (positiveComparisonData.{uR, uM, uObj, uHom, uNative, uProbe} R n).val

private theorem positiveEquivApplyComputed (R : Type uR) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1)
      (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
      (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)) :
    quillenIndependentPlusPositiveHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R n a =
      HomotopyGroup.mapHomOfEq
        (quillenIndependentPlusForwardProjection.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (quillenIndependentPlusForwardProjection_point.{uR, uM, uObj, uHom, uNative, uProbe} R) n a :=
  (positiveComparisonData.{uR, uM, uObj, uHom, uNative, uProbe} R n).property.1 a

/-- The positive comparison is induced by the actual second coordinate of F. -/
public theorem quillenIndependentPlusPositiveHomotopyEquiv_apply (R : Type uR) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1)
      (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
      (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)) :
    quillenIndependentPlusPositiveHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R n a =
      HomotopyGroup.mapHomOfEq
        (quillenIndependentPlusForwardProjection.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (quillenIndependentPlusForwardProjection_point.{uR, uM, uObj, uHom, uNative, uProbe} R) n a :=
  positiveEquivApplyComputed.{uR, uM, uObj, uHom, uNative, uProbe} R n a

private theorem positiveEquivSymmApplyComputed (R : Type uR) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1)
      (plusSpace.{uR, uM, uObj, uHom, uNative} R)
      (plusPoint.{uR, uM, uObj, uHom, uNative} R)) :
    (quillenIndependentPlusPositiveHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R n).symm a =
      HomotopyGroup.mapHomOfEq
        (quillenIndependentPlusInverseSection.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (quillenIndependentPlusInverseSection_point.{uR, uM, uObj, uHom, uNative, uProbe} R) n a :=
  (positiveComparisonData.{uR, uM, uObj, uHom, uNative, uProbe} R n).property.2 a

/-- The inverse positive comparison is induced by G after the actual zero section. -/
public theorem quillenIndependentPlusPositiveHomotopyEquiv_symm_apply (R : Type uR) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1)
      (plusSpace.{uR, uM, uObj, uHom, uNative} R)
      (plusPoint.{uR, uM, uObj, uHom, uNative} R)) :
    (quillenIndependentPlusPositiveHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R n).symm a =
      HomotopyGroup.mapHomOfEq
        (quillenIndependentPlusInverseSection.{uR, uM, uObj, uHom, uNative, uProbe} R)
        (quillenIndependentPlusInverseSection_point.{uR, uM, uObj, uHom, uNative, uProbe} R) n a :=
  positiveEquivSymmApplyComputed.{uR, uM, uObj, uHom, uNative, uProbe} R n a

/-- The same actual pi1 comparison in additive notation for K1 consumers. -/
public def quillenIndependentPlusPiOneAddEquiv (R : Type uR) [Ring R] :
    Additive (HomotopyGroup.Pi 1
      (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)
      (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R)) ≃+
      Additive (HomotopyGroup.Pi 1
        (plusSpace.{uR, uM, uObj, uHom, uNative} R)
        (plusPoint.{uR, uM, uObj, uHom, uNative} R)) :=
  (quillenIndependentPlusPositiveHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R 0).toAdditive

end AlgebraicKTheory.QuillenPlus

end
