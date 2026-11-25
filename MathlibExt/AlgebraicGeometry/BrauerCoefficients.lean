/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`TauCeti/NumberTheory/ClassFieldTheory/Brauer/Basic.lean` and
`TauCeti/RepresentationTheory/Homological/ContCohomology/CohomologyComparison.lean`
(TauCeti, revision `62bbc0596dc3539d488232e4e924a338548ea0a9`):
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Tau Ceti contributors.

Modifications: the same units action is constructed directly by restriction of
algebraic-closure automorphisms to the separable closure, and Mathlib's homogeneous cocycles
are used, so that no second quotient or coefficient model is introduced.
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Instances.Int
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Separable-closure units and native continuous Brauer classes

The coefficient object is the additive group of actual separable-closure
units, with the discrete topology (a scoped instance, active where this
namespace is opened). The group acting is Mathlib's absolute Galois group, and
its action is restriction to that same separable closure. This is the
coefficient/action dictionary of Tau's `unitsRep`, without importing Tau.

Classes and cocycles below are Mathlib's continuous cohomology and its actual
homogeneous cocycles. Inhomogeneous coordinates are fixed at `(1,g,g*h)`.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.BrauerCoefficients

open CategoryTheory ContRepresentation

variable (K : Type) [Field K]

/-- The actual units of the separable closure, written additively. -/
abbrev SepUnits := Additive (SeparableClosure K)ˣ

/-- The arithmetic coefficient topology is discrete. It is scoped: `SepUnits K` unfolds to
`Additive (SeparableClosure K)ˣ`, which should keep Mathlib's units topology elsewhere. -/
scoped instance : TopologicalSpace (SepUnits K) := ⊥

scoped instance : DiscreteTopology (SepUnits K) := ⟨rfl⟩

/-- An absolute Galois automorphism acts by its actual restriction. -/
def unitAction (g : Field.absoluteGaloisGroup K) : SepUnits K ≃+ SepUnits K :=
  (Units.mapEquiv g.separableClosure.toMulEquiv).toAdditive

@[simp] theorem unitAction_apply (g : Field.absoluteGaloisGroup K)
    (u : (SeparableClosure K)ˣ) :
    Additive.toMul (unitAction K g (Additive.ofMul u)) =
      Units.map g.separableClosure.toMonoidHom u := rfl

/-- The discrete continuous representation of the actual separable units.
`ContRepresentation` requires each linear action map to be continuous;
the stronger joint continuity is exposed separately in the derived dictionary. -/
def unitsRep : TopRep ℤ (Field.absoluteGaloisGroup K) :=
  TopRep.of {
    toMonoidHom := {
      toFun g := {
        toLinearMap := (unitAction K g).toIntLinearEquiv.toLinearMap
        cont := continuous_of_discreteTopology }
      map_one' := by
        ext u
        rfl
      map_mul' g h := by
        ext u
        rfl } }

instance unitsRepDiscreteTopology : DiscreteTopology (unitsRep K).V :=
  inferInstanceAs (DiscreteTopology (SepUnits K))

/-- The coefficient dictionary has the identity underlying additive map. -/
def unitsEquiv : SepUnits K ≃+ (unitsRep K).V := AddEquiv.refl _

@[simp] theorem unitsRep_action (g : Field.absoluteGaloisGroup K) (u : SepUnits K) :
    (unitsRep K).ρ g u = unitAction K g u := rfl

/-- The action on the additive unit carrier is exactly restriction of automorphisms. -/
instance sepUnitsAction : DistribMulAction (Field.absoluteGaloisGroup K) (SepUnits K) where
  smul g u := unitAction K g u
  one_smul u := by rfl
  mul_smul g h u := by rfl
  smul_zero g := (unitAction K g).map_zero
  smul_add g u v := (unitAction K g).map_add u v

instance unitsRepAction :
    DistribMulAction (Field.absoluteGaloisGroup K) (unitsRep K).V :=
  inferInstanceAs (DistribMulAction (Field.absoluteGaloisGroup K) (SepUnits K))

/-- The same units action is jointly continuous for the discrete topology.
Its stabilizer is the open Krull stabilizer of the unit's underlying element. -/
instance unitsRepContinuousSMul :
    ContinuousSMul (Field.absoluteGaloisGroup K) (unitsRep K).V := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro u
  have heq :
      (MulAction.stabilizer (Field.absoluteGaloisGroup K) u :
        Set (Field.absoluteGaloisGroup K)) =
      (MulAction.stabilizer Gal(AlgebraicClosure K/K)
        ((u.toMul : (SeparableClosure K)ˣ).val : AlgebraicClosure K) :
        Set Gal(AlgebraicClosure K/K)) := by
    ext g
    change unitAction K g u = u ↔
      g.toRingEquiv
        ((u.toMul : (SeparableClosure K)ˣ).val : AlgebraicClosure K) =
        ((u.toMul : (SeparableClosure K)ˣ).val : AlgebraicClosure K)
    constructor
    · intro h
      exact congrArg (fun a : SepUnits K =>
        ((a.toMul : (SeparableClosure K)ˣ).val : AlgebraicClosure K)) h
    · intro h
      change Additive.ofMul _ = Additive.ofMul _
      congr 1
      apply Units.ext
      apply Subtype.ext
      exact h
  rw [heq]
  exact stabilizer_isOpen_of_isIntegral _

/-- Tau's native cohomological Brauer carrier, on the same actual units. -/
abbrev Br := continuousCohomology 2 (unitsRep K)

/-- Continuous homogeneous two-cocycles of the absolute Galois group of `K` with coefficients in
`unitsRep K`, the units of the separable closure with the discrete topology and the Galois action:
the kernel of the differential leaving degree two in the complex of continuous homogeneous
cochains. -/
abbrev TwoCocycles := ContinuousCohomology.cocycles (unitsRep K) 2

/-- The canonical quotient map from actual cocycles to actual Brauer classes. -/
def cocycleClass : TwoCocycles K →+ Br K :=
  (ContinuousCohomology.π (unitsRep K) 2).hom.toLinearMap.toAddMonoidHom

/-- The uncurried inhomogeneous value of an actual homogeneous two-cocycle.
The ordering is the standard `(1,g,g*h)`, not `(1,g,h)`. -/
def inhomogeneousTwoCocycleValue {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (X : TopRep ℤ G) (c : ContinuousCohomology.cocycles X 2)
    (g h : G) : X.V :=
  ((TopRep.homogeneousCochains X).iCycles 2 c).val 1 g (g * h)

/-- The native inhomogeneous coordinates of a separable-closure-unit cocycle. -/
def inhomogeneousValue (c : TwoCocycles K) (g h : Field.absoluteGaloisGroup K) :
    SepUnits K :=
  inhomogeneousTwoCocycleValue (unitsRep K) c g h

/-- The inhomogeneous values `(g, h) ↦ c(1, g, g h)` of a two-cocycle `c`, as a locally constant
function on `G_K × G_K` with values in the units of the separable closure, where the absolute
Galois group `G_K` of `K` is assumed locally compact. -/
def locallyConstantValues [LocallyCompactSpace (Field.absoluteGaloisGroup K)]
    (c : TwoCocycles K) :
    LocallyConstant (Field.absoluteGaloisGroup K × Field.absoluteGaloisGroup K) (SepUnits K) :=
  { toFun p := inhomogeneousValue K c p.1 p.2
    isLocallyConstant := (IsLocallyConstant.iff_continuous _).mpr <|
      ((((TopRep.homogeneousCochains (unitsRep K)).iCycles 2 c).val 1).uncurry.continuous).comp
        (continuous_fst.prodMk (continuous_fst.mul continuous_snd)) }

@[simp] theorem locallyConstantValues_apply
    [LocallyCompactSpace (Field.absoluteGaloisGroup K)] (c : TwoCocycles K)
    (g h : Field.absoluteGaloisGroup K) :
    locallyConstantValues K c (g, h) = inhomogeneousValue K c g h := rfl

@[simp] theorem cocycleClass_zero : cocycleClass K 0 = 0 := map_zero _

@[simp] theorem inhomogeneousValue_zero (g h : Field.absoluteGaloisGroup K) :
    inhomogeneousValue K 0 g h = 0 := by
  simp [inhomogeneousValue, inhomogeneousTwoCocycleValue]
  rfl

/-- The invariant target is the actual quotient `ℚ/ℤ`. -/
abbrev InvariantTarget := AddCircle (1 : ℚ)

/-- Restriction acts on local invariants by multiplication by the field degree. -/
def invariantRestriction (n : ℕ) : InvariantTarget →+ InvariantTarget :=
  n • AddMonoidHom.id _

@[simp] theorem invariantRestriction_apply (n : ℕ) (q : InvariantTarget) :
    invariantRestriction n q = n • q := rfl

/-- Corestriction preserves a nonarchimedean local invariant. -/
def invariantCorestriction : InvariantTarget →+ InvariantTarget := AddMonoidHom.id _

@[simp] theorem invariantCorestriction_apply (q : InvariantTarget) :
    invariantCorestriction q = q := rfl

end AlgebraicGeometry.BrauerCoefficients
