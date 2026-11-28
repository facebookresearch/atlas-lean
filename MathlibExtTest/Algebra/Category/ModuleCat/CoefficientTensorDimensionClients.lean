/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.TorPID
public import MathlibExt.Algebra.Category.ModuleCat.ProjectiveDimensionFunctor
public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor.Flat
public import MathlibExt.Algebra.Category.ModuleCat.UliftCoherenceSelf
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Ring.Prod

/-!
# Torsion, flat tensor factors and coefficient-universe transport

Degree-two Tor over the integers vanishes for two copies of ZMod 2. Neither argument is
assumed projective. Tensor additivity and flat-factor homology preservation are instantiated
in unequal coefficient carrier universes. A module in an existing lifted carrier universe
uses the contained-ULift self-isomorphism on the nonzero coefficient five.

Restriction along the nonidentity swap of the integer product ring transports projective
bounds and projective dimension, using forward additivity and native inverse inference.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CoefficientTensorDimensionClients

private abbrev Z2 : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ZMod 2)
private abbrev regularZ : ModuleCat.{0} ℤ := ModuleCat.of ℤ ℤ
private abbrev liftedZ2 : ModuleCat.{1} ℤ := ModuleCat.of ℤ (ULift.{1} (ZMod 2))
private abbrev liftedZ : ModuleCat.{1} ℤ := ModuleCat.of ℤ (ULift.{1} ℤ)

-- The second derived argument has integer torsion, so no projective-argument instance is used.
example : IsZero (((CategoryTheory.Tor (ModuleCat.{0} ℤ) 2).obj Z2).obj Z2) :=
  CategoryTheory.isZero_Tor_of_two_le_of_pid Z2 Z2 2 (by decide)

example : ((ModuleCat.tensorBifunctorAt.{0, 0, 1} ℤ).flip.obj liftedZ2).Additive :=
  inferInstance

example : (ModuleCat.tensorRightFunctorAt.{0, 1, 0} ℤ liftedZ2).Additive :=
  inferInstance

-- The fixed regular integer module is flat, while the varying carrier may live in universe one.
example : ((ModuleCat.tensorBifunctorAt.{0, 0, 1} ℤ).obj regularZ).PreservesHomology :=
  ModuleCat.tensorBifunctorAt_obj_preservesHomology.{0, 0, 1} ℤ regularZ

example : (ModuleCat.tensorRightFunctorAt.{0, 0, 1} ℤ regularZ).PreservesHomology :=
  ModuleCat.tensorBifunctorAt_flip_obj_preservesHomology.{0, 1, 0} ℤ regularZ

example :
    ((ModuleCat.uliftFunctorSelfIso.{1, 0} ℤ).hom.app liftedZ).hom
      (ULift.up (ULift.up (5 : ℤ))) = ULift.up (5 : ℤ) := rfl

example :
    ((ModuleCat.uliftFunctorSelfIso.{1, 0} ℤ).inv.app liftedZ).hom
      (ULift.up (5 : ℤ)) = ULift.up (ULift.up (5 : ℤ)) := rfl

private abbrev P := ℤ × ℤ
private def swapRing : P ≃+* P := RingEquiv.prodComm
private abbrev swapEquivalence : ModuleCat.{0} P ≌ ModuleCat.{0} P :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv swapRing
private abbrev regularP : ModuleCat.{0} P := ModuleCat.of P P

example : swapEquivalence.functor.Additive := inferInstance
example : swapEquivalence.inverse.Additive := inferInstance

example : HasProjectiveDimensionLE (swapEquivalence.functor.obj regularP) 0 :=
  (ModuleCat.hasProjectiveDimensionLE_equivalence_iff swapEquivalence regularP 0).mpr
    ((projective_iff_hasProjectiveDimensionLE_zero regularP).mp (by infer_instance))

example : projectiveDimension (swapEquivalence.functor.obj regularP) =
    projectiveDimension regularP :=
  ModuleCat.projectiveDimension_equivalence swapEquivalence regularP

-- The restriction functor changes the two scalar coordinates, so the equivalence is nonidentity.
example :
    (((swapEquivalence.functor.obj regularP).smul ((3, 5) : P)).asHom).hom
        ((7, 11) : P) = ((35, 33) : P) := by
  have h := congrArg
    (fun f : End ((forget₂ (ModuleCat P) AddCommGrpCat).obj regularP) =>
      f.asHom.hom ((7, 11) : P))
    (ModuleCat.smul_restrictScalars swapRing.toRingHom ((3, 5) : P) regularP)
  simpa [swapEquivalence, swapRing, ModuleCat.smul] using h

end CoefficientTensorDimensionClients
