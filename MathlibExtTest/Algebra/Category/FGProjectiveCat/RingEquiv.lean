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

public import MathlibExt.Algebra.Category.FGProjectiveCat.RingEquiv
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

open CategoryTheory

universe v uR uS uT w

namespace FGProjectiveCat.RingEquivChecks

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [Ring R] [Ring S] [Ring T]

private noncomputable def genericTransport (e : R ≃+* S) :
    FGProjectiveCat.{v} S ≌ FGProjectiveCat.{v} R :=
  FGProjectiveCat.restrictScalarsEquivalenceOfRingEquiv e

private theorem genericTransport_obj_property (e : R ≃+* S)
    (P : FGProjectiveCat.{v} S) :
    Module.Finite R ((genericTransport e).functor.obj P) ∧
      Module.Projective R ((genericTransport e).functor.obj P) :=
  ((genericTransport e).functor.obj P).property

private theorem genericTransport_map_characteristic (e : R ≃+* S)
    {P Q : FGProjectiveCat.{v} S} (g : P ⟶ Q) :
    ((genericTransport e).functor.map g).hom =
      (ModuleCat.restrictScalars e.toRingHom).map g.hom :=
  FGProjectiveCat.restrictScalarsEquivalenceOfRingEquiv_functor_map_hom e g

private theorem genericTransport_smul_characteristic (e : R ≃+* S)
    (P : FGProjectiveCat.{v} S) (r : R) (x : P) :
    r • (show (genericTransport e).functor.obj P from x) = e r • x :=
  rfl

private noncomputable def independentUniverseTransport
    (R : Type uR) [Ring R] :
    FGProjectiveCat.{v} R ≌ FGProjectiveCat.{v} (ULift.{w} R) :=
  FGProjectiveCat.restrictScalarsEquivalenceOfRingEquiv
    (ULift.ringEquiv : ULift.{w} R ≃+* R)

private abbrev NoncommutativeTestRing := Matrix (Fin 2) (Fin 2) ℤ

private noncomputable def noncommutativeIdentityTransport :
    FGProjectiveCat.{v} NoncommutativeTestRing ≌
      FGProjectiveCat.{v} NoncommutativeTestRing :=
  FGProjectiveCat.restrictScalarsEquivalenceOfRingEquiv
    (RingEquiv.refl NoncommutativeTestRing)

private noncomputable def zeroRingIdentityTransport :
    FGProjectiveCat.{v} (ZMod 1) ≌ FGProjectiveCat.{v} (ZMod 1) :=
  FGProjectiveCat.restrictScalarsEquivalenceOfRingEquiv
    (RingEquiv.refl (ZMod 1))

private abbrev ZeroRingTestObject : FGProjectiveCat.{v} (ZMod 1) :=
  FGProjectiveCat.of (R := ZMod 1) PUnit

private theorem zeroRing_identity_component :
    Nonempty
      ((zeroRingIdentityTransport).functor.obj ZeroRingTestObject ≅
        ZeroRingTestObject) :=
  ⟨(FGProjectiveCat.restrictScalarsEquivalenceOfRingEquivId
    (ZMod 1)).app ZeroRingTestObject⟩

private noncomputable def identityCoherence (R : Type uR) [Ring R] :
    (FGProjectiveCat.restrictScalarsEquivalenceOfRingEquiv
      (RingEquiv.refl R)).functor ≅ 𝟭 (FGProjectiveCat.{v} R) :=
  FGProjectiveCat.restrictScalarsEquivalenceOfRingEquivId R

private noncomputable def inverseCoherence (e : R ≃+* S) :
    (FGProjectiveCat.restrictScalarsEquivalenceOfRingEquiv e.symm).functor ≅
      (FGProjectiveCat.restrictScalarsEquivalenceOfRingEquiv e).inverse :=
  FGProjectiveCat.restrictScalarsEquivalenceOfRingEquivSymm e

private noncomputable def compositionCoherence
    (e : R ≃+* S) (f : S ≃+* T) :
    (FGProjectiveCat.restrictScalarsEquivalenceOfRingEquiv
      (e.trans f)).functor ≅
      (FGProjectiveCat.restrictScalarsEquivalenceOfRingEquiv f).functor ⋙
        (FGProjectiveCat.restrictScalarsEquivalenceOfRingEquiv e).functor :=
  FGProjectiveCat.restrictScalarsEquivalenceOfRingEquivComp e f

private theorem identityCoherence_apply (R : Type uR) [Ring R]
    (P : FGProjectiveCat.{v} R) (x : P) :
    ((identityCoherence R).hom.app P).hom.hom x = x :=
  rfl

private theorem inverseCoherence_apply (e : R ≃+* S)
    (P : FGProjectiveCat.{v} R) (x : P) :
    ((inverseCoherence e).hom.app P).hom.hom x = x :=
  rfl

private theorem compositionCoherence_apply
    (e : R ≃+* S) (f : S ≃+* T)
    (P : FGProjectiveCat.{v} T) (x : P) :
    ((compositionCoherence e f).hom.app P).hom.hom x = x :=
  rfl

end FGProjectiveCat.RingEquivChecks
