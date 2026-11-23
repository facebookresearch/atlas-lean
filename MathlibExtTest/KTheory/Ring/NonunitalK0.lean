/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Ring.NonunitalK0
import Batteries.Tactic.Lint

open AlgebraicKTheory

noncomputable section
set_option autoImplicit false

universe u v

namespace AlgebraicKTheory.NonunitalK0.Tests

/-- Unitization applies to genuine nonunital maps, including the zero map. -/
example {I : Type u} {J : Type v} [NonUnitalRing I] [NonUnitalRing J] :
    Unitization ℤ I →+* Unitization ℤ J :=
  unitizationMap (0 : I →ₙ+* J)

/-- The native reduced group is the actual augmentation kernel at the original universe. -/
example {I : Type u} [NonUnitalRing I] (x : NonunitalK0 I) :
    FGProjectiveCat.scalarExtensionK0 (augmentation I) x.val = 0 :=
  x.property

/-- The unital compatibility chart works over a noncommutative coefficient ring. -/
example : Unitization ℤ (Matrix (Fin 2) (Fin 2) ℤ) ≃+*
    ℤ × Matrix (Fin 2) (Fin 2) ℤ :=
  unitizationUnitalEquiv _

/-- The integer target stays native even when the coefficient universe is raised. -/
example : NonunitalK0 (ULift.{1} ℤ) →+ RingK0 ℤ :=
  (FGProjectiveCat.scalarExtensionK0 (augmentation (ULift.{1} ℤ))).comp
    (AddSubgroup.subtype _)

#print axioms augmentation
#print axioms unitizationMap
#print axioms AlgebraicKTheory.NonunitalK0
#print axioms map
#print axioms map_id
#print axioms map_comp
#print axioms unitizationUnitalEquiv
#print axioms RingK0.mapNonUnitalRingHom
#print axioms RingK0.mapNonUnitalRingHom_id
#print axioms RingK0.mapNonUnitalRingHom_comp
#print axioms RingK0.mapNonUnitalRingHom_zero
#print axioms RingK0.mapNonUnitalRingHom_toNonUnitalRingHom


/-- Unital compatibility covers the actual noncommutative projective K₀ carrier. -/
example : NonunitalK0 (Matrix (Fin 2) (Fin 2) ℤ) ≃+ RingK0 (Matrix (Fin 2) (Fin 2) ℤ) :=
  unitalEquiv _

/-- The integer augmentation target remains native at a raised coefficient universe. -/
example : NonunitalK0 (ULift.{1} (Matrix (Fin 2) (Fin 2) ℤ)) ≃+
    RingK0 (ULift.{1} (Matrix (Fin 2) (Fin 2) ℤ)) :=
  unitalEquiv _

#print axioms RingK0.mapNonUnitalRingHom_add_of_orthogonal
#print axioms unitalIntegerComplement
#print axioms unitalRingInclusion
#print axioms unitalEquiv
#print axioms unitalEquiv_symm_val
#print axioms unitalEquiv_apply
#print axioms inclusion
#print axioms unitizationMap_injective
#print axioms map_unitalEquiv_symm_val
#print axioms map_unitalEquiv_symm

#lint only unusedArguments in MathlibExt.KTheory.Ring.NonunitalK0

end AlgebraicKTheory.NonunitalK0.Tests
