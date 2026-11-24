/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Basic
public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-!
# Separate uniform, star-linear and CP-contraction representative properties

None of these is added to the raw asymptotic-morphism structure. Uniformity
means an actual continuous map into the bounded continuous function algebra
with its supremum topology, not only joint continuity.

CP maps use the canonical spectral orders locally inside the property; the
raw morphism's norm/topology dictionaries are unchanged.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra BoundedContinuousFunction

namespace AsymptoticMorphism

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The actual continuous A->BCF(Time,B) uniform representative property. -/
def IsUniform (φ : AsymptoticMorphism A B) : Prop :=
  ∃ F : C(A, AsymptoticTime →ᵇ B), ∀ (t : AsymptoticTime) (a : A), F a t = φ t a

/-- Exact star-linear slices, with no boundedness or continuity-in-a premise. -/
def IsStarLinear (φ : AsymptoticMorphism A B) : Prop :=
  ∀ t : AsymptoticTime,
    (∀ a b : A, φ t (a + b) = φ t a + φ t b) ∧
    (∀ (z : ℂ) (a : A), φ t (z • a) = z • φ t a) ∧
    ∀ a : A, φ t (star a) = star (φ t a)

/-- Actual completely positive linear contraction slices for the canonical
C-star orders; no exact algebra homomorphism property is assumed. -/
def IsCompletelyPositiveContraction (φ : AsymptoticMorphism A B) : Prop :=
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  ∀ t : AsymptoticTime, ∃ s : A →CP B,
    (∀ a : A, ‖s a‖ ≤ ‖a‖) ∧ ∀ a : A, s a = φ t a

end AsymptoticMorphism
