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
# Uniform and positive representative properties

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
Uniformity is continuity of a↦(t↦φ_t(a)) as a map A→C_b(T,B) for the supremum norm.
Star-linearity means each φ_t is complex-linear and star-preserving. Complete positivity and
contractivity mean each φ_t is complex-linear, preserves the canonical positive cones at every
matrix level, and satisfies ‖φ_t(a)‖≤‖a‖.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra BoundedContinuousFunction

namespace AsymptoticMorphism

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **Uniform asymptotic representative.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
IsUniform φ means that there is a continuous F:A→C_b(T,B) with F(a)(t)=φ_t(a) for all a,t. The
bounded continuous function algebra C_b(T,B) carries the supremum norm.
-/
def IsUniform (φ : AsymptoticMorphism A B) : Prop :=
  ∃ F : C(A, AsymptoticTime →ᵇ B), ∀ (t : AsymptoticTime) (a : A), F a t = φ t a

/-- **Star-linear time slices.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
IsStarLinear φ means that for every t∈T, φ_t(a+b)=φ_t(a)+φ_t(b), φ_t(z•a)=z•φ_t(a), and
φ_t(star(a))=star(φ_t(a)) for all a,b∈A and z∈ℂ.
-/
def IsStarLinear (φ : AsymptoticMorphism A B) : Prop :=
  ∀ t : AsymptoticTime,
    (∀ a b : A, φ t (a + b) = φ t a + φ t b) ∧
    (∀ (z : ℂ) (a : A), φ t (z • a) = z • φ t a) ∧
    ∀ a : A, φ t (star a) = star (φ t a)

/-- **Completely positive contraction slices.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
IsCompletelyPositiveContraction φ means that for each t∈T, φ_t equals a completely positive
complex-linear map s_t:A→B with ‖s_t(a)‖≤‖a‖ for every a∈A. Positivity uses the canonical
C-star positive cones, including all matrix amplifications.
-/
def IsCompletelyPositiveContraction (φ : AsymptoticMorphism A B) : Prop :=
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  ∀ t : AsymptoticTime, ∃ s : A →CP B,
    (∀ a : A, ‖s a‖ ≤ ‖a‖) ∧ ∀ a : A, s a = φ t a

end AsymptoticMorphism
