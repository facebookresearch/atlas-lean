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

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.SeparationQuotient.Basic
public import Mathlib.Topology.UniformSpace.Separation
public import Mathlib.Algebra.Star.StarAlgHom
public import MathlibExt.Analysis.CStarAlgebra.NonUnitalSeparationQuotient

/-!
# The involution on a seminormed ring's separation quotient

The ring, scalar operations and norm on the quotient are the existing
Mathlib operations. The isometric source involution descends along the
canonical separation map. An actual source C-star norm inequality then
supplies the C-star identity on the separated ring.

These factories are explicit locally activated dictionaries. The source
ring need not be separated, complete or nontrivial; in particular, the
zero seminorm is permitted. No global instance is registered.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SeparationQuotient

universe uA

/-- **Involution on a unital separation quotient.** The involution of a unital seminormed ring `A`, when
isometric, descends to a ring involution on its separation quotient. -/
@[instance_reducible]
def cstarStarRing
    (A : Type uA) [SeminormedRing A] [StarRing A] [NormedStarGroup A] :
    StarRing (SeparationQuotient A) :=
  nonUnitalCstarStarRing A

/-- **Classes of the separated involution.** For a unital seminormed ring `A` with isometric ring
involution and every `a ∈ A`, the separation class of `a*` is the involution of the separation class
of `a`. -/
@[simp]
theorem mk_cstarStar
    (A : Type uA) [SeminormedRing A] [StarRing A] [NormedStarGroup A] (a : A) :
    let _ : StarRing (SeparationQuotient A) := cstarStarRing A
    star (mk a) = mk (star a) := by
  let _ : StarRing (SeparationQuotient A) := cstarStarRing A
  exact mk_nonUnitalCstarStar A a

/-- **Complex scalars and the separated involution.** For a unital seminormed complex algebra `A` with
scalar-compatible isometric ring involution, the separation quotient satisfies `(c x)* =
conjugate(c) x*`. -/
theorem cstarStarModule
    (A : Type uA) [SeminormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [NormedStarGroup A] [StarModule ℂ A] :
    let _ : StarRing (SeparationQuotient A) := cstarStarRing A
    StarModule ℂ (SeparationQuotient A) := by
  let _ : StarRing (SeparationQuotient A) := cstarStarRing A
  exact nonUnitalCstarStarModule A

/-- **C*-identity on a unital separation quotient.** For a unital seminormed ring `A` with isometric
ring involution and `‖a‖² ≤ ‖a* a‖` for all `a`, the separation quotient satisfies the C*-identity
in its norm. -/
theorem cstarRing
    (A : Type uA) [SeminormedRing A] [StarRing A] [NormedStarGroup A]
    (hCStar : ∀ a : A, ‖a‖ * ‖a‖ ≤ ‖star a * a‖) :
    let _ : StarRing (SeparationQuotient A) := cstarStarRing A
    CStarRing (SeparationQuotient A) := by
  let _ : StarRing (SeparationQuotient A) := cstarStarRing A
  exact nonUnitalCstarRing A hCStar

/-- **Star homomorphism onto a separation quotient.** For a unital seminormed complex algebra `A` with
isometric ring involution, the separation projection is a unital complex star homomorphism to the
induced star-algebra quotient. -/
def mkCStarAlgHom
    (A : Type uA) [SeminormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [NormedStarGroup A] :
    let _ : StarRing (SeparationQuotient A) := cstarStarRing A
    A →⋆ₐ[ℂ] SeparationQuotient A := by
  let _ : StarRing (SeparationQuotient A) := cstarStarRing A
  exact
    { toFun := mk
      map_one' := mk_one
      map_zero' := mk_zero
      map_add' := mk_add
      map_mul' := mk_mul
      commutes' := mk_algebraMap
      map_star' := fun a => (mk_cstarStar A a).symm }

/-- **Value of the separation star homomorphism.** For a unital seminormed complex algebra `A` with
isometric ring involution, the canonical star homomorphism sends `a` to its separation-quotient
class. -/
@[simp]
theorem mkCStarAlgHom_apply
    (A : Type uA) [SeminormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [NormedStarGroup A] (a : A) :
    let _ : StarRing (SeparationQuotient A) := cstarStarRing A
    mkCStarAlgHom A a = mk a :=
  rfl

end SeparationQuotient
