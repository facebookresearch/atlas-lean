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

/-!
# The same involution on a nonunital seminormed separation quotient

The source is a nonunital seminormed ring with its original isometric star.
The involution descends by the literal SeparationQuotient.map star. Ring,
scalar and norm data are the stock quotient operations. The source C-star
square inequality gives CStarRing only on this separated quotient.

These are the common implementations also used by the existing unital
quotient interfaces. All factories are explicit locally activated values.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SeparationQuotient

universe uA

/-- **Involution on a separation quotient.** Let `A` be a nonunital seminormed ring with a ring
involution preserving the seminorm. Its separation quotient identifies elements at seminorm distance
zero and carries the induced normed ring structure. The involution of `A` descends to a ring
involution on its separation quotient. -/
@[instance_reducible]
def nonUnitalCstarStarRing
    (A : Type uA) [NonUnitalSeminormedRing A] [StarRing A] [NormedStarGroup A] :
    StarRing (SeparationQuotient A) where
  star := SeparationQuotient.map (star : A → A)
  star_involutive x := by
    have hs : UniformContinuous (star : A → A) := star_isometry.uniformContinuous
    obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk x
    change SeparationQuotient.map (star : A → A)
      (SeparationQuotient.map (star : A → A) (mk a)) = mk a
    rw [map_mk hs, map_mk hs, star_star]
  star_add x y := by
    have hs : UniformContinuous (star : A → A) := star_isometry.uniformContinuous
    obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk x
    obtain ⟨b, rfl⟩ := SeparationQuotient.surjective_mk y
    change SeparationQuotient.map (star : A → A) (mk a + mk b) =
      SeparationQuotient.map (star : A → A) (mk a) +
        SeparationQuotient.map (star : A → A) (mk b)
    rw [← mk_add, map_mk hs, map_mk hs, map_mk hs, star_add, mk_add]
  star_mul x y := by
    have hs : UniformContinuous (star : A → A) := star_isometry.uniformContinuous
    obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk x
    obtain ⟨b, rfl⟩ := SeparationQuotient.surjective_mk y
    change SeparationQuotient.map (star : A → A) (mk a * mk b) =
      SeparationQuotient.map (star : A → A) (mk b) *
        SeparationQuotient.map (star : A → A) (mk a)
    rw [← mk_mul, map_mk hs, map_mk hs, map_mk hs, star_mul, mk_mul]

/-- **Representatives of the quotient involution.** Let `A` be a nonunital seminormed ring with a ring
involution preserving the seminorm. Its separation quotient identifies elements at seminorm distance
zero and carries the induced normed ring structure. For every `a ∈ A`, the class of `a*` is the
involution of the class of `a`. -/
theorem mk_nonUnitalCstarStar
    (A : Type uA) [NonUnitalSeminormedRing A] [StarRing A] [NormedStarGroup A] (a : A) :
    let _ : StarRing (SeparationQuotient A) := nonUnitalCstarStarRing A
    star (mk a) = mk (star a) := by
  let _ : StarRing (SeparationQuotient A) := nonUnitalCstarStarRing A
  change SeparationQuotient.map (star : A → A) (mk a) = mk (star a)
  exact map_mk star_isometry.uniformContinuous a

/-- **Complex scalar compatibility of the separated involution.** Let `A` be a nonunital seminormed ring
and complex seminormed vector space with a seminorm-preserving ring involution satisfying `(c a)* =
conjugate(c) a*`. The induced involution on the separation quotient satisfies the same complex
scalar compatibility. -/
theorem nonUnitalCstarStarModule
    (A : Type uA) [NonUnitalSeminormedRing A] [NormedSpace ℂ A]
    [StarRing A] [NormedStarGroup A] [StarModule ℂ A] :
    let _ : StarRing (SeparationQuotient A) := nonUnitalCstarStarRing A
    StarModule ℂ (SeparationQuotient A) := by
  let _ : StarRing (SeparationQuotient A) := nonUnitalCstarStarRing A
  refine { star_smul := ?_ }
  intro c x
  obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk x
  rw [← mk_smul, mk_nonUnitalCstarStar, star_smul, mk_smul, mk_nonUnitalCstarStar]

/-- **C*-identity on a separation quotient.** Let `A` be a nonunital seminormed ring with a ring
involution preserving the seminorm. Its separation quotient identifies elements at seminorm distance
zero and carries the induced normed ring structure. If additionally `‖a‖² ≤ ‖a* a‖` for every `a ∈
A`, the separation quotient satisfies the C*-identity. -/
theorem nonUnitalCstarRing
    (A : Type uA) [NonUnitalSeminormedRing A] [StarRing A] [NormedStarGroup A]
    (hCStar : ∀ a : A, ‖a‖ * ‖a‖ ≤ ‖star a * a‖) :
    let _ : StarRing (SeparationQuotient A) := nonUnitalCstarStarRing A
    CStarRing (SeparationQuotient A) := by
  let _ : StarRing (SeparationQuotient A) := nonUnitalCstarStarRing A
  refine { norm_mul_self_le := ?_ }
  intro x
  obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk x
  simpa only [mk_nonUnitalCstarStar, ← mk_mul, norm_mk] using hCStar a

end SeparationQuotient
