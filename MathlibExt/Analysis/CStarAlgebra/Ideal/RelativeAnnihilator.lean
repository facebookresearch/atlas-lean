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

public import MathlibExt.Algebra.Star.NonUnitalSubalgebra.RelativeAnnihilator
public import MathlibExt.Analysis.CStarAlgebra.IdealQuotient

/-!
# Closed C-star-ideal adapters for relative annihilators

The algebraic construction lives in the nonunital-subalgebra layers. These
thin adapters retain the `ClosedStarIdeal` source-facing signatures used by
the Blackadar compact-annihilator statements.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ClosedStarIdeal

universe uA

variable {A : Type uA} [NonUnitalCStarAlgebra A]

/-- **Left annihilator modulo an ideal.** Let `A` be a nonunital complex C*-algebra, `I ⊆ A` a closed
two-sided star ideal, and `D ⊆ A` a nonunital star subalgebra. The left relative annihilator is the
nonunital subalgebra of elements `x` satisfying `x d ∈ I` for every `d ∈ D`. -/
def leftAnnihilatorModulo
    (I : ClosedStarIdeal A) (D : NonUnitalStarSubalgebra ℂ A) :
    NonUnitalSubalgebra ℂ A := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  exact I.carrier.toNonUnitalSubalgebra.leftAnnihilatorModulo (D : Set A)

/-- **Right annihilator modulo an ideal.** Let `A` be a nonunital complex C*-algebra, `I ⊆ A` a closed
two-sided star ideal, and `D ⊆ A` a nonunital star subalgebra. The right relative annihilator is the
nonunital subalgebra of elements `x` satisfying `d x ∈ I` for every `d ∈ D`. -/
def rightAnnihilatorModulo
    (I : ClosedStarIdeal A) (D : NonUnitalStarSubalgebra ℂ A) :
    NonUnitalSubalgebra ℂ A := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  exact I.carrier.toNonUnitalSubalgebra.rightAnnihilatorModulo (D : Set A)

/-- **Two-sided annihilator modulo an ideal.** Let `A` be a nonunital complex C*-algebra, `I ⊆ A` a
closed two-sided star ideal, and `D ⊆ A` a nonunital star subalgebra. The two-sided relative
annihilator is the nonunital star subalgebra of elements `x` such that `x d ∈ I` and `d x ∈ I` for
every `d ∈ D`. -/
def annihilatorModulo
    (I : ClosedStarIdeal A) (D : NonUnitalStarSubalgebra ℂ A) :
    NonUnitalStarSubalgebra ℂ A := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  exact NonUnitalStarSubalgebra.annihilatorModulo I.carrier D

@[simp]
theorem mem_leftAnnihilatorModulo_iff
    (I : ClosedStarIdeal A) (D : NonUnitalStarSubalgebra ℂ A) (x : A) :
    x ∈ I.leftAnnihilatorModulo D ↔ ∀ d ∈ D, x * d ∈ I := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  change x ∈ I.carrier.toNonUnitalSubalgebra.leftAnnihilatorModulo
    (D : Set A) ↔ ∀ d ∈ D, x * d ∈ I.carrier
  exact NonUnitalSubalgebra.mem_leftAnnihilatorModulo_iff
    I.carrier.toNonUnitalSubalgebra (D : Set A) x

@[simp]
theorem mem_rightAnnihilatorModulo_iff
    (I : ClosedStarIdeal A) (D : NonUnitalStarSubalgebra ℂ A) (x : A) :
    x ∈ I.rightAnnihilatorModulo D ↔ ∀ d ∈ D, d * x ∈ I := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  change x ∈ I.carrier.toNonUnitalSubalgebra.rightAnnihilatorModulo
    (D : Set A) ↔ ∀ d ∈ D, d * x ∈ I.carrier
  exact NonUnitalSubalgebra.mem_rightAnnihilatorModulo_iff
    I.carrier.toNonUnitalSubalgebra (D : Set A) x

/-- **Intersection description of the relative annihilator.** Let `A` be a nonunital complex C*-algebra,
`I ⊆ A` a closed two-sided star ideal, and `D ⊆ A` a nonunital star subalgebra. An element belongs
to the two-sided relative annihilator exactly when it belongs to both the left and right relative
annihilators. -/
theorem mem_annihilatorModulo_iff_sides
    (I : ClosedStarIdeal A) (D : NonUnitalStarSubalgebra ℂ A) (x : A) :
    x ∈ I.annihilatorModulo D ↔
      x ∈ I.leftAnnihilatorModulo D ∧
        x ∈ I.rightAnnihilatorModulo D := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  change x ∈ NonUnitalStarSubalgebra.annihilatorModulo I.carrier D ↔
    x ∈ I.carrier.toNonUnitalSubalgebra.leftAnnihilatorModulo (D : Set A) ∧
      x ∈ I.carrier.toNonUnitalSubalgebra.rightAnnihilatorModulo (D : Set A)
  exact NonUnitalStarSubalgebra.mem_annihilatorModulo_iff_sides I.carrier D x

/-- **Membership in the relative annihilator.** Let `A` be a nonunital complex C*-algebra, `I ⊆ A` a
closed two-sided star ideal, and `D ⊆ A` a nonunital star subalgebra. For `x ∈ A`, membership in the
two-sided relative annihilator is equivalent to `x d ∈ I` and `d x ∈ I` for every `d ∈ D`. -/
@[simp]
theorem mem_annihilatorModulo_iff
    (I : ClosedStarIdeal A) (D : NonUnitalStarSubalgebra ℂ A) (x : A) :
    x ∈ I.annihilatorModulo D ↔
      (∀ d ∈ D, x * d ∈ I) ∧ ∀ d ∈ D, d * x ∈ I := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  change x ∈ NonUnitalStarSubalgebra.annihilatorModulo I.carrier D ↔
    (∀ d ∈ D, x * d ∈ I.carrier) ∧ ∀ d ∈ D, d * x ∈ I.carrier
  exact NonUnitalStarSubalgebra.mem_annihilatorModulo_iff I.carrier D x

/-- **Left multiplication preserves left relative annihilation.** Let `A` be a nonunital complex
C*-algebra, `I ⊆ A` a closed two-sided star ideal, and `D ⊆ A` a nonunital star subalgebra. If `x d
∈ I` for every `d ∈ D`, then `(a x)d ∈ I` for every `a ∈ A` and `d ∈ D`. -/
theorem mul_mem_leftAnnihilatorModulo_left
    (I : ClosedStarIdeal A) (D : NonUnitalStarSubalgebra ℂ A)
    (a : A) {x : A} (hx : x ∈ I.leftAnnihilatorModulo D) :
    a * x ∈ I.leftAnnihilatorModulo D := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  change x ∈ I.carrier.toNonUnitalSubalgebra.leftAnnihilatorModulo
    (D : Set A) at hx
  change a * x ∈ I.carrier.toNonUnitalSubalgebra.leftAnnihilatorModulo
    (D : Set A)
  exact NonUnitalSubalgebra.mul_mem_leftAnnihilatorModulo_left
    I.carrier.toNonUnitalSubalgebra (D : Set A) a hx

/-- **Right multiplication preserves right relative annihilation.** Let `A` be a nonunital complex
C*-algebra, `I ⊆ A` a closed two-sided star ideal, and `D ⊆ A` a nonunital star subalgebra. If `d x
∈ I` for every `d ∈ D`, then `d(x a) ∈ I` for every `a ∈ A` and `d ∈ D`. -/
theorem mul_mem_rightAnnihilatorModulo_right
    (I : ClosedStarIdeal A) (D : NonUnitalStarSubalgebra ℂ A)
    {x : A} (hx : x ∈ I.rightAnnihilatorModulo D) (a : A) :
    x * a ∈ I.rightAnnihilatorModulo D := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  change x ∈ I.carrier.toNonUnitalSubalgebra.rightAnnihilatorModulo
    (D : Set A) at hx
  change x * a ∈ I.carrier.toNonUnitalSubalgebra.rightAnnihilatorModulo
    (D : Set A)
  exact NonUnitalSubalgebra.mul_mem_rightAnnihilatorModulo_right
    I.carrier.toNonUnitalSubalgebra (D : Set A) hx a

/-- **Star exchanges left and right relative annihilators.** Let `A` be a nonunital complex C*-algebra,
`I ⊆ A` a closed two-sided star ideal, and `D ⊆ A` a nonunital star subalgebra. An element `x*` lies
in the right relative annihilator exactly when `x` lies in the left relative annihilator. -/
theorem star_mem_rightAnnihilatorModulo_iff
    (I : ClosedStarIdeal A) (D : NonUnitalStarSubalgebra ℂ A) (x : A) :
    star x ∈ I.rightAnnihilatorModulo D ↔
      x ∈ I.leftAnnihilatorModulo D := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  change star x ∈ I.carrier.toNonUnitalSubalgebra.rightAnnihilatorModulo
      (D : Set A) ↔
    x ∈ I.carrier.toNonUnitalSubalgebra.leftAnnihilatorModulo (D : Set A)
  exact NonUnitalStarSubalgebra.star_mem_rightAnnihilatorModulo_iff
    I.carrier D x

/-- **Star exchanges right and left relative annihilators.** Let `A` be a nonunital complex C*-algebra,
`I ⊆ A` a closed two-sided star ideal, and `D ⊆ A` a nonunital star subalgebra. An element `x*` lies
in the left relative annihilator exactly when `x` lies in the right relative annihilator. -/
theorem star_mem_leftAnnihilatorModulo_iff
    (I : ClosedStarIdeal A) (D : NonUnitalStarSubalgebra ℂ A) (x : A) :
    star x ∈ I.leftAnnihilatorModulo D ↔
      x ∈ I.rightAnnihilatorModulo D := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  change star x ∈ I.carrier.toNonUnitalSubalgebra.leftAnnihilatorModulo
      (D : Set A) ↔
    x ∈ I.carrier.toNonUnitalSubalgebra.rightAnnihilatorModulo (D : Set A)
  exact NonUnitalStarSubalgebra.star_mem_leftAnnihilatorModulo_iff
    I.carrier D x

/-- **The modulus ideal lies in its relative annihilator.** Let `A` be a nonunital complex C*-algebra,
`I ⊆ A` a closed two-sided star ideal, and `D ⊆ A` a nonunital star subalgebra. Every `x ∈ I`
belongs to the two-sided relative annihilator of `D` modulo `I`. -/
theorem carrier_le_annihilatorModulo
    (I : ClosedStarIdeal A) (D : NonUnitalStarSubalgebra ℂ A) :
    I.carrier ≤ I.annihilatorModulo D := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  change I.carrier ≤ NonUnitalStarSubalgebra.annihilatorModulo I.carrier D
  exact NonUnitalStarSubalgebra.le_annihilatorModulo I.carrier D

end ClosedStarIdeal
