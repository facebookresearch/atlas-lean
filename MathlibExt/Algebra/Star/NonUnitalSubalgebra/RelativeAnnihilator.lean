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

public import MathlibExt.Algebra.NonUnitalSubalgebra.RelativeAnnihilator
public import Mathlib.Algebra.Star.NonUnitalSubalgebra

/-!
# Star-stable relative annihilators

The intersection of the algebraic left and right relative annihilators is
star stable when both the modulus and the tested subalgebra are star stable.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace NonUnitalStarSubalgebra

universe uR uA

variable {R : Type uR} {A : Type uA}
variable [CommSemiring R] [NonUnitalSemiring A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A] [StarRing A]

/-- Let `R` be a commutative semiring and `A` a possibly nonunital star semiring with an `R`-module
structure compatible with multiplication on both sides. Let `I` and `D` be star-closed nonunital
`R`-subalgebras, with `I` two-sided. The relative annihilator consists of `x` satisfying both `x*d ∈
I` and `d*x ∈ I` for every `d ∈ D`.
-/
def annihilatorModulo
    (I D : NonUnitalStarSubalgebra R A)
    [I.toNonUnitalSubalgebra.IsTwoSided] :
    NonUnitalStarSubalgebra R A where
  carrier := {x |
    x ∈ I.toNonUnitalSubalgebra.leftAnnihilatorModulo (D : Set A) ∧
      x ∈ I.toNonUnitalSubalgebra.rightAnnihilatorModulo (D : Set A)}
  zero_mem' := by
    exact ⟨(I.toNonUnitalSubalgebra.leftAnnihilatorModulo
        (D : Set A)).zero_mem,
      (I.toNonUnitalSubalgebra.rightAnnihilatorModulo
        (D : Set A)).zero_mem⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨(I.toNonUnitalSubalgebra.leftAnnihilatorModulo
        (D : Set A)).add_mem hx.1 hy.1,
      (I.toNonUnitalSubalgebra.rightAnnihilatorModulo
        (D : Set A)).add_mem hx.2 hy.2⟩
  mul_mem' := by
    intro x y hx hy
    exact ⟨(I.toNonUnitalSubalgebra.leftAnnihilatorModulo
        (D : Set A)).mul_mem hx.1 hy.1,
      (I.toNonUnitalSubalgebra.rightAnnihilatorModulo
        (D : Set A)).mul_mem hx.2 hy.2⟩
  smul_mem' := by
    intro r x hx
    exact ⟨(I.toNonUnitalSubalgebra.leftAnnihilatorModulo
        (D : Set A)).smul_mem r hx.1,
      (I.toNonUnitalSubalgebra.rightAnnihilatorModulo
        (D : Set A)).smul_mem r hx.2⟩
  star_mem' := by
    intro x hx
    constructor
    · rw [NonUnitalSubalgebra.mem_leftAnnihilatorModulo_iff]
      intro d hd
      have h :=
        (NonUnitalSubalgebra.mem_rightAnnihilatorModulo_iff
          I.toNonUnitalSubalgebra (D : Set A) x).1 hx.2
          (star d) (D.star_mem' hd)
      have hs := I.star_mem' h
      simpa only [star_mul, star_star, NonUnitalStarSubalgebra.mem_carrier,
        NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra] using hs
    · rw [NonUnitalSubalgebra.mem_rightAnnihilatorModulo_iff]
      intro d hd
      have h :=
        (NonUnitalSubalgebra.mem_leftAnnihilatorModulo_iff
          I.toNonUnitalSubalgebra (D : Set A) x).1 hx.1
          (star d) (D.star_mem' hd)
      have hs := I.star_mem' h
      simpa only [star_mul, star_star, NonUnitalStarSubalgebra.mem_carrier,
        NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra] using hs

/-- Let `R` be a commutative semiring and `A` a possibly nonunital star semiring with an `R`-module
structure compatible with multiplication on both sides. Let `I` and `D` be star-closed nonunital
`R`-subalgebras, with `I` two-sided. An element lies in the relative annihilator exactly when it
lies in both the left and right relative annihilators of the underlying subalgebra.
-/
theorem mem_annihilatorModulo_iff_sides
    (I D : NonUnitalStarSubalgebra R A)
    [I.toNonUnitalSubalgebra.IsTwoSided] (x : A) :
    x ∈ I.annihilatorModulo D ↔
      x ∈ I.toNonUnitalSubalgebra.leftAnnihilatorModulo (D : Set A) ∧
        x ∈ I.toNonUnitalSubalgebra.rightAnnihilatorModulo (D : Set A) :=
  Iff.rfl

/-- Let `R` be a commutative semiring and `A` a possibly nonunital star semiring with an `R`-module
structure compatible with multiplication on both sides. Let `I` and `D` be star-closed nonunital
`R`-subalgebras, with `I` two-sided. Membership of `x` is equivalent to the two conditions `∀ d ∈ D,
x*d ∈ I` and `∀ d ∈ D, d*x ∈ I`.
-/
@[simp]
theorem mem_annihilatorModulo_iff
    (I D : NonUnitalStarSubalgebra R A)
    [I.toNonUnitalSubalgebra.IsTwoSided] (x : A) :
    x ∈ I.annihilatorModulo D ↔
      (∀ d ∈ D, x * d ∈ I) ∧ ∀ d ∈ D, d * x ∈ I :=
  Iff.rfl

/-- Let `R` be a commutative semiring and `A` a possibly nonunital star semiring with an `R`-module
structure compatible with multiplication on both sides. Let `I` and `D` be star-closed nonunital
`R`-subalgebras, with `I` two-sided. The element `star x` annihilates `D` on the right modulo `I`
exactly when `x` annihilates it on the left.
-/
theorem star_mem_rightAnnihilatorModulo_iff
    (I D : NonUnitalStarSubalgebra R A)
    [I.toNonUnitalSubalgebra.IsTwoSided] (x : A) :
    star x ∈ I.toNonUnitalSubalgebra.rightAnnihilatorModulo (D : Set A) ↔
      x ∈ I.toNonUnitalSubalgebra.leftAnnihilatorModulo (D : Set A) := by
  constructor
  · intro hx
    rw [NonUnitalSubalgebra.mem_leftAnnihilatorModulo_iff]
    intro d hd
    have h :=
      (NonUnitalSubalgebra.mem_rightAnnihilatorModulo_iff
        I.toNonUnitalSubalgebra (D : Set A) (star x)).1 hx
        (star d) (D.star_mem' hd)
    have hs := I.star_mem' h
    simpa only [star_mul, star_star, NonUnitalStarSubalgebra.mem_carrier,
      NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra] using hs
  · intro hx
    rw [NonUnitalSubalgebra.mem_rightAnnihilatorModulo_iff]
    intro d hd
    have h :=
      (NonUnitalSubalgebra.mem_leftAnnihilatorModulo_iff
        I.toNonUnitalSubalgebra (D : Set A) x).1 hx
        (star d) (D.star_mem' hd)
    have hs := I.star_mem' h
    simpa only [star_mul, star_star, NonUnitalStarSubalgebra.mem_carrier,
      NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra] using hs

/-- Let `R` be a commutative semiring and `A` a possibly nonunital star semiring with an `R`-module
structure compatible with multiplication on both sides. Let `I` and `D` be star-closed nonunital
`R`-subalgebras, with `I` two-sided. The element `star x` annihilates `D` on the left modulo `I`
exactly when `x` annihilates it on the right.
-/
theorem star_mem_leftAnnihilatorModulo_iff
    (I D : NonUnitalStarSubalgebra R A)
    [I.toNonUnitalSubalgebra.IsTwoSided] (x : A) :
    star x ∈ I.toNonUnitalSubalgebra.leftAnnihilatorModulo (D : Set A) ↔
      x ∈ I.toNonUnitalSubalgebra.rightAnnihilatorModulo (D : Set A) := by
  constructor
  · intro hx
    rw [NonUnitalSubalgebra.mem_rightAnnihilatorModulo_iff]
    intro d hd
    have h :=
      (NonUnitalSubalgebra.mem_leftAnnihilatorModulo_iff
        I.toNonUnitalSubalgebra (D : Set A) (star x)).1 hx
        (star d) (D.star_mem' hd)
    have hs := I.star_mem' h
    simpa only [star_mul, star_star, NonUnitalStarSubalgebra.mem_carrier,
      NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra] using hs
  · intro hx
    rw [NonUnitalSubalgebra.mem_leftAnnihilatorModulo_iff]
    intro d hd
    have h :=
      (NonUnitalSubalgebra.mem_rightAnnihilatorModulo_iff
        I.toNonUnitalSubalgebra (D : Set A) x).1 hx
        (star d) (D.star_mem' hd)
    have hs := I.star_mem' h
    simpa only [star_mul, star_star, NonUnitalStarSubalgebra.mem_carrier,
      NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra] using hs

/-- Let `R` be a commutative semiring and `A` a possibly nonunital star semiring with an `R`-module
structure compatible with multiplication on both sides. Let `I` and `D` be star-closed nonunital
`R`-subalgebras, with `I` two-sided. Every element of the two-sided subalgebra `I` lies in its
relative annihilator of `D`.
-/
theorem le_annihilatorModulo
    (I D : NonUnitalStarSubalgebra R A)
    [I.toNonUnitalSubalgebra.IsTwoSided] :
    I ≤ I.annihilatorModulo D := by
  intro x hx
  rw [mem_annihilatorModulo_iff]
  exact ⟨fun d _hd => NonUnitalSubalgebra.IsTwoSided.mul_mem_right hx d,
    fun d _hd => NonUnitalSubalgebra.IsTwoSided.mul_mem_left d hx⟩

end NonUnitalStarSubalgebra
