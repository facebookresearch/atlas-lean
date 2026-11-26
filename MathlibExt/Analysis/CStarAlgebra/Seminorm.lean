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

public import Mathlib.Algebra.Star.Module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.Real.Sqrt

/-!
# C-star seminorms and their bounded supremum

A C-star seminorm is an actual complex seminorm on the original nonunital
complex star algebra, with submultiplicativity, star invariance and the C-star
square identity. The zero seminorm is allowed.

The bounded supremum uses Mathlib's computed supremum of seminorms. Its
submultiplicativity and star invariance follow pointwise; its square identity
follows from the two square bounds and the real square root. These laws supply
the gauge required by separation and completion constructions.

The supplied ring, scalar and star dictionaries describe the original algebra.
This bundle supplies a gauge and its laws. A unital completion construction
also uses the original ring and algebra structures and the actual quotient
and completion maps.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

/-- **Complex C*-seminorm.** Let `A` be a nonunital complex star algebra with scalar-compatible
involution. A C*-seminorm is a complex seminorm `p` satisfying `p(x y) ≤ p(x)p(y)`, `p(x*) = p(x)`,
and `p(x* x) = p(x)²`. -/
structure CStarSeminorm (A : Type u) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarRing A] [StarModule ℂ A]
    extends Seminorm ℂ A where
  /-- The original multiplication is submultiplicative for this gauge. -/
  mul_le' : ∀ x y : A, toFun (x * y) ≤ toFun x * toFun y
  /-- The original involution preserves this gauge. -/
  map_star' : ∀ x : A, toFun (star x) = toFun x
  /-- The C-star square identity for the original product and involution. -/
  cstar_identity' : ∀ x : A, toFun (star x * x) = toFun x ^ 2

namespace CStarSeminorm

open Set

variable {A : Type u} [NonUnitalRing A] [Module ℂ A]
variable [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarRing A] [StarModule ℂ A]

instance funLike : FunLike (CStarSeminorm A) A ℝ where
  coe p := p.toSeminorm
  coe_injective p q h := by
    have hpq : p.toSeminorm = q.toSeminorm := DFunLike.coe_injective h
    cases p
    cases q
    cases hpq
    rfl

instance seminormClass : SeminormClass (CStarSeminorm A) ℂ A where
  map_zero p := p.toSeminorm.map_zero'
  map_add_le_add p := p.toSeminorm.add_le'
  map_neg_eq_map p := p.toSeminorm.neg'
  map_smul_eq_mul p := p.toSeminorm.smul'

instance ringSeminormClass : RingSeminormClass (CStarSeminorm A) A ℝ where
  map_zero p := p.toSeminorm.map_zero'
  map_add_le_add p := p.toSeminorm.add_le'
  map_neg_eq_map p := p.toSeminorm.neg'
  map_mul_le_mul p := p.mul_le'

/-- **Extensionality of C*-seminorms.** Let `A` be a nonunital complex star algebra with
scalar-compatible involution. Two C*-seminorms on `A` are equal if their real values agree at every
element of `A`. -/
@[ext] theorem ext {p q : CStarSeminorm A} (h : ∀ x, p x = q x) : p = q :=
  DFunLike.ext p q h

/-- **Ring seminorm of a C*-seminorm.** Let `A` be a nonunital complex star algebra with
scalar-compatible involution. A complex C*-seminorm `p` defines a ring seminorm on `A` with exactly
the same real-valued gauge. -/
def toRingSeminorm (p : CStarSeminorm A) : RingSeminorm A where
  __ := p.toSeminorm.toAddGroupSeminorm
  mul_le' := p.mul_le'

/-- **Values of the associated ring seminorm.** Let `A` be a nonunital complex star algebra with
scalar-compatible involution. For a C*-seminorm `p` and `x ∈ A`, its associated ring seminorm has
value `p(x)`. -/
@[simp] theorem toRingSeminorm_apply (p : CStarSeminorm A) (x : A) :
    p.toRingSeminorm x = p x :=
  rfl

/-- **A C*-seminorm preserves the involution.** Let `A` be a nonunital complex star algebra with
scalar-compatible involution. For every C*-seminorm `p` and `x ∈ A`, `p(x*) = p(x)`. -/
@[simp] theorem map_star (p : CStarSeminorm A) (x : A) : p (star x) = p x :=
  p.map_star' x

/-- **C*-seminorm square identity.** Let `A` be a nonunital complex star algebra with scalar-compatible
involution. For every C*-seminorm `p` and `x ∈ A`, `p(x* x) = p(x)²`. -/
@[simp] theorem map_star_mul_self (p : CStarSeminorm A) (x : A) :
    p (star x * x) = p x ^ 2 :=
  p.cstar_identity' x

instance : Zero (CStarSeminorm A) where
  zero :=
    { toSeminorm := 0
      mul_le' := fun _ _ => by
        change (0 : ℝ) ≤ 0 * 0
        simpa only [zero_mul] using (le_refl (0 : ℝ))
      map_star' := fun _ => rfl
      cstar_identity' := fun _ => by
        change (0 : ℝ) = 0 ^ 2
        simp only [pow_two, zero_mul] }

/-- **Zero C*-seminorm.** Let `A` be a nonunital complex star algebra with scalar-compatible involution.
The zero C*-seminorm on `A` has value zero at every `x ∈ A`. -/
@[simp] theorem zero_apply (x : A) : (0 : CStarSeminorm A) x = 0 :=
  rfl

instance : Inhabited (CStarSeminorm A) := ⟨0⟩

/-- **Pointwise supremum of C*-seminorms.** Let `A` be a nonunital complex star algebra with
scalar-compatible involution. Let `S` be a nonempty set of C*-seminorms on `A` such that `{p(x) : p
∈ S}` is bounded above for every `x ∈ A`. The pointwise supremum `x ↦ sup {p(x) : p ∈ S}` is a
C*-seminorm. -/
def sSup (S : Set (CStarSeminorm A)) (hS : S.Nonempty)
    (hb : ∀ x : A, BddAbove ((fun p : CStarSeminorm A => p x) '' S)) :
    CStarSeminorm A := by
  let q : Seminorm ℂ A := (⨆ p : S, p.val.toSeminorm)
  have : Nonempty S := hS.coe_sort
  have hb' : BddAbove (range fun p : S => p.val.toSeminorm) := by
    apply Seminorm.bddAbove_range_iff.mpr
    intro y
    rcases hb y with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro r ⟨p, rfl⟩
    exact hC ⟨p.val, p.property, rfl⟩
  have hdom (p : S) (x : A) : p.val x ≤ q x := by
    change p.val.toSeminorm x ≤ (⨆ r : S, r.val.toSeminorm) x
    exact (Seminorm.le_def.mp
      (le_ciSup (f := fun r : S => r.val.toSeminorm)
        hb' p)) x
  refine
    { toSeminorm := q
      mul_le' := ?_
      map_star' := ?_
      cstar_identity' := ?_ }
  · intro x y
    change (⨆ p : S, p.val.toSeminorm) (x * y) ≤ q x * q y
    rw [Seminorm.iSup_apply (x := x * y) hb']
    apply ciSup_le
    intro p
    exact (p.val.mul_le' x y).trans
      (mul_le_mul (hdom p x) (hdom p y) (apply_nonneg p.val y) (apply_nonneg q x))
  · intro x
    change (⨆ p : S, p.val.toSeminorm) (star x) = (⨆ p : S, p.val.toSeminorm) x
    rw [Seminorm.iSup_apply (x := star x) hb', Seminorm.iSup_apply (x := x) hb']
    exact iSup_congr fun p : S => p.val.map_star x
  · intro x
    change q (star x * x) = q x ^ 2
    apply le_antisymm
    · change (⨆ p : S, p.val.toSeminorm) (star x * x) ≤ q x ^ 2
      rw [Seminorm.iSup_apply (x := star x * x) hb']
      apply ciSup_le
      intro p
      change p.val (star x * x) ≤ q x ^ 2
      rw [p.val.map_star_mul_self x]
      simpa only [pow_two] using
        mul_le_mul (hdom p x) (hdom p x) (apply_nonneg p.val x) (apply_nonneg q x)
    · have hroot : q x ≤ Real.sqrt (q (star x * x)) := by
        change (⨆ p : S, p.val.toSeminorm) x ≤ Real.sqrt (q (star x * x))
        rw [Seminorm.iSup_apply (x := x) hb']
        apply ciSup_le
        intro p
        apply Real.le_sqrt_of_sq_le
        change p.val x ^ 2 ≤ q (star x * x)
        rw [← p.val.map_star_mul_self x]
        exact hdom p (star x * x)
      calc
        q x ^ 2 = q x * q x := pow_two _
        _ ≤ Real.sqrt (q (star x * x)) * Real.sqrt (q (star x * x)) :=
          mul_le_mul hroot hroot (apply_nonneg q x) (Real.sqrt_nonneg _)
        _ = q (star x * x) := Real.mul_self_sqrt (apply_nonneg q (star x * x))

/-- **Evaluation of a supremum C*-seminorm.** Let `A` be a nonunital complex star algebra with
scalar-compatible involution. Let `S` be a nonempty set of C*-seminorms on `A` such that `{p(x) : p
∈ S}` is bounded above for every `x ∈ A`. For each `x ∈ A`, the supremum C*-seminorm has value `sup
{p(x) : p ∈ S}` in `ℝ`. -/
theorem sSup_apply (S : Set (CStarSeminorm A)) (hS : S.Nonempty)
    (hb : ∀ x : A, BddAbove ((fun p : CStarSeminorm A => p x) '' S)) (x : A) :
    sSup S hS hb x = SupSet.sSup ((fun p : CStarSeminorm A => p x) '' S) := by
  change (⨆ p : S, p.val.toSeminorm) x =
    SupSet.sSup ((fun p : CStarSeminorm A => p x) '' S)
  have hb' : BddAbove (range fun p : S => p.val.toSeminorm) := by
    apply Seminorm.bddAbove_range_iff.mpr
    intro y
    rcases hb y with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro r ⟨p, rfl⟩
    exact hC ⟨p.val, p.property, rfl⟩
  rw [Seminorm.iSup_apply (x := x) hb', ← sSup_range]
  congr 1
  ext r
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.val, p.property, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩

/-- **Each seminorm lies below the pointwise supremum.** Let `A` be a nonunital complex star algebra
with scalar-compatible involution. Let `S` be a nonempty set of C*-seminorms on `A` such that `{p(x)
: p ∈ S}` is bounded above for every `x ∈ A`. For every `p ∈ S` and `x ∈ A`, `p(x)` is at most the
supremum C*-seminorm at `x`. -/
theorem le_sSup (S : Set (CStarSeminorm A)) (hS : S.Nonempty)
    (hb : ∀ x : A, BddAbove ((fun p : CStarSeminorm A => p x) '' S))
    {p : CStarSeminorm A} (hp : p ∈ S) (x : A) : p x ≤ sSup S hS hb x := by
  rw [sSup_apply S hS hb x]
  exact le_csSup (hb x) ⟨p, hp, rfl⟩

/-- **Upper bound on a supremum C*-seminorm.** Let `A` be a nonunital complex star algebra with
scalar-compatible involution. Let `S` be a nonempty set of C*-seminorms on `A` such that `{p(x) : p
∈ S}` is bounded above for every `x ∈ A`. For fixed `x ∈ A`, if `p(x) ≤ C` for every `p ∈ S`, the
supremum C*-seminorm at `x` is at most `C`. -/
theorem sSup_le (S : Set (CStarSeminorm A)) (hS : S.Nonempty)
    (hb : ∀ x : A, BddAbove ((fun p : CStarSeminorm A => p x) '' S))
    {x : A} {C : ℝ} (hC : ∀ p ∈ S, p x ≤ C) : sSup S hS hb x ≤ C := by
  rw [sSup_apply S hS hb x]
  refine csSup_le (hS.image fun p : CStarSeminorm A => p x) ?_
  rintro r ⟨p, hp, rfl⟩
  exact hC p hp

end CStarSeminorm
