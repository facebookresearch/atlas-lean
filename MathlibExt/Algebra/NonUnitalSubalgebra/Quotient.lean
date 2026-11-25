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

public import MathlibExt.Algebra.NonUnitalSubalgebra.TwoSided
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic.Abel
public meta import Mathlib.Tactic.FastInstance

/-!
# Algebraic quotients by two-sided nonunital subalgebras

The quotient carrier is the native `Submodule.Quotient` of the original
scalar submodule. Multiplication, the nonunital ring structure and scalar
compatibility are scoped under `NonUnitalSubalgebra.Quotient`.

The additive and module structures and the quotient projection remain the
native ones. This algebraic owner also supplies the quotient structures
used by the normed quotient owner.
-/

@[expose] public section

noncomputable section

namespace NonUnitalSubalgebra

section Carrier

variable {𝕜 A : Type*} [CommRing 𝕜] [NonUnitalRing A] [Module 𝕜 A]

/-- Let `𝕜` be a commutative ring, `A` a possibly nonunital ring with a `𝕜`-module structure, and `S` a
nonunital `𝕜`-subalgebra of `A`. Its underlying `𝕜`-submodule is used for the additive quotient.
-/
abbrev quotientSubmodule (S : NonUnitalSubalgebra 𝕜 A) : Submodule 𝕜 A :=
  S.toSubmodule

/-- Let `𝕜` be a commutative ring, `A` a possibly nonunital ring with a `𝕜`-module structure, and `S` a
nonunital `𝕜`-subalgebra of `A`. The quotient carrier is the ordinary additive `𝕜`-module quotient
`A / S`.
-/
abbrev Quotient (S : NonUnitalSubalgebra 𝕜 A) :=
  A ⧸ quotientSubmodule S

end Carrier

namespace Quotient

section Algebra

variable {𝕜 A : Type*} [CommRing 𝕜] [NonUnitalRing A] [Module 𝕜 A]
variable (S : NonUnitalSubalgebra 𝕜 A)

/-- Let `𝕜` be a commutative ring, `A` a possibly nonunital ring with a `𝕜`-module structure, and `S` a
nonunital `𝕜`-subalgebra of `A`. The quotient projection `A → A / S` is `𝕜`-linear.
-/
def mkL : A →ₗ[𝕜] S.Quotient :=
  (quotientSubmodule S).mkQ

@[simp]
theorem mkL_apply (a : A) : mkL S a = Submodule.Quotient.mk a := rfl

/-- Let `𝕜` be a commutative ring, `A` a possibly nonunital ring with a `𝕜`-module structure, and `S` a
nonunital `𝕜`-subalgebra of `A`. Every additive quotient class has a representative in `A`, so the
linear quotient projection is surjective.
-/
theorem mkL_surjective : Function.Surjective (mkL S) :=
  (quotientSubmodule S).mkQ_surjective

/-- Let `𝕜` be a commutative ring, `A` a possibly nonunital ring with a `𝕜`-module structure, and `S` a
nonunital `𝕜`-subalgebra of `A`. If `S` absorbs multiplication by arbitrary elements of `A` on both
sides, multiplication descends to `A / S`.
-/
@[instance_reducible]
def quotientMul [S.IsTwoSided] : Mul S.Quotient where
  mul := _root_.Quotient.map₂
    (fun x y : A ↦ x * y)
    (by
      intro x x' hx y y' hy
      apply (Submodule.quotientRel_def (quotientSubmodule S)).2
      have hx' : x - x' ∈ S :=
        (Submodule.quotientRel_def (quotientSubmodule S)).1 hx
      have hy' : y - y' ∈ S :=
        (Submodule.quotientRel_def (quotientSubmodule S)).1 hy
      rw [show x * y - x' * y' = x * (y - y') + (x - x') * y' by
        rw [mul_sub, sub_mul]; abel]
      exact S.add_mem (IsTwoSided.mul_mem_left x hy')
        (IsTwoSided.mul_mem_right hx' y'))

/-- Scoped quotient multiplication. -/
scoped instance instMul [S.IsTwoSided] : Mul S.Quotient := quotientMul S

open scoped NonUnitalSubalgebra.Quotient

@[simp]
theorem mk_mul [S.IsTwoSided] (x y : A) :
    (Submodule.Quotient.mk (x * y) : S.Quotient) =
      Submodule.Quotient.mk x * Submodule.Quotient.mk y := by
  rfl

/-- Scoped nonunital ring structure induced from the ambient ring. -/
scoped instance instNonUnitalRing [S.IsTwoSided] : NonUnitalRing S.Quotient := fast_instance%
  Function.Surjective.nonUnitalRing Submodule.Quotient.mk
    (Submodule.Quotient.mk_surjective (quotientSubmodule S)) rfl
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- Scoped scalar-tower law for the quotient nonunital algebra. -/
scoped instance instIsScalarTower [IsScalarTower 𝕜 A A] [S.IsTwoSided] :
    IsScalarTower 𝕜 S.Quotient S.Quotient where
  smul_assoc := by
    intro c x y
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    change Submodule.Quotient.mk ((c • x) * y) =
      Submodule.Quotient.mk (c • (x * y))
    rw [smul_mul_assoc]

/-- Scoped scalar-commutation law for the quotient nonunital algebra. -/
scoped instance instSMulCommClass [SMulCommClass 𝕜 A A] [S.IsTwoSided] :
    SMulCommClass 𝕜 S.Quotient S.Quotient where
  smul_comm := by
    intro c x y
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    exact congrArg (fun t : A ↦ (Submodule.Quotient.mk t : S.Quotient))
      (mul_smul_comm (α := 𝕜) c x y).symm

/-- Let `𝕜` be a commutative ring, `A` a possibly nonunital ring with a `𝕜`-module structure, and `S` a
nonunital `𝕜`-subalgebra of `A`. If `S` is two-sided, the quotient projection preserves
multiplication as well as addition and the `𝕜`-action.
-/
def mk [S.IsTwoSided] : A →ₙₐ[𝕜] S.Quotient where
  toFun := Submodule.Quotient.mk
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem mk_apply [S.IsTwoSided] (x : A) : mk S x = Submodule.Quotient.mk x := rfl

/-- Let `𝕜` be a commutative ring, `A` a possibly nonunital ring with a `𝕜`-module structure, and `S` a
nonunital `𝕜`-subalgebra of `A`. If `S` is two-sided, the multiplicative `𝕜`-linear quotient
projection is surjective.
-/
theorem mk_surjective [S.IsTwoSided] : Function.Surjective (mk S) :=
  mkL_surjective S

theorem mk_eq_zero [S.IsTwoSided] (x : A) : mk S x = 0 ↔ x ∈ S :=
  Submodule.Quotient.mk_eq_zero (quotientSubmodule S)

end Algebra

end Quotient

end NonUnitalSubalgebra
