/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.TensorPower.Snoc
public import MathlibExt.Algebra.Module.AlgHomAction
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# The enveloping action on the two outer tensor factors

For a commutative semiring `k`, tensor reassociation identifies `A ⊗[k] (V ⊗[k] A)` with `(A
⊗[k] Aᵐᵒᵖ) ⊗[k] V`, sending `a ⊗ (v ⊗ b)` to `(a ⊗ op(b)) ⊗ v`.

When `A` is a `k`-algebra, this identifies `A ⊗[k] A^(⊗(n+1))` with the induced enveloping
module on its first and last factors. The pure scalar `l ⊗ op(r)` multiplies the first factor
on the left and the final factor on the right, leaving the middle word unchanged.

Reference: Loday, *Cyclic Homology*, Section 1.1.
-/
@[expose] public section
noncomputable section

open scoped TensorProduct
open MulOpposite

namespace TensorPower
universe u v w

variable (k : Type u) [CommSemiring k]

section Coordinates
variable (A : Type v) [AddCommMonoid A] [Module k A]

/-- Let `k` be a commutative semiring and `A` a `k`-semimodule. For a `k`-semimodule `V`, this is
the `k`-linear equivalence `A ⊗[k] (V ⊗[k] A) ≃ₗ[k] (A ⊗[k] Aᵐᵒᵖ) ⊗[k] V`, sending `a⊗(x⊗b)`
to `(a⊗op(b))⊗x`. -/
def outerTensorCoordinate (V : Type w) [AddCommMonoid V] [Module k V] :
    A ⊗[k] (V ⊗[k] A) ≃ₗ[k] (A ⊗[k] Aᵐᵒᵖ) ⊗[k] V :=
  (TensorProduct.assoc k A V A).symm.trans
    ((TensorProduct.congr (TensorProduct.comm k A V) (MulOpposite.opLinearEquiv k (M := A))).trans
      ((TensorProduct.assoc k V A Aᵐᵒᵖ).trans
        (TensorProduct.comm k V (A ⊗[k] Aᵐᵒᵖ))))

/-- Let `k` be a commutative semiring and `A` a `k`-semimodule. For a `k`-semimodule `V`, `a,b :
A`, and `x : V`, `outerTensorCoordinate k A V (a⊗(x⊗b))=(a⊗op(b))⊗x`. -/
theorem outerTensorCoordinate_tmul (V : Type w) [AddCommMonoid V] [Module k V]
    (a b : A) (x : V) :
    outerTensorCoordinate k A V (a ⊗ₜ[k] (x ⊗ₜ[k] b)) =
      (a ⊗ₜ[k] op b) ⊗ₜ[k] x := by
  simp only [outerTensorCoordinate, LinearEquiv.trans_apply, TensorProduct.assoc_symm_tmul,
    TensorProduct.congr_tmul, TensorProduct.comm_tmul, TensorProduct.assoc_tmul,
    MulOpposite.coe_opLinearEquiv]

/-- Let `k` be a commutative semiring and `A` a `k`-semimodule. For `n : ℕ`, this is `A ⊗[k]
TensorPower k (n+1) A ≃ₗ[k] (A ⊗[k] Aᵐᵒᵖ) ⊗[k] TensorPower k n A`, separating the final factor
of the tensor word from its middle factors. -/
def outerCoordinate (n : ℕ) :
    A ⊗[k] TensorPower k (n + 1) A ≃ₗ[k]
      (A ⊗[k] Aᵐᵒᵖ) ⊗[k] TensorPower k n A :=
  (TensorProduct.congr (LinearEquiv.refl k A) (snocEquiv k A n).symm).trans
    (outerTensorCoordinate k A (TensorPower k n A))

/-- Let `k` be a commutative semiring and `A` a `k`-semimodule. For `n : ℕ`, `a₀ : A`, and `a :
Fin(n+1) → A`, the map sends `a₀ ⊗ tprod(a)` to `(a₀ ⊗ op(a(Fin.last n))) ⊗ tprod(Fin.init
a)`. -/
theorem outerCoordinate_tprod (n : ℕ) (a₀ : A) (a : Fin (n + 1) → A) :
    outerCoordinate k A n (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a) =
      (a₀ ⊗ₜ[k] op (a (Fin.last n))) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.init a) := by
  simp only [outerCoordinate, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    snocEquiv_symm_tprod, LinearEquiv.refl_apply, outerTensorCoordinate_tmul]

end Coordinates

variable (A : Type v) [Semiring A] [Algebra k A]

/-- Let `k` be a commutative semiring and `A` a `k`-algebra whose underlying multiplication may be
noncommutative. Put `E=A ⊗[k] Aᵐᵒᵖ` and `X_n=A ⊗[k] TensorPower k (n+1) A`. The `k`-algebra
homomorphism `outerRepresentation k A n : E →ₐ[k] End_k(X_n)` is the regular left action on
the enveloping coordinate, transported by `outerCoordinate`. -/
def outerRepresentation (n : ℕ) :
    (A ⊗[k] Aᵐᵒᵖ) →ₐ[k] Module.End k (A ⊗[k] TensorPower k (n + 1) A) :=
  ((outerCoordinate k A n).symm.conjAlgEquiv k).toAlgHom.comp
    (Algebra.lsmul (A := A ⊗[k] Aᵐᵒᵖ) k k
      ((A ⊗[k] Aᵐᵒᵖ) ⊗[k] TensorPower k n A))

/-- Let `k` be a commutative semiring and `A` a `k`-algebra whose underlying multiplication may be
noncommutative. Put `E=A ⊗[k] Aᵐᵒᵖ` and `X_n=A ⊗[k] TensorPower k (n+1) A`. For `z : E` and `x
: X_n`, `outerRepresentation k A n z x = outerCoordinate⁻¹(z • outerCoordinate x)`. -/
theorem outerRepresentation_apply (n : ℕ) (z : A ⊗[k] Aᵐᵒᵖ)
    (x : A ⊗[k] TensorPower k (n + 1) A) :
    outerRepresentation k A n z x =
      (outerCoordinate k A n).symm (z • outerCoordinate k A n x) := rfl

/-- Let `k` be a commutative semiring and `A` a `k`-algebra whose underlying multiplication may be
noncommutative. Put `E=A ⊗[k] Aᵐᵒᵖ` and `X_n=A ⊗[k] TensorPower k (n+1) A`. For `n : ℕ`,
`outerModule k A n : Module E X_n` uses the action defined by `outerRepresentation k A n`. -/
@[instance_reducible]
def outerModule (n : ℕ) : Module (A ⊗[k] Aᵐᵒᵖ) (A ⊗[k] TensorPower k (n + 1) A) :=
  Module.compHom _ (outerRepresentation k A n).toRingHom

/-- Let `k` be a commutative semiring and `A` a `k`-algebra whose underlying multiplication may be
noncommutative. Put `E=A ⊗[k] Aᵐᵒᵖ` and `X_n=A ⊗[k] TensorPower k (n+1) A`. With `outerModule
k A n`, `IsScalarTower k E X_n` holds, so `(c • z) • x=c • (z • x)`. -/
theorem outerScalarTower (n : ℕ) :
    letI := outerModule k A n
    IsScalarTower k (A ⊗[k] Aᵐᵒᵖ) (A ⊗[k] TensorPower k (n + 1) A) :=
  AlgHom.moduleEnd_compHom_isScalarTower (outerRepresentation k A n)

/-- Let `k` be a commutative semiring and `A` a `k`-algebra whose underlying multiplication may be
noncommutative. Put `E=A ⊗[k] Aᵐᵒᵖ` and `X_n=A ⊗[k] TensorPower k (n+1) A`. For `l,r,a₀ : A`
and `a : Fin(n+1) → A`, `(l⊗op(r)) • (a₀⊗tprod(a)) = (l*a₀) ⊗ tprod(Fin.snoc (Fin.init a)
(a(Fin.last n)*r))`. The right scalar multiplies after the final factor. -/
theorem outerModule_tprod (n : ℕ) (l r a₀ : A) (a : Fin (n + 1) → A) :
    letI := outerModule k A n
    (l ⊗ₜ[k] op r) • (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a) =
      (l * a₀) ⊗ₜ[k]
        PiTensorProduct.tprod k (Fin.snoc (Fin.init a) (a (Fin.last n) * r)) := by
  let := outerModule k A n
  apply (outerCoordinate k A n).injective
  change outerCoordinate k A n
    (outerRepresentation k A n (l ⊗ₜ[k] op r) (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a)) = _
  rw [outerRepresentation_apply, LinearEquiv.apply_symm_apply]
  rw [outerCoordinate_tprod, outerCoordinate_tprod]
  simp only [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul,
    MulOpposite.op_mul, Fin.snoc_last, Fin.init_snoc]

end TensorPower
