/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Nonunital coefficient representations and unitization

Let k be a commutative ring, A a nonunital associative ring with
k-bilinear multiplication, and M a k-module. Nonunital k-algebra maps
l : A → End_k(M), r : Aᵐᵒᵖ → End_k(M) give left and right actions.
The left law is l(ab)m = l(a)(l(b)m); the right law is
r(op(ab))m = r(op b)(r(op a)m).

If the two representations commute, they define a nonunital bimodule.
On U(A) = k ⊕ A the extended left action is
(λ,a)m = λm + l(a)m, and the extended right action is
m(λ,a) = λm + r(op a)m. The extended actions commute as well.
Regular right multiplication is r(op a)(b) = ba.

The ground, algebra and coefficient carrier universes are independent.

Reference: J.-L. Loday, Cyclic Homology, §1.1, for bimodule coefficient
actions in Hochschild chains.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable {k : Type u} [CommRing k]
  {A : Type v} [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]
  {M : Type w} [AddCommGroup M] [Module k M]

section TensorActions

/-- Let k be a commutative ring, A a nonunital associative ring with
a k-module structure, and M a k-module. A left representation
l : A → End_k(M) or right representation r : Aᵐᵒᵖ → End_k(M)
is multiplicative and k-linear.
The left representation induces the k-linear tensor action
A ⊗[k] M → M, a ⊗ m ↦ l(a)m. -/
def leftTensor (l : A →ₙₐ[k] Module.End k M) : A ⊗[k] M →ₗ[k] M :=
  TensorProduct.lift (l : A →ₗ[k] Module.End k M)

/-- Let k be a commutative ring, A a nonunital associative ring with
a k-module structure, and M a k-module. A left representation
l : A → End_k(M) or right representation r : Aᵐᵒᵖ → End_k(M)
is multiplicative and k-linear.
The right representation induces the k-linear tensor action
M ⊗[k] A → M, m ⊗ a ↦ r(op a)m. -/
def rightTensor (r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M) : M ⊗[k] A →ₗ[k] M :=
  TensorProduct.lift
    (((r : Aᵐᵒᵖ →ₗ[k] Module.End k M).comp (MulOpposite.opLinearEquiv k).toLinearMap).flip)

omit [IsScalarTower k A A] [SMulCommClass k A A] in
@[simp]
theorem leftTensor_tmul (l : A →ₙₐ[k] Module.End k M) (a : A) (m : M) :
    leftTensor l (a ⊗ₜ[k] m) = l a m := rfl

omit [IsScalarTower k A A] [SMulCommClass k A A] in
@[simp]
theorem rightTensor_tmul (r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M) (m : M) (a : A) :
    rightTensor r (m ⊗ₜ[k] a) = r (MulOpposite.op a) m := rfl

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Let k be a commutative ring, A a nonunital associative ring with
a k-module structure, and M a k-module. A left representation
l : A → End_k(M) or right representation r : Aᵐᵒᵖ → End_k(M)
is multiplicative and k-linear.
For a left representation l, multiplication in A acts by composition:
l(ab)m = l(a)(l(b)m) for all a,b ∈ A and m ∈ M. -/
theorem left_mul_apply (l : A →ₙₐ[k] Module.End k M) (a b : A) (m : M) :
    l (a * b) m = l a (l b m) := by
  rw [map_mul]
  rfl

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Let k be a commutative ring, A a nonunital associative ring with
a k-module structure, and M a k-module. A left representation
l : A → End_k(M) or right representation r : Aᵐᵒᵖ → End_k(M)
is multiplicative and k-linear.
For a right representation r, opposite multiplication gives
r(op(ab))m = r(op b)(r(op a)m).
Thus applying the right a-action and then the right b-action gives
the right ab-action. -/
theorem right_mul_apply (r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M) (a b : A) (m : M) :
    r (MulOpposite.op (a * b)) m = r (MulOpposite.op b) (r (MulOpposite.op a) m) := by
  rw [MulOpposite.op_mul, map_mul]
  rfl

/-- Let k be commutative, A a nonunital associative ring with
k-bilinear multiplication, and M a k-module. Write U(A) = k ⊕ A
for its unitization.
For the regular coefficient A, right multiplication is the
nonunital k-algebra representation Aᵐᵒᵖ → End_k(A)
with r(op a)(b) = ba. -/
def regularRight : Aᵐᵒᵖ →ₙₐ[k] Module.End k A :=
  (((MulOpposite.opLinearEquiv k).symm.conjAlgEquiv k).toAlgHom.toNonUnitalAlgHom).comp
    (NonUnitalAlgHom.lmul k Aᵐᵒᵖ)

@[simp]
theorem regularRight_apply (a b : A) : regularRight (k := k) (MulOpposite.op a) b = b * a :=
  rfl

/-- Let k be commutative, A a nonunital associative ring with
k-bilinear multiplication, and M a k-module. Write U(A) = k ⊕ A
for its unitization.
On the regular coefficient A, the left and right multiplication
operators commute: a(xb) = (ax)b for every a,b,x ∈ A. -/
theorem regular_commute (a b x : A) :
    NonUnitalAlgHom.lmul k A a (regularRight (k := k) (MulOpposite.op b) x) =
      regularRight (k := k) (MulOpposite.op b) (NonUnitalAlgHom.lmul k A a x) := by
  change a * (x * b) = (a * x) * b
  exact (mul_assoc a x b).symm

end TensorActions

section Unitization

/-- Let k be commutative, A a nonunital associative ring with
k-bilinear multiplication, and M a k-module. Write U(A) = k ⊕ A
for its unitization.
A nonunital left representation l : A → End_k(M) extends to
a unital k-algebra representation U(A) → End_k(M), with
(λ,a) acting as m ↦ λm + l(a)m. -/
def unitizationLeft (l : A →ₙₐ[k] Module.End k M) :
    Unitization k A →ₐ[k] Module.End k M :=
  Unitization.lift l

@[simp]
theorem unitizationLeft_apply (l : A →ₙₐ[k] Module.End k M)
    (a : Unitization k A) (m : M) :
    unitizationLeft l a m = a.fst • m + l a.snd m := rfl

theorem unitizationLeft_inr (l : A →ₙₐ[k] Module.End k M) (a : A) (m : M) :
    unitizationLeft l (Unitization.inr a) m = l a m := by
  rw [unitizationLeft_apply, Unitization.fst_inr, Unitization.snd_inr, zero_smul, zero_add]

/-- Let k be commutative, A a nonunital associative ring with
k-bilinear multiplication, and M a k-module. Write U(A) = k ⊕ A
for its unitization.
The k-algebra map U(A)ᵐᵒᵖ → U(Aᵐᵒᵖ) sends
op(λ,a) to (λ,op a), keeping the ground-scalar coordinate fixed. -/
def oppositeUnitization :
    (Unitization k A)ᵐᵒᵖ →ₐ[k] Unitization k Aᵐᵒᵖ where
  toFun a := Unitization.mk (a.unop.fst, MulOpposite.op a.unop.snd)
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := rfl
  map_mul' a b := by
    apply Unitization.ext
    · exact mul_comm _ _
    · simp only [MulOpposite.unop_mul, Unitization.snd_mul,
        MulOpposite.op_add, MulOpposite.op_smul, MulOpposite.op_mul]
      exact congrArg (fun q => q + MulOpposite.op a.unop.snd * MulOpposite.op b.unop.snd)
        (add_comm _ _)
  commutes' c := rfl

/-- Let k be commutative, A a nonunital associative ring with
k-bilinear multiplication, and M a k-module. Write U(A) = k ⊕ A
for its unitization.
A nonunital right representation r : Aᵐᵒᵖ → End_k(M)
extends to a unital representation U(A)ᵐᵒᵖ → End_k(M),
with op(λ,a) acting as m ↦ λm + r(op a)m. -/
def unitizationRight (r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M) :
    (Unitization k A)ᵐᵒᵖ →ₐ[k] Module.End k M :=
  (Unitization.lift r).comp oppositeUnitization

@[simp]
theorem unitizationRight_apply (r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M)
    (a : (Unitization k A)ᵐᵒᵖ) (m : M) :
    unitizationRight r a m = a.unop.fst • m + r (MulOpposite.op a.unop.snd) m := rfl

theorem unitizationRight_inr (r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M) (a : A) (m : M) :
    unitizationRight r (MulOpposite.op (Unitization.inr a)) m =
      r (MulOpposite.op a) m := by
  rw [unitizationRight_apply, MulOpposite.unop_op, Unitization.fst_inr,
    Unitization.snd_inr, zero_smul, zero_add]

/-- Let k be commutative, A a nonunital associative ring with
k-bilinear multiplication, and M a k-module. Write U(A) = k ⊕ A
for its unitization.
Suppose l : A → End_k(M) and r : Aᵐᵒᵖ → End_k(M)
satisfy l(a)(r(b)m) = r(b)(l(a)m) for all a,b,m.
Then their unitized representations commute on every element of
U(A) and U(A)ᵐᵒᵖ. -/
theorem unitization_commute (l : A →ₙₐ[k] Module.End k M)
    (r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M)
    (h : ∀ a b m, l a (r b m) = r b (l a m))
    (a : Unitization k A) (b : (Unitization k A)ᵐᵒᵖ) (m : M) :
    unitizationLeft l a (unitizationRight r b m) =
      unitizationRight r b (unitizationLeft l a m) := by
  simp only [unitizationLeft_apply, unitizationRight_apply, smul_add,
    (l a.snd).map_add, (r (MulOpposite.op b.unop.snd)).map_add,
    (l a.snd).map_smul, (r (MulOpposite.op b.unop.snd)).map_smul, h]
  rw [smul_smul, smul_smul, mul_comm a.fst b.unop.fst]
  abel

end Unitization

end ModuleCat.Algebra.Hochschild.NonUnital
