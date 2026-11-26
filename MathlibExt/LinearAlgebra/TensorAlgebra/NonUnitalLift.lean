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

public import MathlibExt.LinearAlgebra.TensorAlgebra.NonUnital
public import Mathlib.Algebra.Algebra.Unitization

/-!
# Extending a linear map to nonunital tensors

Let R be a commutative semiring, V an R-module with additive commutative
monoid structure, and A a nonunital semiring with an R-module structure.
The scalar action is compatible with multiplication on both sides:
(r • a)b = r • (ab) = a(r • b). The carriers of R, V and A may have
independent universes.

For s : V →ₗ[R] A, the tensor-algebra lift to the unitization R ⊕ A
sends ι(v) to (0, s(v)). Its scalar component is the tensor augmentation
ε : T_R(V) → R. Restricting to ker ε and taking the A component therefore
defines a nonunital R-algebra homomorphism ker ε → A.
Its value on the degree-one generator associated to v is s(v).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

universe uR uV uA
namespace NonUnitalTensorAlgebra

variable (R : Type uR) [CommSemiring R]
variable (V : Type uV) [AddCommMonoid V] [Module R V]
variable {A : Type uA} [NonUnitalSemiring A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- Let R be a commutative semiring, V an R-module with additive
commutative monoid structure, and A a nonunital semiring with a central
R-module action satisfying (r • a)b = r • (ab) = a(r • b).
For s : V →ₗ[R] A, this is the R-algebra homomorphism
T_R(V) → Unitization R A extending v ↦ (0, s(v)). -/
def unitizationLift (s : V →ₗ[R] A) : TensorAlgebra R V →ₐ[R] Unitization R A :=
  TensorAlgebra.lift R ((Unitization.inrHom R R A).comp s)

/-- Let R be a commutative semiring, V an R-module with additive
commutative monoid structure, A a nonunital semiring with an R-action
compatible with multiplication on both sides, and s : V →ₗ[R] A.
The lift to Unitization R A sends each tensor generator ι(v) to
the scalar-zero element (0, s(v)). -/
theorem unitizationLift_ι (s : V →ₗ[R] A) (v : V) :
    unitizationLift R V s (TensorAlgebra.ι R v) = (s v : Unitization R A) :=
  TensorAlgebra.lift_ι_apply ((Unitization.inrHom R R A).comp s) v

/-- Let R be a commutative semiring, V an R-module with additive
commutative monoid structure, A a nonunital semiring with an R-action
compatible with multiplication on both sides, and s : V →ₗ[R] A.
For every x ∈ T_R(V), the scalar component of the unitization lift is
ε(x), the tensor augmentation. In particular it vanishes on ker ε. -/
theorem unitizationLift_fst (s : V →ₗ[R] A) (x : TensorAlgebra R V) :
    (unitizationLift R V s x).fst = TensorAlgebra.algebraMapInv x := by
  have h : (Unitization.fstHom (R := R) (A := A)).comp (unitizationLift R V s) =
      TensorAlgebra.algebraMapInv := by
    apply TensorAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    change (unitizationLift R V s (TensorAlgebra.ι R v)).fst =
      TensorAlgebra.algebraMapInv (TensorAlgebra.ι R v)
    rw [unitizationLift_ι, TensorAlgebra.algebraMapInv_ι R V v]
    exact Unitization.fst_inr R (s v)
  exact congrArg (fun f : TensorAlgebra R V →ₐ[R] R => f x) h

/-- Let R be a commutative semiring, V an R-module with additive
commutative monoid structure, A a nonunital semiring with an R-action
compatible with multiplication on both sides, and s : V →ₗ[R] A.
This nonunital R-algebra homomorphism ker(ε : T_R(V) → R) → A
is the restriction of the unitization lift followed by its A component,
and extends s on degree-one tensors. -/
def lift (s : V →ₗ[R] A) : NonUnitalTensorAlgebra R V →ₙₐ[R] A where
  toFun x := (unitizationLift R V s x.1).snd
  map_zero' := by
    change (unitizationLift R V s 0).snd = 0
    rw [map_zero]
    exact Unitization.snd_zero
  map_add' := by
    intro x y
    change (unitizationLift R V s (x.1 + y.1)).snd =
      (unitizationLift R V s x.1).snd + (unitizationLift R V s y.1).snd
    rw [map_add, Unitization.snd_add]
  map_mul' := by
    intro x y
    change (unitizationLift R V s (x.1 * y.1)).snd =
      (unitizationLift R V s x.1).snd * (unitizationLift R V s y.1).snd
    rw [map_mul, Unitization.snd_mul]
    have hx := (TensorAlgebra.mem_augmentationKernel R V x.1).1 x.property
    have hy := (TensorAlgebra.mem_augmentationKernel R V y.1).1 y.property
    simp only [unitizationLift_fst, hx, hy, zero_smul, zero_add]
  map_smul' := by
    intro r x
    change (unitizationLift R V s (r • x.1)).snd = r • (unitizationLift R V s x.1).snd
    rw [map_smul, Unitization.snd_smul]

/-- Let R be a commutative semiring, V an R-module with additive
commutative monoid structure, A a nonunital semiring with an R-action
compatible with multiplication on both sides, and s : V →ₗ[R] A.
For x ∈ ker(ε : T_R(V) → R), the nonunital lift has value equal to
the A component of the unitization lift evaluated on x. -/
theorem lift_apply (s : V →ₗ[R] A) (x : NonUnitalTensorAlgebra R V) :
    lift R V s x = (unitizationLift R V s x.1).snd := rfl

/-- Let R be a commutative semiring, V an R-module with additive
commutative monoid structure, A a nonunital semiring with an R-action
compatible with multiplication on both sides, and s : V →ₗ[R] A.
The nonunital tensor lift sends the augmentation-kernel generator
associated to v ∈ V to s(v). -/
theorem lift_ι (s : V →ₗ[R] A) (v : V) :
    lift R V s (ι R V v) = s v := by
  change (unitizationLift R V s (TensorAlgebra.ι R v)).snd = s v
  rw [unitizationLift_ι]
  exact Unitization.snd_inr R (s v)

end NonUnitalTensorAlgebra
