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

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import MathlibExt.LinearAlgebra.ExteriorAlgebra.CoalgebraGrading
public import MathlibExt.RingTheory.Kaehler.DeRham

/-!
# The exterior coproduct as a diagonal

The diagonal map into a product of modules induces an algebra map into
the Koszul tensor of their exterior algebras. Its underlying linear map
agrees with the exterior coproduct. Graded tensor interchange therefore
fixes that coproduct.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

local notation "E" => ExteriorAlgebra R M
local notation "ℰ" => fun n : ℕ => ⋀[R]^n M
local notation "G" => ℰ ᵍ⊗[R] ℰ
local notation "γ" => (CliffordAlgebra.involute : E →ₐ[R] E)

/-- The actual exterior diagonal, with the native graded tensor algebra as target. -/
def diagonalGraded : E →ₐ[R] G :=
  (prodEquivTensor R M M).toAlgHom.comp
    (map ((LinearMap.id : M →ₗ[R] M).prod (LinearMap.id : M →ₗ[R] M)))

@[simp]
theorem diagonalGraded_ι (x : M) :
    diagonalGraded R M (ι R x) = ι R x ᵍ⊗ₜ[R] (1 : E) + (1 : E) ᵍ⊗ₜ[R] ι R x := by
  unfold diagonalGraded
  rw [AlgHom.comp_apply, map_apply_ι]
  change prodEquivTensorForward R M M (ι R (x, x)) = _
  exact prodEquivTensorForward_ι_apply R M M (x, x)

/-- The underlying linear diagonal uses the native equivalence to the ordinary tensor module. -/
def diagonalLinear : E →ₗ[R] E ⊗[R] E :=
  (GradedTensorProduct.of R ℰ ℰ).symm.toLinearMap.comp (diagonalGraded R M).toLinearMap

@[simp]
theorem diagonalLinear_algebraMap (r : R) :
    diagonalLinear R M (algebraMap R E r) = r • ((1 : E) ⊗ₜ[R] (1 : E)) := by
  simp only [diagonalLinear, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.commutes, Algebra.algebraMap_eq_smul_one, map_smul,
    map_one, GradedTensorProduct.of_symm_one, Algebra.TensorProduct.one_def]
  have h₁ : (GradedTensorProduct.of R ℰ ℰ).symm (1 : G) =
      (1 : E) ⊗ₜ[R] (1 : E) := rfl
  exact (congrArg (fun z : E ⊗[R] E => r • z) h₁).trans
    (TensorProduct.smul_tmul' r (1 : E) (1 : E))

private theorem diagonalGraded_mul_insertion (x : M) (t : E ⊗[R] E) :
    (GradedTensorProduct.of R ℰ ℰ).symm (diagonalGraded R M (ι R x) * (GradedTensorProduct.of R ℰ ℰ) t) =
      signedInsertion R M x t := by
  let A : Module.End R (E ⊗[R] E) := (GradedTensorProduct.of R ℰ ℰ).symm.toLinearMap.comp
    (((Algebra.lmul R G) (diagonalGraded R M (ι R x))).comp (GradedTensorProduct.of R ℰ ℰ).toLinearMap)
  have h : A = signedInsertion R M x := by
    apply TensorProduct.ext'
    intro a b
    change (GradedTensorProduct.of R ℰ ℰ).symm (diagonalGraded R M (ι R x) * (a ᵍ⊗ₜ[R] b)) =
      signedInsertion R M x (a ⊗ₜ[R] b)
    induction a using DirectSum.Decomposition.inductionOn ℰ with
    | zero =>
        simp only [TensorProduct.zero_tmul, GradedTensorProduct.tmul, map_zero, mul_zero]
    | add a c ha hc =>
        simp only [TensorProduct.add_tmul, GradedTensorProduct.tmul, map_add, mul_add, ha, hc]
    | @homogeneous n a =>
        let sx : ⋀[R]^1 M := ⟨ι R x, by simpa only [pow_one] using LinearMap.mem_range_self (ι R) x⟩
        have hm : ((1 : E) ᵍ⊗ₜ[R] (sx : E) * (a : E) ᵍ⊗ₜ[R] b : G) =
            (-1 : ℤˣ) ^ (1 * n) • (((1 : E) * a) ᵍ⊗ₜ[R] ((sx : E) * b)) :=
          GradedTensorProduct.tmul_coe_mul_coe_tmul ℰ ℰ 1 sx a b
        rw [diagonalGraded_ι, add_mul, map_add,
          GradedTensorProduct.tmul_one_mul_coe_tmul]
        rw [hm, signedInsertion_tmul,
          involute_of_mem_exteriorPower (A := R) (M := M) (n := n) a.property]
        simp only [one_mul, sx]
        rw [@Units.smul_def _ _ (_) (_), ← Int.cast_smul_eq_zsmul R, LinearEquiv.map_smul]
        simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
          Int.cast_pow, Int.cast_neg, Int.cast_one, GradedTensorProduct.tmul,
          GradedTensorProduct.of_symm_of, TensorProduct.smul_tmul']
  exact LinearMap.congr_fun h t

/-- The native exterior diagonal obeys the actual signed insertion recursion. -/
theorem diagonalLinear_ι_mul (x : M) (a : E) :
    diagonalLinear R M (ι R x * a) = signedInsertion R M x (diagonalLinear R M a) := by
  change (GradedTensorProduct.of R ℰ ℰ).symm (diagonalGraded R M (ι R x * a)) =
    signedInsertion R M x ((GradedTensorProduct.of R ℰ ℰ).symm (diagonalGraded R M a))
  rw [map_mul]
  simpa only [LinearEquiv.apply_symm_apply] using
    diagonalGraded_mul_insertion R M x ((GradedTensorProduct.of R ℰ ℰ).symm (diagonalGraded R M a))

/-- The fold-built coproduct is exactly the native exterior diagonal. -/
theorem coproduct_eq_diagonalLinear : coproduct R M = diagonalLinear R M := by
  apply LinearMap.ext
  intro a
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => rw [coproduct_algebraMap, diagonalLinear_algebraMap]
  | add a b ha hb => simp only [map_add, ha, hb]
  | ι_mul a x ha => rw [coproduct_ι_mul, diagonalLinear_ι_mul, ha]

private theorem one_mem_exteriorPower_zero : (1 : E) ∈ ⋀[R]^0 M := by
  change (1 : E) ∈ (LinearMap.range (ι R : M →ₗ[R] E)) ^ 0
  rw [pow_zero]
  exact Submodule.mem_one.mpr ⟨(1 : R), by simp only [map_one]⟩

/-- Native graded tensor interchange fixes the native exterior diagonal. -/
theorem diagonalGraded_comm :
    (GradedTensorProduct.comm ℰ ℰ).toAlgHom.comp (diagonalGraded R M) = diagonalGraded R M := by
  apply ExteriorAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  change GradedTensorProduct.comm ℰ ℰ (diagonalGraded R M (ι R x)) =
    diagonalGraded R M (ι R x)
  rw [diagonalGraded_ι, map_add]
  let sx : ⋀[R]^1 M := ⟨ι R x, by simpa only [pow_one] using LinearMap.mem_range_self (ι R) x⟩
  let s0 : ⋀[R]^0 M := ⟨1, one_mem_exteriorPower_zero R M⟩
  change GradedTensorProduct.comm ℰ ℰ ((sx : E) ᵍ⊗ₜ[R] (s0 : E)) +
      GradedTensorProduct.comm ℰ ℰ ((s0 : E) ᵍ⊗ₜ[R] (sx : E)) =
    (sx : E) ᵍ⊗ₜ[R] (s0 : E) + (s0 : E) ᵍ⊗ₜ[R] (sx : E)
  simp only [GradedTensorProduct.comm_coe_tmul_coe, mul_zero, zero_mul,
    pow_zero, one_smul]
  exact add_comm _ _

/-- The actual Koszul interchange on the ordinary underlying tensor module. -/
def koszulSwap : (E ⊗[R] E) ≃ₗ[R] (E ⊗[R] E) :=
  (GradedTensorProduct.of R ℰ ℰ).trans
    ((GradedTensorProduct.comm ℰ ℰ).toLinearEquiv.trans (GradedTensorProduct.of R ℰ ℰ).symm)

/-- The native exterior diagonal proves graded cocommutativity of the actual coproduct. -/
theorem koszulSwap_coproduct (a : E) : koszulSwap R M (coproduct R M a) = coproduct R M a := by
  rw [coproduct_eq_diagonalLinear]
  change (GradedTensorProduct.of R ℰ ℰ).symm (GradedTensorProduct.comm ℰ ℰ (diagonalGraded R M a)) =
    (GradedTensorProduct.of R ℰ ℰ).symm (diagonalGraded R M a)
  exact congrArg (GradedTensorProduct.of R ℰ ℰ).symm (AlgHom.congr_fun (diagonalGraded_comm R M) a)

/-- The Koszul interchange has the usual homogeneous sign over the original ring. -/
theorem koszulSwap_tmul (p q : ℕ) (a : ⋀[R]^p M) (b : ⋀[R]^q M) :
    koszulSwap R M ((a : E) ⊗ₜ[R] (b : E)) =
      (-1 : R) ^ (p * q) • ((b : E) ⊗ₜ[R] (a : E)) := by
  change (GradedTensorProduct.of R ℰ ℰ).symm (GradedTensorProduct.comm ℰ ℰ ((a : E) ᵍ⊗ₜ[R] (b : E))) = _
  rw [GradedTensorProduct.comm_coe_tmul_coe]
  rw [@Units.smul_def _ _ (_) (_), ← Int.cast_smul_eq_zsmul R, LinearEquiv.map_smul]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    Int.cast_pow, Int.cast_neg, Int.cast_one, GradedTensorProduct.tmul,
    GradedTensorProduct.of_symm_of, Nat.mul_comm]

end ExteriorAlgebra
