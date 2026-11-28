/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import MathlibExt.LinearAlgebra.ExteriorAlgebra.CoalgebraGrading

/-!
# The graded algebra diagonal and Koszul symmetry

For `E=ExteriorAlgebra R M`, the diagonal linear map `M → M×M`, `x ↦ (x,x)`, induces an
algebra map into the graded tensor product of the exterior degree families. Its multiplication
has sign `(-1)^(q*r)` when a right factor of degree `q` crosses a left factor of degree `r`.

The underlying linear map to `E ⊗[R] E` is the exterior coproduct. The graded interchange
fixes this diagonal. On homogeneous tensors the induced interchange is `a_p⊗b_q ↦
(-1)^(p*q)(b_q⊗a_p)`, and it fixes the coproduct.

References: Bourbaki, *Algebra*, Chapter III; Loday, *Cyclic Homology*, Section 4.5.
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

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. Let `G` be the graded tensor algebra of the exterior degree families and
`τ : E ⊗[R] E ≃ₗ[R] G` its linear identification. Its homogeneous product is
`(a_p⊗b_q)(c_r⊗d_s)=(-1)^(q*r)(a_pc_r⊗b_qd_s)`. The `R`-algebra map `diagonalGraded R M : E
→ₐ[R] G` is induced by `x ↦ (x,x)` followed by the exterior-algebra product equivalence. It
sends a generator to `ι(x)⊗1+1⊗ι(x)` in `G`. -/
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

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. Let `G` be the graded tensor algebra of the exterior degree families and
`τ : E ⊗[R] E ≃ₗ[R] G` its linear identification. Its homogeneous product is
`(a_p⊗b_q)(c_r⊗d_s)=(-1)^(q*r)(a_pc_r⊗b_qd_s)`. The `R`-linear map `diagonalLinear R M : E →
E⊗E` is `τ⁻¹ ∘ diagonalGraded R M`. -/
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
    (GradedTensorProduct.of R ℰ ℰ).symm
      (diagonalGraded R M (ι R x) * (GradedTensorProduct.of R ℰ ℰ) t) =
      signedInsertion R M x t := by
  let A : Module.End R (E ⊗[R] E) := (GradedTensorProduct.of R ℰ ℰ).symm.toLinearMap.comp
    (((Algebra.lmul R G) (diagonalGraded R M (ι R x))).comp
      (GradedTensorProduct.of R ℰ ℰ).toLinearMap)
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
        rw [hm, signedInsertion_tmul, involute_of_mem_exteriorPower
          (A := R) (M := M) (n := n) (x := a) a.property]
        simp only [one_mul, sx]
        rw [@Units.smul_def _ _ (_) (_), ← Int.cast_smul_eq_zsmul R, LinearEquiv.map_smul]
        simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
          Int.cast_pow, Int.cast_neg, Int.cast_one, GradedTensorProduct.tmul,
          GradedTensorProduct.of_symm_of, TensorProduct.smul_tmul']
  exact LinearMap.congr_fun h t

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. Let `G` be the graded tensor algebra of the exterior degree families and
`τ : E ⊗[R] E ≃ₗ[R] G` its linear identification. Its homogeneous product is
`(a_p⊗b_q)(c_r⊗d_s)=(-1)^(q*r)(a_pc_r⊗b_qd_s)`. For `x : M` and `a : E`, `diagonalLinear R M
(ι(x)*a)=signedInsertion R M x (diagonalLinear R M a)`. -/
theorem diagonalLinear_ι_mul (x : M) (a : E) :
    diagonalLinear R M (ι R x * a) = signedInsertion R M x (diagonalLinear R M a) := by
  change (GradedTensorProduct.of R ℰ ℰ).symm (diagonalGraded R M (ι R x * a)) =
    signedInsertion R M x ((GradedTensorProduct.of R ℰ ℰ).symm (diagonalGraded R M a))
  rw [map_mul]
  simpa only [LinearEquiv.apply_symm_apply] using
    diagonalGraded_mul_insertion R M x ((GradedTensorProduct.of R ℰ ℰ).symm (diagonalGraded R M a))

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. Let `G` be the graded tensor algebra of the exterior degree families and
`τ : E ⊗[R] E ≃ₗ[R] G` its linear identification. Its homogeneous product is
`(a_p⊗b_q)(c_r⊗d_s)=(-1)^(q*r)(a_pc_r⊗b_qd_s)`. The maps satisfy `coproduct R M =
diagonalLinear R M : E →ₗ[R] E⊗E`. -/
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

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. Let `G` be the graded tensor algebra of the exterior degree families and
`τ : E ⊗[R] E ≃ₗ[R] G` its linear identification. Its homogeneous product is
`(a_p⊗b_q)(c_r⊗d_s)=(-1)^(q*r)(a_pc_r⊗b_qd_s)`. The graded tensor interchange `κ_G : G → G`
satisfies `κ_G ∘ diagonalGraded R M = diagonalGraded R M` as `R`-algebra maps. -/
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

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. Let `G` be the graded tensor algebra of the exterior degree families and
`τ : E ⊗[R] E ≃ₗ[R] G` its linear identification. Its homogeneous product is
`(a_p⊗b_q)(c_r⊗d_s)=(-1)^(q*r)(a_pc_r⊗b_qd_s)`. The `R`-linear equivalence `koszulSwap R M :
E⊗E ≃ₗ[R] E⊗E` is `τ⁻¹ ∘ κ_G ∘ τ`, where `κ_G` is graded tensor interchange. -/
def koszulSwap : (E ⊗[R] E) ≃ₗ[R] (E ⊗[R] E) :=
  (GradedTensorProduct.of R ℰ ℰ).trans
    ((GradedTensorProduct.comm ℰ ℰ).toLinearEquiv.trans (GradedTensorProduct.of R ℰ ℰ).symm)

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. Let `G` be the graded tensor algebra of the exterior degree families and
`τ : E ⊗[R] E ≃ₗ[R] G` its linear identification. Its homogeneous product is
`(a_p⊗b_q)(c_r⊗d_s)=(-1)^(q*r)(a_pc_r⊗b_qd_s)`. For every `a : E`, `koszulSwap R M (Δ a)=Δ a`. -/
theorem koszulSwap_coproduct (a : E) : koszulSwap R M (coproduct R M a) = coproduct R M a := by
  rw [coproduct_eq_diagonalLinear]
  change (GradedTensorProduct.of R ℰ ℰ).symm (GradedTensorProduct.comm ℰ ℰ (diagonalGraded R M a)) =
    (GradedTensorProduct.of R ℰ ℰ).symm (diagonalGraded R M a)
  exact congrArg (GradedTensorProduct.of R ℰ ℰ).symm (AlgHom.congr_fun (diagonalGraded_comm R M) a)

/-- Let `R` be a commutative ring, `M` an `R`-module, and `E = ExteriorAlgebra R M`. Write `ι : M
→ E` for the generators, `γ` for the grade involution, and `Δ : E →ₗ[R] E ⊗[R] E` for the
exterior coproduct. Let `G` be the graded tensor algebra of the exterior degree families and
`τ : E ⊗[R] E ≃ₗ[R] G` its linear identification. Its homogeneous product is
`(a_p⊗b_q)(c_r⊗d_s)=(-1)^(q*r)(a_pc_r⊗b_qd_s)`. For `p,q : ℕ`, `a : Λ^p_R M`, and `b : Λ^q_R
M`, `koszulSwap R M ((a:E)⊗(b:E))=(-1:R)^(p*q) • ((b:E)⊗(a:E))`. -/
theorem koszulSwap_tmul (p q : ℕ) (a : ⋀[R]^p M) (b : ⋀[R]^q M) :
    koszulSwap R M ((a : E) ⊗ₜ[R] (b : E)) =
      (-1 : R) ^ (p * q) • ((b : E) ⊗ₜ[R] (a : E)) := by
  change (GradedTensorProduct.of R ℰ ℰ).symm
    (GradedTensorProduct.comm ℰ ℰ ((a : E) ᵍ⊗ₜ[R] (b : E))) = _
  rw [GradedTensorProduct.comm_coe_tmul_coe]
  rw [@Units.smul_def _ _ (_) (_), ← Int.cast_smul_eq_zsmul R, LinearEquiv.map_smul]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    Int.cast_pow, Int.cast_neg, Int.cast_one, GradedTensorProduct.tmul,
    GradedTensorProduct.of_symm_of, Nat.mul_comm]

end ExteriorAlgebra
