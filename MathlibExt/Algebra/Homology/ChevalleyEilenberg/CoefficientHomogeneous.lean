/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientBoundary

/-!
# Homogeneous coefficient boundaries and their exterior coordinates

Let M be a left Lie module over an R-Lie algebra L, with R commutative. The decomposition of
ExteriorAlgebra R L into exterior degrees gives a tensor decomposition after tensoring with M.
Its degree-n submodule is linearly equivalent to ⋀[R]^n L ⊗[R] M, and its inclusion into the
ambient tensor product is injective because it is a summand of that decomposition.

The ambient CE coefficient boundary maps degree n + 1 into degree n. Restricting and
transporting it through these homogeneous coordinates defines the coefficient differential.
Consecutive differentials compose to zero. In degree one, the formula is δ(x ⊗ m) = −(1 ⊗
⁅x,m⁆), with 1 the empty exterior word.

See Weibel, *An Introduction to Homological Algebra*, Chapter 7.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v w

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]
variable (M : Type w) [AddCommGroup M] [Module R M]

local notation "E" => ExteriorAlgebra R L
local notation "G" => fun n : ℕ => (⋀[R]^n L)

private theorem coefficientDegree_tmul_mem (n : ℕ) (a : E)
    (ha : a ∈ ⋀[R]^n L) (m : M) :
    a ⊗ₜ[R] m ∈ DirectSum.decomposeTensor G M n := by
  rw [DirectSum.decomposeTensor_apply]
  refine ⟨(⟨a, ha⟩ : ⋀[R]^n L) ⊗ₜ[R] m, ?_⟩
  simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply]

private theorem coefficientDegree_ιMulti_tmul_mem (n : ℕ) (a : Fin n → L) (m : M) :
    ExteriorAlgebra.ιMulti R n a ⊗ₜ[R] m ∈ DirectSum.decomposeTensor G M n :=
  coefficientDegree_tmul_mem R L M n _ (ExteriorAlgebra.ιMulti_range R n ⟨a, rfl⟩) m

variable [LieRingModule L M] [LieModule R L M]

omit [LieRingModule L M] [LieModule R L M] in
private theorem coefficientInsertion_mem_degree (x : L) (n : ℕ)
    (p : E ⊗[R] M) (hp : p ∈ DirectSum.decomposeTensor G M n) :
    coefficientInsertion R L M x p ∈ DirectSum.decomposeTensor G M (n + 1) := by
  rw [DirectSum.decomposeTensor_apply] at hp
  obtain ⟨t, rfl⟩ := hp
  induction t using TensorProduct.inductionOn with
  | tmul a m =>
      simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply,
        coefficientInsertion_tmul]
      apply coefficientDegree_tmul_mem
      change ExteriorAlgebra.ι R x * (a : E) ∈
        (LinearMap.range (ExteriorAlgebra.ι R)) ^ (n + 1)
      rw [pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ x) a.property
  | add p q hp hq =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hp hq

private theorem coefficientDiagonalAction_mem_degree (x : L) (n : ℕ)
    (p : E ⊗[R] M) (hp : p ∈ DirectSum.decomposeTensor G M n) :
    coefficientDiagonalAction R L M x p ∈ DirectSum.decomposeTensor G M n := by
  rw [DirectSum.decomposeTensor_apply] at hp
  obtain ⟨t, rfl⟩ := hp
  induction t using TensorProduct.inductionOn with
  | tmul a m =>
      simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply,
        coefficientDiagonalAction_tmul]
      exact Submodule.add_mem _
        (coefficientDegree_tmul_mem R L M n _
          (adjointAction_mem_exteriorPower R L x n a a.property) m)
        (coefficientDegree_tmul_mem R L M n a a.property ⁅x, m⁆)
  | add p q hp hq =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hp hq

private theorem coefficientBoundary_ιMulti_mem_degree (n : ℕ) :
    ∀ (a : Fin (n + 1) → L) (m : M),
      coefficientBoundary R L M (ExteriorAlgebra.ιMulti R (n + 1) a ⊗ₜ[R] m) ∈
        DirectSum.decomposeTensor G M n := by
  induction n with
  | zero =>
      intro a m
      rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
        mul_one, coefficientBoundary_ι_tmul]
      simpa only [ExteriorAlgebra.ιMulti_zero_apply] using
        Submodule.neg_mem (DirectSum.decomposeTensor G M 0)
          (coefficientDegree_ιMulti_tmul_mem R L M 0 Fin.elim0 ⁅a 0, m⁆)
  | succ n ih =>
      intro a m
      rw [ExteriorAlgebra.ιMulti_succ_apply, coefficientBoundary_ι_mul_tmul]
      exact Submodule.sub_mem _
        (Submodule.neg_mem _ (coefficientDiagonalAction_mem_degree R L M (a 0) (n + 1)
          _ (coefficientDegree_ιMulti_tmul_mem R L M (n + 1) (Matrix.vecTail a) m)))
        (coefficientInsertion_mem_degree R L M (a 0) n _ (ih (Matrix.vecTail a) m))

private theorem coefficientBoundary_tmul_mem_degree (n : ℕ) (a : E)
    (ha : a ∈ ⋀[R]^(n + 1) L) (m : M) :
    coefficientBoundary R L M (a ⊗ₜ[R] m) ∈ DirectSum.decomposeTensor G M n := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree R (n + 1)] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨v, rfl⟩ := ha
      exact coefficientBoundary_ιMulti_mem_degree R L M n v m
  | zero =>
      rw [TensorProduct.zero_tmul, map_zero]
      exact Submodule.zero_mem _
  | add a b ha hb iha ihb =>
      rw [TensorProduct.add_tmul, map_add]
      exact Submodule.add_mem _ iha ihb
  | smul r a ha ih =>
      rw [← TensorProduct.smul_tmul', map_smul]
      exact Submodule.smul_mem _ r ih

/-- Let R be a commutative ring, L an R-Lie algebra and M a left Lie module over L. Put E =
ExteriorAlgebra R L and let H_n be the image of (⋀[R]^n L) ⊗[R] M in E ⊗[R] M under the
homogeneous inclusion. For every n : ℕ and p ∈ H_(n+1), coefficientBoundary R L M p belongs to
H_n. -/
theorem coefficientBoundary_mem_degree (n : ℕ) (p : E ⊗[R] M)
    (hp : p ∈ DirectSum.decomposeTensor G M (n + 1)) :
    coefficientBoundary R L M p ∈ DirectSum.decomposeTensor G M n := by
  rw [DirectSum.decomposeTensor_apply] at hp
  obtain ⟨t, rfl⟩ := hp
  induction t using TensorProduct.inductionOn with
  | tmul a m =>
      simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply]
      exact coefficientBoundary_tmul_mem_degree R L M n a a.property m
  | add p q hp hq =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hp hq

/-- Let R be a commutative ring, L an R-Lie algebra and M a left Lie module over L. Put E =
ExteriorAlgebra R L and let H_n be the image of (⋀[R]^n L) ⊗[R] M in E ⊗[R] M under the
homogeneous inclusion. For n : ℕ, coefficientDifferential R L M n : ⋀[R]^(n+1) L ⊗[R] M →ₗ[R]
⋀[R]^n L ⊗[R] M is obtained by the degree-(n+1) inclusion, the ambient coefficientBoundary,
and the inverse degree-n tensor-decomposition equivalence. -/
def coefficientDifferential (n : ℕ) :
    ((⋀[R]^(n + 1) L) ⊗[R] M) →ₗ[R] ((⋀[R]^n L) ⊗[R] M) :=
  (DirectSum.decomposeTensorEquiv G M n).symm.toLinearMap.comp
    (((coefficientBoundary R L M).comp ((⋀[R]^(n + 1) L).subtype.rTensor M)).codRestrict
      (DirectSum.decomposeTensor G M n)
      (fun p => coefficientBoundary_mem_degree R L M n _
        (by
          rw [DirectSum.decomposeTensor_apply]
          exact LinearMap.mem_range_self ((⋀[R]^(n + 1) L).subtype.rTensor M) p)))

/-- Let R be a commutative ring, L an R-Lie algebra and M a left Lie module over L. Put E =
ExteriorAlgebra R L and let H_n be the image of (⋀[R]^n L) ⊗[R] M in E ⊗[R] M under the
homogeneous inclusion. Let J_n : ⋀[R]^n L ⊗[R] M →ₗ[R] E ⊗[R] M be the homogeneous inclusion.
Then J_n ∘ coefficientDifferential n = coefficientBoundary ∘ J_(n+1) for every n : ℕ. -/
theorem coefficientDifferential_inclusion (n : ℕ) :
    ((⋀[R]^n L).subtype.rTensor M).comp (coefficientDifferential R L M n) =
      (coefficientBoundary R L M).comp ((⋀[R]^(n + 1) L).subtype.rTensor M) := by
  apply LinearMap.ext
  intro p
  let q : DirectSum.decomposeTensor G M n :=
    ⟨coefficientBoundary R L M (((⋀[R]^(n + 1) L).subtype.rTensor M) p),
      coefficientBoundary_mem_degree R L M n _ (by
        rw [DirectSum.decomposeTensor_apply]
        exact LinearMap.mem_range_self ((⋀[R]^(n + 1) L).subtype.rTensor M) p)⟩
  change ((⋀[R]^n L).subtype.rTensor M)
      ((DirectSum.decomposeTensorEquiv G M n).symm q) = (q : E ⊗[R] M)
  exact (DirectSum.val_decomposeTensorEquiv_apply G M
    ((DirectSum.decomposeTensorEquiv G M n).symm q)).symm.trans
      (congrArg Subtype.val ((DirectSum.decomposeTensorEquiv G M n).apply_symm_apply q))

/-- Let R be a commutative ring, L an R-Lie algebra and M a left Lie module over L. Put E =
ExteriorAlgebra R L and let H_n be the image of (⋀[R]^n L) ⊗[R] M in E ⊗[R] M under the
homogeneous inclusion. For n : ℕ and p : ⋀[R]^(n+1) L ⊗[R] M, inclusion of
coefficientDifferential R L M n p into E ⊗[R] M equals coefficientBoundary applied to the
degree-(n+1) inclusion of p. -/
@[simp]
theorem coefficientDifferential_inclusion_apply (n : ℕ)
    (p : (⋀[R]^(n + 1) L) ⊗[R] M) :
    ((⋀[R]^n L).subtype.rTensor M) (coefficientDifferential R L M n p) =
      coefficientBoundary R L M (((⋀[R]^(n + 1) L).subtype.rTensor M) p) :=
  LinearMap.congr_fun (coefficientDifferential_inclusion R L M n) p

/-- Let R be a commutative ring, L an R-Lie algebra and M a left Lie module over L. For every n :
ℕ, coefficientDifferential R L M n ∘ coefficientDifferential R L M (n + 1) = 0 as an R-linear
map from ⋀[R]^(n+2) L ⊗[R] M to ⋀[R]^n L ⊗[R] M. -/
theorem coefficientDifferential_comp_differential (n : ℕ) :
    (coefficientDifferential R L M n).comp (coefficientDifferential R L M (n + 1)) = 0 := by
  apply LinearMap.ext
  intro p
  apply DirectSum.subtype_rTensor_injective G M n
  rw [LinearMap.comp_apply, LinearMap.zero_apply, map_zero,
    coefficientDifferential_inclusion_apply, coefficientDifferential_inclusion_apply,
    coefficientBoundary_squared]

/-- Let R be a commutative ring, L an R-Lie algebra and M a left Lie module over L. For x : L and
m : M, coefficientDifferential R L M 0 sends exteriorPower.ιMulti R 1 (fun _ => x) ⊗ₜ[R] m to
−(exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R] ⁅x,m⁆). -/
@[simp]
theorem coefficientDifferential_ι_tmul (x : L) (m : M) :
    coefficientDifferential R L M 0
        (exteriorPower.ιMulti R 1 (fun _ => x) ⊗ₜ[R] m) =
      -(exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R] ⁅x, m⁆) := by
  apply DirectSum.subtype_rTensor_injective G M 0
  rw [coefficientDifferential_inclusion_apply]
  rw [map_neg ((⋀[R]^0 L).subtype.rTensor M)
    (exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R] ⁅x, m⁆)]
  simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one,
    coefficientBoundary_ι_tmul]

end ChevalleyEilenberg
