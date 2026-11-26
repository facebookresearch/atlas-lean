/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Lie.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import MathlibExt.LinearAlgebra.ExteriorPower.Deletion

/-!
# The left-coefficient action term in the exterior boundary

Let R be a commutative ring, L an R-Lie algebra and M a left Lie
module compatible with the R-action. The action term on exterior-first
tensors is
A_n((x_0∧⋯∧x_n)⊗m)=
∑_{i=0}^{n}(−1)^{i+1}(x with entry i deleted)⊗[x_i,m].
The remaining generators retain their order.

It is an R-linear map Λ_R^{n+1}L⊗M→Λ_R^nL⊗M.
In degree one the target exterior word is empty; after Λ_R^0L⊗M≃M,
the value is −[x,m]. The term is natural in Lie-module coefficient
maps with independent carrier universes and is zero for a trivial
Lie action. The full CE differential also includes the bracket term.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w w'

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]
variable (M : Type w) [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
The coefficient action term is the R-linear map
A_n:Λ_R^{n+1}L⊗M→Λ_R^nL⊗M obtained by deleting one
Lie generator and applying its left action with coefficient (−1)^{i+1}. -/
def coefficientActionBoundary (n : ℕ) :
    ((⋀[R]^(n + 1) L) ⊗[R] M) →ₗ[R] ((⋀[R]^n L) ⊗[R] M) :=
  (-1 : R) • (((LieModule.toModuleHom R L M).toLinearMap.lTensor (⋀[R]^n L)).comp
    ((TensorProduct.assoc R (⋀[R]^n L) L M).toLinearMap.comp
      ((exteriorPower.deletion R L n).rTensor M)))

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
For x:Fin(n+1)→L and m∈M,
A_n((x_0∧⋯∧x_n)⊗m)=∑_i(−1)^{i+1}
(x with entry i deleted)⊗[x_i,m], with ordered deletion. -/
theorem coefficientActionBoundary_apply_ιMulti_tmul (n : ℕ)
    (v : Fin (n + 1) → L) (m : M) :
    coefficientActionBoundary R L M n
        ((exteriorPower.ιMulti R (n + 1) v) ⊗ₜ[R] m) =
      ∑ i : Fin (n + 1), (-1 : R) ^ (i.val + 1) •
        ((exteriorPower.ιMulti R n (v ∘ i.succAbove)) ⊗ₜ[R] ⁅v i, m⁆) := by
  change (-1 : R) • ((LieModule.toModuleHom R L M).toLinearMap.lTensor (⋀[R]^n L)
      ((TensorProduct.assoc R (⋀[R]^n L) L M)
        ((exteriorPower.deletion R L n (exteriorPower.ιMulti R (n + 1) v))
          ⊗ₜ[R] m))) = _
  rw [exteriorPower.deletion_apply_ιMulti, TensorProduct.sum_tmul]
  simp only [map_sum, ← TensorProduct.smul_tmul', map_smul,
    TensorProduct.assoc_tmul, LinearMap.lTensor_tmul,
    LieModuleHom.coe_toLinearMap, LieModule.toModuleHom_apply]
  simp only [Finset.smul_sum, smul_smul, ← pow_succ']

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
In degree one, the action term has value
A_0(x⊗m)=−(1_{Λ^0L}⊗[x,m]), using the empty exterior word. -/
@[simp]
theorem coefficientActionBoundary_zero_apply_ιMulti_tmul
    (v : Fin 1 → L) (m : M) :
    coefficientActionBoundary R L M 0
        ((exteriorPower.ιMulti R 1 v) ⊗ₜ[R] m) =
      -((exteriorPower.ιMulti R 0 (fun i : Fin 0 ↦ Fin.elim0 i))
        ⊗ₜ[R] ⁅v 0, m⁆) := by
  have hv : v ∘ (0 : Fin 1).succAbove = (fun i : Fin 0 ↦ Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  calc
    _ = ∑ i : Fin 1, (-1 : R) ^ (i.val + 1) •
        (exteriorPower.ιMulti R 0 (v ∘ i.succAbove) ⊗ₜ[R] ⁅v i, m⁆) :=
      coefficientActionBoundary_apply_ιMulti_tmul R L M 0 v m
    _ = (-1 : R) ^ 1 •
        (exteriorPower.ιMulti R 0 (v ∘ (0 : Fin 1).succAbove) ⊗ₜ[R] ⁅v 0, m⁆) :=
      Fin.sum_univ_one (fun i : Fin 1 => (-1 : R) ^ (i.val + 1) •
        (exteriorPower.ιMulti R 0 (v ∘ i.succAbove) ⊗ₜ[R] ⁅v i, m⁆))
    _ = -((exteriorPower.ιMulti R 0 (fun i : Fin 0 ↦ Fin.elim0 i))
        ⊗ₜ[R] ⁅v 0, m⁆) := by
      rw [pow_one, hv]
      exact neg_one_smul R
        (exteriorPower.ιMulti R 0 (fun i : Fin 0 ↦ Fin.elim0 i) ⊗ₜ[R] ⁅v 0, m⁆)

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
Under Λ_R^0L⊗M≃R⊗M≃M, the first coefficient action
boundary has value −[x,m]. -/
theorem coefficientActionBoundary_zero_lid (v : Fin 1 → L) (m : M) :
    TensorProduct.lid R M
        ((exteriorPower.zeroEquiv R L).rTensor M
          (coefficientActionBoundary R L M 0
            ((exteriorPower.ιMulti R 1 v) ⊗ₜ[R] m))) =
      -⁅v 0, m⁆ := by
  let degreeZero : ((⋀[R]^0 L) ⊗[R] M) →ₗ[R] M :=
    (TensorProduct.lid R M).toLinearMap.comp
      ((exteriorPower.zeroEquiv R L).rTensor M).toLinearMap
  let z : (⋀[R]^0 L) ⊗[R] M :=
    exteriorPower.ιMulti R 0 (fun i : Fin 0 ↦ Fin.elim0 i) ⊗ₜ[R] ⁅v 0, m⁆
  have hz : degreeZero z = ⁅v 0, m⁆ := by
    calc
      _ = TensorProduct.lid R M
          ((exteriorPower.zeroEquiv R L
            (exteriorPower.ιMulti R 0 (fun i : Fin 0 ↦ Fin.elim0 i))) ⊗ₜ[R] ⁅v 0, m⁆) :=
        congrArg (TensorProduct.lid R M)
          (LinearEquiv.rTensor_tmul (M := M) (f := exteriorPower.zeroEquiv R L)
            (m := ⁅v 0, m⁆) (n := exteriorPower.ιMulti R 0 (fun i : Fin 0 ↦ Fin.elim0 i)))
      _ = TensorProduct.lid R M ((1 : R) ⊗ₜ[R] ⁅v 0, m⁆) :=
        congrArg (fun r : R => TensorProduct.lid R M (r ⊗ₜ[R] ⁅v 0, m⁆))
          (exteriorPower.zeroEquiv_ιMulti (R := R) (M := L) (fun i : Fin 0 ↦ Fin.elim0 i))
      _ = (1 : R) • ⁅v 0, m⁆ := TensorProduct.lid_tmul ⁅v 0, m⁆ 1
      _ = ⁅v 0, m⁆ := one_smul R ⁅v 0, m⁆
  calc
    _ = degreeZero (-z) :=
      congrArg degreeZero (coefficientActionBoundary_zero_apply_ιMulti_tmul R L M v m)
    _ = -(degreeZero z) := map_neg degreeZero z
    _ = -⁅v 0, m⁆ := congrArg Neg.neg hz

section Naturality

variable {N : Type w'} [AddCommGroup N] [Module R N]
  [LieRingModule L N] [LieModule R L N]

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
For a homomorphism f:M→N of R-Lie modules over the same L,
with N in an independent carrier universe,
(id⊗f)A_n^M=A_n^N(id⊗f) on the corresponding exterior powers. -/
theorem coefficientActionBoundary_naturality (n : ℕ) (f : M →ₗ⁅R,L⁆ N) :
    (f.toLinearMap.lTensor (⋀[R]^n L)).comp
        (coefficientActionBoundary R L M n) =
      (coefficientActionBoundary R L N n).comp
        (f.toLinearMap.lTensor (⋀[R]^(n + 1) L)) := by
  apply TensorProduct.ext'
  intro a m
  have h :
      ((f.toLinearMap.lTensor (⋀[R]^n L)).comp
        (coefficientActionBoundary R L M n)).comp
          ((TensorProduct.mk R (⋀[R]^(n + 1) L) M).flip m) =
      ((coefficientActionBoundary R L N n).comp
        (f.toLinearMap.lTensor (⋀[R]^(n + 1) L))).comp
          ((TensorProduct.mk R (⋀[R]^(n + 1) L) M).flip m) := by
    apply exteriorPower.linearMap_ext (R := R) (n := n + 1) (M := L)
      (N := (⋀[R]^n L) ⊗[R] N)
    apply AlternatingMap.ext
    intro v
    change (f.toLinearMap.lTensor (⋀[R]^n L))
        (coefficientActionBoundary R L M n
          ((exteriorPower.ιMulti R (n + 1) v) ⊗ₜ[R] m)) =
      coefficientActionBoundary R L N n
        ((exteriorPower.ιMulti R (n + 1) v) ⊗ₜ[R] f m)
    simp only [coefficientActionBoundary_apply_ιMulti_tmul, map_sum, map_smul,
      LinearMap.lTensor_tmul, LieModuleHom.coe_toLinearMap, LieModuleHom.map_lie]
  exact LinearMap.congr_fun h a

end Naturality

/-- Let R be commutative, L an R-Lie algebra and M a left
L-module whose Lie action is compatible with its R-module structure.
If the L-action on M is trivial, [x,m]=0 for every x,m,
then A_n=0 as an R-linear map in every degree. -/
@[simp]
theorem coefficientActionBoundary_eq_zero [LieModule.IsTrivial L M] (n : ℕ) :
    coefficientActionBoundary R L M n = 0 := by
  have haction : (LieModule.toModuleHom R L M).toLinearMap = 0 := by
    apply TensorProduct.ext'
    intro x m
    change LieModule.toModuleHom R L M (x ⊗ₜ[R] m) = 0
    rw [LieModule.toModuleHom_apply, trivial_lie_zero L M]
  rw [coefficientActionBoundary, haction, LinearMap.lTensor_zero,
    LinearMap.zero_comp, smul_zero]

end ChevalleyEilenberg
