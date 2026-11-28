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

public import Mathlib.Data.Fin.VecNotation
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientAction
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientHomogeneous
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Exterior
import Mathlib.Tactic.Abel

/-!
# Bracket and action terms in the coefficient differential

Let R be commutative, L an R-Lie algebra and M a compatible left Lie
module. On exterior-first tensors, the homogeneous coefficient
differential is
d_n^M=(d_n^trivial⊗id_M)+A_n,
where
A_n((x_0∧⋯∧x_n)⊗m)=
∑_i(−1)^{i+1}(x with entry i deleted)⊗[x_i,m].

The bracket term puts each [x_i,x_j] first, with coefficient
(−1)^{i+j} and the other entries in their given order. If the coefficient
action is trivial, only the bracket differential tensored with M remains.
The formulas apply to arbitrary Lie algebras and modules over R.
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
  [LieRingModule L M] [LieModule R L M]

local notation "G" => fun n : ℕ => (⋀[R]^n L)

private theorem coefficientActionBoundary_inclusion_ιMulti (n : ℕ)
    (v : Fin (n + 1) → L) (m : M) :
    ((⋀[R]^n L).subtype.rTensor M)
        (coefficientActionBoundary R L M n
          (exteriorPower.ιMulti R (n + 1) v ⊗ₜ[R] m)) =
      ∑ i : Fin (n + 1), (-1 : R) ^ (i.val + 1) •
        (ExteriorAlgebra.ιMulti R n (v ∘ i.succAbove) ⊗ₜ[R] ⁅v i, m⁆) := by
  rw [coefficientActionBoundary_apply_ιMulti_tmul]
  simp only [map_sum, map_smul, LinearMap.rTensor_tmul, Submodule.subtype_apply,
    exteriorPower.ιMulti_apply_coe]

private theorem coefficientActionBoundary_inclusion_cons (n : ℕ) (x : L)
    (v : Fin (n + 1) → L) (m : M) :
    ((⋀[R]^(n + 1) L).subtype.rTensor M)
        (coefficientActionBoundary R L M (n + 1)
          (exteriorPower.ιMulti R (n + 2) (Fin.cons x v) ⊗ₜ[R] m)) =
      -(ExteriorAlgebra.ιMulti R (n + 1) v ⊗ₜ[R] ⁅x, m⁆) -
        coefficientInsertion R L M x
          (((⋀[R]^n L).subtype.rTensor M)
            (coefficientActionBoundary R L M n
              (exteriorPower.ιMulti R (n + 1) v ⊗ₜ[R] m))) := by
  rw [coefficientActionBoundary_inclusion_ιMulti R L M (n + 1),
    coefficientActionBoundary_inclusion_ιMulti R L M n, Fin.sum_univ_succ]
  have hhead : (Fin.cons x v) ∘ (0 : Fin (n + 2)).succAbove = v := by
    funext i
    simp only [Function.comp_apply, Fin.zero_succAbove, Fin.cons_succ]
  rw [hhead]
  simp only [Fin.val_zero, Nat.zero_add, pow_one, Fin.cons_zero, Fin.cons_succ]
  rw [neg_one_smul R (ExteriorAlgebra.ιMulti R (n + 1) v ⊗ₜ[R] ⁅x, m⁆)]
  rw [sub_eq_add_neg]
  congr 1
  rw [map_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hdelete :
      (Fin.cons x v) ∘ i.succ.succAbove = Fin.cons x (v ∘ i.succAbove) :=
    Fin.cons_comp_succ_succAbove x v i
  have hsign : (-1 : R) ^ (i.succ.val + 1) = -((-1 : R) ^ (i.val + 1)) := by
    change (-1 : R) ^ ((i.val + 1) + 1) = _
    rw [pow_succ, mul_neg, mul_one]
  rw [hdelete, hsign, ExteriorAlgebra.ιMulti_succ_apply, map_smul,
    coefficientInsertion_tmul]
  simp only [Fin.cons_zero, Matrix.vecTail, Function.comp_def, Fin.cons_succ]
  exact neg_smul ((-1 : R) ^ (i.val + 1))
    ((ExteriorAlgebra.ι R x * ExteriorAlgebra.ιMulti R n (v ∘ i.succAbove))
      ⊗ₜ[R] ⁅v i, m⁆)

private theorem coefficientBoundary_ιMulti_eq_boundary_add_action (n : ℕ) :
    ∀ (v : Fin (n + 1) → L) (m : M),
      coefficientBoundary R L M (ExteriorAlgebra.ιMulti R (n + 1) v ⊗ₜ[R] m) =
        boundary R L (ExteriorAlgebra.ιMulti R (n + 1) v) ⊗ₜ[R] m +
          ((⋀[R]^n L).subtype.rTensor M)
            (coefficientActionBoundary R L M n
              (exteriorPower.ιMulti R (n + 1) v ⊗ₜ[R] m)) := by
  induction n with
  | zero =>
      intro v m
      rw [coefficientActionBoundary_zero_apply_ιMulti_tmul]
      rw [map_neg ((⋀[R]^0 L).subtype.rTensor M)
        (exteriorPower.ιMulti R 0 (fun i : Fin 0 => Fin.elim0 i) ⊗ₜ[R] ⁅v 0, m⁆)]
      simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply,
        exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
        ExteriorAlgebra.ιMulti_zero_apply, mul_one, coefficientBoundary_ι_tmul,
        boundary_ι, TensorProduct.zero_tmul, zero_add]
  | succ n ih =>
      intro v m
      obtain ⟨x, v, rfl⟩ := Fin.exists_cons v
      have hword :
          ExteriorAlgebra.ιMulti R (n + 2) (Fin.cons x v) =
            ExteriorAlgebra.ι R x * ExteriorAlgebra.ιMulti R (n + 1) v := by
        rw [ExteriorAlgebra.ιMulti_succ_apply]
        simp only [Fin.cons_zero, Matrix.vecTail, Function.comp_def, Fin.cons_succ]
      rw [coefficientActionBoundary_inclusion_cons R L M n x v m]
      simp only [hword]
      rw [coefficientBoundary_ι_mul_tmul, boundary_ι_mul, ih v m,
        coefficientDiagonalAction_tmul]
      simp only [TensorProduct.sub_tmul, TensorProduct.neg_tmul, map_add,
        coefficientInsertion_tmul]
      abel

/-- Let R be commutative, L an R-Lie algebra and M a compatible
left Lie module. The coefficient tensor order is Λ_R^nL⊗M.
The homogeneous differential is the sum
 d_n^M=d_n^trivial⊗id_M+A_n,
where A_n is signed deletion followed by the left coefficient action. -/
theorem coefficientDifferential_eq_bracket_add_action (n : ℕ) :
    coefficientDifferential R L M n =
      (differential R L n).rTensor M + coefficientActionBoundary R L M n := by
  apply TensorProduct.ext'
  intro a m
  have h : (coefficientDifferential R L M n).comp
      ((TensorProduct.mk R (⋀[R]^(n + 1) L) M).flip m) =
    ((differential R L n).rTensor M + coefficientActionBoundary R L M n).comp
      ((TensorProduct.mk R (⋀[R]^(n + 1) L) M).flip m) := by
    apply exteriorPower.linearMap_ext (R := R) (n := n + 1) (M := L)
      (N := (⋀[R]^n L) ⊗[R] M)
    apply AlternatingMap.ext
    intro v
    change coefficientDifferential R L M n
        (exteriorPower.ιMulti R (n + 1) v ⊗ₜ[R] m) =
      differential R L n (exteriorPower.ιMulti R (n + 1) v) ⊗ₜ[R] m +
        coefficientActionBoundary R L M n
          (exteriorPower.ιMulti R (n + 1) v ⊗ₜ[R] m)
    apply DirectSum.subtype_rTensor_injective G M n
    rw [coefficientDifferential_inclusion_apply, map_add]
    simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply, differential_coe,
      exteriorPower.ιMulti_apply_coe]
    exact coefficientBoundary_ιMulti_eq_boundary_add_action R L M n v m
  exact LinearMap.congr_fun h a

/-- Let R be commutative, L an R-Lie algebra and M a compatible
left Lie module. The coefficient tensor order is Λ_R^nL⊗M.
For x:Fin(n+1)→L and m∈M,
d_n^M((x_0∧⋯∧x_n)⊗m)=β_n(x)⊗m
+∑_i(−1)^{i+1}(x with entry i deleted)⊗[x_i,m]. -/
theorem coefficientDifferential_apply_ιMulti_tmul (n : ℕ)
    (v : Fin (n + 1) → L) (m : M) :
    coefficientDifferential R L M n
        (exteriorPower.ιMulti R (n + 1) v ⊗ₜ[R] m) =
      differential R L n (exteriorPower.ιMulti R (n + 1) v) ⊗ₜ[R] m +
        ∑ i : Fin (n + 1), (-1 : R) ^ (i.val + 1) •
          (exteriorPower.ιMulti R n (v ∘ i.succAbove) ⊗ₜ[R] ⁅v i, m⁆) := by
  rw [coefficientDifferential_eq_bracket_add_action, LinearMap.add_apply,
    LinearMap.rTensor_tmul, coefficientActionBoundary_apply_ιMulti_tmul]

/-- Let R be commutative, L an R-Lie algebra and M a compatible
left Lie module. The coefficient tensor order is Λ_R^nL⊗M.
If the Lie action on M is trivial, then
 d_n^M=d_n^trivial⊗id_M in every exterior degree. -/
theorem coefficientDifferential_eq_bracket_of_isTrivial
    [LieModule.IsTrivial L M] (n : ℕ) :
    coefficientDifferential R L M n = (differential R L n).rTensor M := by
  rw [coefficientDifferential_eq_bracket_add_action, coefficientActionBoundary_eq_zero,
    add_zero]

end ChevalleyEilenberg
