/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import MathlibExt.LinearAlgebra.ExteriorPower.ContractionWedge
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Actual leading exterior determinant coefficients

The coefficient functional uses the original exterior pairing on the actual
dual coordinate tuple. When an outside basis index is absent from the other
wedge factors, determinant expansion isolates that coordinate. No coefficient
or containment model is supplied.
-/

public section
noncomputable section
namespace exteriorPower

open Module
universe u v w
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {I : Type w} [LinearOrder I] (b : Module.Basis I R M)

/-- The actual determinant coefficient with an outside coordinate prepended to a basis tuple. -/
def leadingCoefficient {n : ℕ} (j : I) (s : Set.powersetCard I n) :
    (⋀[R]^(n + 1) M) →ₗ[R] R :=
  pairingDual R M (n + 1)
    (ιMulti R (n + 1) (Fin.cons (b.coord j) (fun i => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s i))))

/-- The original determinant functional has its literal actual-coordinate matrix value. -/
theorem leadingCoefficient_ιMulti {n : ℕ} (j : I) (s : Set.powersetCard I n) (a : Fin (n + 1) → M) :
    leadingCoefficient b j s (ιMulti R (n + 1) a) =
      Matrix.det (Matrix.of (fun i k =>
        (Fin.cons (b.coord j) (fun l => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s l)) :
          Fin (n + 1) → Module.Dual R M) k (a i))) := by
  unfold leadingCoefficient
  rw [pairingDual_ιMulti_ιMulti]

/-- The actual exterior determinant isolates an outside coordinate on a tuple with no outside factor. -/
theorem leadingCoefficient_cons {n : ℕ} (j : I) (s : Set.powersetCard I n) (x : M) (a : Fin n → M)
    (ha : ∀ i, b.coord j (a i) = 0) :
    leadingCoefficient b j s (ιMulti R (n + 1) (Fin.cons x a)) =
      b.coord j x * ιMultiDual R n b s (ιMulti R n a) := by
  classical
  rw [leadingCoefficient_ιMulti, Matrix.det_succ_column_zero]
  rw [Finset.sum_eq_single 0]
  · simp only [Fin.val_zero, pow_zero, one_mul, Matrix.of_apply, Fin.cons_zero]
    rw [ιMultiDual_apply_ιMulti]
    have hminor : (Matrix.of (fun i k =>
        (Fin.cons (b.coord j) (fun l => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s l)) :
          Fin (n + 1) → Module.Dual R M) k ((Fin.cons x a : Fin (n + 1) → M) i))).submatrix
          (Fin.succAbove 0) Fin.succ =
        Matrix.of (fun i k => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s k) (a i)) := by
      ext i k
      simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.zero_succAbove, Fin.cons_succ]
    rw [hminor]
  · intro i _ hi
    have he : i = (i.pred hi).succ := (Fin.succ_pred i hi).symm
    rw [he]
    simp only [Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, ha (i.pred hi), mul_zero, zero_mul]
  · intro h
    exact False.elim (h (Finset.mem_univ 0))

/-- A leading exterior determinant vanishes on every different actual basis tuple without the outside index. -/
theorem leadingCoefficient_wedge_basis {n : ℕ} (j : I) (s t : Set.powersetCard I n) (x : M)
    (hj : j ∉ t) :
    leadingCoefficient b j s (wedgeLeft R M x n (b.exteriorPower n t)) =
      if s = t then b.coord j x else 0 := by
  classical
  rw [basis_apply, ιMulti_family, wedgeLeft_apply_ιMulti]
  change leadingCoefficient b j s (ιMulti R (n + 1)
    (Fin.cons x (b ∘ Set.powersetCard.ofFinEmbEquiv.symm t))) = _
  rw [leadingCoefficient_cons]
  · change b.coord j x * ιMultiDual R n b s (ιMulti_family R n b t) = _
    by_cases hst : s = t
    · rw [ite_eq_left hst, hst, ιMultiDual_apply_diag, mul_one]
    · rw [ite_eq_right hst, ιMultiDual_apply_nondiag R n b s t hst, mul_zero]
  · intro i
    rw [Module.Basis.coord_apply, Function.comp_apply, Module.Basis.repr_self, Finsupp.single_apply]
    apply ite_eq_right
    intro he
    apply hj
    rw [← he]
    exact Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t _ |>.mp ⟨i, rfl⟩

end exteriorPower
