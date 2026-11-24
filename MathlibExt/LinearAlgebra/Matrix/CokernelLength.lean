/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.Matrix.PivotCokernel
public import MathlibExt.LinearAlgebra.Matrix.CokernelReindex
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Option

/-!
# Determinants and full cokernel length over one-dimensional domains

The proof uses division-free elimination and induction on the actual matrix
size. It retains nonunit pivots and full quotient modules over singular
Noetherian domains. No finite-length or determinant-length premise is needed.
-/

@[expose] public section
noncomputable section

universe u v

namespace Matrix

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]

private def pivotIndexEquiv {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) ≃ Unit ⊕ Fin n :=
  (finSuccEquiv' i).trans ((Equiv.optionEquivSumPUnit.{0, 0} (Fin n)).trans
    ((Equiv.sumComm (Fin n) PUnit.{1}).trans
      (Equiv.sumCongr (Equiv.ofUnique PUnit.{1} Unit) (Equiv.refl (Fin n)))))

private theorem pivotIndexEquiv_symm_pivot {n : ℕ} (i : Fin (n + 1)) :
    (pivotIndexEquiv i).symm (Sum.inl ()) = i := by
  simp [pivotIndexEquiv]

private theorem length_coker_fin_eq_ord_det (n : ℕ) (A : Matrix (Fin n) (Fin n) R)
    (hA : A.det ≠ 0) :
    Module.length R ((Fin n → R) ⧸ A.mulVecLin.range) = Ring.ord R A.det := by
  induction n with
  | zero =>
    rw [det_isEmpty, Ring.ord_one]
    exact Module.length_eq_zero
  | succ n ih =>
    have hex : ∃ i j, A i j ≠ 0 := by
      by_contra h
      push Not at h
      have hzero : A = 0 := Matrix.ext h
      exact hA (hzero ▸ det_zero)
    obtain ⟨i, j, hp⟩ := hex
    let er := pivotIndexEquiv i
    let ec := pivotIndexEquiv j
    let C := A.reindex er ec
    let a := C (Sum.inl ()) (Sum.inl ())
    let r : Matrix Unit (Fin n) R := C.submatrix Sum.inl Sum.inr
    let c : Matrix (Fin n) Unit R := C.submatrix Sum.inr Sum.inl
    let B : Matrix (Fin n) (Fin n) R := C.submatrix Sum.inr Sum.inr
    have ha : a ≠ 0 := by
      simpa [a, C, er, ec, reindex_apply, pivotIndexEquiv_symm_pivot] using hp
    have hC : C = pivotBlock a r c B := by
      ext x y
      cases x with
      | inl x =>
        cases x
        cases y with
        | inl y => cases y; simp [pivotBlock, a]
        | inr y => rfl
      | inr x =>
        cases y with
        | inl y => rfl
        | inr y => rfl
    have hdet : (pivotBlock a r c B).det ≠ 0 := by
      rw [← hC]
      exact (det_reindex_ne_zero_iff er ec A).mpr hA
    have hS := det_pivotSchur_ne_zero a ha r c B hdet
    have hlength := length_coker_pivot_matrix_relation a ha r c B hdet
    rw [LinearMap.length_scalar_coker_eq_ord, ih _ hS, Fintype.card_fin] at hlength
    have horder := congrArg (Ring.ord R) (det_pivotSchur_relation a r c B)
    rw [Ring.ord_mul' R (by simpa using ha),
      Ring.ord_mul' R (by simpa using pow_ne_zero n ha),
      Ring.ord_pow (by simpa using ha), nsmul_eq_mul, Fintype.card_fin] at horder
    have hfinite : (n : ℕ∞) * Ring.ord R a ≠ ⊤ := by
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp
        (Ring.ord_ne_top (R := R) (a := a) (by simpa using ha))
      rw [← hk, ← ENat.natCast_mul]
      exact ENat.natCast_ne_top (n * k)
    have hpivot : Module.length R (((Unit ⊕ Fin n) → R) ⧸ (pivotBlock a r c B).mulVecLin.range) =
        Ring.ord R (pivotBlock a r c B).det := by
      apply ENat.add_left_injective_of_ne_top hfinite
      exact hlength.trans (horder.trans (add_comm _ _))
    rw [← hC] at hpivot
    exact (length_coker_reindex er ec A).symm.trans
      (hpivot.trans (ord_det_reindex er ec A))

/-- The full cokernel of every square matrix with nonzero determinant over
a one-dimensional Noetherian domain has length equal to the existing order
of its determinant. The proof includes the empty matrix, singular domains,
and all nonreduced principal quotients, with no finite-length premise. -/
theorem length_coker_eq_ord_det {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (hA : A.det ≠ 0) :
    Module.length R ((ι → R) ⧸ A.mulVecLin.range) = Ring.ord R A.det := by
  let e := Fintype.equivFin ι
  have hdet : (A.reindex e e).det ≠ 0 := (det_reindex_ne_zero_iff e e A).mpr hA
  exact (length_coker_reindex e e A).symm.trans
    ((length_coker_fin_eq_ord_det (Fintype.card ι) (A.reindex e e) hdet).trans
      (ord_det_reindex e e A))

/-- Finite length of the full matrix cokernel is earned from its actual
nonzero determinant and the one-dimensional Noetherian domain hypotheses. -/
theorem length_coker_ne_top_of_det_ne_zero {ι : Type v} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (hA : A.det ≠ 0) :
    Module.length R ((ι → R) ⧸ A.mulVecLin.range) ≠ ⊤ := by
  rw [length_coker_eq_ord_det A hA]
  exact Ring.ord_ne_top (by simpa using hA)

end Matrix
