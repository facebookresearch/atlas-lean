/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSpecialLinear
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.HeterogeneousBruhat
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.GeneralLinearEquiv
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Monomial
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.UpperElementary
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.SemidirectProduct
/-!
# Uniqueness of monomial factors in Bruhat cells

For matrices over a field indexed by a finite linear order, two equal
factorizations with upper-elementary left and right factors have the same
monomial middle factor, including its permutation and unit weights.

A preliminary algebraic rearrangement works for arbitrary invertible outer
factors. In the uniqueness arguments, the upper-elementary condition supplies
triangularity and diagonal entries equal to one. The earlier triangular
matrix lemmas use a ring, and the bundled upper-unitriangular subgroup uses
a commutative ring.
-/
@[expose] public section

open Matrix
open Equiv
open PermutationBilinearCocycle

namespace Matrix.GeneralLinearGroup

section UpperTriangularRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {R : Type*} [Ring R]

omit [Fintype ι] in
/-- Elementary transvection `E_{i,j}(a)` with `i < j` is upper triangular. -/
theorem elementary_isUpperTriangular {i j : ι} (hij : i < j) (a : R) :
    IsUpperTriangular (1 + Matrix.single i j a : Matrix ι ι R) := by
  intro r s hrs
  have h1 : (1 : Matrix ι ι R) r s = 0 := by
    simp only [Matrix.one_apply]
    split
    next h =>
      exact absurd h (Ne.symm (ne_of_lt hrs))
    rfl
  have h2 : (Matrix.single i j a : Matrix ι ι R) r s = 0 := by
    rw [Matrix.single_apply]
    split
    next h =>
      rcases h with ⟨hr, hs⟩
      have : r < s := hr ▸ hs ▸ hij
      exact absurd this (not_lt_of_gt hrs)
    rfl
  simp [Matrix.add_apply, h1, h2]

omit [Fintype ι] [LinearOrder ι] in
theorem elementary_diag {i j : ι} (hij : i ≠ j) (a : R) (k : ι) :
    (1 + Matrix.single i j a : Matrix ι ι R) k k = 1 := by
  have hSingle : (Matrix.single i j a : Matrix ι ι R) k k = 0 := by
    rw [Matrix.single_apply]
    split
    next h =>
      rcases h with ⟨hi, hj⟩
      exact absurd (hi.trans hj.symm) hij
    rfl
  simp [Matrix.add_apply, hSingle]

omit [DecidableEq ι] in
/-- Product of upper-triangular matrices has diagonal product. -/
theorem isUpperTriangular_mul_diag {M N : Matrix ι ι R}
    (hM : IsUpperTriangular M) (hN : IsUpperTriangular N) (i : ι) :
    (M * N) i i = M i i * N i i := by
  classical
  have hMul : (M * N) i i = ∑ k : ι, M i k * N k i := by
    simp [Matrix.mul_apply]
  rw [hMul]
  have hZero : ∀ k : ι, k ≠ i → M i k * N k i = 0 := by
    intro k hk
    rcases lt_trichotomy k i with hlt | heq | hgt
    · have hM0 : M i k = 0 := hM hlt
      simp [hM0]
    · exact absurd heq hk
    · have hN0 : N k i = 0 := hN hgt
      simp [hN0]
  calc ∑ k : ι, M i k * N k i
      = ∑ k ∈ (Finset.univ : Finset ι), M i k * N k i := rfl
    _ = M i i * N i i + ∑ k ∈ (Finset.univ : Finset ι).erase i, M i k * N k i := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    _ = M i i * N i i + 0 := by
        have hSumZero :
            ∑ k ∈ (Finset.univ : Finset ι).erase i, M i k * N k i = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          have hkNe : k ≠ i := by
            intro heq
            have : k ∈ (Finset.univ : Finset ι).erase i := hk
            simp [heq] at this
          exact hZero k hkNe
        rw [hSumZero, add_zero]
    _ = M i i * N i i := by simp

end UpperTriangularRing

section UpperUnitriangularCommRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {R : Type*} [CommRing R]

/-- Set of upper unitriangular matrices in `GL ι R`. -/
def upperUnitriangularSet (ι : Type*) [DecidableEq ι] [Fintype ι] [LinearOrder ι]
    (R : Type*) [CommRing R] : Set (GL ι R) :=
  { g | IsUpperTriangular (g : Matrix ι ι R) ∧ ∀ i, (g : Matrix ι ι R) i i = 1 }

/-- Bundled upper unitriangular subgroup. -/
def upperUnitriangularSubgroup (ι : Type*) [DecidableEq ι] [Fintype ι] [LinearOrder ι]
    (R : Type*) [CommRing R] : Subgroup (GL ι R) where
  carrier := upperUnitriangularSet ι R
  mul_mem' := by
    intro a b ha hb
    constructor
    · exact ha.1.mul hb.1
    · intro i
      have hMul := isUpperTriangular_mul_diag ha.1 hb.1 i
      have hVal :
          ((a * b : GL ι R) : Matrix ι ι R) =
            (a : Matrix ι ι R) * (b : Matrix ι ι R) := by simp
      calc ((a * b : GL ι R) : Matrix ι ι R) i i
          = ((a : Matrix ι ι R) * (b : Matrix ι ι R)) i i := by rw [hVal]
        _ = (a : Matrix ι ι R) i i * (b : Matrix ι ι R) i i := hMul
        _ = 1 * 1 := by rw [ha.2 i, hb.2 i]
        _ = 1 := by simp
  one_mem' := by
    constructor
    · exact blockTriangular_one
    · intro i
      simp
  inv_mem' := by
    intro g hg
    have hTri : BlockTriangular (g : Matrix ι ι R) id := hg.1
    have hDiag := hg.2
    have hInvTri : BlockTriangular ((g⁻¹ : GL ι R) : Matrix ι ι R) id := by
      let hInv : Invertible (g : Matrix ι ι R) :=
        { invOf := (g⁻¹ : GL ι R).val
          invOf_mul_self := by
            calc (↑(g⁻¹ : GL ι R) : Matrix ι ι R) * (↑g : Matrix ι ι R)
                = ((g⁻¹ * g : GL ι R) : Matrix ι ι R) := by simp
              _ = ((1 : GL ι R) : Matrix ι ι R) := by rw [inv_mul_cancel]
              _ = 1 := by simp
          mul_invOf_self := by
            calc (↑g : Matrix ι ι R) * (↑(g⁻¹ : GL ι R) : Matrix ι ι R)
                = ((g * g⁻¹ : GL ι R) : Matrix ι ι R) := by simp
              _ = ((1 : GL ι R) : Matrix ι ι R) := by rw [mul_inv_cancel]
              _ = 1 := by simp }
      have hTriInv : BlockTriangular (↑g : Matrix ι ι R)⁻¹ id :=
        blockTriangular_inv_of_blockTriangular (b := id) hTri
      have h1 : ⅟(↑g : Matrix ι ι R) = (↑g : Matrix ι ι R)⁻¹ :=
        invOf_eq_nonsing_inv _
      have h2 : ⅟(↑g : Matrix ι ι R) = (↑(g⁻¹ : GL ι R) : Matrix ι ι R) := rfl
      have hEq : (↑g : Matrix ι ι R)⁻¹ = (↑(g⁻¹ : GL ι R) : Matrix ι ι R) :=
        h1.symm.trans h2
      rw [hEq] at hTriInv
      exact hTriInv
    constructor
    · exact hInvTri
    · intro i
      have hMulOne : ((g : Matrix ι ι R) * (g⁻¹ : GL ι R).val) i i = 1 := by
        have h1 : (g : Matrix ι ι R) * (g⁻¹ : GL ι R).val = 1 := by
          calc (↑g : Matrix ι ι R) * (↑(g⁻¹ : GL ι R) : Matrix ι ι R)
              = ((g * g⁻¹ : GL ι R) : Matrix ι ι R) := by simp
            _ = ((1 : GL ι R) : Matrix ι ι R) := by rw [mul_inv_cancel]
            _ = 1 := by simp
        rw [h1]
        simp
      have hMulDiag := isUpperTriangular_mul_diag hTri hInvTri i
      rw [hMulDiag] at hMulOne
      have hGi : (g : Matrix ι ι R) i i = 1 := hDiag i
      rw [hGi, one_mul] at hMulOne
      exact hMulOne

theorem upperElementarySet_subset_upperUnitriangularSet_commRing :
    upperElementarySet ι R ⊆ upperUnitriangularSet ι R := by
  intro g hg
  obtain ⟨i, j, hij, a, rfl⟩ := hg
  constructor
  · have h :
        (elementary i j (ne_of_lt hij) a : GL ι R).val =
          (1 + Matrix.single i j a : Matrix ι ι R) := rfl
    rw [h]
    exact elementary_isUpperTriangular hij a
  · intro k
    have h :
        (elementary i j (ne_of_lt hij) a : GL ι R).val =
          (1 + Matrix.single i j a : Matrix ι ι R) := rfl
    rw [h]
    exact elementary_diag (ne_of_lt hij) a k

theorem upperElementarySubgroup_le_upperUnitriangularSubgroup_commRing :
    upperElementarySubgroup ι R ≤ upperUnitriangularSubgroup ι R := by
  rw [upperElementarySubgroup]
  rw [Subgroup.closure_le]
  exact upperElementarySet_subset_upperUnitriangularSet_commRing

theorem upperElementary_isUpperTriangular_commRing
    (g : upperElementarySubgroup ι R) :
    IsUpperTriangular ((g : GL ι R) : Matrix ι ι R) :=
  (upperElementarySubgroup_le_upperUnitriangularSubgroup_commRing (R := R) g.2).1

theorem upperElementary_diag_one_commRing (g : upperElementarySubgroup ι R) (i : ι) :
    ((g : GL ι R) : Matrix ι ι R) i i = 1 :=
  (upperElementarySubgroup_le_upperUnitriangularSubgroup_commRing (R := R) g.2).2 i

theorem upperElementary_entry_zero_of_lt_commRing (g : upperElementarySubgroup ι R)
    {r s : ι} (h : s < r) :
    ((g : GL ι R) : Matrix ι ι R) r s = 0 :=
  upperElementary_isUpperTriangular_commRing g h

end UpperUnitriangularCommRing

section MonomialLemmas

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {F : Type*} [Field F]

omit [LinearOrder ι] in
/-- Entry of a monomial matrix: `M i j = if σ j = i then w i else 0`. -/
theorem monomialMatrixHom_entry (w : ι → Fˣ) (σ : Equiv.Perm ι) (i j : ι) :
    (monomialMatrixHom F ι ⟨w, σ⟩ : Matrix ι ι F) i j =
      if σ j = i then (w i : F) else 0 := by
  have hCoe :
      (monomialMatrixHom F ι ⟨w, σ⟩ : Matrix ι ι F) =
        Matrix.diagonal (fun k => (w k : F)) * (σ⁻¹).permMatrix F := by
    simp
  have hDiag : (Matrix.diagonal (fun k => (w k : F)) *
      (σ⁻¹).permMatrix F : Matrix ι ι F) i j =
      if (σ⁻¹ : Equiv.Perm ι) i = j then (w i : F) else 0 := by
    rw [diag_mul_perm_eq]
  rw [hCoe, hDiag]
  have hEquiv : (σ⁻¹ : Equiv.Perm ι) i = j ↔ σ j = i := by
    constructor
    · intro hh
      have : σ (σ⁻¹ i) = i := Equiv.apply_symm_apply σ i
      calc σ j = σ (σ⁻¹ i) := by rw [hh]
        _ = i := this
    · intro hh
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact hh.symm
  by_cases h : σ j = i
  · have h1 : (σ⁻¹ : Equiv.Perm ι) i = j := hEquiv.mpr h
    rw [ite_eq_left h1, ite_eq_left h]
  · have h1 : ¬ (σ⁻¹ : Equiv.Perm ι) i = j := by
      intro heq
      exact h (hEquiv.mp heq)
    rw [ite_eq_right h1, ite_eq_right h]

omit [DecidableEq ι] [Fintype ι] [LinearOrder ι] in
theorem monomialMatrixHom_weight_ne_zero (w : ι → Fˣ) (_σ : Equiv.Perm ι) (i : ι) :
    (w i : F) ≠ 0 := (w i).ne_zero

omit [LinearOrder ι] in
/-- Left multiplication by arbitrary `T` on a monomial
` (T * M) i j = T i (σ j) * w (σ j)`. -/
theorem upper_mul_monomial_apply (T : Matrix ι ι F) (w : ι → Fˣ)
    (σ : Equiv.Perm ι) (i j : ι) :
    (T * (monomialMatrixHom F ι ⟨w, σ⟩ : Matrix ι ι F)) i j =
      T i (σ j) * (w (σ j) : F) := by
  classical
  have hEntry : ∀ k : ι,
      (monomialMatrixHom F ι ⟨w, σ⟩ : Matrix ι ι F) k j =
        if σ j = k then (w k : F) else 0 :=
    fun k => monomialMatrixHom_entry w σ k j
  calc (T * (monomialMatrixHom F ι ⟨w, σ⟩ : Matrix ι ι F)) i j
      = ∑ k : ι, T i k * (monomialMatrixHom F ι ⟨w, σ⟩ : Matrix ι ι F) k j := by
          simp [Matrix.mul_apply]
    _ = ∑ k : ι, T i k * if σ j = k then (w k : F) else 0 := by
          apply Fintype.sum_congr
          intro k
          rw [hEntry k]
    _ = ∑ k : ι, if σ j = k then T i k * (w k : F) else 0 := by
          apply Fintype.sum_congr
          intro k
          by_cases hk : σ j = k
          · simp [hk]
          · simp [hk]
    _ = ∑ k ∈ (Finset.univ : Finset ι),
          if σ j = k then T i k * (w k : F) else 0 := rfl
    _ = T i (σ j) * (w (σ j) : F) := by
          rw [Finset.sum_ite_eq Finset.univ (σ j)
            (fun k => T i k * (w k : F))]
          simp

omit [LinearOrder ι] in
/-- Right multiplication by arbitrary `T` on a monomial
` (M * T) i j = w i * T (σ⁻¹ i) j`. -/
theorem monomial_mul_upper_apply (w : ι → Fˣ) (σ : Equiv.Perm ι)
    (T : Matrix ι ι F) (i j : ι) :
    ((monomialMatrixHom F ι ⟨w, σ⟩ : Matrix ι ι F) * T) i j =
      (w i : F) * T (σ⁻¹ i) j := by
  classical
  have hEntry : ∀ k : ι,
      (monomialMatrixHom F ι ⟨w, σ⟩ : Matrix ι ι F) i k =
        if σ k = i then (w i : F) else 0 :=
    fun k => monomialMatrixHom_entry w σ i k
  calc ((monomialMatrixHom F ι ⟨w, σ⟩ : Matrix ι ι F) * T) i j
      = ∑ k : ι, (monomialMatrixHom F ι ⟨w, σ⟩ : Matrix ι ι F) i k * T k j := by
          simp [Matrix.mul_apply]
    _ = ∑ k : ι, (if σ k = i then (w i : F) else 0) * T k j := by
          apply Fintype.sum_congr
          intro k
          rw [hEntry k]
    _ = ∑ k : ι, if σ k = i then (w i : F) * T k j else 0 := by
          apply Fintype.sum_congr
          intro k
          by_cases hk : σ k = i
          · simp [hk]
          · simp [hk]
    _ = ∑ k ∈ (Finset.univ : Finset ι),
          if σ k = i then (w i : F) * T k j else 0 := rfl
    _ = ∑ k ∈ (Finset.univ : Finset ι),
          if k = σ⁻¹ i then (w i : F) * T k j else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          have hSym : (σ k = i ↔ k = σ⁻¹ i) := by
            constructor
            · intro hk
              have : σ⁻¹ i = k := by
                rw [Equiv.Perm.inv_eq_iff_eq]
                exact hk.symm
              exact this.symm
            · intro hk
              rw [hk]
              simp
          by_cases hk : σ k = i
          · have hk' : k = σ⁻¹ i := hSym.mp hk
            rw [ite_eq_left hk, ite_eq_left hk']
          · have hk' : ¬ k = σ⁻¹ i := by
              intro heq
              exact hk (hSym.mpr heq)
            rw [ite_eq_right hk, ite_eq_right hk']
    _ = (w i : F) * T (σ⁻¹ i) j := by
          rw [Finset.sum_ite_eq' Finset.univ (σ⁻¹ i)
            (fun k => (w i : F) * T k j)]
          simp

end MonomialLemmas

section BruhatCellUniqueness

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {F : Type*} [Field F]

omit [LinearOrder ι] in
/-- Over a field on a finite index set, for arbitrary invertible outer
factors, equality `L * M * R = L' * M' * R'` of products with monomial
factors yields `T * M = M' * T'`, where `T = L'⁻¹ * L` and
`T' = R' * R⁻¹`. -/
theorem bruhatCell_rearrange (L R L' R' : GL ι F)
    (w : ι → Fˣ) (σ : Equiv.Perm ι) (w' : ι → Fˣ) (σ' : Equiv.Perm ι)
    (h : L * monomialMatrixHom F ι ⟨w, σ⟩ * R =
      L' * monomialMatrixHom F ι ⟨w', σ'⟩ * R') :
    (L'⁻¹ * L : GL ι F).val * (monomialMatrixHom F ι ⟨w, σ⟩ : Matrix ι ι F) =
      (monomialMatrixHom F ι ⟨w', σ'⟩ : Matrix ι ι F) *
        (R' * R⁻¹ : GL ι F).val := by
  have hGL : (L'⁻¹ * L : GL ι F) * monomialMatrixHom F ι ⟨w, σ⟩ =
      monomialMatrixHom F ι ⟨w', σ'⟩ * (R' * R⁻¹ : GL ι F) := by
    calc (L'⁻¹ * L : GL ι F) * monomialMatrixHom F ι ⟨w, σ⟩
        = L'⁻¹ * (L * monomialMatrixHom F ι ⟨w, σ⟩ * R) * R⁻¹ := by
          simp [mul_assoc]
      _ = L'⁻¹ * (L' * monomialMatrixHom F ι ⟨w', σ'⟩ * R') * R⁻¹ := by rw [h]
      _ = monomialMatrixHom F ι ⟨w', σ'⟩ * (R' * R⁻¹ : GL ι F) := by
          simp [mul_assoc]
  calc ((L'⁻¹ * L : GL ι F).val : Matrix ι ι F) *
        (monomialMatrixHom F ι ⟨w, σ⟩ : Matrix ι ι F)
      = (((L'⁻¹ * L : GL ι F) * monomialMatrixHom F ι ⟨w, σ⟩ : GL ι F).val :
          Matrix ι ι F) := by simp
    _ = ((monomialMatrixHom F ι ⟨w', σ'⟩ * (R' * R⁻¹ : GL ι F) : GL ι F).val :
          Matrix ι ι F) := by rw [hGL]
    _ = (monomialMatrixHom F ι ⟨w', σ'⟩ : Matrix ι ι F) *
        (R' * R⁻¹ : GL ι F).val := by simp

section BruhatPermWeight

/-- Over a field on a finite linearly ordered index set, two equal
products with monomial middle factors and all four outer factors
upper-elementary have the same inverse permutation in their middle factors. -/
theorem bruhatCell_perm_inv_unique
    (L R L' R' : upperElementarySubgroup ι F)
    (w : ι → Fˣ) (σ : Equiv.Perm ι) (w' : ι → Fˣ) (σ' : Equiv.Perm ι)
    (h : (L : GL ι F) * monomialMatrixHom F ι ⟨w, σ⟩ * (R : GL ι F) =
      (L' : GL ι F) * monomialMatrixHom F ι ⟨w', σ'⟩ * (R' : GL ι F)) :
    σ⁻¹ = σ'⁻¹ := by
  classical
  let T : GL ι F := (L' : GL ι F)⁻¹ * (L : GL ι F)
  let T' : GL ι F := (R' : GL ι F) * (R : GL ι F)⁻¹
  have hTmem : T ∈ upperElementarySubgroup ι F := by
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ L'.2) L.2
  have hT'mem : T' ∈ upperElementarySubgroup ι F := by
    exact Subgroup.mul_mem _ R'.2 (Subgroup.inv_mem _ R.2)
  have hT_tri : IsUpperTriangular (T : Matrix ι ι F) :=
    upperElementary_isUpperTriangular_commRing ⟨T, hTmem⟩
  have hT'_tri : IsUpperTriangular (T' : Matrix ι ι F) :=
    upperElementary_isUpperTriangular_commRing ⟨T', hT'mem⟩
  have hT_diag : ∀ i, (T : Matrix ι ι F) i i = 1 :=
    fun i => upperElementary_diag_one_commRing ⟨T, hTmem⟩ i
  have hMat : (T : Matrix ι ι F) * (monomialMatrixHom F ι ⟨w, σ⟩ : Matrix ι ι F) =
      (monomialMatrixHom F ι ⟨w', σ'⟩ : Matrix ι ι F) * (T' : Matrix ι ι F) :=
    bruhatCell_rearrange (L : GL ι F) (R : GL ι F) (L' : GL ι F) (R' : GL ι F)
      w σ w' σ' h
  have hLe1 : ∀ i : ι, σ'⁻¹ i ≤ σ⁻¹ i := by
    intro i
    have hEq := congrFun (congrFun hMat i) (σ⁻¹ i)
    rw [upper_mul_monomial_apply (T : Matrix ι ι F) w σ i (σ⁻¹ i),
      monomial_mul_upper_apply w' σ' (T' : Matrix ι ι F) i (σ⁻¹ i)] at hEq
    have hLeft : (T : Matrix ι ι F) i (σ (σ⁻¹ i)) * (w (σ (σ⁻¹ i)) : F) =
        (w i : F) := by
      have : σ (σ⁻¹ i) = i := Equiv.apply_symm_apply σ i
      rw [this, hT_diag i, one_mul]
    rw [hLeft] at hEq
    by_contra hNot
    have hLt : (σ⁻¹ i) < (σ'⁻¹ i) := lt_of_not_ge hNot
    have hZero : (T' : Matrix ι ι F) (σ'⁻¹ i) (σ⁻¹ i) = 0 := hT'_tri hLt
    rw [hZero, mul_zero] at hEq
    have hwNe : (w i : F) ≠ 0 := (w i).ne_zero
    exact hwNe hEq
  have hOther :
      ((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F).val *
        (monomialMatrixHom F ι ⟨w', σ'⟩ : Matrix ι ι F) =
        (monomialMatrixHom F ι ⟨w, σ⟩ : Matrix ι ι F) *
          ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F).val := by
    have hSym : (L' : GL ι F) * monomialMatrixHom F ι ⟨w', σ'⟩ * (R' : GL ι F) =
        (L : GL ι F) * monomialMatrixHom F ι ⟨w, σ⟩ * (R : GL ι F) := h.symm
    have hGL : ((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) *
        monomialMatrixHom F ι ⟨w', σ'⟩ =
        monomialMatrixHom F ι ⟨w, σ⟩ *
          ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F) := by
      calc ((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) *
            monomialMatrixHom F ι ⟨w', σ'⟩
          = (L : GL ι F)⁻¹ * (L' * monomialMatrixHom F ι ⟨w', σ'⟩ * R') * R'⁻¹ := by
            simp [mul_assoc]
        _ = (L : GL ι F)⁻¹ * (L * monomialMatrixHom F ι ⟨w, σ⟩ * R) * R'⁻¹ := by
            rw [hSym]
        _ = monomialMatrixHom F ι ⟨w, σ⟩ * ((R : GL ι F) * (R' : GL ι F)⁻¹) := by
            simp [mul_assoc]
    calc (((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F).val : Matrix ι ι F) *
          (monomialMatrixHom F ι ⟨w', σ'⟩ : Matrix ι ι F)
        = (((L : GL ι F)⁻¹ * (L' : GL ι F) * monomialMatrixHom F ι ⟨w', σ'⟩ :
            GL ι F).val : Matrix ι ι F) := by simp
      _ = ((monomialMatrixHom F ι ⟨w, σ⟩ *
            ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F) : GL ι F).val :
            Matrix ι ι F) := by rw [hGL]
      _ = (monomialMatrixHom F ι ⟨w, σ⟩ : Matrix ι ι F) *
          ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F).val := by simp
  have hLe2 : ∀ i : ι, σ⁻¹ i ≤ σ'⁻¹ i := by
    intro i
    let T2 : GL ι F := (L : GL ι F)⁻¹ * (L' : GL ι F)
    let S2 : GL ι F := (R : GL ι F) * (R' : GL ι F)⁻¹
    have hT2mem : T2 ∈ upperElementarySubgroup ι F := by
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ L.2) L'.2
    have hS2mem : S2 ∈ upperElementarySubgroup ι F := by
      exact Subgroup.mul_mem _ R.2 (Subgroup.inv_mem _ R'.2)
    have hS2_tri : IsUpperTriangular (S2 : Matrix ι ι F) :=
      upperElementary_isUpperTriangular_commRing ⟨S2, hS2mem⟩
    have hT2_diag : ∀ k, (T2 : Matrix ι ι F) k k = 1 :=
      fun k => upperElementary_diag_one_commRing ⟨T2, hT2mem⟩ k
    have hEq := congrFun (congrFun hOther i) (σ'⁻¹ i)
    rw [upper_mul_monomial_apply (T2 : Matrix ι ι F) w' σ' i (σ'⁻¹ i),
      monomial_mul_upper_apply w σ (S2 : Matrix ι ι F) i (σ'⁻¹ i)] at hEq
    have hLeft : (T2 : Matrix ι ι F) i (σ' (σ'⁻¹ i)) * (w' (σ' (σ'⁻¹ i)) : F) =
        (w' i : F) := by
      have : σ' (σ'⁻¹ i) = i := Equiv.apply_symm_apply σ' i
      rw [this, hT2_diag i, one_mul]
    rw [hLeft] at hEq
    by_contra hNot
    have hLt : (σ'⁻¹ i) < (σ⁻¹ i) := lt_of_not_ge hNot
    have hZero : (S2 : Matrix ι ι F) (σ⁻¹ i) (σ'⁻¹ i) = 0 := hS2_tri hLt
    rw [hZero, mul_zero] at hEq
    have hwNe : (w' i : F) ≠ 0 := (w' i).ne_zero
    exact hwNe hEq
  have hEqInv : σ'⁻¹ = σ⁻¹ := by
    ext i
    exact le_antisymm (hLe1 i) (hLe2 i)
  exact hEqInv.symm

/-- Over a field on a finite linearly ordered index set, suppose two
products with monomial middle factors are equal and all four outer factors
are upper-elementary. If their inverse permutations agree, then their unit
weight functions agree. -/
theorem bruhatCell_weight_unique
    (L R L' R' : upperElementarySubgroup ι F)
    (w : ι → Fˣ) (σ : Equiv.Perm ι) (w' : ι → Fˣ) (σ' : Equiv.Perm ι)
    (h : (L : GL ι F) * monomialMatrixHom F ι ⟨w, σ⟩ * (R : GL ι F) =
      (L' : GL ι F) * monomialMatrixHom F ι ⟨w', σ'⟩ * (R' : GL ι F))
    (hPermInv : σ⁻¹ = σ'⁻¹) :
    w = w' := by
  classical
  let T : GL ι F := (L' : GL ι F)⁻¹ * (L : GL ι F)
  let T' : GL ι F := (R' : GL ι F) * (R : GL ι F)⁻¹
  have hTmem : T ∈ upperElementarySubgroup ι F := by
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ L'.2) L.2
  have hT'mem : T' ∈ upperElementarySubgroup ι F := by
    exact Subgroup.mul_mem _ R'.2 (Subgroup.inv_mem _ R.2)
  have hT_diag : ∀ i, (T : Matrix ι ι F) i i = 1 :=
    fun i => upperElementary_diag_one_commRing ⟨T, hTmem⟩ i
  have hT'_diag : ∀ i, (T' : Matrix ι ι F) i i = 1 :=
    fun i => upperElementary_diag_one_commRing ⟨T', hT'mem⟩ i
  have hMat : (T : Matrix ι ι F) * (monomialMatrixHom F ι ⟨w, σ⟩ : Matrix ι ι F) =
      (monomialMatrixHom F ι ⟨w', σ'⟩ : Matrix ι ι F) * (T' : Matrix ι ι F) :=
    bruhatCell_rearrange (L : GL ι F) (R : GL ι F) (L' : GL ι F) (R' : GL ι F)
      w σ w' σ' h
  funext i
  have hEq := congrFun (congrFun hMat i) (σ⁻¹ i)
  rw [upper_mul_monomial_apply (T : Matrix ι ι F) w σ i (σ⁻¹ i),
    monomial_mul_upper_apply w' σ' (T' : Matrix ι ι F) i (σ⁻¹ i)] at hEq
  have hLeft : (T : Matrix ι ι F) i (σ (σ⁻¹ i)) * (w (σ (σ⁻¹ i)) : F) =
      (w i : F) := by
    have : σ (σ⁻¹ i) = i := Equiv.apply_symm_apply σ i
    rw [this, hT_diag i, one_mul]
  rw [hLeft] at hEq
  have hPermEq : σ'⁻¹ i = σ⁻¹ i := by
    exact congrArg (fun p : Equiv.Perm ι => p i) hPermInv.symm
  rw [← hPermEq] at hEq
  have hT'_diag_i : (T' : Matrix ι ι F) (σ'⁻¹ i) (σ'⁻¹ i) = 1 :=
    hT'_diag (σ'⁻¹ i)
  rw [hT'_diag_i, mul_one] at hEq
  exact Units.ext hEq

/-- Over a field on a finite linearly ordered index set, two equal
products with upper-elementary left and right factors have equal monomial
middle factors. -/
theorem bruhatCell_monomial_unique
    (L R L' R' : upperElementarySubgroup ι F)
    (w : ι → Fˣ) (σ : Equiv.Perm ι) (w' : ι → Fˣ) (σ' : Equiv.Perm ι)
    (h : (L : GL ι F) * monomialMatrixHom F ι ⟨w, σ⟩ * (R : GL ι F) =
      (L' : GL ι F) * monomialMatrixHom F ι ⟨w', σ'⟩ * (R' : GL ι F)) :
    monomialMatrixHom F ι ⟨w, σ⟩ = monomialMatrixHom F ι ⟨w', σ'⟩ := by
  have hPermInv := bruhatCell_perm_inv_unique L R L' R' w σ w' σ' h
  have hPerm : σ = σ' := by
    calc σ = σ⁻¹⁻¹ := by simp
      _ = σ'⁻¹⁻¹ := by rw [hPermInv]
      _ = σ' := by simp
  have hW := bruhatCell_weight_unique L R L' R' w σ w' σ' h hPermInv
  rw [hW, hPerm]

theorem bruhatCell_unique_full
    (L R L' R' : upperElementarySubgroup ι F)
    (w : ι → Fˣ) (σ : Equiv.Perm ι) (w' : ι → Fˣ) (σ' : Equiv.Perm ι)
    (h : (L : GL ι F) * monomialMatrixHom F ι ⟨w, σ⟩ * (R : GL ι F) =
      (L' : GL ι F) * monomialMatrixHom F ι ⟨w', σ'⟩ * (R' : GL ι F)) :
    w = w' ∧ σ = σ' ∧
      monomialMatrixHom F ι ⟨w, σ⟩ = monomialMatrixHom F ι ⟨w', σ'⟩ := by
  have hPermInv := bruhatCell_perm_inv_unique L R L' R' w σ w' σ' h
  have hPerm : σ = σ' := by
    calc σ = σ⁻¹⁻¹ := by simp
      _ = σ'⁻¹⁻¹ := by rw [hPermInv]
      _ = σ' := by simp
  have hW := bruhatCell_weight_unique L R L' R' w σ w' σ' h hPermInv
  exact ⟨hW, hPerm, bruhatCell_monomial_unique L R L' R' w σ w' σ' h⟩

end BruhatPermWeight

end BruhatCellUniqueness

end Matrix.GeneralLinearGroup

namespace Matrix.GeneralLinearGroup

section HeterogeneousUniqueness

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {F : Type*} [Field F]

open Matrix.GeneralLinearEquiv

theorem heterogeneousBruhatDecomposition_middle_unique
    (e : GeneralLinearEquiv ι ι F)
    (d₁ d₂ : HeterogeneousBruhatDecomposition e) :
    d₁.weights = d₂.weights ∧ d₁.perm = d₂.perm := by
  classical
  have hVal1 := d₁.val_eq
  have hVal2 := d₂.val_eq
  have hEqMat : (d₁.left : GL ι F).val * (monomialEquiv d₁.weights d₁.perm).val *
      (d₁.right : GL ι F).val =
      (d₂.left : GL ι F).val * (monomialEquiv d₂.weights d₂.perm).val *
        (d₂.right : GL ι F).val := by rw [← hVal1, ← hVal2]
  have hMono1 :
      (monomialEquiv d₁.weights d₁.perm).val =
        (monomialMatrixHom F ι ⟨d₁.weights, d₁.perm⟩ : Matrix ι ι F) :=
    monomialEquiv_eq_monomialMatrixHom d₁.weights d₁.perm
  have hMono2 :
      (monomialEquiv d₂.weights d₂.perm).val =
        (monomialMatrixHom F ι ⟨d₂.weights, d₂.perm⟩ : Matrix ι ι F) :=
    monomialEquiv_eq_monomialMatrixHom d₂.weights d₂.perm
  have hGL : (d₁.left : GL ι F) * monomialMatrixHom F ι ⟨d₁.weights, d₁.perm⟩ *
      (d₁.right : GL ι F) =
      (d₂.left : GL ι F) * monomialMatrixHom F ι ⟨d₂.weights, d₂.perm⟩ *
        (d₂.right : GL ι F) := by
    apply Units.ext
    calc ((d₁.left : GL ι F) * monomialMatrixHom F ι ⟨d₁.weights, d₁.perm⟩ *
        (d₁.right : GL ι F) : GL ι F).val
        = (d₁.left : GL ι F).val * (monomialMatrixHom F ι ⟨d₁.weights, d₁.perm⟩ : Matrix ι ι F) *
          (d₁.right : GL ι F).val := by simp
      _ = (d₁.left : GL ι F).val * (monomialEquiv d₁.weights d₁.perm).val *
          (d₁.right : GL ι F).val := by rw [← hMono1]
      _ = (d₂.left : GL ι F).val * (monomialEquiv d₂.weights d₂.perm).val *
          (d₂.right : GL ι F).val := hEqMat
      _ = (d₂.left : GL ι F).val *
          (monomialMatrixHom F ι ⟨d₂.weights, d₂.perm⟩ : Matrix ι ι F) *
          (d₂.right : GL ι F).val := by rw [hMono2]
      _ = ((d₂.left : GL ι F) * monomialMatrixHom F ι ⟨d₂.weights, d₂.perm⟩ *
          (d₂.right : GL ι F) : GL ι F).val := by simp
  have hFull := bruhatCell_unique_full d₁.left d₁.right d₂.left d₂.right
    d₁.weights d₁.perm d₂.weights d₂.perm hGL
  exact ⟨hFull.1, hFull.2.1⟩

end HeterogeneousUniqueness

section SLUniqueness

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {F : Type*} [Field F]

open Matrix.SpecialLinearGroup

theorem specialLinearBruhatDecomposition_middle_unique
    (g : Matrix.SpecialLinearGroup ι F)
    (d₁ d₂ : SpecialLinearBruhatDecomposition g) :
    d₁.middle = d₂.middle := by
  classical
  have hGL1 := d₁.factorizationGL
  have hGL2 := d₂.factorizationGL
  have hEq : (d₁.left : GL ι F) *
      monomialMatrixHom F ι (d₁.middle : MonomialBase Fˣ ι) *
        (d₁.right : GL ι F) =
      (d₂.left : GL ι F) *
        monomialMatrixHom F ι (d₂.middle : MonomialBase Fˣ ι) *
          (d₂.right : GL ι F) := by rw [← hGL1, ← hGL2]
  have hPermInv := bruhatCell_perm_inv_unique d₁.left d₁.right d₂.left d₂.right
    d₁.middle.1.left d₁.middle.1.right d₂.middle.1.left d₂.middle.1.right hEq
  have hW := bruhatCell_weight_unique d₁.left d₁.right d₂.left d₂.right
    d₁.middle.1.left d₁.middle.1.right d₂.middle.1.left d₂.middle.1.right hEq hPermInv
  have hBase : (d₁.middle : MonomialBase Fˣ ι) = (d₂.middle : MonomialBase Fˣ ι) := by
    have hPerm : (d₁.middle : MonomialBase Fˣ ι).right =
        (d₂.middle : MonomialBase Fˣ ι).right := by
      calc (d₁.middle : MonomialBase Fˣ ι).right
          = (d₁.middle : MonomialBase Fˣ ι).right⁻¹⁻¹ := by simp
        _ = (d₂.middle : MonomialBase Fˣ ι).right⁻¹⁻¹ := by rw [hPermInv]
        _ = (d₂.middle : MonomialBase Fˣ ι).right := by simp
    exact SemidirectProduct.ext hW hPerm
  exact Subtype.ext hBase

theorem bruhatMiddle_eq_of_decomposition
    (g : Matrix.SpecialLinearGroup ι F)
    (d : SpecialLinearBruhatDecomposition g) :
    bruhatMiddle g = d.middle := by
  let hCanon := specialLinearBruhatDecomposition g
  have hUniq := specialLinearBruhatDecomposition_middle_unique g hCanon d
  calc bruhatMiddle g = hCanon.middle := rfl
    _ = d.middle := hUniq

theorem bruhatMiddle_factorization_elim
    (g : Matrix.SpecialLinearGroup ι F)
    (left : upperElementarySubgroup ι F) (middle : MonomialSL F ι)
    (right : upperElementarySubgroup ι F)
    (hSL : g = UpperElementary.toSLHom left * monomialSLHom F ι middle *
      UpperElementary.toSLHom right) :
    bruhatMiddle g = middle := by
  have hGL : (Matrix.SpecialLinearGroup.toGL g : GL ι F) =
      (left : GL ι F) * monomialMatrixHom F ι (middle : MonomialBase Fˣ ι) *
        (right : GL ι F) := by
    have hToGL : Matrix.SpecialLinearGroup.toGL g =
        Matrix.SpecialLinearGroup.toGL
          (UpperElementary.toSLHom left * monomialSLHom F ι middle *
            UpperElementary.toSLHom right) := by rw [← hSL]
    simp only [map_mul, UpperElementary.toGL_toSLHom, monomialSLHom_toGL] at hToGL
    exact hToGL
  let d : SpecialLinearBruhatDecomposition g :=
    { left := left
      middle := middle
      right := right
      factorizationGL := hGL
      factorizationSL := hSL }
  exact bruhatMiddle_eq_of_decomposition g d

theorem bruhatMiddle_monomialSLHom (x : MonomialSL F ι) :
    bruhatMiddle (monomialSLHom F ι x) = x := by
  have hSL : monomialSLHom F ι x =
      UpperElementary.toSLHom (1 : upperElementarySubgroup ι F) *
        monomialSLHom F ι x *
        UpperElementary.toSLHom (1 : upperElementarySubgroup ι F) := by simp
  exact bruhatMiddle_factorization_elim
    (monomialSLHom F ι x) 1 x 1 hSL

end SLUniqueness

section RetractionNaturality

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {F : Type*} [Field F]
variable {K : Type*} [Field K]
variable {L : Type*} [Field L]

theorem bruhatMiddle_map (f : F →+* K) (g : Matrix.SpecialLinearGroup ι F) :
    bruhatMiddle (Matrix.SpecialLinearGroup.map f g) =
      monomialSLMap F K ι f (bruhatMiddle g) := by
  classical
  let d := specialLinearBruhatDecomposition g
  have hMid : d.middle = bruhatMiddle g := rfl
  let dMap := d.map f
  have hMapMid : dMap.middle = monomialSLMap F K ι f d.middle := rfl
  have hEq := bruhatMiddle_eq_of_decomposition (Matrix.SpecialLinearGroup.map f g) dMap
  calc bruhatMiddle (Matrix.SpecialLinearGroup.map f g)
      = dMap.middle := hEq
    _ = monomialSLMap F K ι f d.middle := hMapMid
    _ = monomialSLMap F K ι f (bruhatMiddle g) := by rw [hMid]

theorem bruhatMiddle_map_id (g : Matrix.SpecialLinearGroup ι F) :
    bruhatMiddle (Matrix.SpecialLinearGroup.map (RingHom.id F) g) =
      bruhatMiddle g := by
  rw [bruhatMiddle_map]
  have hId := monomialSLMap_id F ι
  have h : monomialSLMap F F ι (RingHom.id F) (bruhatMiddle g) = bruhatMiddle g := by
    calc monomialSLMap F F ι (RingHom.id F) (bruhatMiddle g)
        = (MonoidHom.id (MonomialSL F ι)) (bruhatMiddle g) := by rw [hId]
      _ = bruhatMiddle g := rfl
  rw [h]

theorem bruhatMiddle_map_comp (f : F →+* K) (g : K →+* L)
    (x : Matrix.SpecialLinearGroup ι F) :
    bruhatMiddle (Matrix.SpecialLinearGroup.map (g.comp f) x) =
      monomialSLMap K L ι g
        (monomialSLMap F K ι f (bruhatMiddle x)) := by
  rw [bruhatMiddle_map]
  have hComp := monomialSLMap_comp F K L ι f g
  calc monomialSLMap F L ι (g.comp f) (bruhatMiddle x)
      = ((monomialSLMap K L ι g).comp (monomialSLMap F K ι f)) (bruhatMiddle x) := by
          rw [hComp]
    _ = monomialSLMap K L ι g (monomialSLMap F K ι f (bruhatMiddle x)) := rfl

end RetractionNaturality

end Matrix.GeneralLinearGroup
