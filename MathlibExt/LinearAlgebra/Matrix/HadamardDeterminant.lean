/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Tactic.Ring

@[expose]
public section

open Finset Matrix BigOperators
open InnerProductSpace
open scoped InnerProductSpace

namespace MathlibExt.LinearAlgebra.Matrix.HadamardDeterminant

private theorem det_updateRow_sub_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) (s : Finset (Fin n)) (hi : i ∉ s) (a : Fin n → ℂ) :
    (M.updateRow i (M i - ∑ k ∈ s, a k • M k)).det = M.det := by
  induction s using Finset.induction with
  | empty =>
    have hself : M.updateRow i (M i) = M := by
      apply Matrix.ext
      intro r c
      by_cases hr : r = i
      · subst hr
        simp [Matrix.updateRow_self]
      · simp [Matrix.updateRow_ne, hr]
    simp
  | insert k s' hk ih =>
    have hik : i ≠ k := by
      intro h
      subst h
      exact hi (Finset.mem_insert_self i s')
    have hi' : i ∉ s' := fun h => hi (Finset.mem_insert_of_mem h)
    have ih' : (M.updateRow i (M i - ∑ j ∈ s', a j • M j)).det = M.det := ih hi'
    rw [Finset.sum_insert hk]
    have hsub : M i - (a k • M k + ∑ j ∈ s', a j • M j)
        = (M i - ∑ j ∈ s', a j • M j) + (-a k) • M k := by
      apply funext
      intro j
      simp [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      ring
    rw [hsub]
    set M' : Matrix (Fin n) (Fin n) ℂ := M.updateRow i (M i - ∑ j ∈ s', a j • M j) with hM'
    have hik' : k ≠ i := fun h => hik h.symm
    have hMk : M' k = M k := by simp [hM', Matrix.updateRow_ne, hik']
    have hMi : M' i = M i - ∑ j ∈ s', a j • M j := by
      simp [hM', Matrix.updateRow_self]
    have heq : M.updateRow i ((M i - ∑ j ∈ s', a j • M j) + (-a k) • M k)
        = M'.updateRow i (M' i + (-a k) • M' k) := by
      rw [hMi, hMk]
      apply Matrix.ext
      intro r c
      by_cases hr : r = i
      · subst hr
        simp [Matrix.updateRow_self]
      · simp [hM', Matrix.updateRow_ne, hr]
    rw [heq]
    have hdet : (M'.updateRow i (M' i + (-a k) • M' k)).det = M'.det := by
      rw [Matrix.det_updateRow_add, Matrix.det_updateRow_smul]
      have hzero : (M'.updateRow i (M' k)).det = 0 :=
        Matrix.det_updateRow_eq_zero hik'
      rw [hzero, Matrix.updateRow_eq_self]
      simp
    rw [hdet, hM']
    exact ih'

/--
**Hadamard's determinant inequality.** For every natural number $n$ and every $n \times n$
complex matrix $A = (a_{ij})$,

$$|\det A| \le \prod_{i=1}^{n} \Big( \sum_{j=1}^{n} |a_{ij}|^2 \Big)^{1/2},$$

that is, the absolute value of the determinant of $A$ is at most the product of the Euclidean
lengths of its rows.

Source: J. Hadamard, Résolution d'une question relative aux déterminants,
Bulletin des Sciences Mathématiques 17 (1893), 240–246.
-/
public theorem hadamard_determinant_inequality {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ ≤ ∏ i : Fin n, Real.sqrt (∑ j : Fin n, Complex.normSq (A i j)) := by
  set v : Fin n → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 (fun j => A i j) with hv
  set e : Fin n → EuclideanSpace ℂ (Fin n) := gramSchmidt ℂ v with he
  set E : Matrix (Fin n) (Fin n) ℂ := fun i j => e i j with hE
  set B : ℕ → Matrix (Fin n) (Fin n) ℂ := fun m i j => if (i.val < m) then e i j else A i j with hB
  have hv_apply : ∀ i j, v i j = A i j := fun i j => by simp [hv, PiLp.toLp_apply]
  have hE_apply : ∀ i j, E i j = e i j := fun i j => by simp [hE]
  have hB_apply : ∀ m i j, B m i j = (if (i.val < m) then e i j else A i j) :=
    fun m i j => by simp [hB]
  have hB0 : B 0 = A := by
    apply Matrix.ext
    intro i j
    have h : ¬ (i.val < 0) := by omega
    simp [hB_apply, h]
  have hBn : B n = E := by
    apply Matrix.ext
    intro i j
    have h : i.val < n := i.isLt
    simp [hB_apply, hE_apply, h]
  have hBdet : ∀ m, m ≤ n → (B m).det = A.det := by
    intro m
    induction m with
    | zero =>
      intro hm
      rw [hB0]
    | succ m ih =>
      intro hm
      have hm' : m ≤ n := by omega
      have ih' : (B m).det = A.det := ih hm'
      have hmn : m < n := by omega
      set j : Fin n := ⟨m, hmn⟩ with hj
      have hj_val : j.val = m := rfl
      have hBu : B (m + 1) = (B m).updateRow j (e j).ofLp := by
        apply Matrix.ext
        intro r c
        by_cases hr : r = j
        · subst hr
          have h1 : (j.val < m + 1) := by rw [hj_val]; omega
          have hL : B (m + 1) j c = e j c := by simp [hB_apply, h1]
          have hR : ((B m).updateRow j (e j).ofLp) j c = (e j).ofLp c := by
            simp [Matrix.updateRow_self]
          have hOf : (e j).ofLp c = e j c := rfl
          rw [hL, hR, hOf]
        · have hrval : r.val ≠ m := by
            intro hcon
            apply hr
            apply Fin.ext
            rw [hj_val]
            exact hcon
          have hiff : (r.val < m + 1) ↔ (r.val < m) := by omega
          simp [hB_apply, hiff, Matrix.updateRow_ne, hr]
      have hBj : (B m) j = (v j).ofLp := by
        apply funext
        intro c
        have h : ¬ (j.val < m) := by rw [hj_val]; omega
        have h1 : (B m) j c = A j c := by simp [hB_apply, h]
        have hOf : (v j).ofLp c = v j c := rfl
        have hvj : v j c = A j c := hv_apply j c
        rw [h1, hOf, hvj]
      have hBk : ∀ k, k < j → (B m) k = (e k).ofLp := by
        intro k hk
        have hkm : k.val < m := by
          have h1 : k.val < j.val := hk
          rw [hj_val] at h1
          exact h1
        apply funext
        intro c
        have h1 : (B m) k c = e k c := by simp [hB_apply, hkm]
        have hOf : (e k).ofLp c = e k c := rfl
        rw [h1, hOf]
      set s : Finset (Fin n) := Finset.Iio j with hs
      have hdef0 : e j = v j - ∑ k ∈ s, (Submodule.span ℂ {e k}).starProjection (v j) := by
        rw [he, hs]
        exact gramSchmidt_def ℂ v j
      have hmem : ∀ k, ∃ a : ℂ, a • e k = (Submodule.span ℂ {e k}).starProjection (v j) := by
        intro k
        have hproj_mem :
          (Submodule.span ℂ {e k}).starProjection (v j) ∈ Submodule.span ℂ {e k} := by
          apply Submodule.starProjection_apply_mem
        exact Submodule.mem_span_singleton.mp hproj_mem
      choose a ha using hmem
      have hdef : e j = v j - ∑ k ∈ s, a k • e k := by
        rw [hdef0]
        congr 1
        exact Finset.sum_congr rfl (fun k _ => (ha k).symm)
      have hsum : (∑ k ∈ s, a k • e k).ofLp = ∑ k ∈ s, a k • (B m) k := by
        rw [WithLp.ofLp_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have hkj : k < j := by simpa [hs] using hk
        have hke : (B m) k = (e k).ofLp := hBk k hkj
        have hsmul : (a k • e k).ofLp = a k • (e k).ofLp := rfl
        rw [hsmul, hke]
      have hj_nmem : j ∉ s := by simp [hs]
      have hej : (e j).ofLp = (B m) j - ∑ k ∈ s, a k • (B m) k := by
        have h := congrArg WithLp.ofLp hdef
        rwa [WithLp.ofLp_sub, ←hBj, hsum] at h
      rw [hBu, hej]
      have hdet : ((B m).updateRow j ((B m) j - ∑ k ∈ s, a k • (B m) k)).det
          = (B m).det := det_updateRow_sub_sum (B m) j s hj_nmem a
      rw [hdet]
      exact ih'
  have hdetE : E.det = A.det := by
    have h : (B n).det = A.det := hBdet n (le_refl n)
    rw [hBn] at h
    exact h
  have hmul_inner : ∀ i j, (E * Matrix.conjTranspose E) i j = ⟪e j, e i⟫_ℂ := by
    intro i j
    have h1 : (E * Matrix.conjTranspose E) i j = ∑ k, e i k * star (e j k) := by
      simp [hE_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    have hej : e j = WithLp.toLp 2 (fun k => e j k) := by
      ext k
      simp
    have hei : e i = WithLp.toLp 2 (fun k => e i k) := by
      ext k
      simp
    have h2 : ⟪e j, e i⟫_ℂ
        = dotProduct (fun k => e i k) (star (fun k => e j k)) := by
      rw [hej, hei]
      exact EuclideanSpace.inner_toLp_toLp (fun k => e j k) (fun k => e i k)
    rw [h1, h2]
    simp only [dotProduct, Pi.star_apply]
  have hdiag : E * Matrix.conjTranspose E
      = Matrix.diagonal (fun i => ((‖e i‖^2 : ℝ) : ℂ)) := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst hij
      have hpow : ((‖e i‖^2 : ℝ) : ℂ) = (‖e i‖ : ℂ)^2 := by
        rw [pow_two, pow_two, Complex.ofReal_mul]
      have hself : ⟪e i, e i⟫_ℂ = ((‖e i‖^2 : ℝ) : ℂ) := by
        rw [hpow]
        exact inner_self_eq_norm_sq_to_K _
      simp [hmul_inner]
    · have hne : j ≠ i := fun h => hij h.symm
      have horth : ⟪e j, e i⟫_ℂ = 0 := gramSchmidt_orthogonal ℂ v hne
      simp [hmul_inner, horth, hij]
  have hdet_diag : (Matrix.diagonal (fun i => ((‖e i‖^2 : ℝ) : ℂ))).det
      = ∏ i, ((‖e i‖^2 : ℝ) : ℂ) := Matrix.det_diagonal
  have hdet_mul : (E * Matrix.conjTranspose E).det
      = E.det * (Matrix.conjTranspose E).det := Matrix.det_mul _ _
  have hdet_conj : (Matrix.conjTranspose E).det = star E.det :=
    Matrix.det_conjTranspose _
  have hnormE : (‖E.det‖^2 : ℝ) = ∏ i, (‖e i‖^2 : ℝ) := by
    have h1 : ‖(E * Matrix.conjTranspose E).det‖
        = ‖E.det‖ * ‖(Matrix.conjTranspose E).det‖ := by
      rw [hdet_mul]
      exact norm_mul _ _
    have h2 : ‖(Matrix.conjTranspose E).det‖ = ‖E.det‖ := by
      rw [hdet_conj, norm_star]
    have h3 : ‖(E * Matrix.conjTranspose E).det‖ = ∏ i, (‖e i‖^2 : ℝ) := by
      rw [hdiag, hdet_diag, norm_prod]
      apply Finset.prod_congr rfl
      intro i _
      exact (RCLike.norm_ofReal _).trans (abs_of_nonneg (sq_nonneg _))
    rw [h2] at h1
    have hsq : ‖E.det‖ * ‖E.det‖ = (‖E.det‖^2 : ℝ) := by ring
    rw [hsq] at h1
    rw [h3] at h1
    exact h1.symm
  have hnormA : (‖A.det‖^2 : ℝ) = ∏ i, (‖e i‖^2 : ℝ) := by
    rw [←hdetE]
    exact hnormE
  have hle_sq : ∀ i, (‖e i‖^2 : ℝ) ≤ ‖v i‖^2 := by
    intro i
    have hdef0 : e i = v i - ∑ k ∈ Finset.Iio i, (Submodule.span ℂ {e k}).starProjection (v i) := by
      rw [he]
      exact gramSchmidt_def ℂ v i
    have hmem : ∀ k, ∃ a : ℂ, a • e k = (Submodule.span ℂ {e k}).starProjection (v i) := by
      intro k
      have hproj_mem : (Submodule.span ℂ {e k}).starProjection (v i) ∈ Submodule.span ℂ {e k} := by
        apply Submodule.starProjection_apply_mem
      exact Submodule.mem_span_singleton.mp hproj_mem
    choose a ha using hmem
    have hdef : e i = v i - ∑ k ∈ Finset.Iio i, a k • e k := by
      rw [hdef0]
      congr 1
      exact Finset.sum_congr rfl (fun k _ => (ha k).symm)
    have hsub : v i - e i = ∑ k ∈ Finset.Iio i, a k • e k := by simp [hdef]
    have horth : ⟪e i, v i - e i⟫_ℂ = 0 := by
      rw [hsub, inner_sum]
      apply Finset.sum_eq_zero
      intro k hk
      have hki : k < i := by simpa using hk
      have hne : i ≠ k := by
        intro h
        subst h
        exact lt_irrefl _ hki
      have hor : ⟪e i, e k⟫_ℂ = 0 := gramSchmidt_orthogonal ℂ v hne
      rw [inner_smul_right, hor, mul_zero]
    have hadd : v i = e i + (v i - e i) := by simp
    have hpy : (‖v i‖^2 : ℝ) = (‖e i‖^2 : ℝ) + (‖v i - e i‖^2 : ℝ) := by
      have h0 : ‖e i + (v i - e i)‖ * ‖e i + (v i - e i)‖
          = ‖e i‖ * ‖e i‖ + ‖v i - e i‖ * ‖v i - e i‖ :=
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (e i) (v i - e i) horth
      have h : (‖e i + (v i - e i)‖^2 : ℝ)
          = (‖e i‖^2 : ℝ) + (‖v i - e i‖^2 : ℝ) := by
        simpa [pow_two] using h0
      rw [←hadd] at h
      exact h
    rw [hpy]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hnorm_v : ∀ i, (‖v i‖^2 : ℝ) = ∑ j, Complex.normSq (A i j) := by
    intro i
    have h1 : (‖v i‖^2 : ℝ) = ∑ j, (‖v i j‖^2 : ℝ) := EuclideanSpace.norm_sq_eq _
    have h2 : ∀ j, (‖v i j‖^2 : ℝ) = Complex.normSq (A i j) := by
      intro j
      have hvj : v i j = A i j := by simp [hv, PiLp.toLp_apply]
      rw [hvj, Complex.normSq_eq_norm_sq]
    rw [h1]
    exact Finset.sum_congr rfl (fun x _ => h2 x)
  have hprod_le : ∏ i, (‖e i‖^2 : ℝ) ≤ ∏ i, ∑ j, Complex.normSq (A i j) := by
    have h1 : ∏ i : Fin n, (‖e i‖^2 : ℝ) ≤ ∏ i : Fin n, (‖v i‖^2 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact sq_nonneg _
      · intro i _
        exact hle_sq i
    have h2 : ∏ i : Fin n, (‖v i‖^2 : ℝ) = ∏ i, ∑ j, Complex.normSq (A i j) :=
      Finset.prod_congr rfl (fun i _ => hnorm_v i)
    rw [h2] at h1
    exact h1
  have hle : (‖A.det‖^2 : ℝ) ≤ ∏ i, ∑ j, Complex.normSq (A i j) := by
    rw [hnormA]
    exact hprod_le
  have hy_nn : (0 : ℝ) ≤ ∏ i : Fin n, Real.sqrt (∑ j, Complex.normSq (A i j)) := by
    apply Finset.prod_nonneg
    intro i _
    exact Real.sqrt_nonneg _
  have hx_nn : (0 : ℝ) ≤ ‖A.det‖ := norm_nonneg _
  have hsq_y : (∏ i : Fin n, Real.sqrt (∑ j, Complex.normSq (A i j)))^2
      = ∏ i, ∑ j, Complex.normSq (A i j) := by
    have h : ∀ i : Fin n, (Real.sqrt (∑ j, Complex.normSq (A i j)))^2
        = ∑ j, Complex.normSq (A i j) := by
      intro i
      exact Real.sq_sqrt (Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _))
    have hprod : (∏ i : Fin n, Real.sqrt (∑ j, Complex.normSq (A i j)))^2
        = ∏ i : Fin n, (Real.sqrt (∑ j, Complex.normSq (A i j)))^2 := by
      rw [pow_two, ←Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => (pow_two _).symm)
    rw [hprod]
    exact Finset.prod_congr rfl (fun i _ => h i)
  have hx_eq : ‖A.det‖ = Real.sqrt (‖A.det‖^2) := (Real.sqrt_sq hx_nn).symm
  have hy_eq : (∏ i : Fin n, Real.sqrt (∑ j, Complex.normSq (A i j)))
      = Real.sqrt ((∏ i : Fin n, Real.sqrt (∑ j, Complex.normSq (A i j)))^2) :=
    (Real.sqrt_sq hy_nn).symm
  rw [hx_eq, hy_eq, hsq_y]
  exact Real.sqrt_le_sqrt hle

end MathlibExt.LinearAlgebra.Matrix.HadamardDeterminant

end
