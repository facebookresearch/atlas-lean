/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QMA.ThresholdOperator

/-!
# Tests: Threshold operator: spectral identities
-/

@[expose] public section

open scoped BigOperators Matrix
namespace CslibTest.Complexity.Classes.QMA

set_option autoImplicit false

open Cslib.Complexity.Classes.QMA

#print axioms star_dotProduct_thresholdOp_mulVec
#print axioms re_star_dotProduct_thresholdOp_mulVec_le
#print axioms star_dotProduct_thresholdOp_mulVec_blockProd_const

/-- Boundary tail weights: all-ones parameters give weight `1` below the count. -/
theorem tailWeight_one_of_le (k : ℕ) {T : ℝ} (hT : T ≤ k) :
    tailWeight (fun _ : Fin k => (1 : ℝ)) T = 1 := by
  have h1 : ∀ b ∈ Finset.univ.filter (fun b : Fin k → Bool => T ≤ acceptCount b),
      b ≠ (fun _ : Fin k => true) → (∏ i, (if b i then (1 : ℝ) else 1 - 1)) = 0 := by
    intro b _ hbne
    have hex : ∃ i, b i = false := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hbne
      have hi' : b i = false := by
        cases h : b i <;> simp_all
      exact ⟨i, hi'⟩
    obtain ⟨i, hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]
  have h2 : (fun _ : Fin k => true)
      ∉ Finset.univ.filter (fun b : Fin k → Bool => T ≤ acceptCount b) →
      (∏ i, (if (fun _ : Fin k => true) i then (1 : ℝ) else 1 - 1)) = 0 := by
    intro hcon
    have hmem : (fun _ : Fin k => true)
        ∈ Finset.univ.filter (fun b : Fin k → Bool => T ≤ acceptCount b) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hacc : acceptCount (fun _ : Fin k => true) = (k : ℝ) := by
        show (∑ i : Fin k, (if (true : Bool) then (1 : ℝ) else 0)) = (k : ℝ)
        simp
      rw [hacc]
      exact hT
    exact absurd hmem hcon
  have hmain := Finset.sum_eq_single (fun _ : Fin k => true) h1 h2
  show (∑ b ∈ Finset.univ.filter (fun b : Fin k → Bool => T ≤ acceptCount b),
      ∏ i, (if b i then (1 : ℝ) else 1 - 1)) = 1
  rw [hmain]
  simp

/-- Zero parameters give weight `0` above zero. -/
theorem tailWeight_zero_of_pos (k : ℕ) {T : ℝ} (hT : 0 < T) :
    tailWeight (fun _ : Fin k => (0 : ℝ)) T = 0 := by
  show (∑ b ∈ Finset.univ.filter (fun b : Fin k → Bool => T ≤ acceptCount b),
      ∏ i, (if b i then (0 : ℝ) else 1 - 0)) = 0
  apply Finset.sum_eq_zero
  intro b hb
  obtain ⟨_, hbT⟩ := Finset.mem_filter.mp hb
  have hpos : 0 < acceptCount b := lt_of_lt_of_le hT hbT
  have hex : ∃ i, b i = true := by
    by_contra hcon
    push_neg at hcon
    have hacc0 : acceptCount b = 0 := by
      unfold acceptCount
      simp [hcon]
    rw [hacc0] at hpos
    simp at hpos
  obtain ⟨i, hi⟩ := hex
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi]

/-- The explicit diagonal Hermitian matrix `diag(0,1)`. -/
theorem diag01_isHermitian :
    (Matrix.diagonal ![0, 1] :
      Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ).IsHermitian := by
  show (Matrix.diagonal ![0, 1] :
    Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ)ᴴ =
    (Matrix.diagonal ![0, 1] :
      Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem diag01_det : (Matrix.diagonal ![0, 1] :
    Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ).det = 0 := by
  simp [Matrix.det_diagonal, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]

private theorem diag01_trace : (Matrix.diagonal ![0, 1] :
    Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ).trace = 1 := by
  simp [Matrix.trace_diagonal, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]

/-- One eigenvalue of `diag(0,1)` is `0`. -/
private theorem diag01_exists_zero :
    ∃ a : Fin (2 ^ 1), diag01_isHermitian.eigenvalues a = 0 := by
  have hdet := diag01_isHermitian.det_eq_prod_eigenvalues
  rw [diag01_det] at hdet
  obtain ⟨a, _, ha⟩ := Finset.prod_eq_zero_iff.mp hdet.symm
  refine ⟨a, ?_⟩
  have ha' : ((diag01_isHermitian.eigenvalues a : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by
    simpa using ha
  exact Complex.ofReal_inj.mp ha'

/-- One eigenvalue of `diag(0,1)` is `1`. -/
private theorem diag01_exists_one :
    ∃ b : Fin (2 ^ 1), diag01_isHermitian.eigenvalues b = 1 := by
  obtain ⟨a, ha⟩ := diag01_exists_zero
  have htr := diag01_isHermitian.trace_eq_sum_eigenvalues
  rw [diag01_trace] at htr
  have hsplit : (∑ i : Fin (2 ^ 1), ((diag01_isHermitian.eigenvalues i : ℝ) : ℂ))
      = ((diag01_isHermitian.eigenvalues a : ℝ) : ℂ)
        + ∑ i ∈ Finset.univ.erase a, ((diag01_isHermitian.eigenvalues i : ℝ) : ℂ) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ a)).symm
  have hcard : (Finset.univ.erase a).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
      Fintype.card_fin]
    norm_num
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcard
  have h1 : (∑ i ∈ Finset.univ.erase a, ((diag01_isHermitian.eigenvalues i : ℝ) : ℂ))
      = ((diag01_isHermitian.eigenvalues b : ℝ) : ℂ) := by
    rw [hb, Finset.sum_singleton]
  have haC : ((diag01_isHermitian.eigenvalues a : ℝ) : ℂ) = 0 := by
    exact_mod_cast ha
  have hb1 : ((diag01_isHermitian.eigenvalues b : ℝ) : ℂ) = 1 := by
    linear_combination -htr - hsplit - h1 - haC
  exact ⟨b, by exact_mod_cast hb1⟩

/-- Diagonal two-block example: eigen-expectations `1` and `0` at the extreme
basis vectors. -/
theorem thresholdOp_diag01_extreme :
    ∃ j₁ j₀ : Fin 2 → Fin (2 ^ 1),
      thresholdOp 2 (Matrix.diagonal ![0, 1] : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) 1
          *ᵥ productEigenvector diag01_isHermitian j₁
        = productEigenvector diag01_isHermitian j₁
      ∧ thresholdOp 2 (Matrix.diagonal ![0, 1] : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) 1
          *ᵥ productEigenvector diag01_isHermitian j₀ = 0 := by
  obtain ⟨a, ha⟩ := diag01_exists_zero
  obtain ⟨b, hb⟩ := diag01_exists_one
  refine ⟨fun _ => b, fun _ => a, ?_, ?_⟩
  · have hdiag := thresholdOp_mulVec_productEigenvector diag01_isHermitian 1 (fun _ : Fin 2 => b)
    have htail : tailWeight (fun i => diag01_isHermitian.eigenvalues ((fun _ : Fin 2 => b) i)) 1
        = tailWeight (fun _ : Fin 2 => (1 : ℝ)) 1 := by
      congr 1
      funext i
      exact hb
    have hw1 : tailWeight (fun _ : Fin 2 => (1 : ℝ)) 1 = 1 :=
      tailWeight_one_of_le 2 (by norm_num)
    rw [htail, hw1] at hdiag
    simpa using hdiag
  · have hdiag := thresholdOp_mulVec_productEigenvector diag01_isHermitian 1 (fun _ : Fin 2 => a)
    have htail : tailWeight (fun i => diag01_isHermitian.eigenvalues ((fun _ : Fin 2 => a) i)) 1
        = tailWeight (fun _ : Fin 2 => (0 : ℝ)) 1 := by
      congr 1
      funext i
      exact ha
    have hw0 : tailWeight (fun _ : Fin 2 => (0 : ℝ)) 1 = 0 :=
      tailWeight_zero_of_pos 2 (by norm_num)
    rw [htail, hw0] at hdiag
    simpa using hdiag

/-- Entangled equal superposition: expectation is the strict midpoint `1/2` of
the two eigen-tuple tails. -/
theorem thresholdOp_diag01_midpoint :
    ∃ Ψ : Fin (2 ^ (2 * 1)) → ℂ,
      (star Ψ ⬝ᵥ (thresholdOp 2 (Matrix.diagonal ![0, 1] :
        Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) 1 *ᵥ Ψ)).re = 1 / 2 := by
  obtain ⟨a, ha⟩ := diag01_exists_zero
  obtain ⟨b, hb⟩ := diag01_exists_one
  have hne : (fun _ : Fin 2 => b) ≠ (fun _ : Fin 2 => a) := by
    intro hcon
    have hba : b = a := congrFun hcon 0
    rw [hba] at hb
    rw [ha] at hb
    exact zero_ne_one hb
  have hpe : ∀ j : Fin 2 → Fin (2 ^ 1),
      ⇑(productEigenbasis diag01_isHermitian 2 j) = productEigenvector diag01_isHermitian j :=
    fun j => productEigenbasis_apply diag01_isHermitian j
  have horth : ∀ j j' : Fin 2 → Fin (2 ^ 1),
      star (productEigenvector diag01_isHermitian j)
        ⬝ᵥ productEigenvector diag01_isHermitian j'
        = if j = j' then 1 else 0 := by
    intro j j'
    have h := EuclideanSpace.inner_eq_star_dotProduct
      (productEigenbasis diag01_isHermitian 2 j) (productEigenbasis diag01_isHermitian 2 j')
    have h' : inner ℂ (productEigenbasis diag01_isHermitian 2 j)
          (productEigenbasis diag01_isHermitian 2 j')
        = (⇑(productEigenbasis diag01_isHermitian 2 j'))
          ⬝ᵥ star ⇑(productEigenbasis diag01_isHermitian 2 j) := h
    have hite := orthonormal_iff_ite.mp
      (productEigenbasis diag01_isHermitian 2).orthonormal j j'
    rw [hite] at h'
    simp only [productEigenbasis_apply] at h'
    rw [dotProduct_comm] at h'
    exact h'.symm
  refine ⟨(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (productEigenvector diag01_isHermitian (fun _ : Fin 2 => b)
      + productEigenvector diag01_isHermitian (fun _ : Fin 2 => a)), ?_⟩
  set c : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) with hc_def
  have hc_norm : ‖c‖ ^ 2 = 1 / 2 := by
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hpos : (0 : ℝ) < (Real.sqrt 2)⁻¹ := by positivity
    rw [hc_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, inv_pow, hsqrt]
    norm_num
  have ht1 : tailWeight (fun i => diag01_isHermitian.eigenvalues ((fun _ : Fin 2 => b) i)) 1 = 1 := by
    rw [show (fun i => diag01_isHermitian.eigenvalues ((fun _ : Fin 2 => b) i))
        = (fun _ : Fin 2 => (1 : ℝ)) from funext fun i => hb]
    exact tailWeight_one_of_le 2 (by norm_num)
  have ht0 : tailWeight (fun i => diag01_isHermitian.eigenvalues ((fun _ : Fin 2 => a) i)) 1 = 0 := by
    rw [show (fun i => diag01_isHermitian.eigenvalues ((fun _ : Fin 2 => a) i))
        = (fun _ : Fin 2 => (0 : ℝ)) from funext fun i => ha]
    exact tailWeight_zero_of_pos 2 (by norm_num)
  have hc : ∀ j : Fin 2 → Fin (2 ^ 1),
      inner ℂ (productEigenbasis diag01_isHermitian 2 j)
        (WithLp.toLp 2 (c • (productEigenvector diag01_isHermitian (fun _ : Fin 2 => b)
          + productEigenvector diag01_isHermitian (fun _ : Fin 2 => a))))
        = c * ((if j = (fun _ : Fin 2 => b) then (1 : ℂ) else 0)
          + (if j = (fun _ : Fin 2 => a) then (1 : ℂ) else 0)) := by
    intro j
    have h := EuclideanSpace.inner_eq_star_dotProduct (productEigenbasis diag01_isHermitian 2 j)
      (WithLp.toLp 2 (c • (productEigenvector diag01_isHermitian (fun _ : Fin 2 => b)
        + productEigenvector diag01_isHermitian (fun _ : Fin 2 => a))))
    have h' : inner ℂ (productEigenbasis diag01_isHermitian 2 j)
          (WithLp.toLp 2 (c • (productEigenvector diag01_isHermitian (fun _ : Fin 2 => b)
            + productEigenvector diag01_isHermitian (fun _ : Fin 2 => a))))
        = (c • (productEigenvector diag01_isHermitian (fun _ : Fin 2 => b)
            + productEigenvector diag01_isHermitian (fun _ : Fin 2 => a)))
          ⬝ᵥ star ⇑(productEigenbasis diag01_isHermitian 2 j) := h
    rw [h', hpe, dotProduct_comm]
    simp only [dotProduct_smul, dotProduct_add, smul_eq_mul]
    rw [horth j (fun _ : Fin 2 => b), horth j (fun _ : Fin 2 => a)]
  have hexp := star_dotProduct_thresholdOp_mulVec diag01_isHermitian 1
    (c • (productEigenvector diag01_isHermitian (fun _ : Fin 2 => b)
      + productEigenvector diag01_isHermitian (fun _ : Fin 2 => a)))
  rw [hexp, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hsub : (∑ j : Fin 2 → Fin (2 ^ 1),
          ‖inner ℂ (productEigenbasis diag01_isHermitian 2 j)
            (WithLp.toLp 2 (c • (productEigenvector diag01_isHermitian (fun _ : Fin 2 => b)
              + productEigenvector diag01_isHermitian (fun _ : Fin 2 => a))))‖ ^ 2
            * tailWeight (fun i => diag01_isHermitian.eigenvalues (j i)) 1)
      = ∑ j ∈ ({(fun _ : Fin 2 => b), (fun _ : Fin 2 => a)} : Finset (Fin 2 → Fin (2 ^ 1))),
        ‖inner ℂ (productEigenbasis diag01_isHermitian 2 j)
          (WithLp.toLp 2 (c • (productEigenvector diag01_isHermitian (fun _ : Fin 2 => b)
            + productEigenvector diag01_isHermitian (fun _ : Fin 2 => a))))‖ ^ 2
          * tailWeight (fun i => diag01_isHermitian.eigenvalues (j i)) 1 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    · intro j _ hjn
      rw [Finset.mem_insert, Finset.mem_singleton] at hjn
      obtain ⟨hn1, hn0⟩ := not_or.mp hjn
      have hc0 : inner ℂ (productEigenbasis diag01_isHermitian 2 j)
          (WithLp.toLp 2 (c • (productEigenvector diag01_isHermitian (fun _ : Fin 2 => b)
            + productEigenvector diag01_isHermitian (fun _ : Fin 2 => a)))) = 0 := by
        rw [hc j, ite_eq_right hn1, ite_eq_right hn0]
        simp
      rw [hc0]
      simp
  rw [hsub, Finset.sum_pair hne]
  have hw1 : ‖inner ℂ (productEigenbasis diag01_isHermitian 2 (fun _ : Fin 2 => b))
      (WithLp.toLp 2 (c • (productEigenvector diag01_isHermitian (fun _ : Fin 2 => b)
        + productEigenvector diag01_isHermitian (fun _ : Fin 2 => a))))‖ ^ 2 = 1 / 2 := by
    have hii : inner ℂ (productEigenbasis diag01_isHermitian 2 (fun _ : Fin 2 => b))
        (WithLp.toLp 2 (c • (productEigenvector diag01_isHermitian (fun _ : Fin 2 => b)
          + productEigenvector diag01_isHermitian (fun _ : Fin 2 => a)))) = c := by
      rw [hc (fun _ : Fin 2 => b), ite_eq_left rfl, ite_eq_right hne]
      simp
    rw [hii, hc_norm]
  have hw0 : ‖inner ℂ (productEigenbasis diag01_isHermitian 2 (fun _ : Fin 2 => a))
      (WithLp.toLp 2 (c • (productEigenvector diag01_isHermitian (fun _ : Fin 2 => b)
        + productEigenvector diag01_isHermitian (fun _ : Fin 2 => a))))‖ ^ 2 = 1 / 2 := by
    have hii : inner ℂ (productEigenbasis diag01_isHermitian 2 (fun _ : Fin 2 => a))
        (WithLp.toLp 2 (c • (productEigenvector diag01_isHermitian (fun _ : Fin 2 => b)
          + productEigenvector diag01_isHermitian (fun _ : Fin 2 => a)))) = c := by
      rw [hc (fun _ : Fin 2 => a), ite_eq_right hne.symm, ite_eq_left rfl]
      simp
    rw [hii, hc_norm]
  rw [hw1, hw0, ht1, ht0]
  norm_num

end CslibTest.Complexity.Classes.QMA
