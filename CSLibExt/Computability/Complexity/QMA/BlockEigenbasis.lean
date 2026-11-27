/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Classes
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Block tensor products and product eigenbases

This file defines the `k`-block form of the Atlas tensor product on vectors
indexed by `Fin (2 ^ (k * m))`, with block `0` in the low digits. It also
defines block operators and the product eigenbasis of a Hermitian block
operator. No Mathlib Kronecker transport is used; all statements stay in the
Atlas digit convention.
-/

@[expose] public section

namespace Cslib.Complexity.Classes.QMA

set_option autoImplicit false

open scoped Matrix BigOperators

/-- The `i`-th `m`-bit digit of a `k`-block index, with block `0` lowest. -/
def blockDigit (k m : ℕ) (i : Fin k) (s : Fin (2 ^ (k * m))) : Fin (2 ^ m) :=
  ⟨s.val / 2 ^ (i.val * m) % 2 ^ m,
    Nat.mod_lt _ (by positivity)⟩

/-- The digit bijection between block indices and one global index. -/
def blockEquiv (k m : ℕ) : (Fin k → Fin (2 ^ m)) ≃ Fin (2 ^ (k * m)) :=
  finFunctionFinEquiv.trans
    (finCongr (by rw [← pow_mul, Nat.mul_comm m k]))

/-- Reading the digits of a global index gives its block indices. -/
lemma blockEquiv_symm_apply (k m : ℕ) (s : Fin (2 ^ (k * m))) (i : Fin k) :
    (blockEquiv k m).symm s i = blockDigit k m i s := by
  have hpow : (2 ^ m) ^ i.val = 2 ^ (i.val * m) := by
    rw [← pow_mul, mul_comm]
  ext
  simp [blockEquiv, blockDigit, finFunctionFinEquiv, finCongr, hpow]

/-- The product state over `k` blocks, in Atlas low-digit-first order. -/
def blockProd {k m : ℕ} (ψ : Fin k → Fin (2 ^ m) → ℂ) :
    Fin (2 ^ (k * m)) → ℂ :=
  fun s => ∏ i, ψ i (blockDigit k m i s)

/-- A cons block product is the Atlas binary tensor product, transported
along the equality `(k + 1) * m = m + k * m`. -/
theorem blockProd_cons {k m : ℕ}
    (ψ₀ : Fin (2 ^ m) → ℂ) (ψ : Fin k → Fin (2 ^ m) → ℂ)
    (s : Fin (2 ^ ((k + 1) * m))) :
    blockProd (Fin.cons ψ₀ ψ) s =
      tensorProd ψ₀ (blockProd ψ)
        (Fin.cast (by rw [add_mul, one_mul, add_comm]) s) := by
  have hbound : s.val / 2 ^ m < 2 ^ (k * m) := by
    have hlt : s.val < 2 ^ m * 2 ^ (k * m) := by
      calc s.val < 2 ^ ((k + 1) * m) := s.isLt
        _ = 2 ^ m * 2 ^ (k * m) := by
          rw [show (k + 1) * m = m + k * m by ring, pow_add]
    exact Nat.div_lt_of_lt_mul hlt
  have h0 : blockDigit (k + 1) m 0 s
      = ⟨s.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩ := by
    ext
    simp [blockDigit, Nat.div_one]
  have hS : ∀ i : Fin k, blockDigit (k + 1) m i.succ s
      = blockDigit k m i ⟨s.val / 2 ^ m, hbound⟩ := by
    intro i
    ext
    simp only [blockDigit]
    have hs1 : i.succ.val = i.val + 1 := rfl
    rw [hs1]
    have hexp : (i.val + 1) * m = m + i.val * m := by ring
    rw [hexp, pow_add, Nat.div_div_eq_div_mul]
  simp only [blockProd, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    tensorProd, Fin.cast, h0, hS]

/-- The block operator `⊗ᵢ Aᵢ` in Atlas digit coordinates. -/
def blockOp {k m : ℕ}
    (A : Fin k → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) :
    Matrix (Fin (2 ^ (k * m))) (Fin (2 ^ (k * m))) ℂ :=
  fun s t => ∏ i, A i (blockDigit k m i s) (blockDigit k m i t)

/-- The threshold block operator selecting `Q` or `1 - Q` in each block. -/
def thresholdBlockOp {k m : ℕ}
    (Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) (b : Fin k → Bool) :
    Matrix (Fin (2 ^ (k * m))) (Fin (2 ^ (k * m))) ℂ :=
  blockOp (fun i => if b i then Q else 1 - Q)

/-- The dot product as an explicit sum. -/
private lemma dotProduct_eq_sum {n : ℕ} (v w : Fin n → ℂ) :
    v ⬝ᵥ w = ∑ i, v i * w i := rfl

/-- A block operator acts blockwise on a product state. -/
theorem blockOp_mulVec_blockProd {k m : ℕ}
    (A : Fin k → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ)
    (ψ : Fin k → Fin (2 ^ m) → ℂ) :
    blockOp A *ᵥ blockProd ψ = blockProd (fun i => A i *ᵥ ψ i) := by
  have hdigit : ∀ g i, blockDigit k m i (blockEquiv k m g) = g i := by
    intro g i
    have h := blockEquiv_symm_apply k m (blockEquiv k m g) i
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  ext s
  simp only [Matrix.mulVec, dotProduct_eq_sum, blockOp, blockProd,
    ← Finset.prod_mul_distrib]
  rw [(Equiv.sum_comp (blockEquiv k m) _).symm]
  simp only [hdigit, Fintype.prod_sum]

/-- The inner product of two product states factors over blocks. -/
theorem star_blockProd_dotProduct_blockProd {k m : ℕ}
    (φ ψ : Fin k → Fin (2 ^ m) → ℂ) :
    star (blockProd φ) ⬝ᵥ blockProd ψ =
      ∏ i, star (φ i) ⬝ᵥ ψ i := by
  have hdigit : ∀ g i, blockDigit k m i (blockEquiv k m g) = g i := by
    intro g i
    have h := blockEquiv_symm_apply k m (blockEquiv k m g) i
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  simp only [dotProduct_eq_sum, blockProd, Pi.star_apply, star_prod,
    ← Finset.prod_mul_distrib]
  rw [(Equiv.sum_comp (blockEquiv k m) _).symm]
  simp only [hdigit, Fintype.prod_sum]

/-- The expectation of a block operator in a product state factors. -/
theorem blockExpectation_blockProd {k m : ℕ}
    (A : Fin k → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ)
    (ψ : Fin k → Fin (2 ^ m) → ℂ) :
    star (blockProd ψ) ⬝ᵥ (blockOp A *ᵥ blockProd ψ) =
      ∏ i, star (ψ i) ⬝ᵥ (A i *ᵥ ψ i) := by
  rw [blockOp_mulVec_blockProd, star_blockProd_dotProduct_blockProd]

/-- Atlas squared norm as the real part of the dot product. -/
lemma sqNorm_eq_re_star_dotProduct {n : ℕ} (ψ : Fin (2 ^ n) → ℂ) :
    sqNorm ψ = (star ψ ⬝ᵥ ψ).re := by
  simp only [sqNorm, dotProduct_eq_sum, Pi.star_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp

/-- The squared norm of a product state is the product of squared norms. -/
theorem sqNorm_blockProd {k m : ℕ}
    (ψ : Fin k → Fin (2 ^ m) → ℂ) :
    sqNorm (blockProd ψ) = ∏ i, sqNorm (ψ i) := by
  have hcast : ∀ i, star (ψ i) ⬝ᵥ ψ i
      = ((‖WithLp.toLp 2 (ψ i)‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    have h := EuclideanSpace.inner_eq_star_dotProduct
      (WithLp.toLp 2 (ψ i)) (WithLp.toLp 2 (ψ i))
    rw [inner_self_eq_norm_sq_to_K, dotProduct_comm,
      ← RCLike.ofReal_pow] at h
    exact h.symm
  rw [sqNorm_eq_re_star_dotProduct, star_blockProd_dotProduct_blockProd]
  simp only [sqNorm_eq_re_star_dotProduct, hcast, ← Complex.ofReal_prod,
    Complex.ofReal_re]

/-- A product of unit vectors is a unit vector. -/
theorem sqNorm_blockProd_eq_one {k m : ℕ}
    (ψ : Fin k → Fin (2 ^ m) → ℂ) (h : ∀ i, sqNorm (ψ i) = 1) :
    sqNorm (blockProd ψ) = 1 := by
  rw [sqNorm_blockProd]; simp [h]

/-- The product eigenvector indexed by one single-block eigenvector in each
block. -/
noncomputable def productEigenvector {k m : ℕ}
    {Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ}
    (hQ : Q.IsHermitian) (j : Fin k → Fin (2 ^ m)) :
    Fin (2 ^ (k * m)) → ℂ :=
  blockProd (fun i => ⇑(hQ.eigenvectorBasis (j i)))

/-- Product eigenvectors are orthonormal. -/
theorem orthonormal_productEigenvector {k m : ℕ}
    {Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ}
    (hQ : Q.IsHermitian) :
    Orthonormal ℂ
      (fun j => WithLp.toLp 2 (productEigenvector hQ j) :
        (Fin k → Fin (2 ^ m)) → EuclideanSpace ℂ (Fin (2 ^ (k * m)))) := by
  have hsingle := hQ.eigenvectorBasis.orthonormal
  have hinner : ∀ j j' : Fin k → Fin (2 ^ m),
      inner ℂ (WithLp.toLp 2 (productEigenvector hQ j))
        (WithLp.toLp 2 (productEigenvector hQ j'))
        = ∏ i, inner ℂ (hQ.eigenvectorBasis (j i))
          (hQ.eigenvectorBasis (j' i)) := by
    intro j j'
    simp only [productEigenvector]
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm,
      star_blockProd_dotProduct_blockProd]
    apply Finset.prod_congr rfl
    intro i _
    rw [dotProduct_comm]
    exact (EuclideanSpace.inner_eq_star_dotProduct _ _).symm
  have h1 : ∀ j : Fin k → Fin (2 ^ m), ∀ i,
      inner ℂ (hQ.eigenvectorBasis (j i))
        (hQ.eigenvectorBasis (j i)) = 1 := by
    intro j i
    have h := (orthonormal_iff_ite.mp hsingle) (j i) (j i)
    rwa [ite_eq_left rfl] at h
  have h0 : ∀ j j' : Fin k → Fin (2 ^ m), ∀ i, j i ≠ j' i →
      inner ℂ (hQ.eigenvectorBasis (j i))
        (hQ.eigenvectorBasis (j' i)) = 0 := by
    intro j j' i hi
    exact hsingle.inner_eq_zero hi
  rw [orthonormal_iff_ite]
  intro j j'
  by_cases h : j = j'
  · rw [ite_eq_left h]
    subst h
    simp only [hinner, h1, Finset.prod_const_one]
  · obtain ⟨i, hi⟩ : ∃ i, j i ≠ j' i := Function.ne_iff.mp h
    simp only [hinner]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (h0 j j' i hi),
      ite_eq_right h]

/-- The orthonormal basis of product eigenvectors. -/
noncomputable def productEigenbasis {m : ℕ}
    {Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ}
    (hQ : Q.IsHermitian) (k : ℕ) :
    OrthonormalBasis (Fin k → Fin (2 ^ m)) ℂ
      (EuclideanSpace ℂ (Fin (2 ^ (k * m)))) :=
  OrthonormalBasis.mk (orthonormal_productEigenvector hQ) (by
    have h_ind : LinearIndependent ℂ (fun j : Fin k → Fin (2 ^ m) =>
        WithLp.toLp 2 (productEigenvector hQ j)) :=
      (orthonormal_productEigenvector (k := k) hQ).linearIndependent
    have hcard : Fintype.card (Fin k → Fin (2 ^ m))
        = Module.finrank ℂ (EuclideanSpace ℂ (Fin (2 ^ (k * m)))) := by
      rw [finrank_euclideanSpace, Fintype.card_pi, Finset.prod_const,
        Finset.card_univ]
      simp only [Fintype.card_fin]
      rw [← pow_mul, mul_comm]
    exact ge_of_eq (h_ind.span_eq_top_of_card_eq_finrank hcard))

/-- The vector of the product eigenbasis at `j` is the product eigenvector for `j`. -/
theorem productEigenbasis_apply {k m : ℕ}
    {Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ}
    (hQ : Q.IsHermitian) (j : Fin k → Fin (2 ^ m)) :
    ⇑(productEigenbasis hQ k j) = productEigenvector hQ j := by
  simp [productEigenbasis, productEigenvector]

/-- Threshold block operators act diagonally on product eigenvectors, with
the product of the selected eigenvalue factors. -/
theorem thresholdBlockOp_mulVec_productEigenvector {k m : ℕ}
    {Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ}
    (hQ : Q.IsHermitian) (b : Fin k → Bool)
    (j : Fin k → Fin (2 ^ m)) :
    thresholdBlockOp Q b *ᵥ productEigenvector hQ j =
      (∏ i, if b i then ((hQ.eigenvalues (j i) : ℝ) : ℂ)
        else 1 - ((hQ.eigenvalues (j i) : ℝ) : ℂ)) •
          productEigenvector hQ j := by
  have hblock : ∀ i, (if b i then Q else 1 - Q)
      *ᵥ ⇑(hQ.eigenvectorBasis (j i))
      = (if b i then ((hQ.eigenvalues (j i) : ℝ) : ℂ)
        else 1 - ((hQ.eigenvalues (j i) : ℝ) : ℂ)) •
        ⇑(hQ.eigenvectorBasis (j i)) := by
    intro i
    by_cases hb : b i
    · simp [ite_eq_left hb, hQ.mulVec_eigenvectorBasis]
    · simp [ite_eq_right hb, Matrix.sub_mulVec, Matrix.one_mulVec,
        hQ.mulVec_eigenvectorBasis, sub_smul, one_smul]
  simp only [thresholdBlockOp, productEigenvector, blockOp_mulVec_blockProd,
    hblock]
  ext s
  simp only [blockProd, Pi.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib]

end Cslib.Complexity.Classes.QMA
