/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.RingTheory.PicardGroup

/-!
# Singular value decomposition

Every square complex matrix admits a singular value decomposition:
`Matrix.exists_unitaryGroup_diagonal_nonneg`.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Moving a matrix across a `dotProduct`: pairing the `A`-images of two vectors is the
same as pairing one vector against the `(Aᴴ * A)`-image of the other. -/
private theorem aux_star_mulVec_dotProduct (A : Matrix n n ℂ) (a b : n → ℂ) :
    star (A *ᵥ a) ⬝ᵥ (A *ᵥ b) = star a ⬝ᵥ ((Aᴴ * A) *ᵥ b) := by
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec]

/-- The `dotProduct` of two eigenvectors of `Aᴴ * A` (one conjugated) is the Kronecker delta. -/
private theorem aux_bridge_star_dotProduct (A : Matrix n n ℂ) (hB : (Aᴴ * A).IsHermitian)
    (i j : n) :
    star (hB.eigenvectorBasis i).ofLp ⬝ᵥ (hB.eigenvectorBasis j).ofLp
      = (if i = j then (1 : ℂ) else 0) := by
  have h := orthonormal_iff_ite.mp hB.eigenvectorBasis.orthonormal i j
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  exact h

/-- Inner products of `A`-images of eigenvectors of `Aᴴ * A`. -/
private theorem aux_inner_toLp_mulVec (A : Matrix n n ℂ) (hB : (Aᴴ * A).IsHermitian)
    (i j : n) :
    inner ℂ (WithLp.toLp 2 (A *ᵥ (hB.eigenvectorBasis i).ofLp))
        (WithLp.toLp 2 (A *ᵥ (hB.eigenvectorBasis j).ofLp))
      = ((hB.eigenvalues j : ℂ)) * (if i = j then (1 : ℂ) else 0) := by
  have hconv : ∀ (r : ℝ) (z : ℂ), r • z = (r : ℂ) * z := fun r z => by simp
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, aux_star_mulVec_dotProduct,
    hB.mulVec_eigenvectorBasis j, dotProduct_smul,
    aux_bridge_star_dotProduct A hB i j, hconv _ _]

/--
**Singular value decomposition of a complex square matrix.** Let $A$ be a square complex matrix
whose rows and columns are indexed by a finite type $n$. Then there are unitary matrices $U$ and $V$
and nonnegative real numbers $\sigma_i$ for $i \in n$ such that, writing $D$ for the diagonal
matrix with diagonal entries $\sigma_i$ and $V^*$ for the conjugate transpose of $V$, we have
$A = U D V^*$.

Source: R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013).
Proves `Wanted` entry `complex_svd`, restated over `Matrix.unitaryGroup` in place of the entry's
`IsUnitaryMatrix`.
-/
theorem exists_unitaryGroup_diagonal_nonneg (A : Matrix n n ℂ) :
    ∃ (U V : Matrix.unitaryGroup n ℂ) (σ : n → ℝ), (∀ i, 0 ≤ σ i) ∧
      A = (U : Matrix n n ℂ) * diagonal (fun i => (σ i : ℂ)) * star (V : Matrix n n ℂ) := by
  have hBherm : (Aᴴ * A).IsHermitian := isHermitian_conjTranspose_mul_self A
  -- Singular values: square roots of the (nonnegative) eigenvalues of `Aᴴ * A`.
  set σ : n → ℝ := fun j => Real.sqrt (hBherm.eigenvalues j) with hσdef
  have hlam_nonneg : ∀ j, 0 ≤ hBherm.eigenvalues j :=
    fun j => Matrix.eigenvalues_conjTranspose_mul_self_nonneg A j
  have hσ_nonneg : ∀ j, 0 ≤ σ j := by
    intro j
    simp only [hσdef]
    exact Real.sqrt_nonneg _
  have hσ_sq : ∀ j, σ j ^ 2 = hBherm.eigenvalues j := by
    intro j
    simp only [hσdef]
    exact Real.sq_sqrt (hlam_nonneg j)
  have heig_eq : ∀ j, ((hBherm.eigenvalues j : ℂ)) = ((σ j : ℂ)) ^ 2 := by
    intro j
    rw [← hσ_sq j, Complex.ofReal_pow]
  -- Unnormalized left singular vectors, as elements of Euclidean space.
  set w : n → EuclideanSpace ℂ n := fun j =>
    ((σ j : ℂ))⁻¹ • WithLp.toLp 2 (A *ᵥ (hBherm.eigenvectorBasis j).ofLp) with hw_def
  have hw_ofLp : ∀ j,
      (w j).ofLp = ((σ j : ℂ))⁻¹ • (A *ᵥ (hBherm.eigenvectorBasis j).ofLp) := by
    intro j
    ext k
    simp only [hw_def, PiLp.smul_apply, Pi.smul_apply]
  have hw_inner : ∀ i j : n, inner ℂ (w i) (w j)
      = (starRingEnd ℂ) ((σ i : ℂ))⁻¹
        * ((((σ j : ℂ))⁻¹ * ((hBherm.eigenvalues j : ℂ) * (if i = j then (1 : ℂ) else 0)))) := by
    intro i j
    have e := aux_inner_toLp_mulVec A hBherm i j
    simp only [hw_def]
    rw [inner_smul_left, inner_smul_right, e]
  have hci : ∀ k : n, (starRingEnd ℂ) ((σ k : ℂ))⁻¹ = ((σ k : ℂ))⁻¹ := by
    intro k
    simp
  -- The `w j` with `σ j ≠ 0` form an orthonormal family.
  have horth : Orthonormal ℂ ((({j | σ j ≠ 0} : Set n)).domRestrict w) := by
    rw [orthonormal_iff_ite]
    intro xi yj
    obtain ⟨i, hi⟩ := xi
    obtain ⟨j, hj⟩ := yj
    have hi' : σ i ≠ 0 := hi
    have hj' : σ j ≠ 0 := hj
    change inner ℂ (w i) (w j) = _
    rw [hw_inner i j, hci i, heig_eq j]
    by_cases hij : i = j
    · subst hij
      have hc : ((σ i : ℂ)) ≠ 0 := by exact_mod_cast hi'
      have hself : (⟨i, hi⟩ : ↥(({j | σ j ≠ 0} : Set n))) = ⟨i, hj'⟩ := rfl
      rw [hself]
      simp only [ite_true]
      have e1 : ((σ i : ℂ))⁻¹ * (((σ i : ℂ)) * ((σ i : ℂ))) = ((σ i : ℂ)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      rw [mul_one, pow_two, e1, inv_mul_cancel₀ hc]
    · have hne : (⟨i, hi⟩ : ↥(({j | σ j ≠ 0} : Set n))) ≠ ⟨j, hj⟩ :=
        fun h => hij (Subtype.ext_iff.mp h)
      simp [hij, hne]
  -- Extend to a full orthonormal basis; its change-of-basis matrix is the left factor.
  obtain ⟨bU, hbU⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq finrank_euclideanSpace horth
  set U : Matrix n n ℂ :=
    (EuclideanSpace.basisFun n ℂ).toBasis.toMatrix ⇑bU with hU_def
  set V : Matrix n n ℂ := ↑hBherm.eigenvectorUnitary with hV_def
  have hUcol : ∀ j, U.col j = (bU j).ofLp := by
    intro j
    rw [hU_def]
    rfl
  have hVcol : ∀ j, V.col j = (hBherm.eigenvectorBasis j).ofLp := by
    intro j
    rw [hV_def]
    exact hBherm.eigenvectorUnitary_col_eq j
  have hUunit : U ∈ Matrix.unitaryGroup n ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hU_def]
    exact OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self _ _
  have hVunit : V ∈ Matrix.unitaryGroup n ℂ := hBherm.eigenvectorUnitary.2
  -- Each column satisfies `A *ᵥ v j = σ j • u j`.
  have hAVcol : ∀ j,
      A *ᵥ (hBherm.eigenvectorBasis j).ofLp = ((σ j : ℂ)) • (bU j).ofLp := by
    intro j
    by_cases hj : σ j = 0
    · have hcast0 : ((σ j : ℂ)) = 0 := by exact_mod_cast hj
      have heig0 : hBherm.eigenvalues j = 0 := by
        have h := hσ_sq j
        rw [hj] at h
        simpa using h.symm
      have hnorm :
          star (A *ᵥ (hBherm.eigenvectorBasis j).ofLp)
            ⬝ᵥ (A *ᵥ (hBherm.eigenvectorBasis j).ofLp) = 0 := by
        rw [aux_star_mulVec_dotProduct, hBherm.mulVec_eigenvectorBasis j, heig0,
          zero_smul, dotProduct_zero]
      have hA0 : A *ᵥ (hBherm.eigenvectorBasis j).ofLp = 0 :=
        dotProduct_star_self_eq_zero.mp hnorm
      rw [hcast0, zero_smul]
      exact hA0
    · have hbUw : bU j = w j := hbU j hj
      have hc : ((σ j : ℂ)) ≠ 0 := by exact_mod_cast hj
      rw [hbUw, hw_ofLp j, ← mul_smul, mul_inv_cancel₀ hc, one_smul]
  have hsingle : ∀ (c : ℂ) (j : n), Pi.single j c = c • Pi.single j (1 : ℂ) := by
    intro c j
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  have hAV : A * V = U * diagonal (fun i => ((σ i : ℂ))) := by
    apply Matrix.ext_of_mulVec_single
    intro j
    conv_lhs => rw [← mulVec_mulVec, mulVec_single_one, hVcol j]
    conv_rhs => rw [← mulVec_mulVec, Matrix.diagonal_mulVec_single]
    change A *ᵥ (hBherm.eigenvectorBasis j).ofLp = U *ᵥ Pi.single j (((σ j : ℂ)) * 1)
    rw [mul_one, hsingle, mulVec_smul, mulVec_single_one, hUcol j]
    exact hAVcol j
  refine ⟨⟨U, hUunit⟩, ⟨V, hVunit⟩, σ, hσ_nonneg, ?_⟩
  have hVV : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hVunit
  rw [Matrix.star_eq_conjTranspose]
  calc A = (A * V) * Vᴴ := by rw [mul_assoc, hVV, mul_one]
    _ = U * diagonal (fun i => ((σ i : ℂ))) * Vᴴ := by rw [hAV]

end Matrix
