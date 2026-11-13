/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic

/-!
# CH39: Variational method, perturbation theory and Hückel MO theory

Reuse-verified exception: this module depends ONLY on pinned Mathlib at main
(in particular `Matrix.IsHermitian.eigenvalues`, `SimpleGraph.adjMatrix`,
real trigonometry) and on no CH36/MF03/MF10 file.

Model boundary: Hückel parameters α, β are empirical (one-electron
approximation, MOD); all spectra and inequalities are MC. Beta < 0 sign
convention. Hückel energies are not total energies. Infinite-dimensional
variational principle needs form domains (deferred, not claimed).

CH39.1: The general Cauchy interlacing theorem (all principal submatrices,
all orders) is NOT proved; the pinned `cauchyInterlacing_oneDim` is its
one-dimensional case (diagonal entries lie between the extreme eigenvalues),
proved from the Rayleigh bounds.

CH39.2: The eigenvector-curve existence theorem is NOT proved; the pinned
statements are the coefficient identities.

CH39.3: The pinned eigenvector theorems certify that the listed numbers ARE
eigenvalues (with explicit eigenvectors); the full "these are ALL the
eigenvalues" completeness is the standard dimension argument from the n
distinct path eigenvalues / the orthogonal cos+sin families and is NOT
separately formalized.

CH39.4: Physical reading (Aufbau): 2 electrons per orbital, spin-paired.
No aromaticity criterion is claimed.
-/

@[expose] public section

open scoped Matrix

namespace PhyslibExt.Chemistry.VariationalPerturbationHuckel

/-- Rayleigh quotient `(x ⬝ᵥ H *ᵥ x) / (x ⬝ᵥ x)`. -/
noncomputable def rayleighQuotient {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : ℝ :=
  (x ⬝ᵥ H *ᵥ x) / (x ⬝ᵥ x)

/-- Generalized Rayleigh quotient `(x ⬝ᵥ H *ᵥ x) / (x ⬝ᵥ S *ᵥ x)`. -/
noncomputable def generalizedRayleighQuotient {n : ℕ}
    (H S : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  (x ⬝ᵥ H *ᵥ x) / (x ⬝ᵥ S *ᵥ x)

/-- Hückel matrix `H = α • 1 + β • Adj(G)`. -/
noncomputable def huckelMatrix {n : ℕ} (α β : ℝ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Matrix (Fin n) (Fin n) ℝ :=
  α • 1 + β • G.adjMatrix ℝ

/-- First-order energy correction: `(H1) 0 0`. -/
noncomputable def pertE1 {n : ℕ} [NeZero n] (H1 : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  H1 0 0

/-- First-order eigenvector correction (zero 0-component). -/
noncomputable def pertV1 {n : ℕ} [NeZero n] (d : Fin n → ℝ)
    (H1 : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  fun j => if j = 0 then 0 else H1 j 0 / (d 0 - d j)

/-- Second-order energy correction. -/
noncomputable def pertE2 {n : ℕ} [NeZero n] (d : Fin n → ℝ)
    (H1 H2 : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  H2 0 0 + ∑ j ∈ Finset.univ.erase 0, (H1 j 0) ^ 2 / (d 0 - d j)

/-- Second-order eigenvector correction (zero 0-component). -/
noncomputable def pertV2 {n : ℕ} [NeZero n] (d : Fin n → ℝ)
    (H1 H2 : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  fun j => if j = 0 then 0 else
    (H2 j 0 + ∑ k ∈ Finset.univ.erase 0, H1 j k * H1 k 0 / (d 0 - d k) -
      pertE1 H1 * H1 j 0 / (d 0 - d j)) / (d 0 - d j)

/-- Alternating-sign flip: `(flip v) j = (-1) ^ j.val * v j`. -/
noncomputable def alternatingFlip {N : ℕ} (v : Fin N → ℝ) : Fin N → ℝ :=
  fun j => (-1 : ℝ) ^ j.val * v j

/-- Eigenvector-basis vectors as plain functions. -/
private noncomputable def rqBasisVec {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsHermitian) (i : Fin n) : Fin n → ℝ :=
  ⇑(hH.eigenvectorBasis i)

/-- Coordinates of `x` in the eigenvector basis. -/
private noncomputable def rqCoord {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsHermitian) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  rqBasisVec hH i ⬝ᵥ x

/-- Basis vectors are eigenvectors. -/
private lemma rq_eigen {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsHermitian) (i : Fin n) :
    H *ᵥ rqBasisVec hH i = (hH.eigenvalues i) • rqBasisVec hH i :=
  hH.mulVec_eigenvectorBasis i

/-- The eigenvector basis is orthonormal for `⬝ᵥ`. -/
private lemma rq_orth {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsHermitian) (i j : Fin n) :
    rqBasisVec hH i ⬝ᵥ rqBasisVec hH j = (if i = j then (1 : ℝ) else 0) := by
  have hortho := (orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal) i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at hortho
  have hstar : ∀ f : Fin n → ℝ, star f = f :=
    fun f => funext fun t => star_trivial (f t)
  rw [hstar, dotProduct_comm] at hortho
  exact hortho

/-- Basis coordinates equal the `repr` coefficients. -/
private lemma rq_repr {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsHermitian) (x : Fin n → ℝ) (i : Fin n) :
    hH.eigenvectorBasis.repr (WithLp.toLp 2 x) i = rqCoord hH x i := by
  rw [OrthonormalBasis.repr_apply_apply, EuclideanSpace.inner_eq_star_dotProduct,
    WithLp.ofLp_toLp]
  have hstar : ∀ f : Fin n → ℝ, star f = f :=
    fun f => funext fun t => star_trivial (f t)
  rw [hstar, dotProduct_comm]
  rfl

/-- Expansion of `x` in the eigenvector basis. -/
private lemma rq_expand {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsHermitian) (x : Fin n → ℝ) :
    x = ∑ i, rqCoord hH x i • rqBasisVec hH i := by
  have hof := congrArg WithLp.ofLp
    (hH.eigenvectorBasis.sum_repr (WithLp.toLp 2 x))
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_toLp] at hof
  conv_lhs => rw [← hof]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : hH.eigenvectorBasis.repr (WithLp.toLp 2 x) i = rqCoord hH x i :=
    rq_repr hH x i
  have h2 : WithLp.ofLp (hH.eigenvectorBasis i) = rqBasisVec hH i := rfl
  rw [h1, h2]

/-- Quadratic form in the eigenvector basis. -/
private lemma rq_quad {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsHermitian) (x : Fin n → ℝ) :
    x ⬝ᵥ H *ᵥ x = ∑ i, hH.eigenvalues i * (rqCoord hH x i) ^ 2 := by
  conv_lhs => rw [rq_expand hH x]
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, rq_eigen hH, ← smul_assoc, sum_dotProduct,
    dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, rq_orth hH,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Squared norm in the eigenvector basis. -/
private lemma rq_normsq {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsHermitian) (x : Fin n → ℝ) :
    x ⬝ᵥ x = ∑ i, (rqCoord hH x i) ^ 2 := by
  have h1 : x ⬝ᵥ x =
      (∑ i, rqCoord hH x i • rqBasisVec hH i) ⬝ᵥ x :=
    congrArg (· ⬝ᵥ x) (rq_expand hH x)
  rw [h1]
  have hci : ∀ i, rqBasisVec hH i ⬝ᵥ x = rqCoord hH x i := fun i => rfl
  simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul, hci, pow_two]

/-- The squared norm of a nonzero vector is positive. -/
private lemma rq_norm_pos {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsHermitian) {x : Fin n → ℝ} (hx : x ≠ 0) :
    (0 : ℝ) < x ⬝ᵥ x := by
  have hW0 : (0 : ℝ) ≤ x ⬝ᵥ x := by
    rw [rq_normsq hH x]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rcases eq_or_lt_of_le hW0 with h0 | hpos
  · exfalso
    rw [rq_normsq hH x] at h0
    have hall : ∀ i ∈ Finset.univ, (rqCoord hH x i) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp h0.symm
    have hall0 : ∀ i, rqCoord hH x i = 0 := by
      intro i
      have h2 := hall i (Finset.mem_univ i)
      have hmul : rqCoord hH x i * rqCoord hH x i = 0 := by
        rw [← pow_two]
        exact h2
      exact mul_self_eq_zero.mp hmul
    apply hx
    rw [rq_expand hH x]
    simp [hall0]
  · exact hpos

/-- Rayleigh quotient is at least the smallest eigenvalue. -/
theorem rayleighQuotient_ge_eigenvalues_min {n : ℕ} (hn : 0 < n)
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian) {x : Fin n → ℝ} (hx : x ≠ 0) :
    sInf (Set.range hH.eigenvalues) ≤ rayleighQuotient H x := by
  have hW := rq_norm_pos hH hx
  have hle : sInf (Set.range hH.eigenvalues) * (x ⬝ᵥ x) ≤ x ⬝ᵥ H *ᵥ x := by
    rw [rq_quad hH x, rq_normsq hH x, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply csInf_le _ (Set.mem_range_self i)
    exact (Set.finite_range _).bddBelow
  show sInf (Set.range hH.eigenvalues) ≤ (x ⬝ᵥ H *ᵥ x) / (x ⬝ᵥ x)
  rw [le_div_iff₀ hW]
  exact hle

/-- Rayleigh quotient is at most the largest eigenvalue. -/
theorem rayleighQuotient_le_eigenvalues_max {n : ℕ} (hn : 0 < n)
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian) {x : Fin n → ℝ} (hx : x ≠ 0) :
    rayleighQuotient H x ≤ sSup (Set.range hH.eigenvalues) := by
  have hW := rq_norm_pos hH hx
  have hle : x ⬝ᵥ H *ᵥ x ≤ sSup (Set.range hH.eigenvalues) * (x ⬝ᵥ x) := by
    rw [rq_quad hH x, rq_normsq hH x, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply le_csSup _ (Set.mem_range_self i)
    exact (Set.finite_range _).bddAbove
  show (x ⬝ᵥ H *ᵥ x) / (x ⬝ᵥ x) ≤ sSup (Set.range hH.eigenvalues)
  rw [div_le_iff₀ hW]
  exact hle

/-- One-dimensional Cauchy interlacing: every diagonal entry lies between the
extreme eigenvalues. -/
theorem cauchyInterlacing_oneDim {n : ℕ} (hn : 0 < n)
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian) (i : Fin n) :
    sInf (Set.range hH.eigenvalues) ≤ H i i ∧ H i i ≤ sSup (Set.range hH.eigenvalues) := by
  have hx : (Pi.single i 1 : Fin n → ℝ) ≠ 0 := by
    intro h
    have h0 := congrArg (fun v : Fin n → ℝ => v i) h
    simp at h0
  have hRQ : rayleighQuotient H (Pi.single i 1) = H i i := by
    unfold rayleighQuotient
    rw [single_dotProduct, Matrix.mulVec_single_one, Matrix.col_apply,
      dotProduct_single, Pi.single_eq_same]
    simp only [mul_one, one_mul, div_one]
  constructor
  · rw [← hRQ]
    exact rayleighQuotient_ge_eigenvalues_min hn hH hx
  · rw [← hRQ]
    exact rayleighQuotient_le_eigenvalues_max hn hH hx

/-- A generalized eigenvalue equals its generalized Rayleigh quotient: in
particular it is real. `S` positive definite, `H c = E • (S *ᵥ c)`, `c ≠ 0`. -/
theorem generalizedEigenvalue_eq_ratio {n : ℕ}
    {H S : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian) (hS : S.IsHermitian)
    (hSpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ S *ᵥ x)
    {c : Fin n → ℝ} (hc : c ≠ 0) {E : ℝ} (hEc : H *ᵥ c = E • (S *ᵥ c)) :
    E = generalizedRayleighQuotient H S c := by
  unfold generalizedRayleighQuotient
  have hpos := hSpos c hc
  have hne : c ⬝ᵥ S *ᵥ c ≠ 0 := ne_of_gt hpos
  have hcongr := congrArg (fun w => c ⬝ᵥ w) hEc
  simp at hcongr
  field_simp
  linarith

/-- First-order perturbation: with `v(t) = e₀ + t • pertV1` and
`E(t) = d 0 + t * pertE1`, the residual of `(diagonal d + t • H1)` is `O(t ^ 2)`. -/
theorem firstOrder_residual {n : ℕ} [NeZero n] (d : Fin n → ℝ)
    (H1 : Matrix (Fin n) (Fin n) ℝ)
    (hd : ∀ j : Fin n, j ≠ 0 → d 0 - d j ≠ 0) (t : ℝ) :
    (Matrix.diagonal d + t • H1) *ᵥ ((Pi.single 0 1 : Fin n → ℝ) + t • pertV1 d H1) -
      (d 0 + t * pertE1 H1) • ((Pi.single 0 1 : Fin n → ℝ) + t • pertV1 d H1) =
      t ^ 2 • (H1 *ᵥ pertV1 d H1 - pertE1 H1 • pertV1 d H1) := by
  funext j
  by_cases hj : j = 0
  · subst hj
    simp only [Pi.sub_apply, Matrix.add_mulVec, Pi.add_apply, Matrix.smul_mulVec,
      Pi.smul_apply, smul_eq_mul, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_single_one, Matrix.col_apply, Matrix.mulVec_diagonal,
      pertV1, pertE1, Pi.single_eq_same, eq_self_iff_true, ite_true,
      Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq]
    ring
  · simp only [Pi.sub_apply, Matrix.add_mulVec, Pi.add_apply, Matrix.smul_mulVec,
      Pi.smul_apply, smul_eq_mul, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_single_one, Matrix.col_apply, Matrix.mulVec_diagonal,
      pertV1, pertE1, Pi.single_eq_of_ne hj, hj, ite_false,
      Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hj]
    field_simp [hd j hj]
    ring

/-- Second-order perturbation: the `e₀`-projected residual of the full family
`diagonal d + t • H1 + t ^ 2 • H2` at `v = e₀ + t • v1 + t ^ 2 • v2`,
`E = d 0 + t * E1 + t ^ 2 * E2` is `O(t ^ 3)` with the explicit remainder. -/
theorem secondOrder_projected_residual {n : ℕ} [NeZero n] (d : Fin n → ℝ)
    (H1 H2 : Matrix (Fin n) (Fin n) ℝ) (hH1 : H1.IsHermitian)
    (hd : ∀ j : Fin n, j ≠ 0 → d 0 - d j ≠ 0) (t : ℝ) :
    (Pi.single 0 1 : Fin n → ℝ) ⬝ᵥ
      ((Matrix.diagonal d + t • H1 + t ^ 2 • H2) *ᵥ
        ((Pi.single 0 1 : Fin n → ℝ) + t • pertV1 d H1 + t ^ 2 • pertV2 d H1 H2) -
        (d 0 + t * pertE1 H1 + t ^ 2 * pertE2 d H1 H2) •
        ((Pi.single 0 1 : Fin n → ℝ) + t • pertV1 d H1 + t ^ 2 • pertV2 d H1 H2)) =
      t ^ 3 * ((H1 *ᵥ pertV2 d H1 H2 - pertE1 H1 • pertV2 d H1 H2 -
        pertE2 d H1 H2 • pertV1 d H1 + H2 *ᵥ pertV1 d H1) 0 +
        t * ((H2 *ᵥ pertV2 d H1 H2 - pertE2 d H1 H2 • pertV2 d H1 H2) 0)) := by
  have key : (H1 *ᵥ pertV1 d H1) 0 =
      ∑ j ∈ Finset.univ.erase 0, (H1 j 0) ^ 2 / (d 0 - d j) := by
    have hmul : (H1 *ᵥ pertV1 d H1) 0 =
        ∑ k, H1 0 k * pertV1 d H1 k := rfl
    have hsplit : (∑ k, H1 0 k * pertV1 d H1 k) =
        H1 0 0 * pertV1 d H1 0 +
          ∑ k ∈ Finset.univ.erase 0, H1 0 k * pertV1 d H1 k := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin n))]
    rw [hmul, hsplit]
    have hv10 : pertV1 d H1 0 = 0 := by simp [pertV1]
    rw [hv10, mul_zero, zero_add]
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk
      exact hk
    have hH : H1 0 k = H1 k 0 := by
      have hH1' : H1ᴴ = H1 := hH1
      have h := congrFun (congrFun hH1' k) 0
      simpa [Matrix.conjTranspose_apply] using h
    rw [hH]
    simp only [pertV1, hk0, ite_false]
    ring
  have hE2 : pertE2 d H1 H2 = H2 0 0 + (H1 *ᵥ pertV1 d H1) 0 := by
    unfold pertE2
    rw [key]
  rw [single_dotProduct]
  simp only [one_mul, Pi.sub_apply, Matrix.add_mulVec, Pi.add_apply, Matrix.smul_mulVec,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_single_one, Matrix.col_apply, Matrix.mulVec_diagonal,
    pertV1, pertE1, pertV2, Pi.single_eq_same, eq_self_iff_true, ite_true,
    Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq]
  rw [hE2]
  ring

/-- Hückel action, pointwise: `(H *ᵥ v) j = α * v j + β * ∑ neighbors`. -/
private lemma huckelMatrix_mulVec_apply {n : ℕ} (α β : ℝ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (v : Fin n → ℝ) (j : Fin n) :
    (huckelMatrix α β G *ᵥ v) j =
      α * v j + β * (∑ u ∈ Finset.univ.filter (fun w => G.Adj j w), v u) := by
  have hadj : ((G.adjMatrix ℝ) *ᵥ v) j =
      ∑ u ∈ Finset.univ.filter (fun w => G.Adj j w), v u := by
    have h1 : ((G.adjMatrix ℝ) *ᵥ v) j = ∑ i, ((G.adjMatrix ℝ) j i) * v i := rfl
    rw [h1, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    rw [SimpleGraph.adjMatrix_apply]
    by_cases h : G.Adj j i <;> simp [h]
  unfold huckelMatrix
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hadj]

/-- Hückel path eigenvector: the sine vector with wavenumber `k` has eigenvalue
`α + 2 * β * cos (k * π / (n + 1))`. -/
theorem huckel_path_eigenvector {n : ℕ} (hn : 0 < n) (α β : ℝ) {k : ℕ}
    (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    huckelMatrix α β (SimpleGraph.pathGraph n) *ᵥ
      (fun j : Fin n => Real.sin ((k * (j.val + 1) : ℕ) * Real.pi / (n + 1))) =
      (α + 2 * β * Real.cos (k * Real.pi / (n + 1))) •
      (fun j : Fin n => Real.sin ((k * (j.val + 1) : ℕ) * Real.pi / (n + 1))) := by
  set v : Fin n → ℝ :=
    fun j => Real.sin ((k * (j.val + 1) : ℕ) * Real.pi / (n + 1)) with hv
  have hvj : ∀ j : Fin n,
      v j = Real.sin ((k * (j.val + 1) : ℕ) * Real.pi / (n + 1)) := fun j => rfl
  have hN : ((n : ℝ) + 1) ≠ 0 := by
    have h := Nat.cast_nonneg (α := ℝ) n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    exact ne_of_gt hpos
  funext j
  have hLHS := huckelMatrix_mulVec_apply α β (SimpleGraph.pathGraph n) v j
  rw [hLHS]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hjN : j.val < n := j.isLt
  by_cases hj0 : j.val = 0
  · by_cases hn1 : n = 1
    · subst hn1
      have hk : k = 1 := by omega
      subst hk
      have hne : Finset.univ.filter
          (fun w => (SimpleGraph.pathGraph 1).Adj j w) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [SimpleGraph.pathGraph_adj]
        intro h
        have hi := i.isLt
        have hjj := j.isLt
        rcases h with h | h <;> omega
      rw [hne, Finset.sum_empty, mul_zero, add_zero]
      have hcos : Real.cos (((1 : ℕ) : ℝ) * Real.pi / (((1 : ℕ) : ℝ) + 1)) = 0 := by
        have harg : ((((1 : ℕ) : ℝ) * Real.pi / (((1 : ℕ) : ℝ) + 1)) : ℝ) =
            Real.pi / 2 := by
          norm_num
        rw [harg, Real.cos_pi_div_two]
      rw [hcos]
      ring
    · have h1 : (1 : ℕ) < n := by omega
      have hne : Finset.univ.filter
          (fun w => (SimpleGraph.pathGraph n).Adj j w) = {⟨1, h1⟩} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        rw [SimpleGraph.pathGraph_adj]
        constructor
        · intro h
          rcases h with h | h
          · have hiv : i.val = 1 := by omega
            exact Fin.ext hiv
          · exfalso
            have hi := i.isLt
            omega
        · intro h
          left
          have hiv : i.val = 1 := congrArg Fin.val h
          omega
      rw [hne, Finset.sum_singleton]
      have hA : ((((k * (j.val + 1) : ℕ)) : ℝ) * Real.pi / ((n : ℝ) + 1)) =
          ((k : ℝ) * Real.pi / ((n : ℝ) + 1)) := by
        rw [hj0]
        push_cast
        ring
      have hB : ((((k * (1 + 1) : ℕ)) : ℝ) * Real.pi / ((n : ℝ) + 1)) =
          2 * (((k : ℝ) * Real.pi / ((n : ℝ) + 1))) := by
        push_cast
        ring
      rw [hvj j, hvj ⟨1, h1⟩, hA, hB, Real.sin_two_mul]
      ring
  · have hj0' : 0 < j.val := Nat.pos_of_ne_zero hj0
    by_cases hjl : j.val + 1 = n
    · have h1 : j.val - 1 < n := by omega
      have hne : Finset.univ.filter
          (fun w => (SimpleGraph.pathGraph n).Adj j w) = {⟨j.val - 1, h1⟩} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        rw [SimpleGraph.pathGraph_adj]
        constructor
        · intro h
          rcases h with h | h
          · exfalso
            have hi := i.isLt
            omega
          · have hiv : i.val = j.val - 1 := by omega
            exact Fin.ext hiv
        · intro h
          right
          have hiv : i.val = j.val - 1 := congrArg Fin.val h
          omega
      rw [hne, Finset.sum_singleton]
      have hA : ((((k * ((j.val - 1) + 1) : ℕ)) : ℝ) * Real.pi / ((n : ℝ) + 1)) =
          ((((k * (j.val + 1) : ℕ)) : ℝ) * Real.pi / ((n : ℝ) + 1)) -
            ((k : ℝ) * Real.pi / ((n : ℝ) + 1)) := by
        rw [show (j.val - 1) + 1 = j.val by omega]
        push_cast
        ring
      have h0 : Real.sin (((((k * (j.val + 1) : ℕ)) : ℝ) * Real.pi / ((n : ℝ) + 1)) +
          ((k : ℝ) * Real.pi / ((n : ℝ) + 1))) = 0 := by
        have harg : (((((k * (j.val + 1) : ℕ)) : ℝ) * Real.pi / ((n : ℝ) + 1)) +
            ((k : ℝ) * Real.pi / ((n : ℝ) + 1))) = ((k : ℝ) * Real.pi) := by
          rw [hjl]
          push_cast
          rw [← add_div, div_eq_iff hN]
          ring
        rw [harg, Real.sin_nat_mul_pi]
      have hadd : Real.sin (((((k * (j.val + 1) : ℕ)) : ℝ) * Real.pi / ((n : ℝ) + 1)) -
          ((k : ℝ) * Real.pi / ((n : ℝ) + 1))) +
          Real.sin (((((k * (j.val + 1) : ℕ)) : ℝ) * Real.pi / ((n : ℝ) + 1)) +
          ((k : ℝ) * Real.pi / ((n : ℝ) + 1))) =
          2 * Real.sin ((((k * (j.val + 1) : ℕ)) : ℝ) * Real.pi / ((n : ℝ) + 1)) *
            Real.cos ((k : ℝ) * Real.pi / ((n : ℝ) + 1)) := by
        rw [Real.sin_sub, Real.sin_add]
        ring
      have hs1 : Real.sin ((((k * ((j.val - 1) + 1) : ℕ)) : ℝ) * Real.pi /
          ((n : ℝ) + 1)) =
          2 * Real.sin ((((k * (j.val + 1) : ℕ)) : ℝ) * Real.pi / ((n : ℝ) + 1)) *
            Real.cos ((k : ℝ) * Real.pi / ((n : ℝ) + 1)) := by
        rw [hA]
        linear_combination hadd - h0
      rw [hvj j, hvj ⟨j.val - 1, h1⟩, hs1]
      ring
    · have hjlt : j.val + 1 < n := by omega
      have h1 : j.val - 1 < n := by omega
      have h2 : j.val + 1 < n := by omega
      have hne : Finset.univ.filter
          (fun w => (SimpleGraph.pathGraph n).Adj j w) =
          {⟨j.val - 1, h1⟩, ⟨j.val + 1, h2⟩} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        rw [SimpleGraph.pathGraph_adj]
        have hi := i.isLt
        constructor
        · intro h
          rcases h with h | h
          · right
            have hiv : i.val = j.val + 1 := by omega
            exact Fin.ext hiv
          · left
            have hiv : i.val = j.val - 1 := by omega
            exact Fin.ext hiv
        · intro h
          rcases h with h | h
          · right
            have hiv : i.val = j.val - 1 := congrArg Fin.val h
            omega
          · left
            have hiv : i.val = j.val + 1 := congrArg Fin.val h
            omega
      have hpair_ne : (⟨j.val - 1, h1⟩ : Fin n) ≠ ⟨j.val + 1, h2⟩ := by
        intro hcon
        have hcc : j.val - 1 = j.val + 1 := congrArg Fin.val hcon
        omega
      rw [hne, Finset.sum_pair hpair_ne]
      have hA : ((((k * ((j.val - 1) + 1) : ℕ)) : ℝ) * Real.pi / ((n : ℝ) + 1)) =
          ((((k * (j.val + 1) : ℕ)) : ℝ) * Real.pi / ((n : ℝ) + 1)) -
            ((k : ℝ) * Real.pi / ((n : ℝ) + 1)) := by
        rw [show (j.val - 1) + 1 = j.val by omega]
        push_cast
        ring
      have hB : ((((k * ((j.val + 1) + 1) : ℕ)) : ℝ) * Real.pi / ((n : ℝ) + 1)) =
          ((((k * (j.val + 1) : ℕ)) : ℝ) * Real.pi / ((n : ℝ) + 1)) +
            ((k : ℝ) * Real.pi / ((n : ℝ) + 1)) := by
        push_cast
        ring
      rw [hvj j, hvj ⟨j.val - 1, h1⟩, hvj ⟨j.val + 1, h2⟩, hA, hB,
        Real.sin_sub, Real.sin_add]
      ring

/-- The path Hückel eigenvalues for distinct `k` are distinct (for `β ≠ 0`). -/
theorem huckel_path_eigenvalues_distinct {n : ℕ} (hn : 0 < n) (α : ℝ) {β : ℝ} (hβ : β ≠ 0)
    {k l : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) (hl1 : 1 ≤ l) (hln : l ≤ n)
    (hkl : k ≠ l) :
    α + 2 * β * Real.cos (k * Real.pi / (n + 1)) ≠
      α + 2 * β * Real.cos (l * Real.pi / (n + 1)) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by
    have h := Nat.cast_nonneg (α := ℝ) n
    linarith
  have harg : ∀ m : ℕ, m ≤ n → (m * Real.pi / (n + 1)) ∈ Set.Icc (0 : ℝ) Real.pi := by
    intro m hm
    refine ⟨?_, ?_⟩
    · apply div_nonneg
      · exact mul_nonneg (Nat.cast_nonneg m) (le_of_lt hπ)
      · exact le_of_lt hn1
    · rw [div_le_iff₀ hn1]
      have hm' : (m : ℝ) ≤ (n : ℝ) + 1 := by
        have hle : m ≤ n + 1 := le_trans hm (Nat.le_succ n)
        exact_mod_cast hle
      calc (m : ℝ) * Real.pi = Real.pi * m := by ring
        _ ≤ Real.pi * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hm' (le_of_lt hπ)
  intro heq
  have hcos : Real.cos (k * Real.pi / (n + 1)) = Real.cos (l * Real.pi / (n + 1)) := by
    have h2β : (2 : ℝ) * β ≠ 0 := mul_ne_zero (by norm_num) hβ
    have hlin : (2 : ℝ) * β * Real.cos (k * Real.pi / (n + 1)) =
        (2 : ℝ) * β * Real.cos (l * Real.pi / (n + 1)) := by
      linear_combination heq
    exact mul_left_cancel₀ h2β hlin
  have hab : (k * Real.pi / (n + 1)) = (l * Real.pi / (n + 1)) :=
    Real.strictAntiOn_cos.injOn (harg k hkn) (harg l hln) hcos
  have hkl' : (k : ℝ) = (l : ℝ) := by
    have hn1' : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hn1
    rw [div_eq_div_iff hn1' hn1'] at hab
    have hmul2 : (k : ℝ) * Real.pi = (l : ℝ) * Real.pi := mul_right_cancel₀ hn1' hab
    exact mul_right_cancel₀ (ne_of_gt hπ) hmul2
  exact hkl (Nat.cast_injective hkl')

/-- Hückel cycle eigenvector (cosine family). -/
theorem huckel_cycle_eigenvector_cos {n : ℕ} (α β : ℝ) (k : ℕ) :
    huckelMatrix α β (SimpleGraph.cycleGraph (n + 3)) *ᵥ
      (fun j : Fin (n + 3) => Real.cos (2 * Real.pi * k * j.val / (n + 3))) =
      (α + 2 * β * Real.cos (2 * Real.pi * k / (n + 3))) •
      (fun j : Fin (n + 3) => Real.cos (2 * Real.pi * k * j.val / (n + 3))) := by
  set v : Fin (n + 3) → ℝ :=
    fun j => Real.cos (2 * Real.pi * k * j.val / (n + 3)) with hv
  have hvj : ∀ j : Fin (n + 3),
      v j = Real.cos (2 * Real.pi * k * j.val / (n + 3)) := fun j => rfl
  haveI : NeZero (n + 3) := ⟨by omega⟩
  have h1val : ((1 : Fin (n + 3))).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have hN3 : ((n : ℝ) + 3) ≠ 0 := by
    have hpos : (0 : ℝ) < (n : ℝ) + 3 := by positivity
    exact ne_of_gt hpos
  have h10ne : (1 : Fin (n + 3)) ≠ 0 := by
    intro hcon
    have hcc := congrArg Fin.val hcon
    rw [h1val, Fin.val_zero] at hcc
    exact one_ne_zero hcc
  funext j
  have hLHS := huckelMatrix_mulVec_apply α β (SimpleGraph.cycleGraph (n + 3)) v j
  rw [hLHS]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hne : Finset.univ.filter
      (fun w => (SimpleGraph.cycleGraph (n + 3)).Adj j w) = {j - 1, j + 1} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    have hadj : (SimpleGraph.cycleGraph (n + 3)).Adj j i ↔
        j - i = 1 ∨ i - j = 1 :=
      SimpleGraph.cycleGraph_adj (n := n + 1) (u := j) (v := i)
    rw [hadj, sub_eq_iff_eq_add', sub_eq_iff_eq_add', eq_sub_iff_add_eq, eq_comm]
  have hpair_ne : (j - 1 : Fin (n + 3)) ≠ j + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc j, left_eq_add]
    exact ne_of_beq_false rfl
  rw [hne, Finset.sum_pair hpair_ne]
  have hjN : j.val < n + 3 := j.isLt
  by_cases hj0 : j.val = 0
  · have huv : j.val + (1 : Fin (n + 3)).val < n + 3 := by rw [h1val, hj0]; omega
    have hplusval : (j + 1).val = 1 := by
      rw [Fin.val_add_eq_of_add_lt huv, h1val, hj0]
    have hjfin : j = 0 := Fin.ext hj0
    have hsubval : (j - 1).val = n + 2 := by
      rw [hjfin, zero_sub, Fin.val_neg, ite_eq_right h10ne, h1val]
      omega
    have hA0 : (2 * Real.pi * k * j.val / (n + 3)) = (0 : ℝ) := by
      rw [hj0]
      push_cast
      ring
    have hB : v (j + 1) = Real.cos (2 * Real.pi * k / (n + 3)) := by
      rw [hvj (j + 1), hplusval]
      congr 1
      push_cast
      ring
    have hC : v (j - 1) = Real.cos (2 * Real.pi * k / (n + 3)) := by
      rw [hvj (j - 1), hsubval]
      push_cast
      have harg : (2 * Real.pi * k * (n + 2) / (n + 3)) =
          ((k : ℝ) * (2 * Real.pi) - (2 * Real.pi * k / (n + 3))) := by
        push_cast
        field_simp [hN3]
        ring
      rw [harg, Real.cos_nat_mul_two_pi_sub]
    rw [hvj j, hA0, hB, hC, Real.cos_zero]
    ring
  · have hj0' : 0 < j.val := Nat.pos_of_ne_zero hj0
    have h1le : (1 : Fin (n + 3)) ≤ j := Fin.le_def.mpr (by rw [h1val]; omega)
    have h1le' : 1 ≤ j.val := hj0'
    have hsubval : (j - 1).val = j.val - 1 := by
      rw [Fin.sub_val_of_le h1le, h1val]
    by_cases hjlast : j.val + 1 = n + 3
    · have hplusval : (j + 1).val = 0 := by
        rw [Fin.val_add, h1val, hjlast, Nat.mod_self]
      have hm1 : v (j - 1) =
          2 * Real.cos (2 * Real.pi * k * j.val / (n + 3)) *
            Real.cos (2 * Real.pi * k / (n + 3)) - 1 := by
        have hA : (2 * Real.pi * k * (j.val - 1) / (n + 3)) =
            (2 * Real.pi * k * j.val / (n + 3)) - (2 * Real.pi * k / (n + 3)) := by
          ring
        have h0 : Real.cos ((2 * Real.pi * k * j.val / (n + 3)) +
            (2 * Real.pi * k / (n + 3))) = 1 := by
          have harg : ((2 * Real.pi * k * j.val / (n + 3)) +
              (2 * Real.pi * k / (n + 3))) = ((k : ℝ) * (2 * Real.pi)) := by
            rw [← add_div, div_eq_iff hN3]
            have hjlastR : (j.val : ℝ) + 1 = (n : ℝ) + 3 := by
              exact_mod_cast hjlast
            linear_combination (2 * Real.pi * (k : ℝ)) * hjlastR
          rw [harg, Real.cos_nat_mul_two_pi]
        have hadd : Real.cos ((2 * Real.pi * k * j.val / (n + 3)) -
            (2 * Real.pi * k / (n + 3))) +
            Real.cos ((2 * Real.pi * k * j.val / (n + 3)) +
            (2 * Real.pi * k / (n + 3))) =
            2 * Real.cos (2 * Real.pi * k * j.val / (n + 3)) *
              Real.cos (2 * Real.pi * k / (n + 3)) := by
          rw [Real.cos_sub, Real.cos_add]
          ring
        rw [hvj (j - 1), hsubval, Nat.cast_sub h1le', Nat.cast_one, hA]
        linear_combination hadd - h0
      have hp1 : v (j + 1) = 1 := by
        rw [hvj (j + 1), hplusval]
        have harg0 : (2 * Real.pi * k * ((0 : ℕ) : ℝ) / (n + 3)) = (0 : ℝ) := by
          push_cast
          ring
        rw [harg0, Real.cos_zero]
      rw [hvj j, hm1, hp1]
      ring
    · have hjlt : j.val + 1 < n + 3 := by omega
      have hplusval : (j + 1).val = j.val + 1 := by
        have huv : j.val + (1 : Fin (n + 3)).val < n + 3 := by rw [h1val]; omega
        rw [Fin.val_add_eq_of_add_lt huv, h1val]
      have hm1 : v (j - 1) =
          Real.cos ((2 * Real.pi * k * j.val / (n + 3)) -
            (2 * Real.pi * k / (n + 3))) := by
        rw [hvj (j - 1), hsubval]
        congr 1
        push_cast
        rw [Nat.cast_sub h1le']
        push_cast
        ring
      have hp1 : v (j + 1) =
          Real.cos ((2 * Real.pi * k * j.val / (n + 3)) +
            (2 * Real.pi * k / (n + 3))) := by
        rw [hvj (j + 1), hplusval]
        congr 1
        push_cast
        ring
      rw [hvj j, hm1, hp1, Real.cos_sub, Real.cos_add]
      ring

/-- Hückel cycle eigenvector (sine family). -/
theorem huckel_cycle_eigenvector_sin {n : ℕ} (α β : ℝ) (k : ℕ) :
    huckelMatrix α β (SimpleGraph.cycleGraph (n + 3)) *ᵥ
      (fun j : Fin (n + 3) => Real.sin (2 * Real.pi * k * j.val / (n + 3))) =
      (α + 2 * β * Real.cos (2 * Real.pi * k / (n + 3))) •
      (fun j : Fin (n + 3) => Real.sin (2 * Real.pi * k * j.val / (n + 3))) := by
  set v : Fin (n + 3) → ℝ :=
    fun j => Real.sin (2 * Real.pi * k * j.val / (n + 3)) with hv
  have hvj : ∀ j : Fin (n + 3),
      v j = Real.sin (2 * Real.pi * k * j.val / (n + 3)) := fun j => rfl
  haveI : NeZero (n + 3) := ⟨by omega⟩
  have h1val : ((1 : Fin (n + 3))).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have hN3 : ((n : ℝ) + 3) ≠ 0 := by
    have hpos : (0 : ℝ) < (n : ℝ) + 3 := by positivity
    exact ne_of_gt hpos
  have h10ne : (1 : Fin (n + 3)) ≠ 0 := by
    intro hcon
    have hcc := congrArg Fin.val hcon
    rw [h1val, Fin.val_zero] at hcc
    exact one_ne_zero hcc
  funext j
  have hLHS := huckelMatrix_mulVec_apply α β (SimpleGraph.cycleGraph (n + 3)) v j
  rw [hLHS]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hne : Finset.univ.filter
      (fun w => (SimpleGraph.cycleGraph (n + 3)).Adj j w) = {j - 1, j + 1} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    have hadj : (SimpleGraph.cycleGraph (n + 3)).Adj j i ↔
        j - i = 1 ∨ i - j = 1 :=
      SimpleGraph.cycleGraph_adj (n := n + 1) (u := j) (v := i)
    rw [hadj, sub_eq_iff_eq_add', sub_eq_iff_eq_add', eq_sub_iff_add_eq, eq_comm]
  have hpair_ne : (j - 1 : Fin (n + 3)) ≠ j + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc j, left_eq_add]
    exact ne_of_beq_false rfl
  rw [hne, Finset.sum_pair hpair_ne]
  have hjN : j.val < n + 3 := j.isLt
  by_cases hj0 : j.val = 0
  · have huv : j.val + (1 : Fin (n + 3)).val < n + 3 := by rw [h1val, hj0]; omega
    have hplusval : (j + 1).val = 1 := by
      rw [Fin.val_add_eq_of_add_lt huv, h1val, hj0]
    have hjfin : j = 0 := Fin.ext hj0
    have hsubval : (j - 1).val = n + 2 := by
      rw [hjfin, zero_sub, Fin.val_neg, ite_eq_right h10ne, h1val]
      omega
    have hA0 : (2 * Real.pi * k * j.val / (n + 3)) = (0 : ℝ) := by
      rw [hj0]
      push_cast
      ring
    have hB : v (j + 1) = Real.sin (2 * Real.pi * k / (n + 3)) := by
      rw [hvj (j + 1), hplusval]
      congr 1
      push_cast
      ring
    have hC : v (j - 1) = -Real.sin (2 * Real.pi * k / (n + 3)) := by
      rw [hvj (j - 1), hsubval]
      push_cast
      have harg : (2 * Real.pi * k * (n + 2) / (n + 3)) =
          ((k : ℝ) * (2 * Real.pi) - (2 * Real.pi * k / (n + 3))) := by
        push_cast
        field_simp [hN3]
        ring
      rw [harg]
      have hneg : ((k : ℝ) * (2 * Real.pi) - (2 * Real.pi * k / (n + 3))) =
          -((2 * Real.pi * k / (n + 3)) - (k : ℝ) * (2 * Real.pi)) := by ring
      rw [hneg, Real.sin_neg, Real.sin_sub_nat_mul_two_pi]
    rw [hvj j, hA0, hB, hC, Real.sin_zero]
    ring
  · have hj0' : 0 < j.val := Nat.pos_of_ne_zero hj0
    have h1le : (1 : Fin (n + 3)) ≤ j := Fin.le_def.mpr (by rw [h1val]; omega)
    have h1le' : 1 ≤ j.val := hj0'
    have hsubval : (j - 1).val = j.val - 1 := by
      rw [Fin.sub_val_of_le h1le, h1val]
    by_cases hjlast : j.val + 1 = n + 3
    · have hplusval : (j + 1).val = 0 := by
        rw [Fin.val_add, h1val, hjlast, Nat.mod_self]
      have hm1 : v (j - 1) =
          2 * Real.sin (2 * Real.pi * k * j.val / (n + 3)) *
            Real.cos (2 * Real.pi * k / (n + 3)) := by
        have hA : (2 * Real.pi * k * (j.val - 1) / (n + 3)) =
            (2 * Real.pi * k * j.val / (n + 3)) - (2 * Real.pi * k / (n + 3)) := by
          ring
        have h0 : Real.sin ((2 * Real.pi * k * j.val / (n + 3)) +
            (2 * Real.pi * k / (n + 3))) = 0 := by
          have harg : ((2 * Real.pi * k * j.val / (n + 3)) +
              (2 * Real.pi * k / (n + 3))) = ((k : ℝ) * (2 * Real.pi)) := by
            rw [← add_div, div_eq_iff hN3]
            have hjlastR : (j.val : ℝ) + 1 = (n : ℝ) + 3 := by
              exact_mod_cast hjlast
            linear_combination (2 * Real.pi * (k : ℝ)) * hjlastR
          rw [harg]
          have h2k : ((k : ℝ) * (2 * Real.pi)) = (((2 * k : ℕ)) : ℝ) * Real.pi := by
            push_cast
            ring
          rw [h2k, Real.sin_nat_mul_pi]
        have hadd : Real.sin ((2 * Real.pi * k * j.val / (n + 3)) -
            (2 * Real.pi * k / (n + 3))) +
            Real.sin ((2 * Real.pi * k * j.val / (n + 3)) +
            (2 * Real.pi * k / (n + 3))) =
            2 * Real.sin (2 * Real.pi * k * j.val / (n + 3)) *
              Real.cos (2 * Real.pi * k / (n + 3)) := by
          rw [Real.sin_sub, Real.sin_add]
          ring
        rw [hvj (j - 1), hsubval, Nat.cast_sub h1le', Nat.cast_one, hA]
        linear_combination hadd - h0
      have hp1 : v (j + 1) = 0 := by
        rw [hvj (j + 1), hplusval]
        have harg0 : (2 * Real.pi * k * ((0 : ℕ) : ℝ) / (n + 3)) = (0 : ℝ) := by
          push_cast
          ring
        rw [harg0, Real.sin_zero]
      rw [hvj j, hm1, hp1]
      ring
    · have hjlt : j.val + 1 < n + 3 := by omega
      have hplusval : (j + 1).val = j.val + 1 := by
        have huv : j.val + (1 : Fin (n + 3)).val < n + 3 := by rw [h1val]; omega
        rw [Fin.val_add_eq_of_add_lt huv, h1val]
      have hm1 : v (j - 1) =
          Real.sin ((2 * Real.pi * k * j.val / (n + 3)) -
            (2 * Real.pi * k / (n + 3))) := by
        rw [hvj (j - 1), hsubval]
        congr 1
        push_cast
        rw [Nat.cast_sub h1le']
        push_cast
        ring
      have hp1 : v (j + 1) =
          Real.sin ((2 * Real.pi * k * j.val / (n + 3)) +
            (2 * Real.pi * k / (n + 3))) := by
        rw [hvj (j + 1), hplusval]
        congr 1
        push_cast
        ring
      rw [hvj j, hm1, hp1, Real.sin_sub, Real.sin_add]
      ring

/-- Bipartite flip: on an even cycle, adjacency anticommutes with the
alternating-sign flip. -/
theorem cycleAdjacency_flip {n : ℕ} (hN : Even (n + 3)) (v : Fin (n + 3) → ℝ) :
    (SimpleGraph.cycleGraph (n + 3)).adjMatrix ℝ *ᵥ alternatingFlip v =
      -alternatingFlip ((SimpleGraph.cycleGraph (n + 3)).adjMatrix ℝ *ᵥ v) := by
  haveI : NeZero (n + 3) := ⟨by omega⟩
  have h1val : ((1 : Fin (n + 3))).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have h10ne : (1 : Fin (n + 3)) ≠ 0 := by
    intro hcon
    have hcc := congrArg Fin.val hcon
    rw [h1val, Fin.val_zero] at hcc
    exact one_ne_zero hcc
  funext j
  have hsum : ∀ w : Fin (n + 3) → ℝ,
      (((SimpleGraph.cycleGraph (n + 3)).adjMatrix ℝ) *ᵥ w) j =
        w (j - 1) + w (j + 1) := by
    intro w
    have hadj : (((SimpleGraph.cycleGraph (n + 3)).adjMatrix ℝ) *ᵥ w) j =
        ∑ u ∈ Finset.univ.filter
          (fun i => (SimpleGraph.cycleGraph (n + 3)).Adj j i), w u := by
      have h1 : (((SimpleGraph.cycleGraph (n + 3)).adjMatrix ℝ) *ᵥ w) j =
          ∑ i, (((SimpleGraph.cycleGraph (n + 3)).adjMatrix ℝ) j i) * w i := rfl
      rw [h1, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      rw [SimpleGraph.adjMatrix_apply]
      by_cases h : (SimpleGraph.cycleGraph (n + 3)).Adj j i <;> simp [h]
    have hne : Finset.univ.filter
        (fun i => (SimpleGraph.cycleGraph (n + 3)).Adj j i) = {j - 1, j + 1} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      have hadj' : (SimpleGraph.cycleGraph (n + 3)).Adj j i ↔
          j - i = 1 ∨ i - j = 1 :=
        SimpleGraph.cycleGraph_adj (n := n + 1) (u := j) (v := i)
      rw [hadj', sub_eq_iff_eq_add', sub_eq_iff_eq_add', eq_sub_iff_add_eq, eq_comm]
    have hpair_ne : (j - 1 : Fin (n + 3)) ≠ j + 1 := by
      simp only [ne_eq, sub_eq_iff_eq_add, add_assoc j, left_eq_add]
      exact ne_of_beq_false rfl
    rw [hadj, hne, Finset.sum_pair hpair_ne]
  have hLHS : (((SimpleGraph.cycleGraph (n + 3)).adjMatrix ℝ) *ᵥ alternatingFlip v) j =
      alternatingFlip v (j - 1) + alternatingFlip v (j + 1) := hsum _
  have hRHS : (-alternatingFlip
      (((SimpleGraph.cycleGraph (n + 3)).adjMatrix ℝ) *ᵥ v)) j =
      -((-1 : ℝ) ^ (j.val) * (v (j - 1) + v (j + 1))) := by
    have h1 : (((SimpleGraph.cycleGraph (n + 3)).adjMatrix ℝ) *ᵥ v) j =
        v (j - 1) + v (j + 1) := hsum v
    simp only [Pi.neg_apply, alternatingFlip]
    rw [h1]
  rw [hLHS, hRHS]
  simp only [alternatingFlip]
  have hp1 : (-1 : ℝ) ^ ((j + 1).val) = -(-1 : ℝ) ^ (j.val) := by
    by_cases hjlast : j.val + 1 = n + 3
    · have hplusval : (j + 1).val = 0 := by
        rw [Fin.val_add, h1val, hjlast, Nat.mod_self]
      rw [hplusval, pow_zero]
      have hodd : Odd j.val := by
        obtain ⟨t, ht⟩ := hN
        exact ⟨t - 1, by omega⟩
      rw [hodd.neg_one_pow]
      norm_num
    · have hjlt : j.val + 1 < n + 3 := by omega
      have hplusval : (j + 1).val = j.val + 1 := by
        have huv : j.val + (1 : Fin (n + 3)).val < n + 3 := by rw [h1val]; omega
        rw [Fin.val_add_eq_of_add_lt huv, h1val]
      rw [hplusval, pow_succ]
      ring
  have hm1 : (-1 : ℝ) ^ ((j - 1).val) = -(-1 : ℝ) ^ (j.val) := by
    by_cases hj0 : j.val = 0
    · have hjfin : j = 0 := Fin.ext hj0
      have hsubval : (j - 1).val = n + 2 := by
        rw [hjfin, zero_sub, Fin.val_neg, ite_eq_right h10ne, h1val]
        omega
      rw [hsubval, hj0, pow_zero]
      have hodd : Odd (n + 2) := by
        obtain ⟨t, ht⟩ := hN
        exact ⟨t - 1, by omega⟩
      rw [hodd.neg_one_pow]
    · have hj0' : 0 < j.val := Nat.pos_of_ne_zero hj0
      have h1le : (1 : Fin (n + 3)) ≤ j := Fin.le_def.mpr (by rw [h1val]; omega)
      have hsubval : (j - 1).val = j.val - 1 := by
        rw [Fin.sub_val_of_le h1le, h1val]
      rw [hsubval]
      rcases Nat.even_or_odd j.val with hev | hodd
      · have hodd' : Odd (j.val - 1) := by
          obtain ⟨s, hs⟩ := hev
          exact ⟨s - 1, by omega⟩
        rw [Even.neg_one_pow hev, Odd.neg_one_pow hodd']
      · have hev' : Even (j.val - 1) := by
          obtain ⟨s, hs⟩ := hodd
          exact ⟨s, by omega⟩
        rw [Odd.neg_one_pow hodd, Even.neg_one_pow hev']
        norm_num
  rw [hp1, hm1]
  ring

/-- Bipartite pairing of Hückel spectra: eigenvalue `E` pairs with `2 * α - E`. -/
theorem huckel_cycle_pairing {n : ℕ} (hN : Even (n + 3)) (α β : ℝ)
    {v : Fin (n + 3) → ℝ} {E : ℝ}
    (hEv : huckelMatrix α β (SimpleGraph.cycleGraph (n + 3)) *ᵥ v = E • v) :
    huckelMatrix α β (SimpleGraph.cycleGraph (n + 3)) *ᵥ alternatingFlip v =
      (2 * α - E) • alternatingFlip v := by
  have flip_smul : ∀ (a : ℝ) (x : Fin (n + 3) → ℝ),
      alternatingFlip (a • x) = a • alternatingFlip x := by
    intro a x
    funext j
    simp only [alternatingFlip, Pi.smul_apply, smul_eq_mul]
    ring
  have flip_neg : ∀ x : Fin (n + 3) → ℝ,
      alternatingFlip (-x) = -alternatingFlip x := by
    intro x
    funext j
    simp only [alternatingFlip, Pi.neg_apply]
    ring
  have hexpand : ∀ w : Fin (n + 3) → ℝ,
      huckelMatrix α β (SimpleGraph.cycleGraph (n + 3)) *ᵥ w =
        α • w + β • ((SimpleGraph.cycleGraph (n + 3)).adjMatrix ℝ *ᵥ w) := by
    intro w
    unfold huckelMatrix
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have hkey : β • (((SimpleGraph.cycleGraph (n + 3)).adjMatrix ℝ) *ᵥ v) =
      (E - α) • v := by
    have hEv' : α • v + β • (((SimpleGraph.cycleGraph (n + 3)).adjMatrix ℝ) *ᵥ v) =
        E • v := by
      rw [hexpand] at hEv
      exact hEv
    have h1 : α • v + β • (((SimpleGraph.cycleGraph (n + 3)).adjMatrix ℝ) *ᵥ v) -
        α • v = E • v - α • v :=
      congrArg (· - α • v) hEv'
    simp only [add_sub_cancel_left] at h1
    rw [h1, sub_smul]
  have hflip : β • (-alternatingFlip
      (((SimpleGraph.cycleGraph (n + 3)).adjMatrix ℝ) *ᵥ v)) =
      (-(E - α)) • alternatingFlip v := by
    rw [smul_neg, ← flip_smul _ _, hkey, flip_smul, ← neg_smul]
  rw [hexpand, cycleAdjacency_flip hN v, hflip, ← add_smul]
  congr 1
  ring

/-- Filtered card over `Fin N` equals the filtered card over `range N`. -/
private lemma filter_univ_fin_card_eq (N : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun k : Fin N => p k.val)).card =
      ((Finset.range N).filter p).card := by
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_filter]
  exact Fin.sum_univ_eq_sum_range (fun j => if p j then (1 : ℕ) else 0) N

/-- Counting: for `N = 4m + 2`, exactly `2m + 1` values of `k` have `cos > 0`. -/
theorem cycle_cos_pos_count_4m2 (m : ℕ) :
    (Finset.univ.filter (fun k : Fin (4 * m + 2) =>
      0 < Real.cos (2 * Real.pi * k.val / (4 * m + 2)))).card = 2 * m + 1 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hN : (0 : ℝ) < 4 * m + 2 := by positivity
  rw [filter_univ_fin_card_eq (4 * m + 2)
    (fun j : ℕ => 0 < Real.cos (2 * Real.pi * j / (4 * m + 2)))]
  have hset : (Finset.range (4 * m + 2)).filter
      (fun j : ℕ => 0 < Real.cos (2 * Real.pi * j / (4 * m + 2))) =
      Finset.range (m + 1) ∪ Finset.Ico (3 * m + 2) (4 * m + 2) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    constructor
    · rintro ⟨hjN, hcos⟩
      by_cases hj1 : j < m + 1
      · exact Or.inl hj1
      · right
        push Not at hj1
        refine ⟨?_, hjN⟩
        by_contra hj2
        push Not at hj2
        have hjle : j ≤ 3 * m + 1 := by omega
        have hBlo : Real.pi / 2 ≤ 2 * Real.pi * (j : ℝ) / (4 * m + 2) := by
          rw [le_div_iff₀ hN]
          have hj' : ((m : ℝ) + 1) ≤ j := by exact_mod_cast hj1
          have e1 : (Real.pi / 2) * (4 * (m : ℝ) + 2) =
              Real.pi * ((4 * m + 2) / 2) := by ring
          have e2 : (2 : ℝ) * Real.pi * j = Real.pi * (2 * j) := by ring
          rw [e1, e2, mul_le_mul_iff_right₀ hπ]
          linarith
        have hBhi : 2 * Real.pi * (j : ℝ) / (4 * m + 2) ≤ Real.pi + Real.pi / 2 := by
          rw [div_le_iff₀ hN]
          have hj' : (j : ℝ) ≤ 3 * m + 1 := by exact_mod_cast hjle
          have e1 : (2 : ℝ) * Real.pi * j = Real.pi * (2 * j) := by ring
          have e2 : (Real.pi + Real.pi / 2) * (4 * (m : ℝ) + 2) =
              Real.pi * ((3 / 2) * (4 * m + 2)) := by ring
          rw [e1, e2, mul_le_mul_iff_right₀ hπ]
          linarith
        have hle := Real.cos_nonpos_of_pi_div_two_le_of_le hBlo hBhi
        exact absurd hcos (not_lt_of_ge hle)
    · rintro (hj | ⟨hjlo, hjhi⟩)
      · refine ⟨?_, ?_⟩
        · omega
        · have hjle : j ≤ m := by omega
          have hx0 : (0 : ℝ) ≤ 2 * Real.pi * (j : ℝ) / (4 * m + 2) := by
            apply div_nonneg
            · exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hπ))
                (Nat.cast_nonneg j)
            · exact le_of_lt hN
          have hxlo : -(Real.pi / 2) < 2 * Real.pi * (j : ℝ) / (4 * m + 2) := by
            linarith
          have hxhi : 2 * Real.pi * (j : ℝ) / (4 * m + 2) < Real.pi / 2 := by
            rw [div_lt_iff₀ hN]
            have hj' : (j : ℝ) ≤ m := by exact_mod_cast hjle
            have e1 : (2 : ℝ) * Real.pi * j = Real.pi * (2 * j) := by ring
            have e2 : (Real.pi / 2) * (4 * (m : ℝ) + 2) =
                Real.pi * ((4 * m + 2) / 2) := by ring
            rw [e1, e2, mul_lt_mul_iff_right₀ hπ]
            linarith
          exact Real.cos_pos_of_mem_Ioo ⟨hxlo, hxhi⟩
      · refine ⟨?_, ?_⟩
        · omega
        · have hCup : 2 * Real.pi * (j : ℝ) / (4 * m + 2) < 2 * Real.pi := by
            rw [div_lt_iff₀ hN]
            have hj' : (j : ℝ) < 4 * m + 2 := by exact_mod_cast hjhi
            have h2π : (0 : ℝ) < 2 * Real.pi := by linarith
            have e1 : (2 : ℝ) * Real.pi * j = (2 * Real.pi) * j := by ring
            have e2 : (2 : ℝ) * Real.pi * (4 * (m : ℝ) + 2) =
                (2 * Real.pi) * (4 * m + 2) := by ring
            rw [e1, e2, mul_lt_mul_iff_right₀ h2π]
            exact hj'
          have hClo : 3 * Real.pi / 2 < 2 * Real.pi * (j : ℝ) / (4 * m + 2) := by
            rw [lt_div_iff₀ hN]
            have hj' : (3 : ℝ) * m + 2 ≤ j := by exact_mod_cast hjlo
            have e1 : (3 * Real.pi / 2) * (4 * (m : ℝ) + 2) =
                Real.pi * ((3 / 2) * (4 * m + 2)) := by ring
            have e2 : (2 : ℝ) * Real.pi * j = Real.pi * (2 * j) := by ring
            rw [e1, e2, mul_lt_mul_iff_right₀ hπ]
            linarith
          have hylo : -(Real.pi / 2) < 2 * Real.pi * (j : ℝ) / (4 * m + 2) - 2 * Real.pi := by
            linarith
          have hyhi : 2 * Real.pi * (j : ℝ) / (4 * m + 2) - 2 * Real.pi < Real.pi / 2 := by
            linarith
          have hcosy : (0 : ℝ) <
              Real.cos (2 * Real.pi * (j : ℝ) / (4 * m + 2) - 2 * Real.pi) :=
            Real.cos_pos_of_mem_Ioo ⟨hylo, hyhi⟩
          have hper : Real.cos (2 * Real.pi * (j : ℝ) / (4 * m + 2)) =
              Real.cos (2 * Real.pi * (j : ℝ) / (4 * m + 2) - 2 * Real.pi) :=
            (Real.cos_sub_two_pi _).symm
          rw [hper]
          exact hcosy
  rw [hset]
  have hdisj : Disjoint (Finset.range (m + 1)) (Finset.Ico (3 * m + 2) (4 * m + 2)) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Finset.mem_range, Finset.mem_Ico] at hj1 hj2
    omega
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_range, Nat.card_Ico]
  omega

/-- Zeros of `cos` on `[0, 2π]` are exactly `π/2` and `3π/2`. -/
private lemma cos_eq_zero_of_mem_Icc (x : ℝ) (hx0 : 0 ≤ x) (hx2 : x ≤ 2 * Real.pi)
    (h : Real.cos x = 0) : x = Real.pi / 2 ∨ x = 3 * Real.pi / 2 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmem : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨by linarith, by linarith⟩
  rcases le_total x Real.pi with hle | hle
  · left
    have hxmem : x ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hx0, hle⟩
    have heq : Real.cos x = Real.cos (Real.pi / 2) := by rw [h, Real.cos_pi_div_two]
    exact Real.strictAntiOn_cos.injOn hxmem hmem heq
  · right
    have hymem : (2 * Real.pi - x) ∈ Set.Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
    have heq : Real.cos (2 * Real.pi - x) = Real.cos (Real.pi / 2) := by
      rw [Real.cos_two_pi_sub, h, Real.cos_pi_div_two]
    have hy : 2 * Real.pi - x = Real.pi / 2 :=
      Real.strictAntiOn_cos.injOn hymem hmem heq
    linarith

/-- Counting: for `N = 4m`, `m ≥ 1`, exactly `2` values of `k` have `cos = 0`. -/
theorem cycle_cos_zero_count_4m {m : ℕ} (hm : 0 < m) :
    (Finset.univ.filter (fun k : Fin (4 * m) =>
      Real.cos (2 * Real.pi * k.val / (4 * m)) = 0)).card = 2 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hN : (0 : ℝ) < 4 * (m : ℝ) := by
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    linarith
  have hNe : ((4 : ℝ) * m) ≠ 0 := ne_of_gt hN
  have hiff : ∀ k : Fin (4 * m),
      (Real.cos (2 * Real.pi * k.val / (4 * m)) = 0) ↔ (k.val = m ∨ k.val = 3 * m) := by
    intro k
    constructor
    · intro hcos
      have hkN : (k.val : ℝ) < 4 * (m : ℝ) := by
        have h1 : (k.val : ℝ) < ((4 * m : ℕ) : ℝ) := by exact_mod_cast k.isLt
        have h2 : ((4 * m : ℕ) : ℝ) = 4 * (m : ℝ) := by push_cast; ring
        linarith
      have hk0 : (0 : ℝ) ≤ k.val := Nat.cast_nonneg k.val
      have hx0 : (0 : ℝ) ≤ 2 * Real.pi * k.val / (4 * m) := by
        apply div_nonneg
        · exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hπ)) hk0
        · exact le_of_lt hN
      have hx2 : 2 * Real.pi * k.val / (4 * m) ≤ 2 * Real.pi := by
        rw [div_le_iff₀ hN]
        have hkle : (k.val : ℝ) ≤ 4 * m := le_of_lt hkN
        have h2π : (0 : ℝ) ≤ 2 * Real.pi := by
          have hpi : (0 : ℝ) ≤ Real.pi := le_of_lt hπ
          linarith
        calc (2 : ℝ) * Real.pi * k.val = (2 * Real.pi) * k.val := by ring
          _ ≤ (2 * Real.pi) * (4 * m) := mul_le_mul_of_nonneg_left hkle h2π
          _ = 2 * Real.pi * (4 * m) := by ring
      rcases cos_eq_zero_of_mem_Icc _ hx0 hx2 hcos with hpi | h3pi
      · left
        have h2 : (2 : ℝ) * Real.pi * k.val = (Real.pi / 2) * (4 * m) :=
          (div_eq_iff hNe).mp hpi
        have h3 : Real.pi * (2 * k.val) = Real.pi * (2 * m) := by linear_combination h2
        have h4 : (2 : ℝ) * k.val = 2 * m := mul_left_cancel₀ (ne_of_gt hπ) h3
        have h5 : (k.val : ℝ) = (m : ℝ) := by linarith
        exact_mod_cast h5
      · right
        have h2 : (2 : ℝ) * Real.pi * k.val = (3 * Real.pi / 2) * (4 * m) :=
          (div_eq_iff hNe).mp h3pi
        have h3 : Real.pi * (2 * k.val) = Real.pi * (6 * m) := by linear_combination h2
        have h4 : (2 : ℝ) * k.val = 6 * m := mul_left_cancel₀ (ne_of_gt hπ) h3
        have h5 : (k.val : ℝ) = 3 * m := by linarith
        exact_mod_cast h5
    · intro hkm
      rcases hkm with hkm | hkm
      · have harg : 2 * Real.pi * k.val / (4 * m) = Real.pi / 2 := by
          rw [hkm, div_eq_iff hNe]
          ring
        rw [harg, Real.cos_pi_div_two]
      · have harg : 2 * Real.pi * k.val / (4 * m) = 3 * Real.pi / 2 := by
          rw [hkm]
          push_cast
          rw [div_eq_iff hNe]
          ring
        have hcos : Real.cos (3 * Real.pi / 2) = 0 := by
          have heq : (3 : ℝ) * Real.pi / 2 = 2 * Real.pi - Real.pi / 2 := by ring
          rw [heq, Real.cos_two_pi_sub, Real.cos_pi_div_two]
        rw [harg]
        exact hcos
  have hm4 : m < 4 * m := by omega
  have h3m4 : 3 * m < 4 * m := by omega
  have hset : Finset.univ.filter (fun k : Fin (4 * m) =>
      Real.cos (2 * Real.pi * k.val / (4 * m)) = 0) =
      {⟨m, hm4⟩, ⟨3 * m, h3m4⟩} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    rw [hiff k]
    constructor
    · intro h
      rcases h with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    · intro h
      rcases h with h | h
      · exact Or.inl (congrArg Fin.val h)
      · exact Or.inr (congrArg Fin.val h)
  rw [hset]
  apply Finset.card_pair
  intro hcon
  have hmul : m = 3 * m := congrArg Fin.val hcon
  omega

/-- For `N = 4m + 2` and `β < 0`, exactly `2m + 1 = N / 2` Hückel levels lie
strictly below `α`: the closed shell (spin-paired Aufbau filling of `N`
electrons uses exactly these orbitals), with a gap to the next level. -/
theorem huckel_bonding_count_4m2 (m : ℕ) (α : ℝ) {β : ℝ} (hβ : β < 0) :
    (Finset.univ.filter (fun k : Fin (4 * m + 2) =>
      α + 2 * β * Real.cos (2 * Real.pi * k.val / (4 * m + 2)) < α)).card =
      2 * m + 1 := by
  have h2β : (2 : ℝ) * β < 0 := by linarith
  have hiff : ∀ k : Fin (4 * m + 2),
      (α + 2 * β * Real.cos (2 * Real.pi * k.val / (4 * m + 2)) < α) ↔
      (0 < Real.cos (2 * Real.pi * k.val / (4 * m + 2))) := by
    intro k
    constructor
    · intro h
      have h' : (2 : ℝ) * β * Real.cos (2 * Real.pi * k.val / (4 * m + 2)) < 0 := by
        linarith
      by_contra hc
      push Not at hc
      have hnn : (0 : ℝ) ≤ (2 : ℝ) * β * Real.cos (2 * Real.pi * k.val / (4 * m + 2)) :=
        mul_nonneg_of_nonpos_of_nonpos (le_of_lt h2β) hc
      linarith
    · intro h
      have h' : (2 : ℝ) * β * Real.cos (2 * Real.pi * k.val / (4 * m + 2)) <
          (2 : ℝ) * β * 0 :=
        mul_lt_mul_of_neg_left h h2β
      rw [mul_zero] at h'
      linarith
  have hset : Finset.univ.filter (fun k : Fin (4 * m + 2) =>
      α + 2 * β * Real.cos (2 * Real.pi * k.val / (4 * m + 2)) < α) =
      Finset.univ.filter (fun k : Fin (4 * m + 2) =>
        0 < Real.cos (2 * Real.pi * k.val / (4 * m + 2))) := by
    apply Finset.filter_congr
    intro k _
    exact hiff k
  rw [hset]
  exact cycle_cos_pos_count_4m2 m

/-- For `N = 4m`, `m ≥ 1`, exactly `2` Hückel levels equal `α`: the Fermi-level
degeneracy of the `4m` case, made explicit. -/
theorem huckel_degenerate_count_4m {m : ℕ} (hm : 0 < m) (α β : ℝ) (hβ : β ≠ 0) :
    (Finset.univ.filter (fun k : Fin (4 * m) =>
      α + 2 * β * Real.cos (2 * Real.pi * k.val / (4 * m)) = α)).card = 2 := by
  have hiff : ∀ k : Fin (4 * m),
      (α + 2 * β * Real.cos (2 * Real.pi * k.val / (4 * m)) = α) ↔
      (Real.cos (2 * Real.pi * k.val / (4 * m)) = 0) := by
    intro k
    constructor
    · intro h
      have h2β : (2 : ℝ) * β ≠ 0 := mul_ne_zero (by norm_num) hβ
      have hlin : (2 : ℝ) * β * Real.cos (2 * Real.pi * k.val / (4 * m)) =
          (2 : ℝ) * β * 0 := by
        linear_combination h
      exact mul_left_cancel₀ h2β hlin
    · intro h
      rw [h]
      ring
  have hset : Finset.univ.filter (fun k : Fin (4 * m) =>
      α + 2 * β * Real.cos (2 * Real.pi * k.val / (4 * m)) = α) =
      Finset.univ.filter (fun k : Fin (4 * m) =>
        Real.cos (2 * Real.pi * k.val / (4 * m)) = 0) := by
    apply Finset.filter_congr
    intro k _
    exact hiff k
  rw [hset]
  exact cycle_cos_zero_count_4m hm

/-- 2×2 LCAO secular determinant factorization. `H = !![α, β; β, α]`,
overlap `Smat = !![1, S; S, 1]`. -/
theorem lcao_det (α β S E : ℝ) (hS : S ^ 2 ≠ 1) :
    ((!![α, β; β, α] : Matrix (Fin 2) (Fin 2) ℝ) -
      E • (!![1, S; S, 1] : Matrix (Fin 2) (Fin 2) ℝ)).det =
      (1 - S ^ 2) * (E - (α + β) / (1 + S)) * (E - (α - β) / (1 - S)) := by
  have h1 : (1 : ℝ) + S ≠ 0 := by
    intro h
    apply hS
    have hSeq : S = -1 := by linarith
    rw [hSeq]
    norm_num
  have h2 : (1 : ℝ) - S ≠ 0 := by
    intro h
    apply hS
    have hSeq : S = 1 := by linarith
    rw [hSeq]
    norm_num
  simp [Matrix.det_fin_two]
  field_simp
  ring

/-- The LCAO energies `(α ± β) / (1 ± S)` annihilate the secular determinant. -/
theorem lcao_energies_are_roots (α β S : ℝ) (hS1 : S ≠ 1) (hS2 : S ≠ -1) :
    ((!![α, β; β, α] : Matrix (Fin 2) (Fin 2) ℝ) -
      ((α + β) / (1 + S)) • (!![1, S; S, 1] : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 ∧
    ((!![α, β; β, α] : Matrix (Fin 2) (Fin 2) ℝ) -
      ((α - β) / (1 - S)) • (!![1, S; S, 1] : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 := by
  have hS : S ^ 2 ≠ 1 := by
    intro h
    have hfact : (S - 1) * (S + 1) = 0 := by
      have hring : (S - 1) * (S + 1) = S ^ 2 - 1 := by ring
      rw [hring]
      linarith [h]
    have hor := mul_eq_zero.mp hfact
    cases hor with
    | inl h1 =>
      apply hS1
      linarith
    | inr h2 =>
      apply hS2
      linarith
  constructor
  · rw [lcao_det α β S _ hS]
    simp
  · rw [lcao_det α β S _ hS]
    simp

end PhyslibExt.Chemistry.VariationalPerturbationHuckel
