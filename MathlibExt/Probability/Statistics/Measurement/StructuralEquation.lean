/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Structural equations for DAG models and Gaussian covariance-fit discrepancy

Nilpotency of DAG-supported coefficient matrices with the finite geometric
series inverse of `1 - B` (D07.2), and nonnegativity with the equality case
of the Gaussian covariance-fit discrepancy (D07.3).
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Measurement

/-- Path-counting estimate: a nonzero entry of `B ^ k` spans at least `k`
topological levels (Drton, arXiv:1612.05994). -/
private theorem pow_entry_ne_zero_le_of_topologicalOrder
    {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]
    (B : Matrix V V R) (ord : V → ℕ)
    (hB : ∀ i j, B i j ≠ 0 → ord j < ord i) (k : ℕ) (i j : V) :
    (B ^ k) i j ≠ 0 → ord j + k ≤ ord i := by
  induction k generalizing i j with
  | zero =>
    intro h
    rw [pow_zero, Matrix.one_apply] at h
    have hij : i = j := by
      by_contra hne
      simp [hne] at h
    subst hij
    omega
  | succ k ih =>
    intro h
    rw [pow_succ, Matrix.mul_apply] at h
    have hex : ∃ l ∈ (Finset.univ : Finset V), (B ^ k) i l * B l j ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h (Finset.sum_eq_zero hc)
    obtain ⟨l, _, hl⟩ := hex
    have h1 : (B ^ k) i l ≠ 0 := fun hz => hl (by rw [hz, zero_mul])
    have h2 : B l j ≠ 0 := fun hz => hl (by rw [hz, mul_zero])
    have g1 := hB l j h2
    have g2 := ih i l h1
    omega

/-- Nilpotency of DAG-supported coefficient matrices: `B ^ Fintype.card V = 0`
when parents precede children in `ord` (Drton, arXiv:1612.05994). -/
theorem pow_card_eq_zero_of_topologicalOrder
    {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]
    (B : Matrix V V R) (ord : V → ℕ)
    (hord : ∀ v, ord v < Fintype.card V)
    (hB : ∀ i j, B i j ≠ 0 → ord j < ord i) :
    B ^ Fintype.card V = 0 := by
  ext i j
  simp only [Matrix.zero_apply]
  by_contra h
  have hle := pow_entry_ne_zero_le_of_topologicalOrder B ord hB _ i j h
  have hi := hord i
  omega

/-- Higher powers vanish too: `B ^ m = 0` for `Fintype.card V ≤ m`
(Drton, arXiv:1612.05994). -/
theorem pow_eq_zero_of_topologicalOrder
    {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]
    (B : Matrix V V R) (ord : V → ℕ)
    (hord : ∀ v, ord v < Fintype.card V)
    (hB : ∀ i j, B i j ≠ 0 → ord j < ord i) (m : ℕ)
    (hm : Fintype.card V ≤ m) :
    B ^ m = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add, pow_card_eq_zero_of_topologicalOrder B ord hord hB, zero_mul]

/-- The finite geometric series `∑ k ∈ Finset.range (Fintype.card V), B ^ k` is a
two-sided inverse of `1 - B` (Drton, arXiv:1612.05994). -/
theorem one_sub_mul_sum_pow_of_topologicalOrder
    {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]
    (B : Matrix V V R) (ord : V → ℕ)
    (hord : ∀ v, ord v < Fintype.card V)
    (hB : ∀ i j, B i j ≠ 0 → ord j < ord i) :
    (1 - B) * ∑ k ∈ Finset.range (Fintype.card V), B ^ k = 1 ∧
      (∑ k ∈ Finset.range (Fintype.card V), B ^ k) * (1 - B) = 1 := by
  have hcard : B ^ Fintype.card V = 0 :=
    pow_card_eq_zero_of_topologicalOrder B ord hord hB
  have hsum : (∑ k ∈ Finset.range (Fintype.card V), B ^ k) =
      ∑ i ∈ Finset.range (Fintype.card V),
        (1 : Matrix V V R) ^ i * B ^ (Fintype.card V - 1 - i) := by
    rw [← Finset.sum_range_reflect (fun k => B ^ k) (Fintype.card V)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp
  have hcomm : Commute (1 : Matrix V V R) B := Commute.one_left B
  have hmul := Commute.mul_geom_sum₂ hcomm (Fintype.card V)
  have hgeom := Commute.geom_sum₂_mul hcomm (Fintype.card V)
  rw [hsum]
  rw [hcard, one_pow, sub_zero] at hmul hgeom
  exact ⟨hmul, hgeom⟩

/-- `(1 - B).det` is a unit when `B` is DAG-supported
(Drton, arXiv:1612.05994). -/
theorem isUnit_det_one_sub_of_topologicalOrder
    {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]
    (B : Matrix V V R) (ord : V → ℕ)
    (hord : ∀ v, ord v < Fintype.card V)
    (hB : ∀ i j, B i j ≠ 0 → ord j < ord i) :
    IsUnit (1 - B).det :=
  Matrix.isUnit_det_of_right_inverse
    (one_sub_mul_sum_pow_of_topologicalOrder B ord hord hB).1

/-- `(1 - B)⁻¹` is the finite geometric series for DAG-supported `B`
(Drton, arXiv:1612.05994). -/
theorem inv_one_sub_eq_sum_pow_of_topologicalOrder
    {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]
    (B : Matrix V V R) (ord : V → ℕ)
    (hord : ∀ v, ord v < Fintype.card V)
    (hB : ∀ i j, B i j ≠ 0 → ord j < ord i) :
    (1 - B)⁻¹ = ∑ k ∈ Finset.range (Fintype.card V), B ^ k :=
  Matrix.inv_eq_right_inv
    (one_sub_mul_sum_pow_of_topologicalOrder B ord hord hB).1

open scoped MatrixOrder

/-- Spectral square root: every positive definite real matrix factors as
`R * R` with `R` Hermitian and invertible. -/
private theorem exists_sqrt_of_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℝ} (hC : C.PosDef) :
    ∃ R : Matrix ι ι ℝ, R * R = C ∧ R.IsHermitian ∧ IsUnit R.det := by
  have hH : C.IsHermitian := hC.1
  have hpos : ∀ i, 0 < hH.eigenvalues i := fun i => hC.eigenvalues_pos i
  set s : ι → ℝ := fun i => Real.sqrt (hH.eigenvalues i) with hs
  have hsq : ∀ i, s i * s i = hH.eigenvalues i :=
    fun i => Real.mul_self_sqrt (le_of_lt (hpos i))
  have hAB : (fun i => s i * s i) = hH.eigenvalues := funext (fun i => hsq i)
  have hmul : (Unitary.conjStarAlgAut ℝ _ hH.eigenvectorUnitary)
      (Matrix.diagonal s) *
      (Unitary.conjStarAlgAut ℝ _ hH.eigenvectorUnitary)
        (Matrix.diagonal s) =
      (Unitary.conjStarAlgAut ℝ _ hH.eigenvectorUnitary)
        (Matrix.diagonal (hH.eigenvalues)) := by
    rw [← map_mul, Matrix.diagonal_mul_diagonal, hAB]
  have hspec := hH.spectral_theorem
  have hRR : (Unitary.conjStarAlgAut ℝ _ hH.eigenvectorUnitary)
      (Matrix.diagonal s) *
      (Unitary.conjStarAlgAut ℝ _ hH.eigenvectorUnitary)
        (Matrix.diagonal s) = C :=
    hmul.trans hspec.symm
  have hstar : star (Matrix.diagonal s) = Matrix.diagonal s := by
    ext i j
    simp only [Matrix.star_apply, Matrix.diagonal_apply]
    by_cases hij : j = i
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  have hRH : ((Unitary.conjStarAlgAut ℝ _ hH.eigenvectorUnitary)
      (Matrix.diagonal s)).IsHermitian := by
    have hRstar : star ((Unitary.conjStarAlgAut ℝ _ hH.eigenvectorUnitary)
        (Matrix.diagonal s)) = (Unitary.conjStarAlgAut ℝ _
        hH.eigenvectorUnitary) (Matrix.diagonal s) := by
      rw [← map_star, hstar]
    exact hRstar
  have hRu : IsUnit (((Unitary.conjStarAlgAut ℝ _ hH.eigenvectorUnitary)
      (Matrix.diagonal s)).det) := by
    have hsqd : (((Unitary.conjStarAlgAut ℝ _ hH.eigenvectorUnitary)
        (Matrix.diagonal s)).det) *
        (((Unitary.conjStarAlgAut ℝ _ hH.eigenvectorUnitary)
        (Matrix.diagonal s)).det) = C.det := by
      rw [← Matrix.det_mul, hRR]
    have hCne : C.det ≠ 0 := ne_of_gt hC.det_pos
    have hRne : ((Unitary.conjStarAlgAut ℝ _ hH.eigenvectorUnitary)
        (Matrix.diagonal s)).det ≠ 0 := by
      intro hz
      apply hCne
      rw [← hsqd, hz, zero_mul]
    exact isUnit_iff_ne_zero.mpr hRne
  exact ⟨_, hRR, hRH, hRu⟩

/-- Log-determinant/trace inequality for positive definite matrices. -/
private theorem log_det_le_trace_sub_card_of_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : X.PosDef) :
    Real.log X.det ≤ X.trace - Fintype.card ι := by
  have hH : X.IsHermitian := hX.1
  have hpos : ∀ i, 0 < hH.eigenvalues i := fun i => hX.eigenvalues_pos i
  have hdet : X.det = ∏ i, hH.eigenvalues i := hH.det_eq_prod_eigenvalues
  have htr : X.trace = ∑ i, hH.eigenvalues i := hH.trace_eq_sum_eigenvalues
  have hlog : Real.log X.det = ∑ i, Real.log (hH.eigenvalues i) := by
    rw [hdet]
    exact Real.log_prod (fun i _ => ne_of_gt (hpos i))
  rw [hlog, htr]
  have hle : ∑ i, Real.log (hH.eigenvalues i) ≤ ∑ i, (hH.eigenvalues i - 1) :=
    Finset.sum_le_sum (fun i _ => Real.log_le_sub_one_of_pos (hpos i))
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_one] at hle
  exact hle

/-- Equality case of the log-determinant/trace inequality. -/
private theorem eq_one_of_log_det_eq_trace_sub_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : X.PosDef)
    (h : Real.log X.det = X.trace - Fintype.card ι) :
    X = 1 := by
  have hH : X.IsHermitian := hX.1
  have hpos : ∀ i, 0 < hH.eigenvalues i := fun i => hX.eigenvalues_pos i
  have hdet : X.det = ∏ i, hH.eigenvalues i := hH.det_eq_prod_eigenvalues
  have htr : X.trace = ∑ i, hH.eigenvalues i := hH.trace_eq_sum_eigenvalues
  have hlog : Real.log X.det = ∑ i, Real.log (hH.eigenvalues i) := by
    rw [hdet]
    exact Real.log_prod (fun i _ => ne_of_gt (hpos i))
  rw [hlog, htr] at h
  have hsum : ∑ i, (hH.eigenvalues i - 1 - Real.log (hH.eigenvalues i)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_one]
    linarith [h]
  have hzero : ∀ i ∈ (Finset.univ : Finset ι),
      hH.eigenvalues i - 1 - Real.log (hH.eigenvalues i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by
      have := Real.log_le_sub_one_of_pos (hpos i)
      linarith)).mp hsum
  have hei : ∀ i, hH.eigenvalues i = 1 := by
    intro i
    by_contra hne
    have hlt := Real.log_lt_sub_one_of_pos (hpos i) hne
    have hz := hzero i (Finset.mem_univ i)
    linarith
  have he1 : RCLike.ofReal ∘ hH.eigenvalues = (1 : ι → ℝ) := funext (fun i => by
    simp only [Function.comp_apply]
    rw [hei i]
    exact RCLike.ofReal_one)
  rw [hH.spectral_theorem, he1, Matrix.diagonal_one', map_one]

/-- Gaussian covariance-fit discrepancy for sample `S` and model `C`
(Bartlett, STAT 241A (2007), Lemma 2). Values outside `Matrix.PosDef` are
meaningless: the definition is total via `Real.log` of a nonpositive determinant
and `C⁻¹` of a singular matrix. -/
noncomputable def gaussianDiscrepancy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S C : Matrix ι ι ℝ) : ℝ :=
  Real.log C.det + (S * C⁻¹).trace - Real.log S.det - Fintype.card ι

/-- The discrepancy is nonnegative for positive definite `S`, `C`
(Bartlett, STAT 241A (2007), Lemma 2). -/
theorem gaussianDiscrepancy_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S C : Matrix ι ι ℝ} (hS : S.PosDef) (hC : C.PosDef) :
    0 ≤ gaussianDiscrepancy S C := by
  obtain ⟨R, hRR, hRH, hRu⟩ := exists_sqrt_of_posDef hC
  have hRinv : (R⁻¹).IsHermitian := hRH.inv
  have eB : (R⁻¹).det * R.det = 1 := Matrix.det_nonsing_inv_mul_det R hRu
  have hinj : Function.Injective (R⁻¹).mulVec :=
    Matrix.mulVec_injective_of_det_ne_zero (left_ne_zero_of_mul_eq_one eB)
  have hTpos : (R⁻¹ * S * R⁻¹).PosDef := by
    have h := hS.conjTranspose_mul_mul_same (B := R⁻¹) hinj
    rwa [hRinv.eq] at h
  have eT : (R⁻¹ * S * R⁻¹).det = (R⁻¹).det * S.det * (R⁻¹).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
  have eC : R.det * R.det = C.det := by
    rw [← Matrix.det_mul, hRR]
  have hdet : (R⁻¹ * S * R⁻¹).det * C.det = S.det := by
    linear_combination C.det * eT -
      (S.det * (R⁻¹).det * (R⁻¹).det) * eC +
      (S.det * ((R⁻¹).det * R.det + 1)) * eB
  have hCinv : R⁻¹ * R⁻¹ = C⁻¹ := by
    rw [← Matrix.mul_inv_rev, hRR]
  have htr : (R⁻¹ * S * R⁻¹).trace = (S * C⁻¹).trace := by
    calc (R⁻¹ * S * R⁻¹).trace
        = (R⁻¹ * (R⁻¹ * S)).trace := Matrix.trace_mul_comm _ _
      _ = ((R⁻¹ * R⁻¹) * S).trace := by rw [← Matrix.mul_assoc]
      _ = (C⁻¹ * S).trace := by rw [hCinv]
      _ = (S * C⁻¹).trace := Matrix.trace_mul_comm _ _
  have hmain := log_det_le_trace_sub_card_of_posDef hTpos
  have hSpos : 0 < S.det := hS.det_pos
  have hCpos : 0 < C.det := hC.det_pos
  have hmul : 0 < C.det * (R⁻¹ * S * R⁻¹).det := by
    rw [mul_comm, hdet]
    exact hSpos
  have hTpos' : 0 < (R⁻¹ * S * R⁻¹).det :=
    pos_of_mul_pos_right hmul (le_of_lt hCpos)
  have hlog : Real.log S.det =
      Real.log (R⁻¹ * S * R⁻¹).det + Real.log C.det := by
    rw [← hdet]
    exact Real.log_mul (ne_of_gt hTpos') (ne_of_gt hCpos)
  unfold gaussianDiscrepancy
  rw [hlog, ← htr]
  linarith [hmain]

/-- The discrepancy vanishes at the fit when `C.det` is a unit. -/
theorem gaussianDiscrepancy_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℝ} (hC : IsUnit C.det) :
    gaussianDiscrepancy C C = 0 := by
  unfold gaussianDiscrepancy
  rw [Matrix.mul_nonsing_inv C hC, Matrix.trace_one]
  ring

/-- The discrepancy is zero exactly at `S = C`
(Bartlett, STAT 241A (2007), Lemma 2). -/
theorem gaussianDiscrepancy_eq_zero_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S C : Matrix ι ι ℝ} (hS : S.PosDef) (hC : C.PosDef) :
    (gaussianDiscrepancy S C = 0 ↔ S = C) := by
  constructor
  · intro hzero
    obtain ⟨R, hRR, hRH, hRu⟩ := exists_sqrt_of_posDef hC
    have hRinv : (R⁻¹).IsHermitian := hRH.inv
    have eB : (R⁻¹).det * R.det = 1 := Matrix.det_nonsing_inv_mul_det R hRu
    have hinj : Function.Injective (R⁻¹).mulVec :=
      Matrix.mulVec_injective_of_det_ne_zero (left_ne_zero_of_mul_eq_one eB)
    have hTpos : (R⁻¹ * S * R⁻¹).PosDef := by
      have h := hS.conjTranspose_mul_mul_same (B := R⁻¹) hinj
      rwa [hRinv.eq] at h
    have eT : (R⁻¹ * S * R⁻¹).det = (R⁻¹).det * S.det * (R⁻¹).det := by
      rw [Matrix.det_mul, Matrix.det_mul]
    have eC : R.det * R.det = C.det := by
      rw [← Matrix.det_mul, hRR]
    have hdet : (R⁻¹ * S * R⁻¹).det * C.det = S.det := by
      linear_combination C.det * eT -
        (S.det * (R⁻¹).det * (R⁻¹).det) * eC +
        (S.det * ((R⁻¹).det * R.det + 1)) * eB
    have hCinv : R⁻¹ * R⁻¹ = C⁻¹ := by
      rw [← Matrix.mul_inv_rev, hRR]
    have htr : (R⁻¹ * S * R⁻¹).trace = (S * C⁻¹).trace := by
      calc (R⁻¹ * S * R⁻¹).trace
          = (R⁻¹ * (R⁻¹ * S)).trace := Matrix.trace_mul_comm _ _
        _ = ((R⁻¹ * R⁻¹) * S).trace := by rw [← Matrix.mul_assoc]
        _ = (C⁻¹ * S).trace := by rw [hCinv]
        _ = (S * C⁻¹).trace := Matrix.trace_mul_comm _ _
    have hSpos : 0 < S.det := hS.det_pos
    have hCpos : 0 < C.det := hC.det_pos
    have hmul : 0 < C.det * (R⁻¹ * S * R⁻¹).det := by
      rw [mul_comm, hdet]
      exact hSpos
    have hTpos' : 0 < (R⁻¹ * S * R⁻¹).det :=
      pos_of_mul_pos_right hmul (le_of_lt hCpos)
    have hlog : Real.log S.det =
        Real.log (R⁻¹ * S * R⁻¹).det + Real.log C.det := by
      rw [← hdet]
      exact Real.log_mul (ne_of_gt hTpos') (ne_of_gt hCpos)
    unfold gaussianDiscrepancy at hzero
    rw [hlog, ← htr] at hzero
    have heq : Real.log (R⁻¹ * S * R⁻¹).det =
        (R⁻¹ * S * R⁻¹).trace - Fintype.card ι := by
      linarith [hzero]
    have hT1 := eq_one_of_log_det_eq_trace_sub_card hTpos heq
    have hR1 : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRu
    have hR2 : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRu
    have hS : S = R * (R⁻¹ * S * R⁻¹) * R := by
      simp only [mul_assoc]
      rw [hR2, mul_one, ← Matrix.mul_assoc, hR1, one_mul]
    rw [hT1, mul_one] at hS
    rw [hS, hRR]
  · intro hSC
    rw [hSC]
    exact gaussianDiscrepancy_self
      (isUnit_iff_ne_zero.mpr (ne_of_gt hC.det_pos))

end MathlibExt.Probability.Statistics.Measurement

end
