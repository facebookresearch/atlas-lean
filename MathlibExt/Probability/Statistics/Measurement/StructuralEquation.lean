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
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import MathlibExt.LinearAlgebra.Matrix.LogDetTrace

/-!
# Structural equations for DAG models and Gaussian covariance-fit discrepancy

Nilpotency of DAG-supported coefficient matrices with the finite geometric
series inverse of `1 - B` (D07.2), and nonnegativity with the equality case
of the Gaussian covariance-fit discrepancy (D07.3). The discrepancy results are
corollaries of the log-determinant/trace inequality
`Matrix.PosDef.log_det_mul_le_trace` and its equality case
`Matrix.PosDef.mul_eq_one_of_log_det_eq_trace`, applied to `S` and `C⁻¹`.

Three-time-point linear-growth covariance identification (D08.1): the
Intercept/Slope loading matrix `growthLoading` with closed-form recovery of
the intercept/slope (co)variances and error variances from the model
covariance (Duncan and Duncan (2009)).
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
  have h := hS.log_det_mul_le_trace hC.inv
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
    Real.log_mul hS.det_pos.ne' (inv_ne_zero hC.det_pos.ne'), Real.log_inv] at h
  unfold gaussianDiscrepancy
  linarith

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
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.mpr hC.det_pos.ne'
  constructor
  · intro hzero
    have hlog : Real.log (S.det * C⁻¹.det) = (S * C⁻¹).trace - Fintype.card ι := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
        Real.log_mul hS.det_pos.ne' (inv_ne_zero hC.det_pos.ne'), Real.log_inv]
      unfold gaussianDiscrepancy at hzero
      linarith
    have h := congrArg (C * ·) (hS.mul_eq_one_of_log_det_eq_trace hC.inv hlog)
    simpa only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv C hCu, Matrix.one_mul,
      Matrix.mul_one] using h
  · intro hSC
    rw [hSC]
    exact gaussianDiscrepancy_self hCu

open scoped Matrix

/-- Linear-growth factor loading matrix for three equally spaced time points
(Duncan and Duncan (2009), Figure 2): Intercept loadings `1, 1, 1`, Slope
loadings `0, 1, 2`. -/
def growthLoading : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 1, 1; 1, 2]

/-- Model covariance entries for the three-time-point linear growth model:
with random intercept/slope covariance `G` and uncorrelated errors `θ`, the
`(s, t)` entry of `growthLoading * G * growthLoadingᵀ + diagonal θ` is
`G 0 0 + (s + t) * G 0 1 + s * t * G 1 1`, plus `θ s` on the diagonal
(Duncan and Duncan (2009)). -/
theorem growthLoading_cov_apply
    (G : Matrix (Fin 2) (Fin 2) ℝ) (hG : G.IsSymm)
    (θ : Fin 3 → ℝ) (s t : Fin 3) :
    ((growthLoading * G * growthLoadingᵀ + Matrix.diagonal θ :
      Matrix (Fin 3) (Fin 3) ℝ)) s t
      = G 0 0 + ((s : ℝ) + (t : ℝ)) * G 0 1
        + (s : ℝ) * (t : ℝ) * G 1 1
        + (if s = t then θ s else 0) := by
  have h10 : G 1 0 = G 0 1 := hG.apply 0 1
  have e0 : ∀ w : Fin 3, growthLoading w 0 = 1 := by
    intro w
    fin_cases w <;> simp [growthLoading]
  have e1 : ∀ w : Fin 3, growthLoading w 1 = (w : ℝ) := by
    intro w
    fin_cases w <;> simp [growthLoading]
  have hLG : ∀ (u : Fin 3) (k : Fin 2),
      ((growthLoading * G : Matrix (Fin 3) (Fin 2) ℝ)) u k
        = G 0 k + (u : ℝ) * G 1 k := by
    intro u k
    rw [Matrix.mul_apply, Fin.sum_univ_two, e0 u, e1 u, one_mul]
  rw [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, hLG s 0, hLG s 1,
    Matrix.transpose_apply, Matrix.transpose_apply, e0 t, e1 t, h10,
    Matrix.diagonal_apply]
  ring

/-- Closed-form recovery of the growth parameters from the model covariance
(Duncan and Duncan (2009)): the intercept/slope (co)variances from the
off-diagonal entries, each error variance by subtraction. -/
theorem growth_recover
    (G : Matrix (Fin 2) (Fin 2) ℝ) (hG : G.IsSymm)
    (θ : Fin 3 → ℝ) :
    G 0 1 = ((growthLoading * G * growthLoadingᵀ + Matrix.diagonal θ :
      Matrix (Fin 3) (Fin 3) ℝ)) 0 2
      - ((growthLoading * G * growthLoadingᵀ + Matrix.diagonal θ :
        Matrix (Fin 3) (Fin 3) ℝ)) 0 1
    ∧ G 0 0 = 2 * ((growthLoading * G * growthLoadingᵀ + Matrix.diagonal θ :
        Matrix (Fin 3) (Fin 3) ℝ)) 0 1
      - ((growthLoading * G * growthLoadingᵀ + Matrix.diagonal θ :
        Matrix (Fin 3) (Fin 3) ℝ)) 0 2
    ∧ G 1 1 = ((((growthLoading * G * growthLoadingᵀ + Matrix.diagonal θ :
        Matrix (Fin 3) (Fin 3) ℝ)) 1 2
      + ((growthLoading * G * growthLoadingᵀ + Matrix.diagonal θ :
        Matrix (Fin 3) (Fin 3) ℝ)) 0 1
      - 2 * ((growthLoading * G * growthLoadingᵀ + Matrix.diagonal θ :
        Matrix (Fin 3) (Fin 3) ℝ)) 0 2)) / 2
    ∧ θ 0 = ((growthLoading * G * growthLoadingᵀ + Matrix.diagonal θ :
        Matrix (Fin 3) (Fin 3) ℝ)) 0 0 - G 0 0
    ∧ θ 1 = ((growthLoading * G * growthLoadingᵀ + Matrix.diagonal θ :
        Matrix (Fin 3) (Fin 3) ℝ)) 1 1
      - (G 0 0 + 2 * G 0 1 + G 1 1)
    ∧ θ 2 = ((growthLoading * G * growthLoadingᵀ + Matrix.diagonal θ :
        Matrix (Fin 3) (Fin 3) ℝ)) 2 2
      - (G 0 0 + 4 * G 0 1 + 4 * G 1 1) := by
  have e := growthLoading_cov_apply G hG θ
  rw [e 0 0, e 0 1, e 0 2, e 1 1, e 1 2, e 2 2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> linarith

/-- The three-time-point growth covariance identifies its parameters: equal
model covariances force equal intercept/slope covariances and error
variances (Duncan and Duncan (2009)). -/
theorem growth_identified
    (G G' : Matrix (Fin 2) (Fin 2) ℝ)
    (hG : G.IsSymm) (hG' : G'.IsSymm) (θ θ' : Fin 3 → ℝ)
    (h : ((growthLoading * G * growthLoadingᵀ + Matrix.diagonal θ :
      Matrix (Fin 3) (Fin 3) ℝ))
      = ((growthLoading * G' * growthLoadingᵀ + Matrix.diagonal θ' :
        Matrix (Fin 3) (Fin 3) ℝ))) :
    G = G' ∧ θ = θ' := by
  have hM : ∀ s t : Fin 3,
      ((growthLoading * G * growthLoadingᵀ + Matrix.diagonal θ :
        Matrix (Fin 3) (Fin 3) ℝ)) s t
        = ((growthLoading * G' * growthLoadingᵀ + Matrix.diagonal θ' :
          Matrix (Fin 3) (Fin 3) ℝ)) s t := by
    intro s t
    rw [h]
  obtain ⟨g01, g00, g11, t0, t1, t2⟩ := growth_recover G hG θ
  obtain ⟨g01', g00', g11', t0', t1', t2'⟩ := growth_recover G' hG' θ'
  have eG01 : G 0 1 = G' 0 1 := by rw [g01, g01', hM 0 2, hM 0 1]
  have eG00 : G 0 0 = G' 0 0 := by rw [g00, g00', hM 0 1, hM 0 2]
  have eG11 : G 1 1 = G' 1 1 := by rw [g11, g11', hM 1 2, hM 0 1, hM 0 2]
  have eG : G = G' := by
    have hall : ∀ i j : Fin 2, G i j = G' i j := by
      simp only [Fin.forall_fin_two]
      refine ⟨⟨eG00, eG01⟩, ?_, eG11⟩
      rw [hG.apply 0 1, hG'.apply 0 1]
      exact eG01
    exact Matrix.ext hall
  have eθ : θ = θ' := by
    have h0 : θ 0 = θ' 0 := by rw [t0, t0', hM 0 0, eG00]
    have h1 : θ 1 = θ' 1 := by rw [t1, t1', hM 1 1, eG00, eG01, eG11]
    have h2 : θ 2 = θ' 2 := by rw [t2, t2', hM 2 2, eG00, eG01, eG11]
    funext s
    fin_cases s <;> assumption
  exact ⟨eG, eθ⟩

end MathlibExt.Probability.Statistics.Measurement

end
