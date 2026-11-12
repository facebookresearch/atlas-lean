/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Finite-node linear structural equation models and interventions

A recursive linear structural equation model (SEM) on real-valued nodes `Fin n` is
`X = B X + e`, where `B i j` is the coefficient of `X_j` in the equation of `X_i`, `B` is
strictly lower triangular (`B i j = 0` for `i ≤ j`, so the nodes are in a causal order), and
`e` is the noise vector. These are real-valued variables with linear mechanisms, distinct from
the finite-state causal Bayesian networks of
`CSLibExt/MachineLearning/GraphicalModels/CausalBayesNet.lean`.

## Main definitions

* `LinearSEM.solve B e`: the solution `(1 - B)⁻¹ e` of the structural equations.
* `LinearSEM.doSolve B k a e`: the solution after the intervention `do(X_k = a)`, which replaces
  row `k` of `B` by zero and the `k`-th noise term by `a` (row-replacement surgery).

## Main results

* `LinearSEM.eq_solve_iff`: `solve B e` is the unique solution of `X = B X + e`.
* `LinearSEM.eq_doSolve_iff`: `do(X_k = a)` replaces exactly the `k`-th structural equation by
  `X_k = a` (Pearl, Glymour and Jewell 2016, §3.8; Pearl 2009, §5.3).
* `LinearSEM.integral_doSolve`: with integrable noise on a probability space, the mean response
  `E[X_i | do(X_k = a)]` is affine in `a` with slope `((1 - B)⁻¹)_{ik}`, the total effect of
  `X_k` on `X_i`. By path tracing this entry is the sum over directed paths from `k` to `i` of
  the products of the edge coefficients (Wright 1934).

The population least-squares slope identity for the bivariate equation `Y = α + β X + U`,
`Cov(X, Y) / Var(X) = β + Cov(X, U) / Var(X)`, is `LinearMomentModel.covariance_div_variance` in
`MathlibExt/Biology/StatisticalGenetics/MendelianRandomization.lean`.

## References

* S. Wright, *The method of path coefficients*, Ann. Math. Statist. 5 (1934), 161–215.
* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press
  (2009), §5.3.
* J. Pearl, M. Glymour and N. P. Jewell, *Causal Inference in Statistics: A Primer*, Wiley
  (2016), §3.8.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels.LinearSEM

open Matrix MeasureTheory

/-- The solution of the recursive linear structural equations `X = B X + e` on the nodes
`Fin n`: `X = (1 - B)⁻¹ e`. Here `B i j` is the coefficient of `X_j` in the equation of `X_i`
and `e` is the noise vector. For strictly lower triangular `B` this is the unique solution
(`eq_solve_iff`). -/
noncomputable def solve {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ) : Fin n → ℝ :=
  (1 - B)⁻¹ *ᵥ e

/-- **Surgery `do(X_k = a)`** on a linear SEM: the `k`-th structural equation is replaced by
`X_k = a`, i.e. row `k` of `B` is replaced by zero and the `k`-th noise term by the constant
`a`; the other equations and noise terms are unchanged. The result is the solution of the
modified system. -/
noncomputable def doSolve {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (a : ℝ)
    (e : Fin n → ℝ) : Fin n → ℝ :=
  solve (B.updateRow k 0) (Function.update e k a)

/-- For strictly lower triangular `B`, `det (1 - B) = 1`. -/
private theorem det_one_sub_eq_one {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : ∀ i j, i ≤ j → B i j = 0) : (1 - B).det = 1 := by
  have htri : (1 - B).IsLowerTriangular := by
    intro i j h
    rw [OrderDual.toDual_lt_toDual] at h
    rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt h), hB i j (le_of_lt h), sub_zero]
  rw [Matrix.det_of_isLowerTriangular _ htri]
  rw [Finset.prod_eq_one]
  intro i _
  rw [Matrix.sub_apply, Matrix.one_apply_eq, hB i i le_rfl, sub_zero]

/-- For strictly lower triangular `B`, `1 - B` has unit determinant. -/
private theorem isUnit_det_one_sub {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : ∀ i j, i ≤ j → B i j = 0) : IsUnit (1 - B).det := by
  rw [det_one_sub_eq_one hB]
  exact isUnit_one

/-- Replacing a row of a strictly lower triangular matrix by zero keeps it strictly lower
triangular. -/
private theorem strictLower_updateRow {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : ∀ i j, i ≤ j → B i j = 0) (k : Fin n) :
    ∀ i j, i ≤ j → (B.updateRow k 0) i j = 0 := by
  intro i j hij
  rw [Matrix.updateRow_apply]
  split_ifs with h
  · rfl
  · exact hB i j hij

/-- For a recursive (strictly lower triangular) `B`, `solve B e` is the unique solution of the
structural equations `X = B X + e`. -/
theorem eq_solve_iff {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : ∀ i j, i ≤ j → B i j = 0)
    (e x : Fin n → ℝ) :
    x = B *ᵥ x + e ↔ x = solve B e := by
  have hdet : IsUnit (1 - B).det := isUnit_det_one_sub hB
  have hInvMul : (1 - B)⁻¹ * (1 - B) = 1 := Matrix.nonsing_inv_mul _ hdet
  have hMulInv : (1 - B) * (1 - B)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hsub : ∀ y : Fin n → ℝ, (1 - B) *ᵥ y = y - B *ᵥ y := by
    intro y
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  unfold solve
  constructor
  · intro hx
    have he : (1 - B) *ᵥ x = e := by
      rw [hsub x]
      nth_rewrite 1 [hx]
      rw [add_sub_cancel_left]
    have hback : x = (1 - B)⁻¹ *ᵥ ((1 - B) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, hInvMul, Matrix.one_mulVec]
    rw [he] at hback
    exact hback
  · intro hx
    have he : (1 - B) *ᵥ x = e := by
      rw [hx, Matrix.mulVec_mulVec, hMulInv, Matrix.one_mulVec]
    rw [hsub x] at he
    have hx2 : x = e + B *ᵥ x := eq_add_of_sub_eq he
    calc x = e + B *ᵥ x := hx2
      _ = B *ᵥ x + e := add_comm _ _

/-- **`do(X_k = a)` replaces the `k`-th structural equation by `X_k = a`**: for a recursive
`B`, `doSolve B k a e` is the unique vector that equals `a` at `k` and satisfies the original
structural equation `X_i = (B X)_i + e_i` at every other node. -/
theorem eq_doSolve_iff {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : ∀ i j, i ≤ j → B i j = 0)
    (k : Fin n) (a : ℝ) (e x : Fin n → ℝ) :
    (x k = a ∧ ∀ i, i ≠ k → x i = (B *ᵥ x) i + e i) ↔ x = doSolve B k a e := by
  have hB' := strictLower_updateRow hB k
  have hrow : B.updateRow k 0 *ᵥ x
      = Function.update (B *ᵥ x) k ((0 : Fin n → ℝ) ⬝ᵥ x) :=
    Matrix.updateRow_mulVec B k 0 x
  unfold doSolve
  rw [← eq_solve_iff hB' (Function.update e k a) x]
  constructor
  · rintro ⟨hk, h⟩
    ext i
    rw [Pi.add_apply]
    by_cases hi : i = k
    · subst hi
      simp only [hk, hrow, Function.update_self, zero_dotProduct, zero_add]
    · rw [h i hi]
      congr 1
      · rw [hrow, Function.update_of_ne hi]
      · exact (Function.update_of_ne hi _ _).symm
  · intro hx
    have hpt : ∀ i, x i = (B.updateRow k 0 *ᵥ x) i + Function.update e k a i := by
      intro i
      have hci := congrFun hx i
      rwa [Pi.add_apply] at hci
    constructor
    · have hkk := hpt k
      simp only [hrow, Function.update_self, zero_dotProduct, zero_add] at hkk
      exact hkk
    · intro i hi
      have hii := hpt i
      rw [hrow, Function.update_of_ne hi, Function.update_of_ne hi] at hii
      exact hii

/-- Splitting the intervened noise vector: `update e k a = update e k 0 + single k a`. -/
private theorem update_eq_update_zero_add_single {n : ℕ} (e : Fin n → ℝ) (k : Fin n) (a : ℝ) :
    Function.update e k a = Function.update e k 0 + Pi.single k a := by
  ext j
  by_cases hj : j = k
  · subst hj
    simp [Function.update_self, Pi.single_eq_same]
  · simp [Function.update_of_ne hj, Pi.single_eq_of_ne hj]

/-- `(N *ᵥ single k a) i = a * N i k`. -/
private theorem mulVec_single_apply {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (a : ℝ)
    (i : Fin n) : (N *ᵥ Pi.single k a) i = a * N i k := by
  rw [Matrix.mulVec_apply_eq_sum]
  rw [Fintype.sum_eq_single k (fun x hx => by rw [Pi.single_eq_of_ne hx, mul_zero])]
  rw [Pi.single_eq_same]
  exact mul_comm _ _

/-- The surgical solution is affine in the intervention value `a`, with slope column `k` of
`(1 - B.updateRow k 0)⁻¹`. -/
private theorem doSolve_split {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (a : ℝ)
    (e : Fin n → ℝ) (i : Fin n) :
    doSolve B k a e i = doSolve B k 0 e i + a * ((1 - B.updateRow k 0)⁻¹) i k := by
  have hdecomp : Function.update e k a = Function.update e k 0 + Pi.single k a :=
    update_eq_update_zero_add_single e k a
  have hmul : (1 - B.updateRow k 0)⁻¹ *ᵥ Function.update e k a
      = (1 - B.updateRow k 0)⁻¹ *ᵥ Function.update e k 0
        + (1 - B.updateRow k 0)⁻¹ *ᵥ Pi.single k a := by
    rw [hdecomp, Matrix.mulVec_add]
  have hcongr := congrFun hmul i
  rw [Pi.add_apply, mulVec_single_apply] at hcongr
  exact hcongr

/-- For strictly lower triangular `B`, column `k` of `(1 - B.updateRow k 0)⁻¹` equals column `k`
of `(1 - B)⁻¹`: directed paths out of `k` never use the equation of `k`. -/
private theorem inv_one_sub_updateRow_col {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : ∀ i j, i ≤ j → B i j = 0) (k : Fin n) (i : Fin n) :
    ((1 - B.updateRow k 0)⁻¹) i k = ((1 - B)⁻¹) i k := by
  have hB' := strictLower_updateRow hB k
  have hMtri : (1 - B).IsLowerTriangular := by
    intro i' j' h
    rw [OrderDual.toDual_lt_toDual] at h
    rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt h), hB i' j' (le_of_lt h), sub_zero]
  have hM'unit : IsUnit (1 - B.updateRow k 0).det := isUnit_det_one_sub hB'
  have hMunit : IsUnit (1 - B).det := isUnit_det_one_sub hB
  have hMN : (1 - B) * (1 - B)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hMunit
  have hN'M' : ((1 - B.updateRow k 0)⁻¹) * (1 - B.updateRow k 0) = 1 :=
    Matrix.nonsing_inv_mul _ hM'unit
  have hNtri : ((1 - B)⁻¹).IsLowerTriangular := by
    have : Invertible (1 - B) := Matrix.invertibleOfIsUnitDet _ hMunit
    exact Matrix.blockTriangular_inv_of_blockTriangular hMtri
  have hNlow : ∀ j, j < k → ((1 - B)⁻¹) j k = 0 := by
    intro j hjk
    exact hNtri (OrderDual.toDual_lt_toDual.mpr hjk)
  have hMv : (1 - B) *ᵥ ((1 - B)⁻¹).col k = Pi.single k 1 := by
    rw [← Matrix.mulVec_single_one ((1 - B)⁻¹) k, Matrix.mulVec_mulVec, hMN,
      Matrix.one_mulVec]
  have hBck : (B *ᵥ ((1 - B)⁻¹).col k) k = 0 := by
    rw [Matrix.mulVec_apply_eq_sum]
    refine Fintype.sum_eq_zero _ fun j => ?_
    rw [Matrix.col_apply]
    by_cases hjk : j < k
    · rw [hNlow j hjk, mul_zero]
    · rw [hB k j (le_of_not_gt hjk), zero_mul]
  have hck : ((1 - B)⁻¹).col k k = 1 := by
    have h1 : ((1 - B) *ᵥ ((1 - B)⁻¹).col k) k = 1 := by
      rw [hMv]
      exact Pi.single_eq_same k 1
    have hsub : (1 - B) *ᵥ ((1 - B)⁻¹).col k
        = ((1 - B)⁻¹).col k - B *ᵥ ((1 - B)⁻¹).col k := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    have h2 : ((1 - B) *ᵥ ((1 - B)⁻¹).col k) k = ((1 - B)⁻¹).col k k := by
      have h3 := congrFun hsub k
      rwa [Pi.sub_apply, hBck, sub_zero] at h3
    exact h2.symm.trans h1
  have hM'v : (1 - B.updateRow k 0) *ᵥ ((1 - B)⁻¹).col k = Pi.single k 1 := by
    ext i'
    by_cases hi' : i' = k
    · have hB'ck : ((B.updateRow k 0) *ᵥ ((1 - B)⁻¹).col k) k = 0 := by
        rw [Matrix.updateRow_mulVec, Function.update_self, zero_dotProduct]
      have hsub' : (1 - B.updateRow k 0) *ᵥ ((1 - B)⁻¹).col k
          = ((1 - B)⁻¹).col k - (B.updateRow k 0) *ᵥ ((1 - B)⁻¹).col k := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      have h4 := congrFun hsub' k
      rw [Pi.sub_apply, hB'ck, sub_zero, hck] at h4
      rw [hi', Pi.single_eq_same]
      exact h4
    · have hrow : ∀ j, (1 - B.updateRow k 0) i' j = (1 - B) i' j := by
        intro j
        simp [Matrix.sub_apply, Matrix.updateRow_apply, hi']
      have h5 : ((1 - B.updateRow k 0) *ᵥ ((1 - B)⁻¹).col k) i'
          = ((1 - B) *ᵥ ((1 - B)⁻¹).col k) i' := by
        simp_rw [Matrix.mulVec_apply_eq_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [hrow j]
      rw [h5]
      exact congrFun hMv i'
  have hcol : ((1 - B)⁻¹).col k = ((1 - B.updateRow k 0)⁻¹).col k := by
    have hback : ((1 - B)⁻¹).col k
        = ((1 - B.updateRow k 0)⁻¹) *ᵥ ((1 - B.updateRow k 0) *ᵥ ((1 - B)⁻¹).col k) := by
      rw [Matrix.mulVec_mulVec, hN'M', Matrix.one_mulVec]
    rw [hM'v, Matrix.mulVec_single_one] at hback
    exact hback
  have hfin := congrFun hcol i
  rw [Matrix.col_apply, Matrix.col_apply] at hfin
  exact hfin.symm

/-- With integrable noise, every coordinate of the surgical solution is integrable. -/
private theorem integrable_doSolve {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (a : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ε : Ω → Fin n → ℝ} (hε : ∀ j, Integrable (fun ω => ε ω j) μ) (i : Fin n) :
    Integrable (fun ω => doSolve B k a (ε ω) i) μ := by
  have hsum : (fun ω => doSolve B k a (ε ω) i)
      = fun ω => ∑ j, ((1 - B.updateRow k 0)⁻¹) i j * Function.update (ε ω) k a j := rfl
  rw [hsum]
  refine integrable_finsetSum Finset.univ fun j _ => ?_
  by_cases hj : j = k
  · have hconst : (fun ω => ((1 - B.updateRow k 0)⁻¹) i k * Function.update (ε ω) k a k)
        = fun _ => ((1 - B.updateRow k 0)⁻¹) i k * a := by
      funext ω
      rw [Function.update_self]
    rw [hj, hconst]
    exact integrable_const _
  · have hfun : (fun ω => ((1 - B.updateRow k 0)⁻¹) i j * Function.update (ε ω) k a j)
        = fun ω => ((1 - B.updateRow k 0)⁻¹) i j * ε ω j := by
      funext ω
      rw [Function.update_of_ne hj]
    rw [hfun]
    exact (hε j).const_mul _

/-- **Mean responses to `do(X_k = a)` are affine in `a`**, with slope the total effect
`((1 - B)⁻¹) i k` of `X_k` on `X_i` (the sum of the path coefficients over the directed paths
from `k` to `i`): for a recursive `B` and integrable noise on a probability space,
`E[X_i | do(X_k = a)] = E[X_i | do(X_k = 0)] + a ((1 - B)⁻¹)_{ik}`. -/
theorem integral_doSolve {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : ∀ i j, i ≤ j → B i j = 0) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ε : Ω → Fin n → ℝ} (hε : ∀ j, Integrable (fun ω => ε ω j) μ)
    (k : Fin n) (a : ℝ) (i : Fin n) :
    ∫ ω, doSolve B k a (ε ω) i ∂μ = ∫ ω, doSolve B k 0 (ε ω) i ∂μ + a * (1 - B)⁻¹ i k := by
  have hcol : ((1 - B.updateRow k 0)⁻¹) i k = ((1 - B)⁻¹) i k :=
    inv_one_sub_updateRow_col hB k i
  have hfun : (fun ω => doSolve B k a (ε ω) i)
      = fun ω => doSolve B k 0 (ε ω) i + a * (1 - B)⁻¹ i k := by
    funext ω
    rw [doSolve_split, hcol]
  rw [hfun]
  rw [integral_add (integrable_doSolve B k 0 hε i) (integrable_const _)]
  congr 1
  rw [integral_const]
  simp

end Cslib.MachineLearning.GraphicalModels.LinearSEM
