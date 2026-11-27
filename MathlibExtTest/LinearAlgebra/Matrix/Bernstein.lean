/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.Bernstein
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MvPolynomial Matrix

-- All entries share a degree vector, while coordinates may have different degrees.
example {ι m : Type*} [Fintype ι] (P : Matrix m m (MvPolynomial ι ℝ))
    (n : ι → ℕ) (hp : ∀ a b i, (P a b).degreeOf i ≤ n i)
    (x : ι → ℝ) (hx : ∀ i, x i ∈ Set.Icc 0 1)
    (hc : ∀ k : (i : ι) → Fin (n i + 1),
      (Matrix.bernsteinCoeff n P (fun i => k i)).PosSemidef) :
    (P.map (eval x)).PosSemidef := by
  exact Matrix.posSemidef_map_eval_of_bernsteinCoeff hp hx hc

-- The margin is uniform in the point and in every vector, including zero.
example {ι m : Type*} [Fintype ι] [Fintype m] [DecidableEq m]
    (P : Matrix m m (MvPolynomial ι ℝ)) (n : ι → ℕ)
    (hp : ∀ a b i, (P a b).degreeOf i ≤ n i)
    (x : ι → ℝ) (hx : ∀ i, x i ∈ Set.Icc 0 1) (δ : ℝ)
    (hc : ∀ k : (i : ι) → Fin (n i + 1),
      (Matrix.bernsteinCoeff n P (fun i => k i) - δ • 1).PosSemidef)
    (v : m → ℝ) :
    δ * ∑ a, (v a)^2 ≤ v ⬝ᵥ (P.map (eval x) *ᵥ v) := by
  exact Matrix.quadraticForm_lower_bound_of_bernsteinCoeff hp hx hc v

example {ι m : Type*} [Fintype ι]
    (P : Matrix m m (MvPolynomial ι ℝ)) (n : ι → ℕ)
    (hp : ∀ r c i, (P r c).degreeOf i ≤ n i)
    (a b x : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (hx : ∀ i, x i ∈ Set.Icc (a i) (b i)) (L : Matrix m m ℝ)
    (hc : ∀ k : (i : ι) → Fin (n i + 1),
      (Matrix.bernsteinCoeff n (P.map (boxPullback a b)) (fun i => k i) - L).PosSemidef) :
    (P.map (eval x) - L).PosSemidef := by
  exact Matrix.posSemidef_map_eval_sub_of_bernsteinCoeff_box hp hab hx hc

private theorem two_by_two_psd (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (!![a, -1; -1, b] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · intro v
    simp only [dotProduct, mulVec, Fin.sum_univ_two, star_trivial]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [sq_nonneg (v 0 - v 1),
      mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg (v 0)),
      mul_nonneg (sub_nonneg.mpr hb) (sq_nonneg (v 1))]

private noncomputable def testMatrix : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 1) ℝ) :=
  !![C 2 + monomial (Finsupp.single 0 1) 1, C (-1);
    C (-1), C 2 + monomial (Finsupp.single 0 1) 2]

private theorem affine_degree (c : ℝ) (hc : c ≠ 0) (i : Fin 1) :
    (C 2 + monomial (Finsupp.single 0 1) c : MvPolynomial (Fin 1) ℝ).degreeOf i ≤ 1 := by
  apply (degreeOf_add_le _ _ _).trans
  apply max_le (by simp)
  rw [degreeOf_monomial_eq _ _ hc]
  fin_cases i
  simp

private theorem testMatrix_degree (r c : Fin 2) (i : Fin 1) :
    (testMatrix r c).degreeOf i ≤ 1 := by
  fin_cases r <;> fin_cases c
  · exact affine_degree 1 (by norm_num) i
  · change (C (-1) : MvPolynomial (Fin 1) ℝ).degreeOf i ≤ 1
    simp only [degreeOf_C, Nat.zero_le]
  · change (C (-1) : MvPolynomial (Fin 1) ℝ).degreeOf i ≤ 1
    simp only [degreeOf_C, Nat.zero_le]
  · exact affine_degree 2 (by norm_num) i

private theorem coeff_one (n k : Fin 1 → ℕ) :
    MvPolynomial.bernsteinCoeff n (1 : MvPolynomial (Fin 1) ℝ) k = 1 :=
  MvPolynomial.bernsteinCoeff_C n k 1

private theorem testMatrix_margin (k : (i : Fin 1) → Fin ((1 : ℕ) + 1)) :
    (Matrix.bernsteinCoeff (fun _ => 1) testMatrix (fun i => k i) - 1).PosSemidef := by
  have heq : Matrix.bernsteinCoeff (fun _ => 1) testMatrix (fun i => k i) - 1 =
      !![1 + (k 0 : ℝ), -1; -1, 1 + 2 * (k 0 : ℝ)] := by
    ext r c
    fin_cases r <;> fin_cases c <;>
      norm_num [Matrix.bernsteinCoeff_apply, testMatrix, Matrix.sub_apply,
        MvPolynomial.bernsteinCoeff_add, MvPolynomial.bernsteinCoeff_monomial,
        Fin.prod_univ_one, Finsupp.single_apply, Nat.choose_one_right, coeff_one] <;> ring
  rw [heq]
  apply two_by_two_psd
  all_goals have hk : 0 ≤ (k 0 : ℝ) := by positivity
            linarith

-- A non-diagonal polynomial matrix with negative off-diagonal entries has
-- the same positive margin 1 at every point, tested for arbitrary vectors.
example (x : Fin 1 → ℝ) (hx : ∀ i, x i ∈ Set.Icc 0 1) (v : Fin 2 → ℝ) :
    ∑ i, (v i)^2 ≤ v ⬝ᵥ (testMatrix.map (eval x) *ᵥ v) := by
  simpa only [one_smul, one_mul] using
    Matrix.quadraticForm_lower_bound_of_bernsteinCoeff (n := fun _ => 1)
      testMatrix_degree hx (δ := 1) (fun k => by simpa only [one_smul] using testMatrix_margin k) v

example (x : Fin 1 → ℝ) (hx : ∀ i, x i ∈ Set.Icc 0 1) :
    (testMatrix.map (eval x)).PosDef := by
  exact Matrix.posDef_map_eval_of_bernsteinCoeff (n := fun _ => 1)
    testMatrix_degree hx (δ := 1) (by norm_num)
    (fun k => by simpa only [one_smul] using testMatrix_margin k)

-- Positive entries are insufficient for PSD: the vector (1,-1) gives -2.
example : ¬ (!![1, 2; 2, 1] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  intro h
  have hv := h.dotProduct_mulVec_nonneg ![1, -1]
  norm_num [dotProduct, mulVec, Fin.sum_univ_two] at hv

-- Singular PSD is distinct from positive definite.
example : (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef :=
  two_by_two_psd 1 1 le_rfl le_rfl

example : ¬ (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  intro h
  have hv := h.dotProduct_mulVec_pos (x := ![1, 1]) (by
    intro heq
    have := congrFun heq 0
    norm_num at this)
  norm_num [dotProduct, mulVec, Fin.sum_univ_two] at hv

private theorem scalar_matrix_psd (c : ℝ) (hc : 0 ≤ c) :
    (!![c] : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef := by
  have heq : (!![c] : Matrix (Fin 1) (Fin 1) ℝ) = diagonal (fun _ => c) := by
    ext i j
    fin_cases i; fin_cases j; rfl
  rw [heq]
  exact PosSemidef.diagonal (fun _ => hc)

private noncomputable def underDegree : Matrix (Fin 1) (Fin 1) (MvPolynomial (Fin 1) ℝ) :=
  !![C 1 + monomial (Finsupp.single 0 1) (-2)]

-- Omitting the degree bound would be unsound: degree-zero coefficients are
-- positive although evaluation at x=1 is negative.
example : (Matrix.bernsteinCoeff (fun _ => 0) underDegree (fun _ => 0)).PosSemidef ∧
    ¬ (underDegree.map (eval (fun _ => 1))).PosSemidef := by
  constructor
  · have heq : Matrix.bernsteinCoeff (fun _ => 0) underDegree (fun _ => 0) = !![1] := by
      ext r c
      fin_cases r; fin_cases c
      norm_num [Matrix.bernsteinCoeff_apply, underDegree, MvPolynomial.bernsteinCoeff_add,
        MvPolynomial.bernsteinCoeff_monomial, Fin.prod_univ_one, Finsupp.single_apply, Nat.choose,
        coeff_one]
    rw [heq]
    exact scalar_matrix_psd 1 zero_le_one
  · intro h
    have := h.diag_nonneg (i := 0)
    norm_num [underDegree, Matrix.map_apply, eval_monomial, Finsupp.prod_single_index] at this

-- Empty variable types still have one coefficient matrix, including degree zero.
example (x : Fin 0 → ℝ) :
    ((!![C (3 : ℝ)] : Matrix (Fin 1) (Fin 1) (MvPolynomial (Fin 0) ℝ)).map (eval x)).PosDef := by
  refine Matrix.posDef_map_eval_of_bernsteinCoeff (n := fun _ => 0)
    (fun _ _ i => Fin.elim0 i) (fun i => Fin.elim0 i) (δ := 1) (by norm_num) ?_
  intro k
  have heq : Matrix.bernsteinCoeff (fun _ : Fin 0 => 0) !![C (3 : ℝ)]
        (fun i => k i) - (1 : Matrix (Fin 1) (Fin 1) ℝ) = !![2] := by
    ext r c
    fin_cases r; fin_cases c
    norm_num [Matrix.bernsteinCoeff_apply, Matrix.sub_apply]
  simpa only [one_smul, heq] using scalar_matrix_psd 2 (by norm_num)

-- Zero-size matrices are allowed; positive definiteness is vacuous in this case.
example (P : Matrix (Fin 0) (Fin 0) (MvPolynomial (Fin 1) ℝ)) :
    (P.map (eval (fun _ => 0))).PosDef := by
  refine Matrix.posDef_map_eval_of_bernsteinCoeff (n := fun _ => 0)
    (fun r => Fin.elim0 r) (by intro i; norm_num) (δ := 1) (by norm_num) ?_
  intro k
  convert (PosSemidef.zero : (0 : Matrix (Fin 0) (Fin 0) ℝ).PosSemidef) using 1
  ext r
  exact Fin.elim0 r

-- A fully collapsed box uses the polynomial at its one point, not on the cube.
example (x : Fin 1 → ℝ) (hx : x 0 = 3) (v : Fin 1 → ℝ) :
    2 * ∑ i, (v i)^2 ≤
      v ⬝ᵥ ((!![X 0] : Matrix (Fin 1) (Fin 1) (MvPolynomial (Fin 1) ℝ)).map (eval x) *ᵥ v) := by
  apply Matrix.quadraticForm_lower_bound_of_bernsteinCoeff_box
    (n := fun _ => 1) (a := fun _ => 3) (b := fun _ => 3)
  · intro r c i
    fin_cases r; fin_cases c; fin_cases i
    simp
  · intro i
    exact le_rfl
  · intro i
    fin_cases i
    simp [hx]
  · intro k
    have heq : Matrix.bernsteinCoeff (fun _ : Fin 1 => 1)
        ((!![X 0] : Matrix (Fin 1) (Fin 1) (MvPolynomial (Fin 1) ℝ)).map
          (boxPullback (fun _ => 3) (fun _ => 3))) (fun i => k i) -
          (2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) = !![1] := by
      ext r c
      fin_cases r; fin_cases c
      norm_num [Matrix.bernsteinCoeff_apply, Matrix.map_apply, Matrix.sub_apply,
        Matrix.smul_apply, boxPullback, eval₂Hom_X']
    rw [heq]
    exact scalar_matrix_psd 1 zero_le_one

private noncomputable def stripMatrix : Matrix (Fin 1) (Fin 1) (MvPolynomial (Fin 2) ℝ) :=
  fun _ _ => C 2 + monomial (Finsupp.single 0 1) 1

private theorem strip_degree (r c : Fin 1) (i : Fin 2) :
    (stripMatrix r c).degreeOf i ≤ (![2, 0] : Fin 2 → ℕ) i := by
  apply (degreeOf_add_le _ _ _).trans
  apply max_le (by simp)
  rw [degreeOf_monomial_eq _ _ (by norm_num)]
  fin_cases i <;> norm_num [Finsupp.single_apply]

-- Heterogeneous degrees include a zero degree in the unused coordinate.
example (x : Fin 2 → ℝ) (hx : ∀ i, x i ∈ Set.Icc 0 1) :
    (stripMatrix.map (eval x)).PosDef := by
  refine Matrix.posDef_map_eval_of_bernsteinCoeff strip_degree hx (δ := 1) (by norm_num) ?_
  intro k
  have heq : Matrix.bernsteinCoeff ![2, 0] stripMatrix (fun i => k i) - 1 =
      !![1 + (k 0 : ℝ) / 2] := by
    ext r c
    fin_cases r; fin_cases c
    norm_num [Matrix.bernsteinCoeff_apply, stripMatrix, Matrix.sub_apply,
      MvPolynomial.bernsteinCoeff_add, MvPolynomial.bernsteinCoeff_monomial,
      Fin.prod_univ_two, Finsupp.single_apply, Nat.choose_one_right]
    ring
  simp only [one_smul, heq]
  apply scalar_matrix_psd
  positivity

private theorem strip_pullback (r c : Fin 1) :
    boxPullback ![1, 7] ![3, 7] (stripMatrix r c) =
      C 3 + monomial (Finsupp.single (0 : Fin 2) 1) (2 : ℝ) := by
  norm_num [stripMatrix, boxPullback, eval₂Hom, ← C_mul_X_pow_eq_monomial]
  rw [show (C (2 : ℝ) : MvPolynomial (Fin 2) ℝ) = 2 from C_eq_natCast 2,
    show (C (3 : ℝ) : MvPolynomial (Fin 2) ℝ) = 3 from C_eq_natCast 3]
  ring

-- A shifted, partially collapsed box uses the actual affine pullback.
example (x : Fin 2 → ℝ) (hx : ∀ i, x i ∈ Set.Icc (![1, 7] i) (![3, 7] i))
    (v : Fin 1 → ℝ) : 3 * ∑ i, (v i)^2 ≤ v ⬝ᵥ (stripMatrix.map (eval x) *ᵥ v) := by
  refine Matrix.quadraticForm_lower_bound_of_bernsteinCoeff_box strip_degree
    (by intro i; fin_cases i <;> norm_num) hx ?_ v
  intro k
  have heq : Matrix.bernsteinCoeff ![2, 0] (stripMatrix.map (boxPullback ![1, 7] ![3, 7]))
      (fun i => k i) - (3 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) = !![(k 0 : ℝ)] := by
    ext r c
    fin_cases r; fin_cases c
    simp only [Matrix.bernsteinCoeff_apply, Matrix.map_apply, strip_pullback, Matrix.sub_apply,
      Matrix.smul_apply]
    norm_num [MvPolynomial.bernsteinCoeff_add, MvPolynomial.bernsteinCoeff_monomial,
      Fin.prod_univ_two, Finsupp.single_apply, Nat.choose_one_right]
    ring
  rw [heq]
  exact scalar_matrix_psd _ (by positivity)

#print axioms Matrix.posSemidef_sum_smul_sub
#print axioms Matrix.map_eval_eq_sum_bernstein
#print axioms Matrix.posSemidef_map_eval_sub_of_bernsteinCoeff_box
#print axioms Matrix.quadraticForm_lower_bound_of_bernsteinCoeff_box
#print axioms Matrix.posDef_map_eval_of_bernsteinCoeff_box
