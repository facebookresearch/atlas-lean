/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Eigenvalue stability of a fixed linear policy model

A two-variable linear policy model `x_{t+1} = A x_t + c` with an
upper-triangular matrix `A = !![a, b; 0, d]`: the eigenvalues `a` and `d`
are readable off the diagonal (proved by the two eigenvector equations),
and when both lie strictly inside the unit circle and `a ≠ d`, the powers
`A ^ n` tend to zero and the affine iteration converges to the explicitly
computed fixed point from any starting state (Atlas roadmap MA08.T04,
bridge).
-/


open Filter Topology Matrix

@[expose] public section

namespace MathlibExt.Economics.Macro.LinearPolicy

/-- A fixed 2-variable linear policy model: the state evolves by
`x_{t+1} = A x_t + c` where `A` is the upper-triangular matrix below.
The diagonal entries `a` and `d` are the policy feedback coefficients
(the eigenvalues, see the two eigenvector equations below); the
off-diagonal entry `b` couples the second state variable into the first
equation. Upper-triangular form is the frozen contract: it makes the
eigenvalues explicitly readable off the diagonal while keeping a
nontrivial coupling term. -/
noncomputable def linearPolicyMatrix (a b d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, b; 0, d]

/-- The candidate fixed point of the affine policy iteration, solved
explicitly from the triangular system (`x*_2 = c_2 / (1 - d)`, then
`x*_1 = (c_1 + b x*_2) / (1 - a)`). It satisfies `x* = A x* + c` when
`a ≠ 1` and `d ≠ 1` (see `linearPolicyMatrix_mulVec_fixedPoint_add`); no
uniqueness is claimed here. -/
noncomputable def policyFixedPoint (a b d : ℝ) (c : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![ (c 0 + b * (c 1 / (1 - d))) / (1 - a), c 1 / (1 - d) ]

/-- Affine policy iteration `x_0 = x0`, `x_{n+1} = A x_n + c`. -/
noncomputable def policyIterate (a b d : ℝ) (c x0 : Fin 2 → ℝ) : ℕ → Fin 2 → ℝ
  | 0 => x0
  | n + 1 => linearPolicyMatrix a b d *ᵥ policyIterate a b d c x0 n + c

/-- First eigenvalue equation: `a` is an eigenvalue with eigenvector `![1, 0]`. -/
theorem linearPolicyMatrix_mulVec_first (a b d : ℝ) :
    linearPolicyMatrix a b d *ᵥ ![1, 0] = a • ![1, 0] := by
  ext i
  fin_cases i <;> simp [linearPolicyMatrix, Matrix.mulVec]

/-- Second eigenvalue equation: `A *ᵥ ![b, d - a] = d • ![b, d - a]`.
The vector `![b, d - a]` is an eigenvector for `d` when it is nonzero;
it is zero (and both sides are zero) only in the degenerate case
`b = 0` and `a = d`. -/
theorem linearPolicyMatrix_mulVec_second (a b d : ℝ) :
    linearPolicyMatrix a b d *ᵥ ![b, d - a] = d • ![b, d - a] := by
  ext i
  fin_cases i
  · simp [linearPolicyMatrix, Matrix.mulVec]
    ring
  · simp [linearPolicyMatrix, Matrix.mulVec]

/-- Explicit powers of the policy matrix when the eigenvalues differ. -/
theorem linearPolicyMatrix_pow (a b d : ℝ) (had : a ≠ d) (n : ℕ) :
    (linearPolicyMatrix a b d) ^ n =
      !![a ^ n, b * (a ^ n - d ^ n) / (a - d); 0, d ^ n] := by
  induction n with
  | zero =>
    simp only [pow_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    have had' : a - d ≠ 0 := sub_ne_zero.mpr had
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [linearPolicyMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp <;> ring

/-- Eigenvalue stability: when both eigenvalues lie strictly inside the
unit circle and `a ≠ d`, the powers of the policy matrix tend to zero.
This is the frozen eigenvalue stability condition for MA08.T04. -/
theorem tendsto_linearPolicyMatrix_pow (a b d : ℝ) (had : a ≠ d)
    (ha : |a| < 1) (hd : |d| < 1) :
    Tendsto (fun n => (linearPolicyMatrix a b d) ^ n) atTop (𝓝 0) := by
  have ha0 : Tendsto (fun n => a ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one ha
  have hd0 : Tendsto (fun n => d ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hd
  have hsub : Tendsto (fun n => a ^ n - d ^ n) atTop (𝓝 0) := by
    have h := ha0.sub hd0
    simpa using h
  have hmul : Tendsto (fun n => b * (a ^ n - d ^ n)) atTop (𝓝 0) := by
    have h := hsub.const_mul b
    simpa using h
  have hoff : Tendsto (fun n => b * (a ^ n - d ^ n) / (a - d)) atTop (𝓝 0) := by
    have h := hmul.div_const (a - d)
    simpa using h
  simp_rw [linearPolicyMatrix_pow a b d had]
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · apply tendsto_pi_nhds.mpr
    intro j
    fin_cases j
    · simpa using ha0
    · simpa using hoff
  · apply tendsto_pi_nhds.mpr
    intro j
    fin_cases j
    · simp
    · simpa using hd0

/-- The explicit fixed point indeed satisfies `x* = A x* + c`. -/
theorem linearPolicyMatrix_mulVec_fixedPoint_add (a b d : ℝ) (ha1 : a ≠ 1)
    (hd1 : d ≠ 1) (c : Fin 2 → ℝ) :
    linearPolicyMatrix a b d *ᵥ policyFixedPoint a b d c + c =
      policyFixedPoint a b d c := by
  have ha' : (1 : ℝ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  have hd' : (1 : ℝ) - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hd1)
  ext i
  fin_cases i <;>
    simp [policyFixedPoint, linearPolicyMatrix] <;>
    field_simp <;> ring

/-- The iteration error is the matrix power applied to the initial error. -/
theorem policyIterate_sub_fixedPoint (a b d : ℝ) (ha1 : a ≠ 1) (hd1 : d ≠ 1)
    (c x0 : Fin 2 → ℝ) (n : ℕ) :
    policyIterate a b d c x0 n - policyFixedPoint a b d c =
      (linearPolicyMatrix a b d) ^ n *ᵥ (x0 - policyFixedPoint a b d c) := by
  induction n with
  | zero =>
    simp [policyIterate, pow_zero, Matrix.one_mulVec]
  | succ n ih =>
    have hfix := linearPolicyMatrix_mulVec_fixedPoint_add a b d ha1 hd1 c
    simp only [policyIterate]
    have h1 : linearPolicyMatrix a b d *ᵥ policyIterate a b d c x0 n + c -
        policyFixedPoint a b d c =
        linearPolicyMatrix a b d *ᵥ policyIterate a b d c x0 n -
          linearPolicyMatrix a b d *ᵥ policyFixedPoint a b d c := by
      conv_lhs => rw [← hfix]
      rw [add_sub_add_right_eq_sub]
    rw [h1, ← Matrix.mulVec_sub, ih, Matrix.mulVec_mulVec, pow_succ']

/-- **Policy stability (MA08.T04).** Under the eigenvalue stability
condition (`|a| < 1`, `|d| < 1`, `a ≠ d`), the affine policy iteration
converges to the explicitly computed fixed point from any starting state. -/
theorem tendsto_policyIterate (a b d : ℝ) (had : a ≠ d)
    (ha : |a| < 1) (hd : |d| < 1) (c x0 : Fin 2 → ℝ) :
    Tendsto (policyIterate a b d c x0) atTop (𝓝 (policyFixedPoint a b d c)) := by
  have ha1 : a ≠ 1 := fun h => by rw [h] at ha; norm_num at ha
  have hd1 : d ≠ 1 := fun h => by rw [h] at hd; norm_num at hd
  have hpow := tendsto_linearPolicyMatrix_pow a b d had ha hd
  have hvec : Tendsto
      (fun n => (linearPolicyMatrix a b d) ^ n *ᵥ (x0 - policyFixedPoint a b d c))
      atTop (𝓝 0) := by
    set v : Fin 2 → ℝ := x0 - policyFixedPoint a b d c with hv
    apply tendsto_pi_nhds.mpr
    intro i
    have hentry : ∀ j : Fin 2,
        Tendsto (fun n => ((linearPolicyMatrix a b d) ^ n) i j * v j)
          atTop (𝓝 0) := by
      intro j
      have hcell : Tendsto (fun n => ((linearPolicyMatrix a b d) ^ n) i j)
          atTop (𝓝 0) := by
        have hrow := tendsto_pi_nhds.mp hpow i
        have hcell0 := tendsto_pi_nhds.mp hrow j
        simpa using hcell0
      have h2 := hcell.mul_const (v j)
      simpa using h2
    have hsum := tendsto_finsetSum Finset.univ (fun j _ => hentry j)
    simpa [Matrix.mulVec] using hsum
  have heq : ∀ n, policyIterate a b d c x0 n =
      policyFixedPoint a b d c +
        ((linearPolicyMatrix a b d) ^ n *ᵥ (x0 - policyFixedPoint a b d c)) := by
    intro n
    have h := policyIterate_sub_fixedPoint a b d ha1 hd1 c x0 n
    have h2 : policyFixedPoint a b d c +
        (policyIterate a b d c x0 n - policyFixedPoint a b d c) =
        policyIterate a b d c x0 n := add_sub_cancel _ _
    rw [h] at h2
    exact h2.symm
  have hfun : policyIterate a b d c x0 =
      fun n => policyFixedPoint a b d c +
        ((linearPolicyMatrix a b d) ^ n *ᵥ (x0 - policyFixedPoint a b d c)) :=
    funext heq
  rw [hfun]
  have hlim := hvec.const_add (policyFixedPoint a b d c)
  simpa using hlim

/-- Concrete policy model: `a = 1/2`, `b = 1/4`, `d = 1/3`, `c = ![1, 1]`,
starting from `![0, 0]`. The fixed point is `![11/4, 3/2]`. -/
theorem policyIterate_example :
    Tendsto (policyIterate (1 / 2 : ℝ) (1 / 4) (1 / 3) ![1, 1] ![0, 0]) atTop
      (𝓝 ![11 / 4, 3 / 2]) := by
  have h := tendsto_policyIterate (1 / 2 : ℝ) (1 / 4) (1 / 3) (by norm_num)
    (by norm_num) (by norm_num) ![1, 1] ![0, 0]
  have hfix : policyFixedPoint (1 / 2 : ℝ) (1 / 4) (1 / 3) ![1, 1] =
      ![11 / 4, 3 / 2] := by
    ext i
    fin_cases i <;> norm_num [policyFixedPoint]
  rwa [hfix] at h

end MathlibExt.Economics.Macro.LinearPolicy
