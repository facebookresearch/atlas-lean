/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The Jukes–Cantor model of nucleotide substitution

The Jukes–Cantor model (JC69) is the continuous-time Markov chain on the four nucleotides
`Fin 4` in which every base is replaced by each of the three other bases at rate `μ / 3`, so the
total substitution rate out of every base is `μ`. Its rate matrix is `jcRate μ`
(`-μ` on the diagonal, `μ / 3` off it) and its transition probabilities over a branch of
length `t` are

`jcProb μ t i j = 1/4 + 3/4 · exp (-4 μ t / 3)` if `i = j`,
`jcProb μ t i j = 1/4 - 1/4 · exp (-4 μ t / 3)` if `i ≠ j`.

Here `μ` is the substitution rate per site and unit time, so `μ * t` is the expected number of
substitutions per site along the branch. The model's statements below hold for all real `μ`
and `t` except nonnegativity, which needs `0 ≤ μ * t`.

The probability that the two ends of a branch carry different bases is
`pDiff μ t i = 3/4 · (1 - exp (-4 μ t / 3))`, and inverting it gives the **Jukes–Cantor
distance** `jcDistance p = -(3/4) · log (1 - 4/3 · p)`, which recovers `μ * t` from the
expected proportion of differing sites.

## Main results

* `sum_jcProb`, `jcProb_nonneg`: each row of `jcProb μ t` is a probability distribution.
* `jcProb_zero`: at `t = 0` the transition matrix is the identity.
* `sum_jcProb_mul_jcProb`: the **Chapman–Kolmogorov equation**.
* `hasDerivAt_jcProb`: the **Kolmogorov forward equation** `P' = P Q` with `Q = jcRate μ`.
* `pDiff_eq`: the probability that the ends differ is `3/4 · (1 - exp (-4 μ t / 3))`.
* `jcDistance_pDiff`: the **JC69 distance correction** recovers `μ * t`.
* `jcProb_eq_exp`: `jcProb μ t` is the matrix exponential `exp (t • jcRateMatrix μ)`, proved by
  diagonalizing the rate matrix (eigenvalue `0` on the constant vector, `-4 μ / 3` with
  multiplicity three).

## References

* T. H. Jukes and C. R. Cantor, *Evolution of protein molecules*, in Mammalian Protein
  Metabolism (H. N. Munro, ed.), Academic Press, 1969, pp. 21–132.
* J. Felsenstein, *Inferring Phylogenies*, Sinauer, 2004, chapters 11 and 13.
* C. Semple and M. Steel, *Phylogenetics*, Oxford University Press, 2003, chapter 8.
-/

@[expose] public section

open Real Finset Matrix

namespace MathlibExt.Biology.Phylogenetics.JukesCantor

/-- The Jukes–Cantor transition probability from base `i` to base `j` over a branch of length
`t`, with substitution rate `μ`. -/
noncomputable def jcProb (μ t : ℝ) (i j : Fin 4) : ℝ :=
  if i = j then 1 / 4 + 3 / 4 * exp (-4 * μ * t / 3) else 1 / 4 - 1 / 4 * exp (-4 * μ * t / 3)

/-- The Jukes–Cantor rate matrix: rate `μ / 3` to each other base, `-μ` on the diagonal. -/
noncomputable def jcRate (μ : ℝ) (k j : Fin 4) : ℝ :=
  if k = j then -μ else μ / 3

/-- The probability that the two ends of a branch of length `t` carry different bases, given
base `i` at the start. -/
noncomputable def pDiff (μ t : ℝ) (i : Fin 4) : ℝ :=
  ∑ j ∈ univ.erase i, jcProb μ t i j

/-- The Jukes–Cantor distance: the expected number of substitutions per site corresponding to a
proportion `p` of differing sites. -/
noncomputable def jcDistance (p : ℝ) : ℝ :=
  -(3 / 4) * log (1 - 4 / 3 * p)

/-- Each row of the Jukes–Cantor transition matrix sums to `1`. -/
theorem sum_jcProb (μ t : ℝ) (i : Fin 4) : ∑ j, jcProb μ t i j = 1 := by
  fin_cases i <;> simp [Fin.sum_univ_four, jcProb] <;> ring

/-- The Jukes–Cantor transition probabilities are nonnegative when `0 ≤ μ * t`. -/
theorem jcProb_nonneg {μ t : ℝ} (h : 0 ≤ μ * t) (i j : Fin 4) : 0 ≤ jcProb μ t i j := by
  have he : exp (-4 * μ * t / 3) ≤ 1 :=
    exp_le_one_iff.mpr (by nlinarith)
  have he0 := exp_pos (-4 * μ * t / 3)
  unfold jcProb
  split_ifs <;> linarith

/-- At time `0` the Jukes–Cantor transition matrix is the identity. -/
theorem jcProb_zero (μ : ℝ) (i j : Fin 4) : jcProb μ 0 i j = if i = j then 1 else 0 := by
  unfold jcProb
  split_ifs <;> norm_num

/-- **Chapman–Kolmogorov equation** for the Jukes–Cantor model. -/
theorem sum_jcProb_mul_jcProb (μ s t : ℝ) (i j : Fin 4) :
    ∑ k, jcProb μ s i k * jcProb μ t k j = jcProb μ (s + t) i j := by
  have he : exp (-4 * μ * (s + t) / 3) = exp (-4 * μ * s / 3) * exp (-4 * μ * t / 3) := by
    rw [← exp_add]; ring_nf
  simp only [jcProb, he]
  generalize exp (-4 * μ * s / 3) = a
  generalize exp (-4 * μ * t / 3) = b
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four] <;> ring

/-- The right-hand side of the forward equation, in closed form. -/
theorem sum_jcProb_mul_jcRate (μ t : ℝ) (i j : Fin 4) :
    ∑ k, jcProb μ t i k * jcRate μ k j =
      if i = j then -μ * exp (-4 * μ * t / 3) else μ / 3 * exp (-4 * μ * t / 3) := by
  simp only [jcProb, jcRate]
  generalize exp (-4 * μ * t / 3) = a
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four] <;> ring

/-- **Kolmogorov forward equation** for the Jukes–Cantor model:
`d/dt P(t) = P(t) Q` with `Q = jcRate μ`. -/
theorem hasDerivAt_jcProb (μ t : ℝ) (i j : Fin 4) :
    HasDerivAt (fun t => jcProb μ t i j) (∑ k, jcProb μ t i k * jcRate μ k j) t := by
  have hlin : HasDerivAt (fun t : ℝ => -4 * μ * t / 3) (-4 * μ / 3) t := by
    simpa using ((hasDerivAt_id t).const_mul (-4 * μ)).div_const 3
  have hexp := hlin.exp
  rw [sum_jcProb_mul_jcRate]
  by_cases h : i = j
  · simp only [jcProb, h, ite_true]
    convert (hexp.const_mul (3 / 4)).const_add (1 / 4) using 1
    ring
  · simp only [jcProb, h, ite_false]
    convert (hexp.const_mul (1 / 4)).const_sub (1 / 4) using 1
    ring

/-- The probability that the two ends of a branch differ is `3/4 · (1 - exp (-4 μ t / 3))`,
whatever the starting base. -/
theorem pDiff_eq (μ t : ℝ) (i : Fin 4) :
    pDiff μ t i = 3 / 4 * (1 - exp (-4 * μ * t / 3)) := by
  rw [pDiff, sum_erase_eq_sub (mem_univ i), sum_jcProb]
  simp only [jcProb, ite_true]
  ring

/-- **The Jukes–Cantor distance correction**: `-(3/4) · log (1 - 4/3 · pDiff μ t i) = μ * t`,
the expected number of substitutions per site along the branch. -/
theorem jcDistance_pDiff (μ t : ℝ) (i : Fin 4) : jcDistance (pDiff μ t i) = μ * t := by
  have h : 1 - 4 / 3 * pDiff μ t i = exp (-4 * μ * t / 3) := by
    rw [pDiff_eq]; ring
  rw [jcDistance, h, log_exp]
  ring

/-! ## The transition matrix as a matrix exponential -/

/-- The Jukes–Cantor rate matrix as a `Matrix`. -/
noncomputable def jcRateMatrix (μ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of (jcRate μ)

/-- An eigenbasis of the Jukes–Cantor rate matrix, as columns: the constant vector (eigenvalue
`0`) and three vectors with zero sum (eigenvalue `-4 μ / 3`). -/
def jcEigenbasis : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1, 1, 1; 1, -1, 0, 0; 1, 0, -1, 0; 1, 0, 0, -1]

/-- The eigenbasis as a unit, with its explicit inverse. -/
noncomputable def jcEigenbasisUnit : (Matrix (Fin 4) (Fin 4) ℝ)ˣ where
  val := jcEigenbasis
  inv := !![1/4, 1/4, 1/4, 1/4; 1/4, -3/4, 1/4, 1/4; 1/4, 1/4, -3/4, 1/4; 1/4, 1/4, 1/4, -3/4]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [jcEigenbasis, mul_apply, Fin.sum_univ_four]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [jcEigenbasis, mul_apply, Fin.sum_univ_four]

/-- Diagonalization of `t • jcRateMatrix μ`. -/
theorem smul_jcRateMatrix_eq (μ t : ℝ) :
    t • jcRateMatrix μ =
      (jcEigenbasisUnit : Matrix (Fin 4) (Fin 4) ℝ) *
        diagonal ![0, -4 * μ * t / 3, -4 * μ * t / 3, -4 * μ * t / 3] *
        (↑jcEigenbasisUnit⁻¹ : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  simp only [jcRateMatrix, jcEigenbasisUnit, Units.inv_mk, Units.val_mk, Matrix.smul_apply,
    of_apply, mul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> norm_num [jcEigenbasis, jcRate] <;> ring

/-- **The Jukes–Cantor transition matrix is the matrix exponential of the rate matrix**:
`jcProb μ t = exp (t • jcRateMatrix μ)`. -/
theorem jcProb_eq_exp (μ t : ℝ) (i j : Fin 4) :
    jcProb μ t i j = NormedSpace.exp (t • jcRateMatrix μ) i j := by
  rw [smul_jcRateMatrix_eq, Matrix.exp_units_conj, Matrix.exp_diagonal]
  simp only [jcEigenbasisUnit, Units.inv_mk, Units.val_mk, mul_apply, Fin.sum_univ_four,
    Pi.exp_def]
  fin_cases i <;> fin_cases j <;> norm_num [jcEigenbasis, jcProb, ← Real.exp_eq_exp_ℝ] <;> ring

end MathlibExt.Biology.Phylogenetics.JukesCantor
