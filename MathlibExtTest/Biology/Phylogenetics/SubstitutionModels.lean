/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.SubstitutionModels

/-!
# Tests for the GTR, HKY85, F81 and K80 substitution models

Non-vacuity witness: GTR with base frequencies `(0.1, 0.2, 0.3, 0.4)` and symmetric
exchangeabilities is a rate matrix with stationary distribution `π` (`π` sums to `1`).
The negative entry of `exp (t • Q)` at `t = -1` documents the domain `t ≥ 0`. Explicit HKY85
entries for a transition (`A → G`), a transversion (`A → C`) and the diagonal,
the K80 and F81 entries, the special-case identities, and the agreement of the equal-rates
GTR transition function with the Jukes–Cantor closed form at concrete values. Boundary case:
zero exchangeabilities give the zero generator.
-/

@[expose] public section

open Finset Matrix ProbabilityTheory MathlibExt.Biology.Phylogenetics.JukesCantor

namespace MathlibExtTest.Biology.Phylogenetics.SubstitutionModels

open MathlibExt.Biology.Phylogenetics.SubstitutionModels

/-- Base frequencies `(πA, πC, πG, πT) = (0.1, 0.2, 0.3, 0.4)`. -/
noncomputable def πex : Fin 4 → ℝ := ![1 / 10, 2 / 10, 3 / 10, 4 / 10]

/-- Symmetric exchangeabilities: `s i j = 1 + i + j`. -/
def sex : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i j => 1 + (i : ℝ) + (j : ℝ)

theorem πex_nonneg (i : Fin 4) : 0 ≤ πex i := by fin_cases i <;> norm_num [πex]

theorem sex_symm (i j : Fin 4) : sex i j = sex j i := by simp only [sex, of_apply]; ring

-- `πex` is a probability vector.
example : ∑ i, πex i = 1 := by norm_num [πex, Fin.sum_univ_four]

-- Non-vacuity witness: the GTR matrix is a rate matrix with stationary distribution `πex`,
-- in detailed balance, at every time.
example : IsRateMatrix (gtrRate πex sex) :=
  isRateMatrix_gtrRate πex_nonneg fun i j _ => by simp only [sex, of_apply]; positivity

-- The diagonal exchangeabilities are not used: with `s i i = -1` and `s i j = 1` off the
-- diagonal, the GTR matrix is still a rate matrix.
example : IsRateMatrix (gtrRate πex (Matrix.of fun i j : Fin 4 => if i = j then -1 else 1)) :=
  isRateMatrix_gtrRate πex_nonneg fun i j hij => by simp [hij]
example : IsDetailedBalance πex (gtrRate πex sex) := isDetailedBalance_gtrRate πex sex_symm
example (t : ℝ) : πex ᵥ* ctmcTransition (gtrRate πex sex) t = πex :=
  vecMul_ctmcTransition_gtrRate πex sex_symm t
example (t : ℝ) (i j : Fin 4) :
    πex i * ctmcTransition (gtrRate πex sex) t i j =
      πex j * ctmcTransition (gtrRate πex sex) t j i :=
  isDetailedBalance_ctmcTransition_gtrRate πex sex_symm t i j
example {t : ℝ} (ht : 0 ≤ t) (i j : Fin 4) : 0 ≤ ctmcTransition (gtrRate πex sex) t i j :=
  (isRateMatrix_gtrRate πex_nonneg fun i j _ => by
    simp only [sex, of_apply]; positivity).ctmcTransition_nonneg ht i j

-- HKY85 with `κ = 2`: a transition `A → G`, a transversion `A → C`, and the diagonal at `A`.
example : hkyRate πex 2 0 2 = 2 * (3 / 10) := by
  norm_num [hkyRate, gtrRate, hkyExchangeability, πex]
example : hkyRate πex 2 0 1 = 2 / 10 := by
  norm_num [hkyRate, gtrRate, hkyExchangeability, πex]
example : hkyRate πex 2 0 0 = -(2 / 10 + 2 * (3 / 10) + 4 / 10) := by
  simp [hkyRate, gtrRate, hkyExchangeability, πex, sum_erase_eq_sub, Fin.sum_univ_four]
  norm_num
example : IsRateMatrix (hkyRate πex 2) := isRateMatrix_hkyRate πex_nonneg (by norm_num)
example : πex ᵥ* ctmcTransition (hkyRate πex 2) 1 = πex :=
  (isDetailedBalance_hkyRate πex 2).vecMul_ctmcTransition (sum_gtrRate _ _) 1

-- K80 with `κ = 3`: transition `C → T` at rate `3/4`, transversion `C → G` at rate `1/4`.
example : k80Rate 3 1 3 = 3 / 4 := by norm_num [k80Rate, hkyRate, gtrRate, hkyExchangeability]
example : k80Rate 3 1 2 = 1 / 4 := by norm_num [k80Rate, hkyRate, gtrRate, hkyExchangeability]
example : IsRateMatrix (k80Rate 3) := isRateMatrix_k80Rate (by norm_num)

-- F81: rate `π j` to every other base; F81 is HKY85 with `κ = 1`.
example : f81Rate πex 3 0 = 1 / 10 := by norm_num [f81Rate, gtrRate, πex]
example : IsRateMatrix (f81Rate πex) := isRateMatrix_f81Rate πex_nonneg
example : IsDetailedBalance πex (f81Rate πex) := isDetailedBalance_f81Rate πex
example : hkyRate πex 1 = f81Rate πex := hkyRate_one πex

-- JC69 as the equal-rates case: K80 with `κ = 1`, and the transition function at concrete
-- values agrees with the Jukes–Cantor closed form.
example : k80Rate 1 = jcRateMatrix (3 / 4) := k80Rate_one
example : IsRateMatrix (jcRateMatrix 2) := isRateMatrix_jcRateMatrix (by norm_num)
example : gtrRate (fun _ : Fin 4 => 1 / 4) (Matrix.of fun _ _ => 4 * 3 / 3) = jcRateMatrix 3 :=
  gtrRate_jukesCantor 3
example :
    ctmcTransition (gtrRate (fun _ : Fin 4 => 1 / 4) (Matrix.of fun _ _ => 4 * 3 / 3)) 1 0 2 =
      1 / 4 - 1 / 4 * Real.exp (-4) := by
  rw [ctmcTransition_gtrRate_jukesCantor]; norm_num [jcProb]

-- Outside the domain `t ≥ 0` the matrix exponential is not stochastic: at `t = -1` an
-- off-diagonal Jukes–Cantor entry is negative.
example :
    ctmcTransition (gtrRate (fun _ : Fin 4 => 1 / 4) (Matrix.of fun _ _ => 4 * 3 / 3)) (-1) 0 2 <
      0 := by
  rw [ctmcTransition_gtrRate_jukesCantor]
  norm_num [jcProb]

-- Boundary case: zero exchangeabilities give the zero generator.
example (π : Fin 4 → ℝ) : gtrRate π 0 = 0 := by
  ext i j; by_cases h : i = j <;> simp [gtrRate, h]

#print axioms isRateMatrix_gtrRate
#print axioms isDetailedBalance_gtrRate
#print axioms vecMul_ctmcTransition_gtrRate
#print axioms ctmcTransition_gtrRate_jukesCantor

end MathlibExtTest.Biology.Phylogenetics.SubstitutionModels
