/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.BivariateLorentzian
import Mathlib.Tactic.NormNum

open Finsupp MvPolynomial
open MathlibExt.Combinatorics.LorentzianPolynomialsWanted.LorentzianPolynomials
open MathlibExt.Combinatorics.LorentzianToolboxWanted

-- The zero polynomial qualifies in every degree, including degrees zero and one.
example (d : ℕ) : (⟨0, isHomogeneous_zero _ _ _⟩ : H 2 d) ∈ L 2 d := by
  apply (bivariate_mem_L_iff _).2
  simp

-- The binomial coefficients attain equality in the normalized inequalities.
example {d : ℕ} (f : H 2 d)
    (h : ∀ k ≤ d, f.1.coeff (single 0 k + single 1 (d - k)) = (d.choose k : ℝ)) :
    f ∈ L 2 d := by
  apply (bivariate_mem_L_iff _).2
  dsimp only
  refine ⟨fun k hk => (h k hk).symm ▸ Nat.cast_nonneg _, ?_, ?_⟩
  · intro k hk hkd
    rw [h (k - 1) (by omega), h (k + 1) (by omega), h k (by omega)]
    have hp (j : ℕ) (hj : j ≤ d) : (0 : ℝ) < d.choose j := by exact_mod_cast Nat.choose_pos hj
    have h₀ := hp (k - 1) (by omega)
    have h₁ := hp k (by omega)
    have h₂ := hp (k + 1) (by omega)
    rw [div_self (mul_ne_zero h₀.ne' h₂.ne'), div_self (pow_ne_zero 2 h₁.ne')]
  · intro i j k _ _ hkd _
    rw [h j (by omega)]
    exact_mod_cast Nat.choose_pos (show j ≤ d by omega)

-- The raw sequence (1, 1, 1) is log-concave, but normalization makes its middle term 1/2.
example (f : H 2 2)
    (h : ∀ k ≤ 2, f.1.coeff (single 0 k + single 1 (2 - k)) = 1) : f ∉ L 2 2 := by
  intro hf
  have hmid := ((bivariate_mem_L_iff f).1 hf).2.1 1 (by decide) (by decide)
  have h₀ : f.1.coeff (single 1 2) = 1 := by simpa using h 0 (by decide)
  have h₂ : f.1.coeff (single 0 2) = 1 := by simpa using h 2 (by decide)
  norm_num [h₀, h₂, h 1 (by decide), Nat.choose] at hmid

-- x⁴ + y⁴ has nonnegative coefficients satisfying all the local inequalities,
-- but its positive endpoint coefficients enclose a zero.
private noncomputable def quartic : H 2 4 :=
  ⟨X 0 ^ 4 + X 1 ^ 4, (isHomogeneous_X_pow 0 4).add (isHomogeneous_X_pow 1 4)⟩

example : quartic ∉ L 2 4 := by
  intro h
  have hg := ((bivariate_mem_L_iff quartic).1 h).2.2 0 1 4 (by decide) (by decide) (by decide)
  norm_num [quartic, coeff_X_pow, Finsupp.ext_iff, Fin.forall_fin_two] at hg
