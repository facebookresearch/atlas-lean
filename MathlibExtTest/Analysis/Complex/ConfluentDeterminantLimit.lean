/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.LinearAlgebra.Vandermonde
import MathlibExt.Analysis.Complex.ConfluentDeterminantLimit

open Complex Finset Filter Topology
open scoped Nat

/-! Concrete instances of the confluent determinant limit. -/

#check @Complex.tendsto_det_div_prod_sub
#check @Complex.tendsto_det_div_prod_sub_of_injective

/-- Sanity check of the denominator: for the monomials `z ^ k` the quotient is identically `1` at
pairwise distinct points (Vandermonde). -/
example {g : ℕ} (z : Fin g → ℂ) (hz : Function.Injective z) :
    (Matrix.of fun k l : Fin g => z l ^ (k : ℕ)).det / ∏ k, ∏ l with k < l, (z l - z k) = 1 := by
  have h : (Matrix.of fun k l : Fin g => z l ^ (k : ℕ)) = (Matrix.vandermonde z).transpose := by
    ext k l
    simp [Matrix.vandermonde]
  have hne : ∏ k, ∏ l ∈ Ioi k, (z l - z k) ≠ 0 :=
    prod_ne_zero_iff.2 fun k _ => prod_ne_zero_iff.2 fun l hl =>
      sub_ne_zero.2 (hz.ne (ne_of_gt (mem_Ioi.1 hl)))
  simp only [filter_lt_eq_Ioi]
  rw [h, Matrix.det_transpose, Matrix.det_vandermonde]
  exact div_self hne

/-- The monomial case for `g = 2`: `f_0 = 1`, `f_1 = z`; the limit is `det [[1, 0], [a, 1]] = 1`. -/
example (a : ℂ) :
    Tendsto (fun z : Fin 2 → ℂ =>
        (Matrix.of fun k l : Fin 2 => z l ^ (k : ℕ)).det / ∏ k, ∏ l with k < l, (z l - z k))
      (𝓝[{z | Function.Injective z ∧ ∀ l, z l ∈ Set.univ}] fun _ => a) (𝓝 1) := by
  have h := tendsto_det_div_prod_sub (f := fun (k : Fin 2) (z : ℂ) => z ^ (k : ℕ)) isOpen_univ
    (Set.mem_univ a)
    (fun k => (differentiable_pow (k : ℕ)).differentiableOn)
  convert h using 2
  simp [Matrix.det_fin_two]

/-- `g = 2` with `f_0 = 1` and `f_1 = exp`: `(e^{z_1} - e^{z_0}) / (z_1 - z_0) → e^a`. -/
example (a : ℂ) :
    Tendsto (fun z : Fin 2 → ℂ =>
        (Matrix.of fun k l => (![fun _ => 1, Complex.exp] : Fin 2 → ℂ → ℂ) k (z l)).det /
          ∏ k, ∏ l ∈ Ioi k, (z l - z k))
      (𝓝[{z | Function.Injective z}] fun _ => a) (𝓝 (Complex.exp a)) := by
  have h := tendsto_det_div_prod_sub_of_injective
    (f := ![fun _ => 1, Complex.exp]) (U := Set.univ) (a := a) Filter.univ_mem
    (fun k => by
      fin_cases k
      · exact differentiableOn_const _
      · exact Complex.differentiable_exp.differentiableOn)
  convert h using 2
  simp [Matrix.det_fin_two]

/-- The `g = 2` quotient is the first divided difference `(f_1(z_1) - f_1(z_0)) / (z_1 - z_0)`
when `f_0 = 1`. -/
example (z : Fin 2 → ℂ) :
    (Matrix.of fun k l => (![fun _ => 1, Complex.exp] : Fin 2 → ℂ → ℂ) k (z l)).det /
        ∏ k, ∏ l ∈ Ioi k, (z l - z k) =
      (Complex.exp (z 1) - Complex.exp (z 0)) / (z 1 - z 0) := by
  have h : Ioi (1 : Fin 2) = ∅ := by decide
  simp [Matrix.det_fin_two, Fin.prod_univ_two, h]
