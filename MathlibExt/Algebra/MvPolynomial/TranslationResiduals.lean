/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import MathlibExt.Algebra.MvPolynomial.TranslationSupport

/-!
# Translating the inputs of a polynomial regression

The polynomial in the new coordinates is obtained by substitution, independently of the
observed rows or their responses. This concerns matching polynomials, not the minimizers of a
penalized objective. Source: Martini et al., Proposition 1, <https://doi.org/10.1534/g3.118.200961>.
-/

namespace MvPolynomial

/-- For a real multivariate polynomial `p` and a shift vector `a`, form `q` by substituting
`X i + C (a i)` for each variable. Then `q(u) = p(u + a)` at every input. At rows shifted by
`-a` the fitted values agree, so the residual sums of squares agree for any finite set of
rows and any real responses. Every coefficient of total degree `p.totalDegree` agrees, even
if it is zero. Neither completeness of a model nor nonemptiness of the data is required. -/
public theorem polynomialTranslation_residuals_and_topCoefficients {σ ι : Type*}
    (p : MvPolynomial σ ℝ) (a : σ → ℝ) (rows : ι → σ → ℝ) (y : ι → ℝ) (s : Finset ι) :
    let q := aeval (fun i => X i + C (a i)) p
    (∀ u, eval u q = eval (u + a) p) ∧
    (∀ j, eval (rows j - a) q = eval (rows j) p) ∧
    (∑ j ∈ s, (y j - eval (rows j - a) q) ^ 2) = (∑ j ∈ s, (y j - eval (rows j) p) ^ 2) ∧
    ∀ d : σ →₀ ℕ, d.degree = p.totalDegree → q.coeff d = p.coeff d := by
  dsimp only
  have ev (u : σ → ℝ) : eval u (aeval (fun i => X i + C (a i)) p) = eval (u + a) p := by
    change aeval u (aeval _ p) = aeval (u + a) p
    simp only [comp_aeval_apply, map_add, aeval_X, aeval_C, Algebra.algebraMap_self_apply,
      Pi.add_def]
  have row (j : ι) := ev (rows j - a)
  simp only [sub_add_cancel] at row
  exact ⟨ev, row, by simp only [row], fun d hd =>
    coeff_aeval_X_add_C_of_totalDegree_le p a d hd.ge⟩

end MvPolynomial
