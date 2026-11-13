/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import MathlibExt.Analysis.SpecialFunctions.Softplus

/-!
# Logistic negative log-likelihood is convex in coefficients

For a design matrix `X`, outcomes `y`, and coefficients `β`, the
logistic negative log-likelihood
`∑ i, [log (1 + exp (x_i ⬝ β)) - y_i (x_i ⬝ β)]` is convex in `β` on
the whole coefficient space. Each summand is the scalar softplus
composed with the linear map `β ↦ x_i ⬝ β`, minus a linear term
(Atlas roadmap ST09.T02). The scalar fact is the shared softplus
convexity `Real.convexOn_softplus`.
-/

@[expose] public section


open Finset

namespace MathlibExt.Probability.Statistics.LogisticRegression

/-- The logistic negative log-likelihood (NLL) of binary outcomes `y`
against a design matrix `X` at coefficients `β`:
`∑ i, [log (1 + exp (x_i ⬝ β)) - y_i (x_i ⬝ β)]`.
For binary outcomes `y_i ∈ {0, 1}` this is the usual logistic NLL;
convexity below holds for arbitrary real `y`, since the second term is
linear in `β`. -/
noncomputable def logisticNLL {n m : ℕ} (X : Fin n → Fin m → ℝ) (y : Fin n → ℝ)
    (β : Fin m → ℝ) : ℝ :=
  ∑ i, (Real.log (1 + Real.exp (∑ j, X i j * β j)) - y i * ∑ j, X i j * β j)

/-- **Logistic NLL is convex in the coefficients (ST09.T02).** Each
summand is the scalar softplus composed with the linear map
`β ↦ x_i ⬝ β`, minus a linear term; a sum of convex functions is convex. -/
theorem convexOn_logisticNLL {n m : ℕ} (X : Fin n → Fin m → ℝ) (y : Fin n → ℝ) :
    ConvexOn ℝ Set.univ (logisticNLL X y) := by
  set L : Fin n → ((Fin m → ℝ) →ₗ[ℝ] ℝ) :=
    fun i => ∑ j : Fin m, X i j • LinearMap.proj j with hLdef
  have hL : ∀ (i : Fin n) (β : Fin m → ℝ), (L i) β = ∑ j, X i j * β j := by
    intro i β
    simp [hLdef]
  have hsoft : ∀ i : Fin n, ConvexOn ℝ Set.univ
      (fun β : Fin m → ℝ => Real.log (1 + Real.exp ((L i) β))) := by
    intro i
    have h := Real.convexOn_softplus.comp_linearMap (L i)
    rw [Set.preimage_univ] at h
    exact h.congr (fun β _ => rfl)
  have hlinmap : ∀ i : Fin n, ConcaveOn ℝ Set.univ
      (fun β : Fin m → ℝ => y i * ((L i) β)) := by
    intro i
    have h := ((y i) • (L i)).concaveOn convex_univ
    refine h.congr (fun β _ => ?_)
    simp [smul_eq_mul]
  have hsummand : ∀ i : Fin n, ConvexOn ℝ Set.univ
      (fun β : Fin m → ℝ => Real.log (1 + Real.exp ((L i) β)) - y i * ((L i) β)) := by
    intro i
    exact ((hsoft i).sub (hlinmap i)).congr (fun β _ => rfl)
  have hsum : ∀ s : Finset (Fin n), ConvexOn ℝ Set.univ
      (fun β : Fin m → ℝ => ∑ i ∈ s,
        (Real.log (1 + Real.exp ((L i) β)) - y i * ((L i) β))) := by
    intro s
    refine Finset.induction ?_ ?_ s
    · have hfun : (fun β : Fin m → ℝ => ∑ i ∈ (∅ : Finset (Fin n)),
          (Real.log (1 + Real.exp ((L i) β)) - y i * ((L i) β))) = fun _ => 0 := by
        funext β
        simp
      rw [hfun]
      exact convexOn_const 0 convex_univ
    · intro a s has ih
      have hfun : (fun β : Fin m → ℝ => ∑ i ∈ insert a s,
            (Real.log (1 + Real.exp ((L i) β)) - y i * ((L i) β)))
          = (fun β : Fin m → ℝ => Real.log (1 + Real.exp ((L a) β)) - y a * ((L a) β))
            + (fun β : Fin m → ℝ => ∑ i ∈ s,
              (Real.log (1 + Real.exp ((L i) β)) - y i * ((L i) β))) := by
        funext β
        simp only [Finset.sum_insert has, Pi.add_apply]
      rw [hfun]
      exact (hsummand a).add ih
  have h := hsum Finset.univ
  have hfun : logisticNLL X y = (fun β : Fin m → ℝ => ∑ i ∈ Finset.univ,
      (Real.log (1 + Real.exp ((L i) β)) - y i * ((L i) β))) := by
    funext β
    simp only [logisticNLL]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hL i β]
  rw [hfun]
  exact h

end MathlibExt.Probability.Statistics.LogisticRegression
