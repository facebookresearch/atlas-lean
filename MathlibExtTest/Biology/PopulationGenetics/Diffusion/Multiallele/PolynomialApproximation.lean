/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.Multiallele.PolynomialApproximation

/-!
# Tests for C² polynomial approximation

The examples restate the polynomial derivative bridge, the compact-set
approximation theorem, and its simplex form.
-/

@[expose] public section

open MvPolynomial MathlibExt.Biology.PopulationGenetics.Diffusion

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.Multiallele.PolynomialApproximation

example {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (fun y => eval y p)
      (∑ i, eval x (pderiv i p) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)
      x :=
  hasFDerivAt_mvPolynomial_eval p x

example {n : ℕ} {K U : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiffOn ℝ 2 f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℝ, ∀ x ∈ K,
      |eval x p - f x| ≤ ε ∧
      (∀ i, |eval x (pderiv i p) - fderiv ℝ f x (Pi.single i 1)| ≤ ε) ∧
      ∀ i j, |eval x (pderiv i (pderiv j p)) -
        fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x (Pi.single i 1)| ≤ ε :=
  exists_mvPolynomial_near_contDiffOn_two hK hU hKU hf hε

example {n : ℕ} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (hΔU : {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} ⊆ U)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ 2 f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℝ, ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → ∑ i, x i ≤ 1 →
      |eval x p - f x| ≤ ε ∧
      (∀ i, |eval x (pderiv i p) - fderiv ℝ f x (Pi.single i 1)| ≤ ε) ∧
      ∀ i j, |eval x (pderiv i (pderiv j p)) -
        fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x (Pi.single i 1)| ≤ ε :=
  exists_mvPolynomial_near_contDiffOn_two_simplex hU hΔU hf hε

#print axioms MathlibExt.Biology.PopulationGenetics.Diffusion.hasFDerivAt_mvPolynomial_eval
#print axioms MathlibExt.Biology.PopulationGenetics.Diffusion.exists_mvPolynomial_near_contDiffOn_two
#print axioms MathlibExt.Biology.PopulationGenetics.Diffusion.exists_mvPolynomial_near_contDiffOn_two_simplex

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.Multiallele.PolynomialApproximation
