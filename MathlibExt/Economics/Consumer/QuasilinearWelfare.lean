/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Envelope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Quasilinear surplus equals the expenditure-based welfare change

Frozen model: one good with consumption set `Z : Set ℝ` and price `p`, and a numeraire `m : ℝ`
with price `1`. Utility is quasilinear, `U(z, m) = φ z + m`, and the numeraire is unrestricted in
sign, so no wealth or nonnegativity constraint on `m` binds: there are no binding income effects.
A bundle `(z, m)` costs `p * z + m`.

Let `e p` be the expenditure function at a reference utility `ubar` (near every price between `p₁`
and `p₀`, the greatest lower bound of the costs of bundles reaching `ubar`), and let `x p ∈ Z`
maximize `φ z - p * z`. If `e` is differentiable along the price path and `x` is interval
integrable, then the expenditure-based welfare change of a price move from `p₀` to `p₁` equals the
change in consumer surplus:

  `e p₀ - e p₁ = ∫ p in p₁..p₀, x p`.

Sign convention: gains are positive. `e p₀ - e p₁` is the compensating variation when `ubar` is
the utility at `p₀` and the equivalent variation when `ubar` is the utility at `p₁`; in this model
both equal the surplus change. The proof is the envelope argument (`e' = x`, Shephard's lemma for
one good) followed by the fundamental theorem of calculus.

## Main results

* `Economics.Consumer.quasilinear_expenditure_sub_eq_integral_demand`.

## References

* A. Mas-Colell, M. D. Whinston, J. R. Green, *Microeconomic Theory*, Oxford University Press
  (1995), Section 3.I.
-/

@[expose] public section

open Filter Topology Set

namespace Economics.Consumer

/-- **Quasilinear surplus equals welfare change.** In the quasilinear model
with unrestricted numeraire, suppose `e` is the expenditure function at
reference utility `ubar` near every price in `[[p₀, p₁]]`, `x p` maximizes
`φ z - p * z` over `Z` for every such price, `e` is differentiable there, and
`x` is interval integrable. Then the expenditure-based welfare change
`e p₀ - e p₁` equals the consumer-surplus change `∫ p in p₁..p₀, x p`. -/
theorem quasilinear_expenditure_sub_eq_integral_demand {Z : Set ℝ}
    {φ : ℝ → ℝ} {x e : ℝ → ℝ} {ubar p₀ p₁ : ℝ}
    (he : ∀ p ∈ uIcc p₀ p₁, ∀ᶠ q in 𝓝 p,
      IsGLB ((fun b : ℝ × ℝ => q * b.1 + b.2) ''
        {b | b.1 ∈ Z ∧ ubar ≤ φ b.1 + b.2}) (e q))
    (hx : ∀ p ∈ uIcc p₀ p₁, x p ∈ Z ∧
      ∀ z ∈ Z, φ z - p * z ≤ φ (x p) - p * x p)
    (hdiff : ∀ p ∈ uIcc p₀ p₁, DifferentiableAt ℝ e p)
    (hint : IntervalIntegrable x MeasureTheory.volume p₁ p₀) :
    e p₀ - e p₁ = ∫ p in p₁..p₀, x p := by
  have hderiv : ∀ q ∈ uIcc p₁ p₀, HasDerivAt e (x q) q := by
    intro q hq
    rw [Set.uIcc_comm p₁ p₀] at hq
    have hubar : ubar ≤ φ (x q) + (ubar - φ (x q)) := by linarith
    have hle : ∀ᶠ t in 𝓝 q, e t ≤ t * x q + (ubar - φ (x q)) := by
      filter_upwards [he q hq] with t ht
      have hmem : t * x q + (ubar - φ (x q)) ∈ (fun b : ℝ × ℝ => t * b.1 + b.2) ''
          {b | b.1 ∈ Z ∧ ubar ≤ φ b.1 + b.2} :=
        ⟨(x q, ubar - φ (x q)), ⟨(hx q hq).1, hubar⟩, rfl⟩
      exact ht.1 hmem
    have heq : e q = q * x q + (ubar - φ (x q)) := by
      have hGLB : IsGLB ((fun b : ℝ × ℝ => q * b.1 + b.2) ''
          {b | b.1 ∈ Z ∧ ubar ≤ φ b.1 + b.2}) (e q) := (he q hq).self_of_nhds
      have hleast : IsLeast ((fun b : ℝ × ℝ => q * b.1 + b.2) ''
          {b | b.1 ∈ Z ∧ ubar ≤ φ b.1 + b.2}) (q * x q + (ubar - φ (x q))) := by
        refine ⟨⟨(x q, ubar - φ (x q)), ⟨(hx q hq).1, hubar⟩, rfl⟩, ?_⟩
        intro c hc
        obtain ⟨b, hb, hcb⟩ := hc
        obtain ⟨hbZ, hbub⟩ := hb
        subst hcb
        show q * x q + (ubar - φ (x q)) ≤ q * b.1 + b.2
        have hmax := (hx q hq).2 b.1 hbZ
        linarith
      exact hGLB.unique hleast.isGLB
    have hmul : HasDerivAt (fun t : ℝ => t * x q) (x q) q := hasDerivAt_mul_const (x q)
    have hg : HasDerivAt (fun t => t * x q + (ubar - φ (x q))) (x q) q :=
      HasDerivAt.add_const (ubar - φ (x q)) hmul
    have hF := Economics.hasFDerivAt_eq_of_eventually_le_of_eq (f := e)
      (g := fun t => t * x q + (ubar - φ (x q))) hle heq
      (hdiff q hq).hasFDerivAt hg.hasFDerivAt
    have hde := (hdiff q hq).hasFDerivAt.hasDerivAt
    rw [hF] at hde
    simpa using hde
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint).symm

end Economics.Consumer
