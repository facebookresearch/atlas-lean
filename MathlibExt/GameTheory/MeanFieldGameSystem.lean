/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
public import MathlibExt.Probability.Diffusion.FokkerPlanckGradient

/-!
# The second-order mean field game system

The mean field game system of Lasry and Lions, in the form of Lions' Collège de France lectures
as written up by Cardaliaguet, on `ℝᵈ` (here `Fin d → ℝ`) and the time interval `[0, T]`:

* (i) `-∂ₜu - Δu + |Du|²/2 = F(x, m(t))` (Hamilton–Jacobi–Bellman, backward);
* (ii) `∂ₜm - Δm - div(m Du) = 0` (Fokker–Planck, forward);
* (iii) `m(0) = m₀`, `u(x, T) = G(x, m(T))`.

`u` is the value function of a typical player, who controls the drift of
`dXₜ = αₜ dt + √2 dWₜ` to minimise `E[∫ (|αₜ|²/2 + F(Xₜ, m(t))) dt + G(X_T, m(T))]`; its optimal
feedback is `α = -Du`, and `m(t)` is the law of the players under that feedback (Cardaliaguet,
Lemma 3.7). The Fokker–Planck equation is written with the repository's `fokkerPlanckOp` with
diffusion `1` and drift `-Du`, and `Δu = div(∇u)` with its `divergence` and `grad`.

## Main definitions

* `IsMFGClassicalSolution F G m₀ T u m μ`: `(u, m)` is a classical solution of the system, `μ t`
  being the probability measure with density `m(·, t)`.

## References

* P. Cardaliaguet, *Notes on Mean Field Games (from P.-L. Lions' lectures at Collège de France)*,
  version of 27 September 2013, §3 (system (8) and the definition before Theorem 3.1).
* J.-M. Lasry and P.-L. Lions, *Mean field games*, Japan. J. Math. 2 (2007) 229–260.
-/

@[expose] public section

open _root_.MeasureTheory Set
open MathlibExt.Probability.FokkerPlanck

namespace MathlibExt.GameTheory.MeanFieldGameSystem

variable {d : ℕ}

/-- **Classical solution of the mean field game system** (Lasry–Lions; Cardaliaguet, *Notes on
Mean Field Games*, 2013, system (8) and the definition of classical solution before
Theorem 3.1). The pair `u, m : ℝᵈ → ℝ → ℝ` is continuous on `ℝᵈ × [0, T]`, of class `C²` in space
and `C¹` in time on `ℝᵈ × (0, T)`, `m(·, t) ≥ 0` is the density of the probability measure `μ t`
for `t ∈ [0, T]` (with finite first moment, so that `F(x, μ t)` is defined on `P₁`), and
`-∂ₜu - Δu + |Du|²/2 = F(x, m(t))`, `∂ₜm - Δm - div(m Du) = 0` on `ℝᵈ × (0, T)`, with
`m(0) = m₀` and `u(·, T) = G(·, m(T))`. Cardaliaguet's sentence asks for the `C²`/`C¹`
regularity on `ℝᵈ × [0, T]`; here it is required only on the open interval, where the equations
are imposed, so that the Hölder initial densities and Lipschitz terminal costs of his
Theorem 3.1 are admissible data. -/
def IsMFGClassicalSolution (F G : (Fin d → ℝ) → ProbabilityMeasure (Fin d → ℝ) → ℝ)
    (m₀ : (Fin d → ℝ) → ℝ) (T : ℝ) (u m : (Fin d → ℝ) → ℝ → ℝ)
    (μ : ℝ → ProbabilityMeasure (Fin d → ℝ)) : Prop :=
  ContinuousOn (fun q : (Fin d → ℝ) × ℝ => u q.1 q.2) (univ ×ˢ Icc 0 T) ∧
  ContinuousOn (fun q : (Fin d → ℝ) × ℝ => m q.1 q.2) (univ ×ˢ Icc 0 T) ∧
  (∀ t ∈ Ioo 0 T, ContDiff ℝ 2 (fun x => u x t) ∧ ContDiff ℝ 2 (fun x => m x t)) ∧
  (∀ x, ContDiffOn ℝ 1 (u x) (Ioo 0 T) ∧ ContDiffOn ℝ 1 (m x) (Ioo 0 T)) ∧
  (∀ t ∈ Icc 0 T, (∀ x, 0 ≤ m x t) ∧ (μ t : Measure (Fin d → ℝ)) =
      volume.withDensity (fun x => ENNReal.ofReal (m x t)) ∧
    Integrable (fun x => ‖x‖) (μ t : Measure (Fin d → ℝ))) ∧
  (∀ t ∈ Ioo 0 T, ∀ x, -deriv (u x) t - divergence (grad fun y => u y t) x +
      (∑ i, grad (fun y => u y t) x i ^ 2) / 2 = F x (μ t)) ∧
  (∀ t ∈ Ioo 0 T, ∀ x,
      deriv (m x) t = fokkerPlanckOp 1 (fun y => -grad (fun z => u z t) y) (fun y => m y t) x) ∧
  (∀ x, m x 0 = m₀ x) ∧ (∀ x, u x T = G x (μ T))

end MathlibExt.GameTheory.MeanFieldGameSystem
