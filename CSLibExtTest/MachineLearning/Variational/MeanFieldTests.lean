/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Variational.MeanField

/-!
# Variational inference tests

Closed checks: ELBO = log evidence - KL, the KL bounds, and the monotone ELBO along mean-field
coordinate-ascent sweeps, instantiated on latent spaces `Fin 3 × Fin 2`. A zero-support
regression shows the finite KL formula's value when `r` lacks full support. The definitions are
real-valued and not executable.
-/

namespace Cslib.MachineLearning.Variational

open Real Cslib.MachineLearning.LatentVariable.ExpectationMaximization

example (p : Fin 3 × Fin 2 → ℝ) (hp : ∀ z, 0 < p z) (q : Fin 3 × Fin 2 → ℝ) (hq : IsDist q) :
    elbo p q = log (evidence p) - kl q (posterior p) :=
  elbo_eq_log_evidence_sub_kl hp hq

example (p : Fin 3 × Fin 2 → ℝ) (q₁ : Fin 3 → ℝ) (q₂ : Fin 2 → ℝ) (h₁ : IsDist q₁)
    (h₂ : IsDist q₂) {s t : ℕ} (hst : s ≤ t) :
    elbo p (prodDist ((sweep p)^[s] (q₁, q₂)).1 ((sweep p)^[s] (q₁, q₂)).2) ≤
      elbo p (prodDist ((sweep p)^[t] (q₁, q₂)).1 ((sweep p)^[t] (q₁, q₂)).2) :=
  elbo_iterate_sweep_monotone p ⟨h₁, h₂⟩ hst

example (p : Fin 3 × Fin 2 → ℝ) (hp : ∀ z, 0 < p z) (q₂ : Fin 2 → ℝ) (h₂ : IsDist q₂) :
    elbo p (prodDist (cavi p q₂) q₂) ≤ log (evidence p) :=
  elbo_prodDist_le_log_evidence hp (isDist_cavi p q₂) h₂

example (q r : Fin 3 → ℝ) (hq : IsDist q) (hr : ∀ z, 0 < r z) (hrs : ∑ z, r z = 1) :
    0 ≤ kl q r :=
  kl_nonneg hq hr hrs

/-- Zero-support regression: for `q = (1/2, 1/2)` and `r = (1, 0)` the true divergence is infinite,
while the finite formula `kl` (with `Real.log 0 = 0`) is `log (1/2) < 0`. This is why every theorem
here takes `r` with full support. -/
example : kl ![(1 / 2 : ℝ), 1 / 2] ![1, 0] = log (1 / 2) := by
  simp [kl, Fin.sum_univ_two]
  ring

#print axioms elbo_eq_log_evidence_sub_kl
#print axioms elbo_iterate_sweep_monotone

end Cslib.MachineLearning.Variational
