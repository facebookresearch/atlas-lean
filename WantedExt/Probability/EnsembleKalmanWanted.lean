/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import MathlibExt.Probability.BayesianInverse.EnsembleKalman

/-!
# Ensemble Kalman inversion: wishlist

Established results on ensemble Kalman inversion whose proofs are deferred. The invariant
subspace property is proved in `MathlibExt.Probability.BayesianInverse.EnsembleKalman`.

* `eki_ensemble_collapse`: in the continuous-time limit of ensemble Kalman inversion for a linear
  forward map and noise-free data, the ensemble collapses: `|E_{lj}(t)| ≤ J/(2t)` (Schillings-Stuart
  Theorem 3, with the explicit constant of its proof).
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.EnsembleKalmanWanted

open MathlibExt.Probability.BayesianInverse
open scoped InnerProductSpace

section EnsembleKalman

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- **Ensemble collapse for continuous-time ensemble Kalman inversion.** Let `A : X → Y` be
bounded linear, `Γ` a positive invertible covariance on `Y` with
`⟨a, b⟩_Γ = ⟨a, Γ⁻¹ b⟩`, and data `y = A u†` without noise. If the ensemble
`u⁽¹⁾(t), …, u⁽ᴶ⁾(t)` solves, for `t > 0`, the continuous-time EKI equations
`du⁽ʲ⁾/dt = (1/J) Σₖ ⟨A(u⁽ᵏ⁾ - ū), y - A u⁽ʲ⁾⟩_Γ (u⁽ᵏ⁾ - ū)`,
then for every `t > 0` every entry `E_{lj}(t) = ⟨A e⁽ˡ⁾, A e⁽ʲ⁾⟩_Γ` of the spread matrix, with
`e⁽ʲ⁾ = u⁽ʲ⁾ - ū`, satisfies `|E_{lj}(t)| ≤ J / (2t)` (Schillings and Stuart, *Analysis of the
ensemble Kalman filter for inverse problems*, SIAM J. Numer. Anal. 55 (2017), arXiv:1602.02020,
equation (8) and Theorem 3). The theorem states `‖E(t)‖ = O(J t⁻¹)`; the explicit bound is what
its proof gives: `E` solves `dE/dt = -(2/J) E²`, so its eigenvalues are
`(2(t - s)/J + 1/λ(s))⁻¹ ≤ J/(2(t - s))` for `0 < s < t` (or `0`), and the entries of a positive
semidefinite matrix are bounded by its largest eigenvalue. -/
theorem_wanted eki_ensemble_collapse {J : ℕ} (A : X →L[ℝ] Y) (Γ : Y ≃L[ℝ] Y)
    (hΓ : (Γ : Y →L[ℝ] Y).IsPositive) (u_true : X) (u : ℝ → Fin J → X)
    (hode : ∀ t > 0, ∀ j, HasDerivAt (fun s ↦ u s j)
      ((J : ℝ)⁻¹ • ∑ k, ⟪A (u t k - ensembleMean (u t)), Γ.symm (A u_true - A (u t j))⟫_ℝ •
        (u t k - ensembleMean (u t))) t)
    (l j : Fin J) {t : ℝ} (ht : 0 < t) :
    |⟪A (u t l - ensembleMean (u t)), Γ.symm (A (u t j - ensembleMean (u t)))⟫_ℝ| ≤
      (J : ℝ) / (2 * t)

end EnsembleKalman

end MathlibExt.Probability.EnsembleKalmanWanted
