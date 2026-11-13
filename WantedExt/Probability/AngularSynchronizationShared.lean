/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Angular synchronization: the Gaussian noise model and the least-squares problem

Shared helper for the UnsolvedMath entries on Bandeira's Open Problems 10.1 and 10.2
(`WantedExt/Probability/AngularSynchronizationPowerMethodAMR27Problem1001Wanted.lean` and
`WantedExt/Probability/AngularSynchronizationSDPTightnessAMR27Problem1002Wanted.lean`), so both
speak about the same noise model and the same problem (P).
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

namespace MathlibExt.Probability.AngularSynchronizationShared

/-!
The model is that of Y. Zhong and N. Boumal, Near-optimal bounds for phase synchronization, SIAM J.
Optim. 28 (2018), 989-1016, arXiv:1703.06605, Section 1, equations (1)-(2) and problem (P): the
signal is `z ∈ ℂⁿ` with `|z_k| = 1`, the measurements are `C = z z* + σ W` with `σ ≥ 0`, where `W`
is Hermitian with `W_kk = 0` and independent standard complex Gaussian entries `W_kl`, `k < l`.
Here the real and imaginary parts of `W_kl` are independent `N(0, 1/2)` (so `E |W_kl|² = 1`); the
theorems of Zhong and Boumal (Section 2) hold for any independent centered sub-gaussian real and
imaginary parts, which covers this choice. The noise is sampled from independent real Gaussians
`ω (k, l, 0)`, `ω (k, l, 1)` indexed by all `(k, l)`; only the pairs `k < l` are used.

Problem (P) is `max x* C x` subject to `|x_k| = 1` for all `k`. Since `C` is unchanged in law when
`z` is replaced by `e^{iθ} z`, solutions are compared up to a global phase.
-/

open MeasureTheory ProbabilityTheory Matrix Complex

/-- The noise distribution in dimension `n`: independent real Gaussians `ω (k, l, i) ∼ N(0, 1/2)`
indexed by `k, l : Fin n` and `i : Fin 2` (only the pairs `k < l` enter `noiseMatrix`). -/
noncomputable def noiseMeasure (n : ℕ) : Measure (Fin n × Fin n × Fin 2 → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 2⁻¹

/-- The Hermitian noise matrix `W`: `W_kl = ω (k, l, 0) + i ω (k, l, 1)` for `k < l` (a standard
complex Gaussian under `noiseMeasure`), `W_lk = conj W_kl` and `W_kk = 0`. -/
def noiseMatrix {n : ℕ} (ω : Fin n × Fin n × Fin 2 → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun k l =>
    if k < l then ⟨ω (k, l, 0), ω (k, l, 1)⟩ else if l < k then ⟨ω (l, k, 0), -ω (l, k, 1)⟩ else 0

/-- The measurement matrix `C = z z* + σ W` of angular synchronization with signal `z`. -/
def measurementMatrix {n : ℕ} (z : Fin n → ℂ) (σ : ℝ) (ω : Fin n × Fin n × Fin 2 → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  vecMulVec z (star z) + (σ : ℂ) • noiseMatrix ω

/-- `x` is a vector of phases, `|x_k| = 1` for every `k`: the feasible set of problem (P). -/
def IsPhaseVector {n : ℕ} (x : Fin n → ℂ) : Prop :=
  ∀ k, ‖x k‖ = 1

/-- The quadratic form `x* C x` (real part; it is real when `C` is Hermitian). -/
noncomputable def quadForm {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : ℝ :=
  (star x ⬝ᵥ (C *ᵥ x)).re

/-- `xhat` is a global maximizer of problem (P), `max x* C x` subject to `|x_k| = 1`, and it is
unique up to a global phase: every maximizer is `e^{iθ} xhat`. -/
def IsUniqueOptimumUpToPhase {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (xhat : Fin n → ℂ) : Prop :=
  IsPhaseVector xhat ∧ (∀ y, IsPhaseVector y → quadForm C y ≤ quadForm C xhat) ∧
    ∀ y, IsPhaseVector y → quadForm C y = quadForm C xhat → ∃ θ : ℝ, y = exp (θ * I) • xhat

end MathlibExt.Probability.AngularSynchronizationShared
