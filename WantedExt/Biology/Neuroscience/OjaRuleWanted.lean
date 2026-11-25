/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Oja's rule extracts the principal component

Oja (1982) proposed the Hebbian learning rule with normalization whose averaged form is the ODE
`z' = C z - (zᵀ C z) z`, where `C` is the input correlation matrix. When `C` is symmetric
positive semidefinite and its largest eigenvalue `λ₁` is simple with unit eigenvector `c`, every
solution with `z(0) · c > 0` converges to `c` (and to `-c` when `z(0) · c < 0`), and `±c` are
exponentially asymptotically stable. The vectors are in `ℝⁿ` with the Euclidean inner product
`z ⬝ᵥ z`; convergence is in the product topology (all norms on `ℝⁿ` agree).

Recorded here: the averaged ODE statements. The stochastic-approximation statement (almost sure
convergence of the stochastic rule with gains `γ_k`, `∑ γ_k = ∞`, `∑ γ_k² < ∞`, via the
Kushner–Clark lemma; Oja and Karhunen 1985) needs boundedness and recurrence hypotheses on the
iterates that the statement used for this module does not fix, so it is not stated. The
condition `λ₁ > 0` is automatic for `n ≥ 2` and is assumed explicitly to exclude `C = 0` in
dimension one.

`MathlibExt.Probability.Statistics.PCA` treats principal components statistically.

Sources: E. Oja, "A simplified neuron model as a principal component analyzer", J. Math. Biol. 15
(1982) 267–273; E. Oja and J. Karhunen, "On stochastic approximation of the eigenvectors and
eigenvalues of the expectation of a random matrix", J. Math. Anal. Appl. 106 (1985) 69–84.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

namespace WantedExt.Biology.Neuroscience.OjaRuleWanted

open Matrix Filter Topology

variable {n : ℕ}

/-- The **averaged Oja vector field** `F(z) = C z - (zᵀ C z) z`. -/
def ojaField (C : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) : Fin n → ℝ :=
  C *ᵥ z - (z ⬝ᵥ C *ᵥ z) • z

/-- `z` solves the averaged Oja ODE `z' = C z - (zᵀ C z) z` for all times `t ≥ 0`. -/
def IsOjaSolution (C : Matrix (Fin n) (Fin n) ℝ) (z : ℝ → Fin n → ℝ) : Prop :=
  ∀ t, 0 ≤ t → HasDerivAt z (ojaField C (z t)) t

/-- `c` is a unit eigenvector for a **simple top eigenvalue** `λ₁ > 0` of `C`: `C c = λ₁ c`,
`c ⬝ᵥ c = 1`, every eigenvector for `λ₁` is a multiple of `c`, and every eigenvalue of `C` is at
most `λ₁`. -/
structure IsTopEigenvector (C : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) (c : Fin n → ℝ) : Prop where
  pos : 0 < lam
  mulVec_eq : C *ᵥ c = lam • c
  unit : c ⬝ᵥ c = 1
  simple : ∀ v : Fin n → ℝ, C *ᵥ v = lam • v → ∃ a : ℝ, v = a • c
  le : ∀ (μ : ℝ) (v : Fin n → ℝ), v ≠ 0 → C *ᵥ v = μ • v → μ ≤ lam

/-- **Convergence of the averaged Oja rule** (Oja 1982). Let `C` be a real symmetric positive
semidefinite `n × n` matrix with a simple top eigenvalue `λ₁ > 0` and unit eigenvector `c`. Then
every solution `z` of `z' = C z - (zᵀ C z) z` on `[0, ∞)` with `z(0) ⬝ᵥ c > 0` converges to `c`,
and every solution with `z(0) ⬝ᵥ c < 0` converges to `-c`.

Source: E. Oja, "A simplified neuron model as a principal component analyzer", J. Math. Biol.
15 (1982) 267–273. -/
public theorem_wanted tendsto_oja {C : Matrix (Fin n) (Fin n) ℝ} (hC : C.PosSemidef) {lam : ℝ}
    {c : Fin n → ℝ} (hc : IsTopEigenvector C lam c) {z : ℝ → Fin n → ℝ}
    (hz : IsOjaSolution C z) :
    (0 < z 0 ⬝ᵥ c → Tendsto z atTop (𝓝 c)) ∧ (z 0 ⬝ᵥ c < 0 → Tendsto z atTop (𝓝 (-c)))

/-- **Exponential stability of the principal eigenvector** (Oja 1982). Under the hypotheses of
`tendsto_oja`, there are `δ > 0`, `K > 0` and `κ > 0` such that every solution `z` of the
averaged Oja ODE on `[0, ∞)` with `‖z(0) - c‖ < δ` satisfies
`‖z(t) - c‖ ≤ K e^{-κ t} ‖z(0) - c‖` for all `t ≥ 0`, and likewise every solution with
`‖z(0) + c‖ < δ` satisfies `‖z(t) + c‖ ≤ K e^{-κ t} ‖z(0) + c‖` for all `t ≥ 0`.

Source: E. Oja, "A simplified neuron model as a principal component analyzer", J. Math. Biol.
15 (1982) 267–273. -/
public theorem_wanted exponentially_stable_oja {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : C.PosSemidef) {lam : ℝ} {c : Fin n → ℝ} (hc : IsTopEigenvector C lam c) :
    ∃ δ > 0, ∃ K > 0, ∃ κ > 0, ∀ z : ℝ → Fin n → ℝ, IsOjaSolution C z →
      (‖z 0 - c‖ < δ → ∀ t, 0 ≤ t → ‖z t - c‖ ≤ K * Real.exp (-κ * t) * ‖z 0 - c‖) ∧
      (‖z 0 + c‖ < δ → ∀ t, 0 ≤ t → ‖z t + c‖ ≤ K * Real.exp (-κ * t) * ‖z 0 + c‖)

end WantedExt.Biology.Neuroscience.OjaRuleWanted
