/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.MachineLearning.NeuralNetworks.BarronSpace

/-!
# The inverse approximation theorem for the Barron space

W. E, C. Ma and L. Wu, *The Barron space and the flow-induced function spaces for neural network
models*, Constr. Approx. 55 (2022), arXiv:1906.08039, §2.2:

* **Theorem 5 (inverse approximation).** A function on the cube that is the pointwise limit of
  two-layer networks with path norm at most `Q` lies in the Barron space with `‖f‖_B ≤ Q`
  (Prokhorov's theorem on the normalized parameter measures).

The direct approximation theorem, Theorem 4 of the same paper, is proved in
`CSLibExt.MachineLearning.NeuralNetworks.BarronApproximation`.

Networks are written with the normalisation of the paper,
`f_m(x; Θ) = (1/m) ∑ₖ aₖ σ(⟨bₖ, x⟩ + cₖ)` and `‖Θ‖_P = (1/m) ∑ₖ |aₖ| (‖bₖ‖₁ + |cₖ|)`, using
`CSLibExt.MachineLearning.NeuralNetworks.reluNeuron` for one neuron. The Barron norm is
`CSLibExt.MachineLearning.NeuralNetworks.barronNorm` (the `B₂` norm, which the paper's
Proposition 1 identifies with every `B_p` norm).
-/

@[expose] public section

set_option autoImplicit false

namespace CSLibExt.MachineLearning.NeuralNetworks

open MeasureTheory Filter Topology

/-- **Inverse approximation theorem for the Barron space** (W. E, C. Ma and L. Wu, *The Barron
space and the flow-induced function spaces for neural network models*, Constr. Approx. 55 (2022),
Theorem 5). Let `f` be continuous on the cube `[0, 1]^d` and `Q` real. Suppose a sequence of
two-layer ReLU networks `f_k(x) = (1/w_k) ∑_{i < w_k} aᵢ σ(⟨bᵢ, x⟩ + cᵢ)` of widths `w_k ≥ 1`,
each with path norm `(1/w_k) ∑ᵢ |aᵢ| (‖bᵢ‖₁ + |cᵢ|) ≤ Q`, converges to `f` at every point of
the cube. Then `f` has a Barron representation `ρ` on the cube, and `‖f‖_B ≤ Q`. -/
theorem_wanted barron_inverse_approximation {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContinuousOn f (unitCube d)) (Q : ℝ) (w : ℕ → ℕ) (hw : ∀ k, 0 < w k)
    (θ : (k : ℕ) → Fin (w k) → ℝ × (Fin d → ℝ) × ℝ)
    (hpath : ∀ k, (w k : ℝ)⁻¹ * ∑ i, |(θ k i).1| * (∑ j, |(θ k i).2.1 j| + |(θ k i).2.2|) ≤ Q)
    (hlim : ∀ x ∈ unitCube d,
      Tendsto (fun k => (w k : ℝ)⁻¹ * ∑ i, reluNeuron (θ k i) x) atTop (𝓝 (f x))) :
    (∃ ρ, IsBarronRepresentation f ρ) ∧ barronNorm f ≤ ENNReal.ofReal Q

end CSLibExt.MachineLearning.NeuralNetworks
