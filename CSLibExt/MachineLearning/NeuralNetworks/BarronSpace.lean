/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The Barron space of two-layer ReLU networks

W. E, C. Ma and L. Wu (*The Barron space and the flow-induced function spaces for neural network
models*, Constr. Approx. 55 (2022), arXiv:1906.08039, §2.1) consider the functions on the cube
`X = [0, 1]^d` that are expectations of single ReLU neurons,

`f(x) = ∫ a σ(⟨b, x⟩ + c) ρ(da, db, dc)`, `σ(t) = max t 0`, (their equation (1))

for a probability measure `ρ` on `ℝ × ℝ^d × ℝ`, the continuum analogue of the two-layer network
`(1/m) ∑ₖ aₖ σ(⟨bₖ, x⟩ + cₖ)`. The Barron norm of `f` is the infimum over such representations of
`(𝔼_ρ |a|^p (‖b‖₁ + |c|)^p)^{1/p}` (their equation (3)); for the ReLU all `p ∈ [1, ∞]` give the
same norm (their Proposition 1, not formalized here). This file records the representations
(`IsBarronRepresentation`) and the norm for `p = 2` (`barronNorm`), the case used in the proofs
of their Theorem 4 and of Theorem 3.1 of E, Ma and Wu, *A priori estimates of the population risk
for two-layer neural networks*, Commun. Math. Sci. 17 (2019). The norm takes values in `[0, ∞]`
and is `∞` exactly when `f` has no representation with finite second moment.

The only theorem proved here is the sanity check that a single neuron has Barron norm at most
`|a| (‖b‖₁ + |c|)` (`barronNorm_neuron_le`), represented by a Dirac mass. The approximation
theorems for the Barron space are recorded in
`WantedExt.ComputerScience.MachineLearning.BarronApproximationWanted`.
-/

@[expose] public section

set_option autoImplicit false

namespace CSLibExt.MachineLearning.NeuralNetworks

open MeasureTheory

variable {d : ℕ}

/-- **The unit cube** `X = [0, 1]^d`, the input domain fixed by E, Ma and Wu (*The Barron space
and the flow-induced function spaces for neural network models*, §1, Notations). -/
def unitCube (d : ℕ) : Set (Fin d → ℝ) := Set.univ.pi fun _ => Set.Icc 0 1

/-- **ReLU neuron.** The output `a σ(⟨b, x⟩ + c)` of the neuron with parameters `θ = (a, b, c)`
at the input `x`, with `σ(t) = max t 0`. -/
def reluNeuron (θ : ℝ × (Fin d → ℝ) × ℝ) (x : Fin d → ℝ) : ℝ :=
  θ.1 * max (∑ j, θ.2.1 j * x j + θ.2.2) 0

/-- **Barron representation.** A measure `ρ` on the parameters `(a, b, c) ∈ ℝ × ℝ^d × ℝ`
represents `f` on the cube when `ρ` is a probability measure and, for every `x ∈ [0, 1]^d`, the
neuron output is `ρ`-integrable with `f(x) = ∫ a σ(⟨b, x⟩ + c) dρ` (E, Ma and Wu, *The Barron space
and the flow-induced function spaces for neural network models*, equation (1)). -/
def IsBarronRepresentation (f : (Fin d → ℝ) → ℝ) (ρ : Measure (ℝ × (Fin d → ℝ) × ℝ)) : Prop :=
  IsProbabilityMeasure ρ ∧ ∀ x ∈ unitCube d,
    Integrable (fun θ => reluNeuron θ x) ρ ∧ f x = ∫ θ, reluNeuron θ x ∂ρ

/-- **Barron norm** (`p = 2`): `‖f‖_B = inf_ρ (𝔼_ρ |a|² (‖b‖₁ + |c|)²)^{1/2}`, the infimum over the
Barron representations `ρ` of `f` on the cube, in `[0, ∞]` (`∞` when there is none). This is
equation (3) of E, Ma and Wu, *The Barron space and the flow-induced function spaces for neural
network models*, for `p = 2`; their Proposition 1 shows that every `p ∈ [1, ∞]` gives the same
value for the ReLU, which is not formalized here. -/
noncomputable def barronNorm (f : (Fin d → ℝ) → ℝ) : ENNReal :=
  ⨅ (ρ : Measure (ℝ × (Fin d → ℝ) × ℝ)) (_ : IsBarronRepresentation f ρ),
    (∫⁻ θ, ‖θ.1‖ₑ ^ 2 * (∑ j, ‖θ.2.1 j‖ₑ + ‖θ.2.2‖ₑ) ^ 2 ∂ρ) ^ (1 / 2 : ℝ)

/-- **A single neuron lies in the Barron space.** The function `x ↦ a σ(⟨b, x⟩ + c)` is
represented by the Dirac mass at `(a, b, c)`, so its Barron norm is at most `|a| (‖b‖₁ + |c|)`,
the path norm of the one-neuron network (compare E, Ma and Wu, *A priori estimates of the
population risk for two-layer neural networks*, §3.1: the Barron norm of a finite two-layer
network is bounded by its path norm). -/
theorem barronNorm_neuron_le (θ : ℝ × (Fin d → ℝ) × ℝ) :
    barronNorm (reluNeuron θ) ≤ ‖θ.1‖ₑ * (∑ j, ‖θ.2.1 j‖ₑ + ‖θ.2.2‖ₑ) := by
  have hrep : IsBarronRepresentation (reluNeuron θ) (Measure.dirac θ) := by
    refine ⟨inferInstance, fun x _ => ⟨?_, ?_⟩⟩
    · exact (integrable_const (reluNeuron θ x)).congr
        (by simp [Filter.EventuallyEq])
    · rw [integral_dirac]
  refine (iInf₂_le _ hrep).trans ?_
  rw [lintegral_dirac, ← mul_pow]
  rw [show (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num, ENNReal.pow_rpow_inv_natCast two_ne_zero]

end CSLibExt.MachineLearning.NeuralNetworks
