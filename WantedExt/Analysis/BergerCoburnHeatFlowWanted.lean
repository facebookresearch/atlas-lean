/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Source record `AIM-ANALYSIS-0004`
# The Berger–Coburn heat-flow criterion for Toeplitz operators on the Fock space

AIM problem list "Riemann-Hilbert problems, Toeplitz matrices, and applications", Conjecture 1.4 (M.
Hitrik; Berger–Coburn 1994).

On the Fock space, `T_p f = Π(p f)` is bounded iff the solution of `u_t = Δu`, `u|_{t=0} = p`, is
bounded at `t = 1/4`. The source's normalization (weight `e^{-|z|²}` with time `1/4`) is off by a
factor two; the record recovers Berger–Coburn's normalization, which is formalized: the Fock space
`F²` of entire functions in `L²(dμ)`, `dμ = (2π)^{-1} e^{-|z|²/2} dA`, with normalized coherent
states `k_a(z) = e^{z ā/2 - |a|²/4}`, a measurable symbol `g` with `g k_a ∈ L²(dμ)` for all `a`, and
the heat transform `H_{1/4} g(z) = π^{-1} ∫ g(w) e^{-|z-w|²} dA(w)`. `T_g` extends boundedly from
the span of the coherent states exactly when the form `(f, φ) ↦ ∫ g f φ̄ dμ` is bounded on that span
(as `⟨T_g f, φ⟩ = ∫ g f φ̄ dμ` and the span is dense), which is the boundedness formalized.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Analysis.BergerCoburnHeatFlowWanted

open MeasureTheory Complex

/-- The Gaussian measure `dμ = (2π)^{-1} e^{-|z|²/2} dA` on `ℂ`. -/
noncomputable def fockMeasure : Measure ℂ :=
  volume.withDensity fun z => ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.exp (-‖z‖ ^ 2 / 2))

/-- The normalized coherent state `k_a(z) = e^{z ā/2 - |a|²/4}`. -/
noncomputable def coherent (a z : ℂ) : ℂ := exp (z * (starRingEnd ℂ) a / 2 - ‖a‖ ^ 2 / 4)

/-- The finite combination `∑ cᵢ k_{aᵢ}` of coherent states. -/
noncomputable def combo {m : ℕ} (a c : Fin m → ℂ) (z : ℂ) : ℂ := ∑ i, c i * coherent (a i) z

/-- The `L²(dμ)` norm. -/
noncomputable def l2Norm (f : ℂ → ℂ) : ℝ := (∫ z, ‖f z‖ ^ 2 ∂fockMeasure) ^ (1 / 2 : ℝ)

/-- `T_g` is bounded: `|∫ g f φ̄ dμ| ≤ C ‖f‖ ‖φ‖` for all finite combinations of coherent states. -/
def ToeplitzBounded (g : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, ∀ (m m' : ℕ) (a c : Fin m → ℂ) (b d : Fin m' → ℂ),
    ‖∫ z, g z * combo a c z * (starRingEnd ℂ) (combo b d z) ∂fockMeasure‖ ≤
      C * l2Norm (combo a c) * l2Norm (combo b d)

/-- The heat transform `H_{1/4} g(z) = π^{-1} ∫ g(w) e^{-|z-w|²} dA(w)`. -/
noncomputable def heatTransform (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (Real.pi⁻¹ : ℂ) * ∫ w, g w * (Real.exp (-‖z - w‖ ^ 2) : ℂ)

/-- The Berger–Coburn conjecture. -/
def conjecture : Prop :=
  ∀ g : ℂ → ℂ, Measurable g → (∀ a, Integrable (fun z => ‖g z * coherent a z‖ ^ 2) fockMeasure) →
    (ToeplitzBounded g ↔ ∃ M : ℝ, ∀ z, ‖heatTransform g z‖ ≤ M)

-- Carried source audit `AIM-ANALYSIS-0004` (see the Moved/ record).

/--
Resolved false: Refuted, in both directions of the equivalence. Looi (arXiv:2601.20859, Theorem
1.2) constructs, in every complex dimension n >= 1 and in the Berger-Coburn normalization used
here (dmu = (2 pi)^{-n} e^{-|z|^2/2} dv, heat transform (4 pi t)^{-n} integral g(w)
e^{-|w-a|^2/(4t)} at t = 1/4), a measurable g with g k_a in L^2(dmu) for every normalized kernel
k_a whose Toeplitz form is bounded on the span of the kernels while the t = 1/4 heat transform
is unbounded. Virtanen (arXiv:2609.11853), citing this as a disproof, also gives a real-valued
admissible g whose t = 1/4 heat transform lies in C_0 while T_g has no bounded extension
(Theorem 1.1(iii)). Both are preprints. The equivalence holds for metaplectic
(quadratic-exponential) symbols (Coburn-Hitrik-Sjöstrand; Xiong, 2023). Source: Sam Looi, A
counterexample to the Berger-Coburn conjecture, arXiv:2601.20859 (2026),
https://arxiv.org/abs/2601.20859; Jani A. Virtanen, The critical Schatten exponent for the
Berger-Coburn endpoint problem, arXiv:2609.11853 (2026), https://arxiv.org/abs/2609.11853. Moved
from `OpenConjectures/Analysis/BergerCoburnHeatFlow`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Analysis.BergerCoburnHeatFlowWanted
