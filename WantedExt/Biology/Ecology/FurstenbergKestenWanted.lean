/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Furstenberg–Kesten theorem: almost-sure growth rate of random matrix products

Let `X_0, X_1, …` be a stationary sequence of random `d × d` matrices (i.i.d. in the common
special case), written as `X_k = X ∘ T^k` for a measure-preserving map `T` of a probability
space, and assume `E log⁺ ‖X_0‖ < ∞`. Furstenberg and Kesten (1960) proved that
`(1/n) log ‖X_{n-1} ⋯ X_0‖` converges almost surely to a limit `γ ∈ [-∞, ∞)`, which is almost
surely constant when `T` is ergodic. For population projection matrices `γ = log λ_s` is the
stochastic growth rate (Cohen 1982, Theorem 4.1(v)). The logarithm is taken in `EReal` so that
a zero product has logarithm `-∞`; the norm is the `ℓ∞` operator norm, which is
submultiplicative (the limit does not depend on the choice of norm).

Kingman's subadditive ergodic theorem is proved in `MathlibExt.Dynamics.Ergodic.KingmanSigned`
(`kingman_ae_general`) for integrable cocycles with a real limit; it does not cover the
`log⁺` hypothesis or the value `-∞` that singular matrices allow.

Sources: H. Furstenberg and H. Kesten, "Products of random matrices", Ann. Math. Statist. 31
(1960) 457–469; A. Karlsson, "Ergodic theorems for noncommuting random products", lecture
notes, §1.5; J. E. Cohen, "Multiregional age-structured populations with changing rates: weak
and stochastic ergodic theorems" (1982), Theorem 4.1(v), p. 494.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Topology.Instances.EReal.Lemmas

@[expose] public section

namespace WantedExt.Biology.Ecology.FurstenbergKestenWanted

open MeasureTheory Filter Topology
open scoped ENNReal

attribute [local instance] Matrix.linftyOpNormedAddCommGroup

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The product `X(T^{n-1} ω) ⋯ X(T ω) X(ω)` of the matrices along the orbit of `ω`
(the identity for `n = 0`). -/
def orbitProduct (T : Ω → Ω) (X : Ω → Matrix (Fin d) (Fin d) ℝ) :
    ℕ → Ω → Matrix (Fin d) (Fin d) ℝ
  | 0, _ => 1
  | n + 1, ω => X (T^[n] ω) * orbitProduct T X n ω

/-- `log ‖X_{n-1} ⋯ X_0‖` in `EReal` (equal to `-∞` when the product is zero), for the `ℓ∞`
operator norm. -/
noncomputable def logNormProduct (T : Ω → Ω) (X : Ω → Matrix (Fin d) (Fin d) ℝ) (n : ℕ)
    (ω : Ω) : EReal :=
  ENNReal.log (‖orbitProduct T X n ω‖₊ : ℝ≥0∞)

/-- **Furstenberg–Kesten theorem** (Furstenberg and Kesten 1960; Karlsson, §1.5). Let `T`
preserve the probability measure `μ`, let `X` be a measurable random matrix (each entry is
measurable), and assume `E log⁺ ‖X‖ < ∞`. Then there is `γ : Ω → EReal` with `γ < ∞` and
`(1/n) log ‖X(T^{n-1} ω) ⋯ X(ω)‖ → γ(ω)` for almost every `ω`; if `T` is ergodic, `γ` is almost
surely constant.

Sources: Furstenberg and Kesten (1960); Karlsson, §1.5; Cohen (1982), Theorem 4.1(v). -/
public theorem_wanted furstenberg_kesten (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (X : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hX : ∀ i j, Measurable (fun ω => X ω i j))
    (hlog : Integrable (fun ω => Real.posLog ‖X ω‖) μ) :
    ∃ γ : Ω → EReal,
      (∀ᵐ ω ∂μ, γ ω < ⊤ ∧
        Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * logNormProduct T X n ω) atTop
          (𝓝 (γ ω))) ∧
      (Ergodic T μ → ∃ c : EReal, ∀ᵐ ω ∂μ, γ ω = c)

end WantedExt.Biology.Ecology.FurstenbergKestenWanted
