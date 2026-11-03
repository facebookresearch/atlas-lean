/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rigorous quasi-steady-state approximation for Michaelis–Menten kinetics

For the mechanism `E + S ⇌ C → E + P` with rate constants `k₁, k₋₁, k₂` (`k₁`, `kb`, `k₂` in
Lean), start with substrate `s₀ > 0`, free enzyme `e₀ > 0` and no complex or product. Measure
time on the slow scale `τ = e₀ t` (Heineken, Tsuchiya and Aris 1967). In the scaled variables
`S(τ) = s(τ / e₀)` and `y = c / e₀` the system is a singularly perturbed system with small
parameter `e₀`: `S` is slow and `y` is fast, its fast subsystem has the attracting
quasi-steady-state manifold `y = S / (K_M + S)`, `K_M = (k₋₁ + k₂)/k₁`, and the reduced
(Michaelis–Menten) equation is

  `dS̄/dτ = -k₂ S̄ / (K_M + S̄)`,   `S̄(0) = s₀`.

**Tikhonov's theorem with the first-order error estimate.** For every time horizon `T > 0`
there is a constant `C` such that every solution of the full mass-action system with these
initial data satisfies `|s(τ / e₀) - S̄(τ)| ≤ C e₀` for all `τ ∈ [0, T]` and all
`0 < e₀ ≤ 1`.

The exact ingredients (conservation laws, the quasi-steady-state manifold, the
Briggs–Haldane rate law and the exponential relaxation of the frozen fast subsystem) are proved
in `MathlibExt.Biology.Dynamics.MichaelisMenten`; the singular-perturbation estimate itself is
deferred.

Sources: A. N. Tikhonov, "Systems of differential equations containing small parameters in the
derivatives", Mat. Sb. (N.S.) 31(73) (1952) 575–586; F. G. Heineken, H. M. Tsuchiya and R.
Aris, "On the mathematical status of the pseudo-steady state hypothesis of biochemical
kinetics", Math. Biosci. 1 (1967) 95–113; L. A. Segel and M. Slemrod, "The quasi-steady-state
assumption: a case study in perturbation", SIAM Rev. 31 (1989) 446–477.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Biology.Dynamics.MichaelisMenten

@[expose] public section

open Set

namespace MathlibExt.Biology.Dynamics.MichaelisMenten

/-- **Rigorous QSSA** (Tikhonov 1952; Heineken–Tsuchiya–Aris 1967). On the slow time scale
`τ = e₀ t`, the substrate of the full Michaelis–Menten system with `s(0) = s₀`, `c(0) = 0`,
`e(0) = e₀` stays within `C e₀` of the solution `S̄` of the reduced equation
`dS̄/dτ = -k₂ S̄ / (K_M + S̄)`, `S̄(0) = s₀`, uniformly on `[0, T]`. -/
theorem_wanted abs_sub_reduced_le {k₁ kb k₂ s₀ T : ℝ} (hk₁ : 0 < k₁) (hkb : 0 ≤ kb)
    (hk₂ : 0 < k₂) (hs₀ : 0 < s₀) (hT : 0 < T) {S : ℝ → ℝ}
    (hS : ∀ τ, 0 ≤ τ → HasDerivAt S (-mmRate k₂ (michaelisConstant k₁ kb k₂) (S τ)) τ)
    (hS₀ : S 0 = s₀) :
    ∃ C : ℝ, ∀ e₀ : ℝ, 0 < e₀ → e₀ ≤ 1 → ∀ s c e p : ℝ → ℝ, IsSolution k₁ kb k₂ s c e p →
      s 0 = s₀ → c 0 = 0 → e 0 = e₀ → ∀ τ ∈ Icc 0 T, |s (τ / e₀) - S τ| ≤ C * e₀

end MathlibExt.Biology.Dynamics.MichaelisMenten
