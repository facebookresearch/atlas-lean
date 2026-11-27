/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Gouy–Chapman solution of the planar Poisson–Boltzmann equation

Near a planar charged surface in a `1:1` electrolyte the potential `ψ(x)` satisfies the nonlinear
Poisson–Boltzmann equation `ψ'' = (2 e C₀ / ε) sinh(e ψ / (k_B T))`, with `C₀` the bulk number
density of each ion species. In the reduced potential `Φ = e ψ / (k_B T)` and the reduced distance
`X = x / λ_D` it becomes `Φ_XX = sinh Φ`, exactly when `λ_D² = ε k_B T / (2 e² C₀)` (the Debye
length). The decaying solution is (Gouy 1910, Chapman 1913; Tokmakoff, Section 6.7)

  `Φ(X) = 2 ln((1 + g e^{-X}) / (1 - g e^{-X}))`,  `g = tanh(Φ(0) / 4) ∈ (-1, 1)`,

and `exp(-Φ(0)/2) = (1 - g)/(1 + g)`, which for `g > 0` also equals `-tanh(ln g / 2)`. The
surface charge density `σ` fixes the boundary slope through Gauss's law: with the Bjerrum length
`ℓ_B = e² / (4π ε k_B T)` (a supplied SI convention), `-Φ_X(0) = h = 4π ℓ_B σ λ_D / e`; for
`σ ≠ 0`, `h = 2 λ_D / x₀` with `x₀ = e / (2π ℓ_B σ)`. The solution with charge `h` has
`g = h / (2 + √(4 + h²))`. For `σ > 0` this is the printed `g = -a + √(1 + a²)`,
`a = x₀ / λ_D`; for `σ < 0` the printed expression exceeds `1` and the correct value is
`-a - √(1 + a²)`; for `σ = 0`, `h = 0`, `g = 0` and `Φ ≡ 0`.

A solution of the boundary-value problem on `[0, ∞)` is a function `Φ` with a derivative `Φ'`
such that `Φ` has derivative `Φ'(X)` and `Φ'` has derivative `sinh Φ(X)` within `[0, ∞)` at every
`X ≥ 0`, and `Φ(X) → 0` as `X → ∞`. Uniqueness is asserted on `[0, ∞)`. The prescribed-charge form
and the signed formula for `g` are a labelled extension of the textbook derivation; the bridge
between surface potential, `g` and `h` is stated as two-sided inverses.

Sources: G. Gouy, "Sur la constitution de la charge électrique à la surface d'un électrolyte",
Journal de Physique Théorique et Appliquée 9 (1910) 457–468;
D. L. Chapman, "A contribution to the theory of electrocapillarity", Philosophical Magazine 25
(1913) 475–481; A. Tokmakoff, *Concepts in Biophysical Chemistry*
(open textbook, University of Chicago, LibreTexts), Section 6.7 (the derivation stated here).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace WantedExt.Biology.Biophysics.GouyChapmanWanted

open Filter Topology Set

/-- The **Gouy–Chapman profile** `Φ(X) = 2 ln((1 + g e^{-X}) / (1 - g e^{-X}))`. -/
noncomputable def gcProfile (g X : ℝ) : ℝ :=
  2 * Real.log ((1 + g * Real.exp (-X)) / (1 - g * Real.exp (-X)))

/-- `Φ` solves the reduced planar Poisson–Boltzmann equation `Φ_XX = sinh Φ` on `[0, ∞)` with
derivative `Φ'` (both derivatives taken within `[0, ∞)`) and decays: `Φ(X) → 0` as `X → ∞`. -/
def IsDecayingPBSolution (Φ Φ' : ℝ → ℝ) : Prop :=
  (∀ X, 0 ≤ X → HasDerivWithinAt Φ (Φ' X) (Ici 0) X ∧
      HasDerivWithinAt Φ' (Real.sinh (Φ X)) (Ici 0) X) ∧
    Tendsto Φ atTop (𝓝 0)

/-- **Prescribed surface potential** (Gouy 1910, Chapman 1913; Tokmakoff, Section 6.7): for every
real `Φ₀`, with `g = tanh(Φ₀ / 4)`, the profile `gcProfile g` (with its derivative) is a decaying
solution of `Φ_XX = sinh Φ` on `[0, ∞)` with `Φ(0) = Φ₀`, and every decaying solution `Φ` with
`Φ(0) = Φ₀` (and any derivative `Φ'`) equals `gcProfile g` on `[0, ∞)`.

Source: Tokmakoff, Section 6.7, after Gouy (1910) and Chapman (1913). -/
public theorem_wanted existsUnique_potential (Φ₀ : ℝ) :
    (∃ Φ' : ℝ → ℝ, IsDecayingPBSolution (gcProfile (Real.tanh (Φ₀ / 4))) Φ') ∧
      gcProfile (Real.tanh (Φ₀ / 4)) 0 = Φ₀ ∧
      ∀ Φ Φ' : ℝ → ℝ, IsDecayingPBSolution Φ Φ' → Φ 0 = Φ₀ →
        ∀ X, 0 ≤ X → Φ X = gcProfile (Real.tanh (Φ₀ / 4)) X

/-- **Prescribed surface charge** (labelled extension of Tokmakoff, Section 6.7): for every real
`h`, with `g = h / (2 + √(4 + h²))`, the profile `gcProfile g` has a derivative `Φ'` making it a
decaying solution of `Φ_XX = sinh Φ` on `[0, ∞)` with `-Φ'(0) = h`, and every decaying solution
`Φ` with derivative `Φ'` and `-Φ'(0) = h` equals `gcProfile g` on `[0, ∞)`.

Source: Tokmakoff, Section 6.7, after Gouy (1910) and Chapman (1913). -/
public theorem_wanted existsUnique_charge (h : ℝ) :
    (∃ Φ' : ℝ → ℝ, IsDecayingPBSolution (gcProfile (h / (2 + Real.sqrt (4 + h ^ 2)))) Φ' ∧
        -Φ' 0 = h) ∧
      ∀ Φ Φ' : ℝ → ℝ, IsDecayingPBSolution Φ Φ' → -Φ' 0 = h →
        ∀ X, 0 ≤ X → Φ X = gcProfile (h / (2 + Real.sqrt (4 + h ^ 2))) X

/-- **The potential–`g`–charge bridge** (Tokmakoff, Section 6.7, made two-sided): `Φ₀ ↦ tanh(Φ₀/4)`
maps `ℝ` into `(-1, 1)` with two-sided inverse `g ↦ 2 ln((1 + g)/(1 - g))` (`= 4 artanh g`);
`g ↦ 4g/(1 - g²)` maps `(-1, 1)` onto `ℝ` with two-sided inverse `h ↦ h/(2 + √(4 + h²))`, which
maps `ℝ` into `(-1, 1)`; and `4 tanh(Φ₀/4)/(1 - tanh²(Φ₀/4)) = 2 sinh(Φ₀/2)` for every real `Φ₀`.

Source: Tokmakoff, Section 6.7. -/
public theorem_wanted potential_g_charge_bridge :
    (∀ Φ₀ : ℝ, Real.tanh (Φ₀ / 4) ∈ Ioo (-1) 1 ∧
        2 * Real.log ((1 + Real.tanh (Φ₀ / 4)) / (1 - Real.tanh (Φ₀ / 4))) = Φ₀) ∧
      (∀ g ∈ Ioo (-1 : ℝ) 1, Real.tanh (2 * Real.log ((1 + g) / (1 - g)) / 4) = g) ∧
      (∀ h : ℝ, h / (2 + Real.sqrt (4 + h ^ 2)) ∈ Ioo (-1) 1 ∧
        4 * (h / (2 + Real.sqrt (4 + h ^ 2))) / (1 - (h / (2 + Real.sqrt (4 + h ^ 2))) ^ 2) = h) ∧
      (∀ g ∈ Ioo (-1 : ℝ) 1, 4 * g / (1 - g ^ 2) / (2 + Real.sqrt (4 + (4 * g / (1 - g ^ 2)) ^ 2))
        = g) ∧
      ∀ Φ₀ : ℝ, 4 * Real.tanh (Φ₀ / 4) / (1 - Real.tanh (Φ₀ / 4) ^ 2) = 2 * Real.sinh (Φ₀ / 2)

/-- **Surface-potential identities** (Tokmakoff, Section 6.7, corrected reading): for every real
`Φ₀` and `g = tanh(Φ₀/4)`, `exp(-Φ₀/2) = (1 - g)/(1 + g)`; and for every `g > 0`,
`(1 - g)/(1 + g) = -tanh(ln g / 2)`. (The printed chain equals `exp(-Φ₀/2)`, not `g`.)

Source: Tokmakoff, Section 6.7. -/
public theorem_wanted surface_potential_identities :
    (∀ Φ₀ : ℝ, Real.exp (-Φ₀ / 2) = (1 - Real.tanh (Φ₀ / 4)) / (1 + Real.tanh (Φ₀ / 4))) ∧
      ∀ g : ℝ, 0 < g → (1 - g) / (1 + g) = -Real.tanh (Real.log g / 2)

/-- The **Bjerrum length** `ℓ_B = e² / (4π ε k_B T)` (supplied SI convention). -/
noncomputable def bjerrum (e ε kB T : ℝ) : ℝ :=
  e ^ 2 / (4 * Real.pi * ε * kB * T)

/-- The **Debye length** `λ_D = √(ε k_B T / (2 e² C₀))` of a `1:1` electrolyte. -/
noncomputable def debye (e ε kB T C₀ : ℝ) : ℝ :=
  Real.sqrt (ε * kB * T / (2 * e ^ 2 * C₀))

/-- The reduced surface charge `h = 4π ℓ_B σ λ_D / e`. -/
noncomputable def reducedCharge (e ε kB T C₀ σ : ℝ) : ℝ :=
  4 * Real.pi * bjerrum e ε kB T * σ * debye e ε kB T C₀ / e

/-- `a = x₀ / λ_D` with `x₀ = e / (2π ℓ_B σ)`. -/
noncomputable def chargeRatio (e ε kB T C₀ σ : ℝ) : ℝ :=
  e / (2 * Real.pi * bjerrum e ε kB T * σ) / debye e ε kB T C₀

/-- **Reduction to the dimensionless equation** (Tokmakoff, Section 6.7): for `e, ε, k_B, T, C₀ > 0`
and `λ = λ_D`, if on `[0, ∞)` `ψ` has within-derivative `ψ'` and `ψ'` has within-derivative
`(2 e C₀ / ε) sinh(e ψ(x) / (k_B T))`, then on `[0, ∞)` the rescaled potential
`Φ(X) = e ψ(λ X) / (k_B T)` has within-derivative `Φ'(X) = e λ ψ'(λ X) / (k_B T)` and `Φ'` has
within-derivative `sinh Φ(X)`; conversely, if for some `λ > 0` such a `ψ` with `ψ(x₁) ≠ 0` at
some `x₁ ≥ 0` makes `Φ'` have within-derivative `sinh Φ` on `[0, ∞)`, then `λ = λ_D`.

Source: Tokmakoff, Section 6.7. -/
public theorem_wanted reduced_equation_iff_debye (e ε kB T C₀ : ℝ) (he : 0 < e) (hε : 0 < ε)
    (hkB : 0 < kB) (hT : 0 < T) (hC : 0 < C₀) (ψ ψ' : ℝ → ℝ)
    (hψ : ∀ x, 0 ≤ x → HasDerivWithinAt ψ (ψ' x) (Ici 0) x ∧
      HasDerivWithinAt ψ' (2 * e * C₀ / ε * Real.sinh (e * ψ x / (kB * T))) (Ici 0) x) :
    (∀ X, 0 ≤ X →
      HasDerivWithinAt (fun X => e * ψ (debye e ε kB T C₀ * X) / (kB * T))
        (e * debye e ε kB T C₀ * ψ' (debye e ε kB T C₀ * X) / (kB * T)) (Ici 0) X ∧
      HasDerivWithinAt (fun X => e * debye e ε kB T C₀ * ψ' (debye e ε kB T C₀ * X) / (kB * T))
        (Real.sinh (e * ψ (debye e ε kB T C₀ * X) / (kB * T))) (Ici 0) X) ∧
      ∀ lam : ℝ, 0 < lam → (∃ x₁, 0 ≤ x₁ ∧ ψ x₁ ≠ 0) →
        (∀ X, 0 ≤ X → HasDerivWithinAt (fun X => e * lam * ψ' (lam * X) / (kB * T))
          (Real.sinh (e * ψ (lam * X) / (kB * T))) (Ici 0) X) →
        lam = debye e ε kB T C₀

/-- **The printed branch for positive charge** (Tokmakoff, Section 6.7): for `e, ε, k_B, T, C₀ > 0`
and `σ > 0`, with `h = 4π ℓ_B σ λ_D / e` and `a = x₀ / λ_D > 0`,
`h / (2 + √(4 + h²)) = -a + √(1 + a²)`, and this value lies in `(0, 1)`.

Source: Tokmakoff, Section 6.7. -/
public theorem_wanted g_eq_printed_of_pos (e ε kB T C₀ σ : ℝ) (he : 0 < e) (hε : 0 < ε)
    (hkB : 0 < kB) (hT : 0 < T) (hC : 0 < C₀) (hσ : 0 < σ) :
    reducedCharge e ε kB T C₀ σ / (2 + Real.sqrt (4 + reducedCharge e ε kB T C₀ σ ^ 2)) =
        -chargeRatio e ε kB T C₀ σ + Real.sqrt (1 + chargeRatio e ε kB T C₀ σ ^ 2) ∧
      -chargeRatio e ε kB T C₀ σ + Real.sqrt (1 + chargeRatio e ε kB T C₀ σ ^ 2) ∈ Ioo 0 1

/-- **The corrected branch for negative charge** (Tokmakoff, Section 6.7, corrected): for
`e, ε, k_B, T, C₀ > 0` and `σ < 0`, with `h` and `a = x₀ / λ_D < 0` as above, the printed value
`-a + √(1 + a²)` exceeds `1`, while `h / (2 + √(4 + h²)) = -a - √(1 + a²)`, which lies in
`(-1, 0)`.

Source: Tokmakoff, Section 6.7. -/
public theorem_wanted g_eq_corrected_of_neg (e ε kB T C₀ σ : ℝ) (he : 0 < e) (hε : 0 < ε)
    (hkB : 0 < kB) (hT : 0 < T) (hC : 0 < C₀) (hσ : σ < 0) :
    1 < -chargeRatio e ε kB T C₀ σ + Real.sqrt (1 + chargeRatio e ε kB T C₀ σ ^ 2) ∧
      reducedCharge e ε kB T C₀ σ / (2 + Real.sqrt (4 + reducedCharge e ε kB T C₀ σ ^ 2)) =
        -chargeRatio e ε kB T C₀ σ - Real.sqrt (1 + chargeRatio e ε kB T C₀ σ ^ 2) ∧
      -chargeRatio e ε kB T C₀ σ - Real.sqrt (1 + chargeRatio e ε kB T C₀ σ ^ 2) ∈ Ioo (-1) 0

/-- **The uncharged surface** (Tokmakoff, Section 6.7): for any `e, ε, k_B, T, C₀` and `σ = 0`,
`h = 0`, hence `g = h / (2 + √(4 + h²)) = 0` and the profile `gcProfile 0` vanishes identically.

Source: Tokmakoff, Section 6.7. -/
public theorem_wanted profile_eq_zero_of_uncharged (e ε kB T C₀ : ℝ) :
    reducedCharge e ε kB T C₀ 0 = 0 ∧
      reducedCharge e ε kB T C₀ 0 / (2 + Real.sqrt (4 + reducedCharge e ε kB T C₀ 0 ^ 2)) = 0 ∧
      ∀ X, gcProfile 0 X = 0

end WantedExt.Biology.Biophysics.GouyChapmanWanted
