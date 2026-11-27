/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Force–extension of the freely jointed chain (Langevin function)

A freely jointed chain has `n` segments of length `ℓ > 0` with independent directions
`u_1, …, u_n` on the unit sphere `S² ⊂ ℝ³`. Under an end force `f` along a fixed unit vector `e`,
at temperature `T > 0`, a configuration has Boltzmann weight `exp (φ ∑_i u_i · e)` with
`φ = f ℓ / (k_B T)`. With `σ` the surface-area measure on `S²` (`σ(S²) = 4π`), the partition
function is `q(f) = ∫_{(S²)^n} exp (φ ∑_i u_i · e) dσ^{⊗n} = (4π sinh φ / φ)^n`, and the mean
extension along the force is

  `⟨r⟩(f) = k_B T ∂_f ln q(f) = n ℓ L(φ)`,   `L(φ) = coth φ - 1/φ`  (the Langevin function),

with `L(0) = 0`. For small forces `⟨r⟩ ≈ n ℓ² f / (3 k_B T)` (a linear entropic spring, and
`f ≈ 3 k_B T ⟨r⟩ / (n ℓ²)` when `n > 0`); for large forces `⟨r⟩ ≈ n ℓ (1 - 1/φ)`. The secondary
source prints the single-segment partition function as `2π sinh φ / φ`; with the standard area
measure the value is `4π sinh φ / φ` (a factor-2 misprint that does not affect `⟨r⟩`). Here
`σ` is `volume.toSphere`, the surface measure on the unit sphere of `ℝ³`.

Sources: W. Kuhn and F. Grün, "Beziehungen zwischen elastischen Konstanten und
Dehnungsdoppelbrechung hochelastischer Stoffe", Kolloid-Z. 101 (1942) 248–271; the derivation
as stated in A. Tokmakoff, *Concepts in Biophysical Chemistry* (open textbook, University of
Chicago), Section 9.3.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Asymptotics.Defs

@[expose] public section

namespace WantedExt.Biology.Biophysics.FreelyJointedChainWanted

open MeasureTheory Filter Topology Asymptotics
open scoped RealInnerProductSpace

/-- The unit sphere `S²` of `ℝ³`. -/
abbrev Sphere : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The surface-area measure `σ` on `S²` (total mass `4π`). -/
noncomputable def sigma : Measure Sphere := (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere

/-- The function `S(φ) = sinh φ / φ`, extended by `S(0) = 1`. -/
noncomputable def sinhc (φ : ℝ) : ℝ := if φ = 0 then 1 else Real.sinh φ / φ

/-- The Langevin function `L(φ) = coth φ - 1/φ`, extended by `L(0) = 0`. -/
noncomputable def langevin (φ : ℝ) : ℝ :=
  if φ = 0 then 0 else Real.cosh φ / Real.sinh φ - 1 / φ

/-- The partition function `q(f) = ∫_{(S²)^n} exp (φ ∑_i u_i · e) dσ^{⊗n}` of `n` segments of
length `ℓ` under the force `f` along the unit vector `e`, with `φ = f ℓ / (k_B T)`. -/
noncomputable def partitionFunction (n : ℕ) (kB T ℓ : ℝ) (e : EuclideanSpace ℝ (Fin 3))
    (f : ℝ) : ℝ :=
  ∫ u : Fin n → Sphere, Real.exp (f * ℓ / (kB * T) * ∑ i, ⟪(u i : EuclideanSpace ℝ (Fin 3)), e⟫)
    ∂(Measure.pi fun _ => sigma)

/-- The mean extension `⟨r⟩(f) = q(f)⁻¹ ∫ ℓ (∑_i u_i · e) exp (φ ∑_i u_i · e) dσ^{⊗n}` along the
force. -/
noncomputable def meanExtension (n : ℕ) (kB T ℓ : ℝ) (e : EuclideanSpace ℝ (Fin 3)) (f : ℝ) : ℝ :=
  (partitionFunction n kB T ℓ e f)⁻¹ *
    ∫ u : Fin n → Sphere, ℓ * (∑ i, ⟪(u i : EuclideanSpace ℝ (Fin 3)), e⟫) *
      Real.exp (f * ℓ / (kB * T) * ∑ i, ⟪(u i : EuclideanSpace ℝ (Fin 3)), e⟫)
      ∂(Measure.pi fun _ => sigma)

/-- **Single-segment partition function** (Tokmakoff, Section 9.3). For every unit vector
`e ∈ ℝ³` and every real `φ`, `∫_{S²} exp (φ u · e) dσ(u) = 4π S(φ)`, where
`S(φ) = sinh φ / φ` for `φ ≠ 0` and `S(0) = 1`. This corrects the cited section, which prints
`q_conf(f) = 2π sinh φ / φ` and
`q = (∫_0^{2π} ∫_0^π exp[φ cos θ] sin θ dθ dϕ)^n = (2π sinh φ / φ)^n`: the integral it displays
equals `4π sinh φ / φ` per segment, since the `θ`-integral is `2 sinh φ / φ`.

Source: Kuhn and Grün (1942); Tokmakoff, Section 9.3. -/
theorem_wanted integral_exp_inner (e : EuclideanSpace ℝ (Fin 3)) (he : ‖e‖ = 1) (φ : ℝ) :
    ∫ u : Sphere, Real.exp (φ * ⟪(u : EuclideanSpace ℝ (Fin 3)), e⟫) ∂sigma =
      4 * Real.pi * sinhc φ

/-- **Partition function and Langevin force–extension law** (Tokmakoff, Section 9.3). Let
`k_B > 0`, `T > 0`, `ℓ > 0`, `n : ℕ`, `f` real and `e` a unit vector in `ℝ³`, and put
`φ = f ℓ / (k_B T)`. Then `q(f) = (4π S(φ))^n`; `⟨r⟩(f) = k_B T ∂_f ln q(f)` (the function
`f ↦ ln q(f)` has derivative `⟨r⟩(f) / (k_B T)` at `f`); and `⟨r⟩(f) = n ℓ L(φ)`. The first
clause corrects the cited section, which prints `q_conf(f) = 2π sinh φ / φ` and
`q = (∫_0^{2π} ∫_0^π exp[φ cos θ] sin θ dθ dϕ)^n = (2π sinh φ / φ)^n`: the integral it displays
equals `(4π sinh φ / φ)^n`, since the `θ`-integral is `2 sinh φ / φ`. The factor does not change
`⟨r⟩(f)`.

Source: Kuhn and Grün (1942); Tokmakoff, Section 9.3. -/
theorem_wanted partitionFunction_and_meanExtension (n : ℕ) (kB T ℓ : ℝ) (hkB : 0 < kB)
    (hT : 0 < T) (hℓ : 0 < ℓ) (e : EuclideanSpace ℝ (Fin 3)) (he : ‖e‖ = 1) (f : ℝ) :
    partitionFunction n kB T ℓ e f = (4 * Real.pi * sinhc (f * ℓ / (kB * T))) ^ n ∧
      HasDerivAt (fun g => Real.log (partitionFunction n kB T ℓ e g))
        (meanExtension n kB T ℓ e f / (kB * T)) f ∧
      meanExtension n kB T ℓ e f = n * ℓ * langevin (f * ℓ / (kB * T))

/-- **Weak- and strong-force limits** (Tokmakoff, Section 9.3). As `φ → 0`,
`L(φ) - φ/3 = O(φ³)`, hence (for `k_B, T, ℓ > 0`, `n : ℕ` and a unit vector `e`)
`⟨r⟩(f) - n ℓ² f / (3 k_B T) = O(f³)` as `f → 0`, and if moreover `n > 0`, the inverse spring
law `f - 3 k_B T ⟨r⟩(f) / (n ℓ²) = O(⟨r⟩(f)³)` as `f → 0`. As `φ → ∞`,
`L(φ) - (1 - 1/φ) = o(1/φ)`.

Source: Kuhn and Grün (1942); Tokmakoff, Section 9.3. -/
theorem_wanted langevin_asymptotics (n : ℕ) (kB T ℓ : ℝ) (hkB : 0 < kB) (hT : 0 < T)
    (hℓ : 0 < ℓ) (e : EuclideanSpace ℝ (Fin 3)) (he : ‖e‖ = 1) :
    (fun φ => langevin φ - φ / 3) =O[𝓝 0] (fun φ => φ ^ 3) ∧
      (fun f => meanExtension n kB T ℓ e f - n * ℓ ^ 2 * f / (3 * kB * T)) =O[𝓝 0]
        (fun f => f ^ 3) ∧
      (0 < n → (fun f => f - 3 * kB * T * meanExtension n kB T ℓ e f / (n * ℓ ^ 2)) =O[𝓝 0]
        (fun f => meanExtension n kB T ℓ e f ^ 3)) ∧
      (fun φ => langevin φ - (1 - 1 / φ)) =o[atTop] (fun φ => 1 / φ)

end WantedExt.Biology.Biophysics.FreelyJointedChainWanted
