/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Global stability of the endemic equilibrium of multigroup SIR models

For groups `k = 1, …, n`, Guo, Li and Shuai (2006, model (1.3)) study

  `S_k' = (1 - p_k) Λ_k - (dS_k + θ_k) S_k - ∑_j β_kj S_k I_j`,
  `I_k' = ∑_j β_kj S_k I_j - (dI_k + ε_k + γ_k) I_k`,

with recruitment `Λ_k > 0`, vaccinated fraction `p_k`, death rates `dS_k, dI_k, dR_k > 0`,
vaccination rate `θ_k ≥ 0`, disease-induced death rate `ε_k ≥ 0`, recovery rate `γ_k ≥ 0` and
transmission coefficients `β_kj ≥ 0`. The disease-free equilibrium has
`S_k⁰ = Λ_k (1 - p_k) / (dS_k + θ_k)` and `I_k⁰ = 0`; the basic reproduction number `R₀` is the
spectral radius of `M₀ = (β_ij S_i⁰ / (dI_i + ε_i + γ_i))`. With `F = (β_ij S_i⁰)` and
`V = diag (dI_i + ε_i + γ_i)`, `M₀ = V⁻¹ F = V⁻¹ (F V⁻¹) V` has the spectrum of the
next-generation matrix `F V⁻¹`, so `R₀` is `NextGenerationMatrix.R0 F V = ρ(F V⁻¹)`, which is
how it is defined here. The feasible region `Γ` is
`S_k ≤ S_k⁰`, `S_k + I_k ≤ Λ_k / d*_k` with `d*_k = min (dS_k, dI_k + ε_k, dR_k)`.

Their Theorem 3.3: if `(β_kj)` is irreducible and `R₀ > 1`, the endemic equilibrium is unique
and globally asymptotically stable in the interior of `Γ`. The proof uses the Lyapunov
function `∑_k v_k (S_k - S_k* ln S_k + I_k - I_k* ln I_k)`, with weights `v_k` given by the
weighted directed matrix-tree theorem. As stated with `p_k ∈ [0, 1]` the theorem needs
`p_k < 1` for every `k` (with `p_k = 1` no equilibrium has all coordinates positive), which is
assumed here.

The source (p. 262) calls an equilibrium with positive coordinates interior to `Γ`, but such an
equilibrium can lie on the boundary of `Γ`. Adding the two equations of (1.3) at it gives
`(dS_k + θ_k) S_k* + (dI_k + ε_k + γ_k) I_k* = (1 - p_k) Λ_k`, so `S_k* + I_k* ≤ Λ_k / d*_k`,
with equality exactly when `p_k = θ_k = γ_k = 0` and `dS_k = dI_k + ε_k ≤ dR_k`. For example,
with two groups, `Λ_k = dS_k = dI_k = dR_k = 1`, all other parameters zero and every
`β_kj = 1`, `R₀ = 2` and the endemic equilibrium `S_k* = I_k* = 1/2` lies on the face
`S_k + I_k = Λ_k / d*_k = 1`. So the theorem below asks only that the equilibrium have positive
coordinates, while the solutions it attracts start in the interior of `Γ`.

The single-group SEIR case with vital dynamics is proved in
`Domains.Biology.Epidemiology.SEIRGlobalStability`, and the finite next-generation matrix
threshold, with the definition of `R₀` used here, in
`Domains.Biology.Epidemiology.NextGenerationMatrix`.

Sources: H. Guo, M. Y. Li and Z. Shuai, "Global stability of the endemic equilibrium of
multigroup SIR epidemic models", Canad. Appl. Math. Q. 14 (2006) 259–284, model (1.3),
Eqs. (1.4)–(1.7) and Theorem 3.3.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.ODE.Basic
public import Domains.Biology.Epidemiology.NextGenerationMatrix
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace WantedExt.Biology.Epidemiology.MultigroupSIRGlobalStabilityWanted

open Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The parameters of the multigroup SIR model (1.3) of Guo, Li and Shuai (2006). -/
structure Params (ι : Type*) where
  /-- Recruitment rate `Λ_k`. -/
  recruit : ι → ℝ
  /-- Fraction `p_k` of recruits that are vaccinated. -/
  vacc : ι → ℝ
  /-- Death rate `dS_k` of susceptibles. -/
  deathS : ι → ℝ
  /-- Death rate `dI_k` of infectives. -/
  deathI : ι → ℝ
  /-- Death rate `dR_k` of recovered individuals. -/
  deathR : ι → ℝ
  /-- Vaccination rate `θ_k` of susceptibles. -/
  vaccRate : ι → ℝ
  /-- Disease-induced death rate `ε_k`. -/
  diseaseDeath : ι → ℝ
  /-- Recovery rate `γ_k`. -/
  recovery : ι → ℝ
  /-- Transmission coefficients `β_kj` from infectives of group `j` to susceptibles of
  group `k`. -/
  beta : Matrix ι ι ℝ

namespace Params

/-- The standing hypotheses: all rates nonnegative, `Λ_k, dS_k, dI_k, dR_k > 0`, and
`0 ≤ p_k < 1`. -/
structure Admissible (P : Params ι) : Prop where
  recruit_pos : ∀ k, 0 < P.recruit k
  vacc_nonneg : ∀ k, 0 ≤ P.vacc k
  vacc_lt_one : ∀ k, P.vacc k < 1
  deathS_pos : ∀ k, 0 < P.deathS k
  deathI_pos : ∀ k, 0 < P.deathI k
  deathR_pos : ∀ k, 0 < P.deathR k
  vaccRate_nonneg : ∀ k, 0 ≤ P.vaccRate k
  diseaseDeath_nonneg : ∀ k, 0 ≤ P.diseaseDeath k
  recovery_nonneg : ∀ k, 0 ≤ P.recovery k
  beta_nonneg : ∀ k j, 0 ≤ P.beta k j

/-- The vector field of model (1.3) on the state `(S, I)`. -/
noncomputable def field (P : Params ι) (x : (ι → ℝ) × (ι → ℝ)) : (ι → ℝ) × (ι → ℝ) :=
  (fun k => (1 - P.vacc k) * P.recruit k - (P.deathS k + P.vaccRate k) * x.1 k
      - ∑ j, P.beta k j * x.1 k * x.2 j,
    fun k => ∑ j, P.beta k j * x.1 k * x.2 j
      - (P.deathI k + P.diseaseDeath k + P.recovery k) * x.2 k)

/-- The susceptible level `S_k⁰ = Λ_k (1 - p_k) / (dS_k + θ_k)` of the disease-free
equilibrium. -/
noncomputable def susceptibleDFE (P : Params ι) (k : ι) : ℝ :=
  P.recruit k * (1 - P.vacc k) / (P.deathS k + P.vaccRate k)

/-- **Basic reproduction number.** The number `R₀ = ρ(M₀)` of Eq. (1.6), taken as the library's
`NextGenerationMatrix.R0 F V = ρ(F V⁻¹)` with new infections `F = (β_ij S_i⁰)` and transfers
`V = diag (dI_i + ε_i + γ_i)`. When every `dI_i + ε_i + γ_i ≠ 0` (for instance under
`Admissible`), `V` is invertible and the matrix `M₀ = (β_ij S_i⁰ / (dI_i + ε_i + γ_i)) = V⁻¹ F`
of Eq. (1.7) is similar to `F V⁻¹`, so `R₀ = ρ(M₀)` as in the source.

Source: Guo, Li and Shuai (2006), Eqs. (1.6) and (1.7). -/
noncomputable def R0 (P : Params ι) : ℝ :=
  MathlibExt.Biology.Epidemiology.NextGenerationMatrix.R0
    (fun i j => P.beta i j * P.susceptibleDFE i)
    (Matrix.diagonal fun i => P.deathI i + P.diseaseDeath i + P.recovery i)

/-- The interior of the feasible region `Γ` of Eq. (1.4): `S_k, I_k > 0`, `S_k < S_k⁰` and
`S_k + I_k < Λ_k / d*_k` with `d*_k = min (dS_k, dI_k + ε_k, dR_k)`. -/
def InteriorFeasible (P : Params ι) (x : (ι → ℝ) × (ι → ℝ)) : Prop :=
  ∀ k, 0 < x.1 k ∧ 0 < x.2 k ∧ x.1 k < P.susceptibleDFE k ∧
    x.1 k + x.2 k < P.recruit k / min (P.deathS k) (min (P.deathI k + P.diseaseDeath k)
      (P.deathR k))

end Params

open Params

/-- **Guo–Li–Shuai theorem.** Let the index set `ι` of groups be finite and nonempty. For
admissible parameters (in particular `p_k < 1` for every `k`) with `(β_kj)` irreducible and
`R₀ > 1`, there is an endemic equilibrium `x*` (all `S_k*, I_k* > 0`; Corollary 3.2); it is the
only equilibrium with all coordinates positive, it is Lyapunov stable for the solutions on
`[0, ∞)` (integral curves of the field) starting in the interior of `Γ`, and every such solution
converges to it (Theorem 3.3). Only the positivity of `x*` is claimed, not that it lies in the
interior of `Γ` as the source has it: `S_k* + I_k* = Λ_k / d*_k` exactly when
`p_k = θ_k = γ_k = 0` and `dS_k = dI_k + ε_k ≤ dR_k`. For example, with two groups,
`Λ_k = dS_k = dI_k = dR_k = 1`, all other parameters zero and every `β_kj = 1`, `R₀ = 2` and the
equilibrium `S_k* = I_k* = 1/2` lies on that face of `Γ`.

Source: Guo, Li and Shuai (2006), Theorem 3.3. -/
theorem_wanted exists_endemic_globallyStable [Nonempty ι] (P : Params ι) (hP : P.Admissible)
    (hirr : P.beta.IsIrreducible) (hR0 : 1 < P.R0) :
    ∃ e : (ι → ℝ) × (ι → ℝ), (∀ k, 0 < e.1 k ∧ 0 < e.2 k) ∧ P.field e = 0 ∧
      (∀ e' : (ι → ℝ) × (ι → ℝ), (∀ k, 0 < e'.1 k ∧ 0 < e'.2 k) → P.field e' = 0 → e' = e) ∧
      (∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → (ι → ℝ) × (ι → ℝ),
        IsIntegralCurveOn x (fun _ => P.field) (Set.Ici 0) → P.InteriorFeasible (x 0) →
          dist (x 0) e < δ → ∀ t, 0 ≤ t → dist (x t) e < ε) ∧
      ∀ x : ℝ → (ι → ℝ) × (ι → ℝ), IsIntegralCurveOn x (fun _ => P.field) (Set.Ici 0) →
        P.InteriorFeasible (x 0) → Tendsto x atTop (𝓝 e)

end WantedExt.Biology.Epidemiology.MultigroupSIRGlobalStabilityWanted
