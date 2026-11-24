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
spectral radius of `M₀ = (β_ij S_i⁰ / (dI_i + ε_i + γ_i))`. The feasible region `Γ` is
`S_k ≤ S_k⁰`, `S_k + I_k ≤ Λ_k / d*_k` with `d*_k = min (dS_k, dI_k + ε_k, dR_k)`.

Their Theorem 3.3: if `(β_kj)` is irreducible and `R₀ > 1`, the endemic equilibrium is unique
and globally asymptotically stable in the interior of `Γ`. The proof uses the Lyapunov
function `∑_k v_k (S_k - S_k* ln S_k + I_k - I_k* ln I_k)`, with weights `v_k` given by the
weighted directed matrix-tree theorem. As stated with `p_k ∈ [0, 1]` the theorem needs
`p_k < 1` for every `k` (with `p_k = 1` no interior endemic equilibrium exists), which is
assumed here.

The single-group SEIR case with vital dynamics is proved in
`Domains.Biology.Epidemiology.SEIRGlobalStability`, and the finite next-generation matrix
threshold in `Domains.Biology.Epidemiology.NextGenerationMatrix`; the multigroup theorem is not
proved yet.

Sources: H. Guo, M. Y. Li and Z. Shuai, "Global stability of the endemic equilibrium of
multigroup SIR epidemic models", Canad. Appl. Math. Q. 14 (2006) 259–284, model (1.3),
Eqs. (1.4)–(1.7) and Theorem 3.3.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Algebra.Spectrum
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

/-- The matrix `M₀ = (β_ij S_i⁰ / (dI_i + ε_i + γ_i))` of Eq. (1.6). -/
noncomputable def nextGen (P : Params ι) : Matrix ι ι ℝ :=
  fun i j => P.beta i j * P.susceptibleDFE i / (P.deathI i + P.diseaseDeath i + P.recovery i)

/-- The basic reproduction number `R₀ = ρ(M₀)` (Eq. (1.7)), the spectral radius of `M₀`
viewed as a complex matrix. -/
noncomputable def R0 (P : Params ι) : ℝ :=
  (spectralRadius ℂ (P.nextGen.map (algebraMap ℝ ℂ))).toReal

/-- The interior of the feasible region `Γ` of Eq. (1.4): `S_k, I_k > 0`, `S_k < S_k⁰` and
`S_k + I_k < Λ_k / d*_k` with `d*_k = min (dS_k, dI_k + ε_k, dR_k)`. -/
def InteriorFeasible (P : Params ι) (x : (ι → ℝ) × (ι → ℝ)) : Prop :=
  ∀ k, 0 < x.1 k ∧ 0 < x.2 k ∧ x.1 k < P.susceptibleDFE k ∧
    x.1 k + x.2 k < P.recruit k / min (P.deathS k) (min (P.deathI k + P.diseaseDeath k)
      (P.deathR k))

/-- A forward solution: `x` has right derivative `field (x t)` at every `t ≥ 0`. -/
def IsSolution (P : Params ι) (x : ℝ → (ι → ℝ) × (ι → ℝ)) : Prop :=
  ∀ t, 0 ≤ t → HasDerivWithinAt x (P.field (x t)) (Set.Ici 0) t

end Params

open Params

/-- **Guo–Li–Shuai theorem** (Guo, Li and Shuai 2006, Theorem 3.3, with Corollary 3.2). For
admissible parameters (in particular `p_k < 1` for every `k`) with `(β_kj)` irreducible and
`R₀ > 1`, there is an endemic equilibrium `x*` (all `S_k*, I_k* > 0`); it is the only
equilibrium with all coordinates positive, it is Lyapunov stable for solutions starting in
the interior of `Γ`, and every forward solution starting in the interior of `Γ` converges
to it.

Source: Guo, Li and Shuai (2006), Theorem 3.3. -/
theorem_wanted exists_endemic_globallyStable [Nonempty ι] (P : Params ι) (hP : P.Admissible)
    (hirr : P.beta.IsIrreducible) (hR0 : 1 < P.R0) :
    ∃ e : (ι → ℝ) × (ι → ℝ), (∀ k, 0 < e.1 k ∧ 0 < e.2 k) ∧ P.field e = 0 ∧
      (∀ e' : (ι → ℝ) × (ι → ℝ), (∀ k, 0 < e'.1 k ∧ 0 < e'.2 k) → P.field e' = 0 → e' = e) ∧
      (∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → (ι → ℝ) × (ι → ℝ), P.IsSolution x →
        P.InteriorFeasible (x 0) → dist (x 0) e < δ → ∀ t, 0 ≤ t → dist (x t) e < ε) ∧
      ∀ x : ℝ → (ι → ℝ) × (ι → ℝ), P.IsSolution x → P.InteriorFeasible (x 0) →
        Tendsto x atTop (𝓝 e)

end WantedExt.Biology.Epidemiology.MultigroupSIRGlobalStabilityWanted
