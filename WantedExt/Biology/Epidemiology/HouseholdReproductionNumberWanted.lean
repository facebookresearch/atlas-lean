/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The basic reproduction number of epidemics with households

In the household branching process of Pellis, Ball and Trapman (2012), each household epidemic
started by one case has `μ_i` expected cases in household generation `i < n_H` (`μ_0 = 1`), and
each case makes on average `μ_G ≥ 0` global contacts, each starting a new household epidemic.
The expected numbers `u_n` of households infected in global generation `n` and `x_n` of cases
in global generation `n` satisfy (their Lemmas 1–2)

  `u_0 = 1`, `u_n = μ_G ∑_{i < n_H} μ_i u_{n-1-i}`, `x_n = ∑_{i < n_H} μ_i u_{n-i}`

(with `u_k = 0` for `k < 0`), that is, `(u_n, u_{n-1}, …, u_{n-n_H+1}) = e₀ A^n` for the matrix
`A` whose first column is `(μ_G μ_0, …, μ_G μ_{n_H-1})`, with ones on the superdiagonal and zeros
elsewhere (Eq. (3.2)). The household `R₀` is the per-generation growth `lim x_n^(1/n)`; the
household reproduction number `R* = μ_G ∑_i μ_i` is the mean number of households infected by a
household. Their Theorem 1 and Corollary 1 identify `R₀` with the dominant eigenvalue of `A`
and with the unique positive root of `1 = ∑_i μ_G μ_i / λ^(i+1)`; `R₀` and `R*` lie on the same
side of `1`. Two points are made precise here: when `μ_G = 0` the limit is `0` and the root
does not exist, and the source's "positive regularity" of `A` is not needed (the root is a
strictly dominant simple root since `μ_0 > 0`).

The household process is a Galton–Watson process in the households, whose offspring number has
mean `R*`; its survival criterion is `MathlibExt.Probability.BranchingProcess.GaltonWatson`
(`extinctionProb_eq_one_iff`). `extinctionProb_lt_one_iff` combines it with the threshold link.
The source's critical vaccination fraction `1 - 1/R₀` for birth thinning is not stated: deleting
infections inside a household need not scale `μ_i` by `(1 - p)^i`.

Sources: L. Pellis, F. Ball and P. Trapman, "Reproduction numbers for epidemic models with
households and other social structures. I. Definition and calculation of R₀", Math. Biosci.
235 (2012) 85–97, Eqs. (3.1)–(3.3), Lemmas 1–3, Theorem 1 and Corollary 1.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.BranchingProcess.GaltonWatson
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Matrix.Mul

@[expose] public section

namespace WantedExt.Biology.Epidemiology.HouseholdReproductionNumberWanted

open Filter Topology MeasureTheory ProbabilityTheory MathlibExt.Probability

variable {nH : ℕ}

/-- The matrix `A_{n_H}` of Pellis, Ball and Trapman (2012, Eq. (3.2)): its first column is
`(μ_G μ_0, …, μ_G μ_{n_H-1})`, it has ones on the superdiagonal, and zeros elsewhere. -/
def householdMatrix (μG : ℝ) (μ : Fin nH → ℝ) : Matrix (Fin nH) (Fin nH) ℝ :=
  fun i j => (if (j : ℕ) = 0 then μG * μ i else 0) + (if (j : ℕ) = (i : ℕ) + 1 then 1 else 0)

/-- The expected number `x_n = ∑_i μ_i u_{n-i}` of cases in global generation `n`, where
`(u_n, …, u_{n-n_H+1}) = e₀ A^n` are the expected numbers of households infected in the last
`n_H` global generations (Lemmas 1–2). -/
noncomputable def expectedCases (μG : ℝ) (μ : Fin nH → ℝ) (n : ℕ) : ℝ :=
  ∑ i, μ i * (Matrix.vecMul (Pi.single ⟨0, Fin.pos i⟩ 1) (householdMatrix μG μ ^ n) i)

/-- The spectral radius of `A_{n_H}`, as a real number. -/
noncomputable def spectralRadiusReal (A : Matrix (Fin nH) (Fin nH) ℝ) : ℝ :=
  (spectralRadius ℂ (A.map (algebraMap ℝ ℂ))).toReal

/-- The household reproduction number `R* = μ_G ∑_i μ_i`: the mean number of households
infected by the cases of one household. -/
def householdR (μG : ℝ) (μ : Fin nH → ℝ) : ℝ :=
  μG * ∑ i, μ i

/-- **The household `R₀` is the dominant eigenvalue** (Pellis, Ball and Trapman 2012,
Theorem 1, with Lemmas 1–3). Let `n_H ≥ 1`, `μ_G > 0`, `μ_0 = 1` and `μ_i ≥ 0` for all `i`.
Then the per-generation growth of the expected numbers of cases exists and equals the spectral
radius of `A_{n_H}`: `x_n^(1/n) → ρ(A_{n_H})` as `n → ∞`.

Source: Pellis, Ball and Trapman (2012), Theorem 1. -/
theorem_wanted tendsto_expectedCases_rpow (hnH : 0 < nH) (μG : ℝ) (μ : Fin nH → ℝ)
    (hμG : 0 < μG) (hμ0 : μ ⟨0, hnH⟩ = 1) (hμ : ∀ i, 0 ≤ μ i) :
    Tendsto (fun n : ℕ => expectedCases μG μ n ^ ((1 : ℝ) / n)) atTop
      (𝓝 (spectralRadiusReal (householdMatrix μG μ)))

/-- **No global transmission** (Pellis, Ball and Trapman 2012, Section 3, the case `μ_G = 0`
of Theorem 1). Let `n_H ≥ 1`, `μ_0 = 1` and `μ_i ≥ 0` for all `i`. If `μ_G = 0`, then
`x_n^(1/n) → 0`, so the household `R₀` is `0`.

Source: Pellis, Ball and Trapman (2012), Theorem 1. -/
theorem_wanted tendsto_expectedCases_rpow_of_zero (hnH : 0 < nH) (μ : Fin nH → ℝ)
    (hμ0 : μ ⟨0, hnH⟩ = 1) (hμ : ∀ i, 0 ≤ μ i) :
    Tendsto (fun n : ℕ => expectedCases 0 μ n ^ ((1 : ℝ) / n)) atTop (𝓝 0)

/-- **`R₀` as the root of the characteristic equation** (Pellis, Ball and Trapman 2012,
Corollary 1). Let `n_H ≥ 1`, `μ_G > 0`, `μ_0 = 1` and `μ_i ≥ 0` for all `i`. Then
`∑_{i < n_H} μ_G μ_i / λ^(i+1) = 1` has exactly one positive solution `λ`, and every positive
solution equals the spectral radius `ρ(A_{n_H})`.

Source: Pellis, Ball and Trapman (2012), Corollary 1, Eq. (3.3). -/
theorem_wanted existsUnique_root_eq_spectralRadius (hnH : 0 < nH) (μG : ℝ) (μ : Fin nH → ℝ)
    (hμG : 0 < μG) (hμ0 : μ ⟨0, hnH⟩ = 1) (hμ : ∀ i, 0 ≤ μ i) :
    (∃! lam : ℝ, 0 < lam ∧ ∑ i, μG * μ i / lam ^ ((i : ℕ) + 1) = 1) ∧
      ∀ lam : ℝ, 0 < lam → ∑ i, μG * μ i / lam ^ ((i : ℕ) + 1) = 1 →
        lam = spectralRadiusReal (householdMatrix μG μ)

/-- **`R₀` and `R*` have the same threshold** (Pellis, Ball and Trapman 2012, Section 2.3).
Let `n_H ≥ 1`, `μ_G > 0`, `μ_0 = 1` and `μ_i ≥ 0` for all `i`. Then
`ρ(A_{n_H}) < 1 ↔ R* < 1`, `ρ(A_{n_H}) = 1 ↔ R* = 1` and `1 < ρ(A_{n_H}) ↔ 1 < R*`, where
`R* = μ_G ∑_i μ_i`.

Source: Pellis, Ball and Trapman (2012), Section 2.3. -/
theorem_wanted spectralRadius_threshold (hnH : 0 < nH) (μG : ℝ) (μ : Fin nH → ℝ)
    (hμG : 0 < μG) (hμ0 : μ ⟨0, hnH⟩ = 1) (hμ : ∀ i, 0 ≤ μ i) :
    (spectralRadiusReal (householdMatrix μG μ) < 1 ↔ householdR μG μ < 1) ∧
      (spectralRadiusReal (householdMatrix μG μ) = 1 ↔ householdR μG μ = 1) ∧
      (1 < spectralRadiusReal (householdMatrix μG μ) ↔ 1 < householdR μG μ)

/-- **Survival of the household process iff `R₀ > 1`** (Pellis, Ball and Trapman 2012,
Section 2.1 and Section 2.3). Let `n_H ≥ 1`, `μ_G > 0`, `μ_0 = 1` and `μ_i ≥ 0` for all `i`, and let
`ν` be a probability law on `ℕ` for the number of households infected by one household, with
mean `R* = μ_G ∑_i μ_i` and `ν{1} ≠ 1`. Then the Galton–Watson process of infected households
with offspring law `ν` survives with positive probability (its extinction probability is
`< 1`) if and only if `1 < ρ(A_{n_H})`, the household `R₀`.

Source: Pellis, Ball and Trapman (2012), Section 2.1, property 1, and Section 2.3. -/
theorem_wanted extinctionProb_lt_one_iff (hnH : 0 < nH) (μG : ℝ) (μ : Fin nH → ℝ)
    (hμG : 0 < μG) (hμ0 : μ ⟨0, hnH⟩ = 1) (hμ : ∀ i, 0 ≤ μ i) (ν : Measure ℕ)
    [IsProbabilityMeasure ν] (hmean : GaltonWatson.mean ν = ENNReal.ofReal (householdR μG μ))
    (h1 : ν {1} ≠ 1) :
    GaltonWatson.extinctionProb ν < 1 ↔ 1 < spectralRadiusReal (householdMatrix μG μ)

end WantedExt.Biology.Epidemiology.HouseholdReproductionNumberWanted
