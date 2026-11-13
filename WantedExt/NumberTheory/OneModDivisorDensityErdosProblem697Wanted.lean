/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Density of multiples of divisors `≡ 1 (mod m)` (Erdős Problem 697)

Erdős Problem 697: let `δ(m, α)` denote the density of the set of integers which are divisible by
some `d ≡ 1 (mod m)` with `1 < d < exp(m^α)`. Does there exist some `β ∈ (1, ∞)` such that `lim_{m →
∞} δ(m, α)` is `0` if `α < β` and `1` if `α > β`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.NumberTheory.OneModDivisorDensityErdosProblem697Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #697, https://www.erdosproblems.com/697 (status
PROVED). UnsolvedMath record UM-30006982 (`EP-697`), dataset ulamai/UnsolvedMath v1.8.0.

`δ(m, α)` is the natural density, the limit (`Filter.limUnder`) of the proportion of `x < N` in the
set; finitely many `d` qualify, so the set is periodic and the limit exists. The target states the
answer with Hall's value `β = 1 / log 2 ≈ 1.443 ∈ (1, ∞)`, which implies the existence asked.
Compared with the formal-conjectures statement `ErdosProblems/697.lean` (equivalent; no code
imported).
-/

open Filter Topology

/-- The set of integers divisible by some `d ≡ 1 (mod m)` with `1 < d < exp(m^α)`. -/
def oneModDivisible (m : ℕ) (α : ℝ) : Set ℕ :=
  {x | ∃ d : ℕ, d ≡ 1 [MOD m] ∧ 1 < d ∧ (d : ℝ) < Real.exp ((m : ℝ) ^ α) ∧ d ∣ x}

/-- `δ(m, α)`: the natural density of `oneModDivisible m α`, the limit of the proportion of
`x < N` in the set. Only finitely many `d` qualify, so the set is periodic modulo their least common
multiple and the limit exists. -/
noncomputable def oneModDensity (m : ℕ) (α : ℝ) : ℝ :=
  limUnder atTop fun N : ℕ => ((oneModDivisible m α ∩ Set.Iio N).ncard : ℝ) / N

/-- Erdős Problem 697, with Hall's threshold `β = 1 / log 2 ∈ (1, ∞)`: `δ(m, α) → 0` as `m → ∞`
for `α < β`, and `δ(m, α) → 1` for `α > β`. -/
def oneModDivisorDensityThreshold : Prop :=
  (∀ α : ℝ, α < 1 / Real.log 2 → Tendsto (fun m : ℕ => oneModDensity m α) atTop (𝓝 0)) ∧
    ∀ α : ℝ, 1 / Real.log 2 < α → Tendsto (fun m : ℕ => oneModDensity m α) atTop (𝓝 1)

/--
Resolved true: Hall proved the threshold behaviour with `β = 1 / log 2`: `δ(m, α) → 0` for `α < 1 /
log 2` and `δ(m, α) → 1` for `α > 1 / log 2` (`1 / log 2 ∈ (1, ∞)`); erdosproblems.com/697 lists the
problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #697,
https://www.erdosproblems.com/697 (status PROVED); resolution: R. R. Hall, On some conjectures of P.
Erdős in Astérisque. I, J. Number Theory 42 (1992), 313-319, erdosproblems.com/697: proved in the
affirmative with β = 1 / log 2 by Hall, https://www.erdosproblems.com/697.
-/
public theorem_wanted oneModDivisorDensityThreshold_holds : oneModDivisorDensityThreshold

end MathlibExt.NumberTheory.OneModDivisorDensityErdosProblem697Wanted
