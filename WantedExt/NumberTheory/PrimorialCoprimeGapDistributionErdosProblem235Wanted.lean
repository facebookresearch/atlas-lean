/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Gaps between reduced residues of primorials (Erdős Problem 235)

Erdős Problem 235: let `N_k = 2 · 3 ⋯ p_k` and `a₁ < ⋯ < a_φ(N_k)` the integers below `N_k` coprime
to `N_k`. Then for every `c ≥ 0` the proportion `#{2 ≤ i ≤ φ(N_k) : aᵢ - aᵢ₋₁ ≤ c N_k / φ(N_k)} /
φ(N_k)` converges as `k → ∞`, and the limit is a continuous function of `c`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.Totient
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.PrimorialCoprimeGapDistributionErdosProblem235Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #235, https://www.erdosproblems.com/235 (status
PROVED). UnsolvedMath record UM-30006785 (`EP-235`), dataset ulamai/UnsolvedMath v1.8.0.

`N_k` is the product of the first `k` primes (`N₀ = 1` has no gaps); continuity is on `[0, ∞)`.
Compared with the formal-conjectures statement `ErdosProblems/235.lean` (there indexed by the
product of the first `k + 1` primes, equivalent; no code imported).
-/

open Filter Topology

/-- `N_k = p₁ p₂ ⋯ p_k`, the product of the first `k` primes. -/
noncomputable def firstPrimesProduct (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- The integers `1 ≤ a < N` coprime to `N`, in increasing order: `a₁ < ⋯ < a_φ(N)`. -/
def coprimeResidues (N : ℕ) : List ℕ :=
  ((Finset.Ico 1 N).filter (fun a => Nat.Coprime a N)).sort (· ≤ ·)

/-- The consecutive gaps `aᵢ - aᵢ₋₁`, `2 ≤ i ≤ φ(N)`, of the integers below `N` coprime to `N`. -/
def coprimeGaps (N : ℕ) : List ℕ :=
  List.zipWith (fun a b => b - a) (coprimeResidues N) (coprimeResidues N).tail

/-- The proportion `#{2 ≤ i ≤ φ(N_k) : aᵢ - aᵢ₋₁ ≤ c N_k / φ(N_k)} / φ(N_k)`. -/
noncomputable def gapProportion (k : ℕ) (c : ℝ) : ℝ :=
  (((coprimeGaps (firstPrimesProduct k)).filter (fun g => decide ((g : ℝ) ≤
      c * firstPrimesProduct k / Nat.totient (firstPrimesProduct k)))).length : ℝ) /
    Nat.totient (firstPrimesProduct k)

/-- Erdős Problem 235: for every `c ≥ 0` the proportion of gaps `aᵢ - aᵢ₋₁ ≤ c N_k / φ(N_k)`
between consecutive integers below `N_k = p₁ ⋯ p_k` coprime to `N_k` converges as `k → ∞`, and the
limit is a continuous function of `c`. -/
def primorialCoprimeGapDistributionContinuous : Prop :=
  ∃ F : ℝ → ℝ, ContinuousOn F (Set.Ici 0) ∧
    ∀ c : ℝ, 0 ≤ c → Tendsto (fun k => gapProportion k c) atTop (𝓝 (F c))

/--
Resolved true: Hooley proved that the normalized gaps have an exponential limiting distribution, the
proportion tending to `1 - e^{-c}` uniformly in `c`, a continuous function; erdosproblems.com/235
lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #235,
https://www.erdosproblems.com/235 (status PROVED); resolution: C. Hooley, On the difference between
consecutive numbers prime to n. II, Publ. Math. Debrecen 12 (1965), 39-49, erdosproblems.com/235:
solved by Hooley, the gaps have exponential limiting distribution f(c) = 1 - e^{-c},
https://doi.org/10.5486/PMD.1965.12.1-4.06.
-/
public theorem_wanted primorialCoprimeGapDistributionContinuous_holds :
    primorialCoprimeGapDistributionContinuous

end MathlibExt.NumberTheory.PrimorialCoprimeGapDistributionErdosProblem235Wanted
