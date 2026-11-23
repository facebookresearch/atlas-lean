/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# `R(3, 3, n)` versus `R(3, n)` (Erdős Problem 553)

Erdős Problem 553 (Erdős and Sós): let `R(3, 3, n)` be the smallest `m` such that every
`3`-colouring of the edges of `K_m` has a monochromatic triangle in one of the first two colours or
a monochromatic `K_n` in the third colour, and define `R(3, n)` similarly with two colours. Show
that `R(3, 3, n) / R(3, n) → ∞` as `n → ∞`.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.Ramsey

@[expose] public section

namespace MathlibExt.GraphTheory.MulticolourRamseyRatioErdosProblem553Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #553, https://www.erdosproblems.com/553 (status
PROVED). UnsolvedMath record UM-30006931 (`EP-553`), dataset ulamai/UnsolvedMath v1.8.0.

Colourings for `R(3, 3, n)` are functions `Sym2 (Fin m) → Fin 3` on the pairs of `Fin m`; only pairs
of distinct vertices matter. `R(3, n)` is MathlibExt's `SimpleGraph.graphRamsey 3 n` (a graph on
`Fin N` and its complement are the two colours). Both minima are `sInf`s of sets that are nonempty
by Ramsey's theorem. The quotient is taken in `ℝ`.
-/

/-- The edge colouring `c` of the complete graph on `Fin m` has a triangle all of whose edges have
colour `i`. -/
def HasMonoTriangle {m k : ℕ} (c : Sym2 (Fin m) → Fin k) (i : Fin k) : Prop :=
  ∃ x y z : Fin m, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ c s(x, y) = i ∧ c s(y, z) = i ∧ c s(x, z) = i

/-- The edge colouring `c` of the complete graph on `Fin m` has `n` vertices all of whose pairs
have colour `i` (a copy of `K_n` in colour `i`). -/
def HasMonoClique {m k : ℕ} (c : Sym2 (Fin m) → Fin k) (i : Fin k) (n : ℕ) : Prop :=
  ∃ S : Finset (Fin m), S.card = n ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c s(x, y) = i

/-- `R(3, 3, n)`: the least `m` such that every `3`-colouring of the edges of `K_m` has a triangle
in colour `0` or `1` or a `K_n` in colour `2`. -/
noncomputable def ramseyThreeThree (n : ℕ) : ℕ :=
  sInf {m | ∀ c : Sym2 (Fin m) → Fin 3, HasMonoTriangle c 0 ∨ HasMonoTriangle c 1 ∨
    HasMonoClique c 2 n}

/-- Erdős Problem 553: `R(3, 3, n) / R(3, n) → ∞` as `n → ∞`. -/
def ramseyThreeThreeRatioTendsToInfinity : Prop :=
  Filter.Tendsto (fun n : ℕ => (ramseyThreeThree n : ℝ) / SimpleGraph.graphRamsey 3 n)
    Filter.atTop Filter.atTop

/--
Resolved true: Alon and Rödl proved `R(3, 3, n) = Θ(n³ (log n)^{O(1)})` (their abstract: `r(K₃, K₃,
K_m) = Θ(m³ poly log m)`), while Shearer proved `R(3, n) ≪ n² / log n`, so the ratio tends to
infinity; erdosproblems.com/553 lists the problem as proved. Source: T. F. Bloom, Erdős Problems,
Problem #553, https://www.erdosproblems.com/553 (status PROVED); resolution: N. Alon and V. Rödl,
Sharp bounds for some multicolor Ramsey numbers, Combinatorica (2005), 125-141, abstract: r(K₃, K₃,
K_m) = Θ(m³ poly log m), solving in a strong form the conjecture of Erdős and Sós; with Shearer's
R(3, n) ≪ n² / log n the ratio tends to infinity (erdosproblems.com/553),
https://www.erdosproblems.com/553.
-/
public theorem_wanted ramseyThreeThreeRatioTendsToInfinity_holds :
    ramseyThreeThreeRatioTendsToInfinity

end MathlibExt.GraphTheory.MulticolourRamseyRatioErdosProblem553Wanted
