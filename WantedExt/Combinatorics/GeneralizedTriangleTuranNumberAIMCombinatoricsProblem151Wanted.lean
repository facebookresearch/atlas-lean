/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Turán numbers of the books B(5,2) and B(6,2) (AimPL, Hypergraph Turán problem, Problem 2.1)

AimPL, Hypergraph Turán problem, Problem 2.1: the book `B_{k,m}` has `m` edges sharing `k - 1`
common points plus one edge containing the remaining `m` points and otherwise disjoint. Frankl and
Füredi determined the Turán densities of `B_{5,2}` and `B_{6,2}` by blowing up a small design.
Determine `ex(n, B_{5,2})` and `ex(n, B_{6,2})` exactly for all large `n`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Lattice.Nat
public import MathlibExt.Combinatorics.SetFamily.UniformHypergraph

@[expose] public section

namespace MathlibExt.Combinatorics.GeneralizedTriangleTuranNumberAIMCombinatoricsProblem151Wanted

/-!
Source: AimPL: Hypergraph Turán problem, Problem 2.1 (Frankl-Füredi),
http://aimpl.org/hypergraphturan/2/. UnsolvedMath record UM-20001026 (`AIM-COMBINATORICS-0151`),
dataset ulamai/UnsolvedMath v1.8.0.

`B_{k,2}` is the generalized triangle `𝒯_k`: edges `D₁, D₂, D₃` with `|D₁ ∩ D₂| = k - 1`, `D₁ △ D₂ ⊆
D₃` and `D₃` disjoint from `D₁ ∩ D₂`. The designs are the Steiner systems `S(4, 5, 11)` and `S(5, 6,
12)` (each unique up to isomorphism), stated existentially. A blow-up of a design along `φ : Fin n →
Fin m` has as edges the `k`-sets that `φ` maps injectively onto a block. 'Determine exactly' is
answered as Norin and Yepremyan do: for large `n`, `ex(n, 𝒯_k)` is the largest size of an `n`-vertex
blow-up of the design.
-/

/-- An `r`-graph `G` on `Fin n` contains a generalized triangle `𝒯_r` (the book `B_{r,2}`): edges
`D₁, D₂, D₃` with `|D₁ ∩ D₂| = r - 1`, `D₁ △ D₂ ⊆ D₃` and `D₃` disjoint from `D₁ ∩ D₂`. -/
def ContainsGeneralizedTriangle {n : ℕ} (r : ℕ) (G : Finset (Finset (Fin n))) : Prop :=
  ∃ D₁ ∈ G, ∃ D₂ ∈ G, ∃ D₃ ∈ G,
    (D₁ ∩ D₂).card + 1 = r ∧ symmDiff D₁ D₂ ⊆ D₃ ∧ Disjoint D₃ (D₁ ∩ D₂)

/-- The Turán number `ex(n, 𝒯_r)`: the largest number of edges of an `r`-graph on `n` vertices
with no generalized triangle. -/
noncomputable def generalizedTriangleTuranNumber (r n : ℕ) : ℕ :=
  sSup {m | ∃ G : Finset (Finset (Fin n)),
    SetFamily.IsUniform G r ∧ ¬ ContainsGeneralizedTriangle r G ∧ G.card = m}

/-- `D` is a Steiner system `S(t, r, m)` on `Fin m`: blocks of size `r` such that every `t`-set
lies in exactly one block. -/
def IsSteinerSystem (t r m : ℕ) (D : Finset (Finset (Fin m))) : Prop :=
  SetFamily.IsUniform D r ∧ ∀ T : Finset (Fin m), T.card = t → ∃! B, B ∈ D ∧ T ⊆ B

/-- The blow-up of the `r`-graph `D` on `Fin m` along `φ : Fin n → Fin m`: the `r`-sets of
`Fin n` that `φ` maps injectively onto a block of `D`. -/
def blowUp {n m : ℕ} (D : Finset (Finset (Fin m))) (r : ℕ) (φ : Fin n → Fin m) :
    Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard r).filter fun e => (e.image φ).card = r ∧ e.image φ ∈ D

/-- The largest number of edges of an `n`-vertex blow-up of `D`. -/
def maxBlowUpSize {m : ℕ} (D : Finset (Finset (Fin m))) (r n : ℕ) : ℕ :=
  Finset.univ.sup fun φ : Fin n → Fin m => (blowUp D r φ).card

/-- AimPL Problem 2.1 (Hypergraph Turán problem), case `k = 5`: for all large `n`, `ex(n, B_{5,2})`
is the largest size of an `n`-vertex blow-up of the Steiner system `S(4, 5, 11)`. -/
def generalizedTriangleFiveTuranNumber : Prop :=
  ∃ D : Finset (Finset (Fin 11)), IsSteinerSystem 4 5 11 D ∧
    ∃ n₀ : ℕ, ∀ n ≥ n₀, generalizedTriangleTuranNumber 5 n = maxBlowUpSize D 5 n

/-- AimPL Problem 2.1 (Hypergraph Turán problem), case `k = 6`: for all large `n`, `ex(n, B_{6,2})`
is the largest size of an `n`-vertex blow-up of the Steiner system `S(5, 6, 12)`. -/
def generalizedTriangleSixTuranNumber : Prop :=
  ∃ D : Finset (Finset (Fin 12)), IsSteinerSystem 5 6 12 D ∧
    ∃ n₀ : ℕ, ∀ n ≥ n₀, generalizedTriangleTuranNumber 6 n = maxBlowUpSize D 6 n

/--
Resolved true: Norin and Yepremyan proved that for all large `n` every extremal `𝒯_5`-free 5-graph
on `n` vertices is a blow-up of the Steiner system `S(4, 5, 11)`, so `ex(n, B_{5,2})` is the largest
size of such a blow-up (the Frankl-Füredi construction). Source: AimPL: Hypergraph Turán problem,
Problem 2.1 (Frankl-Füredi), http://aimpl.org/hypergraphturan/2/; resolution: S. Norin and L.
Yepremyan, Turán number of generalized triangles, J. Combin. Theory Ser. A 146 (2017), 312-343,
arXiv:1501.01913, Theorem 1.1: there is n0 such that for all n ≥ n0, ex(n, 𝒯_r) = ex(n, Σ_r) for r =
5, 6, and the extremal graphs are blow-ups of the unique (11, 5, 4) and (12, 6, 5) Steiner systems;
the blow-ups are the Frankl-Füredi lower-bound constructions named in the AimPL problem,
https://doi.org/10.1016/j.jcta.2016.09.003.
-/
public theorem_wanted generalizedTriangleFiveTuranNumber_holds : generalizedTriangleFiveTuranNumber

/--
Resolved true: Norin and Yepremyan proved that for all large `n` every extremal `𝒯_6`-free 6-graph
on `n` vertices is a blow-up of the Steiner system `S(5, 6, 12)`, so `ex(n, B_{6,2})` is the largest
size of such a blow-up (the Frankl-Füredi construction). Source: AimPL: Hypergraph Turán problem,
Problem 2.1 (Frankl-Füredi), http://aimpl.org/hypergraphturan/2/; resolution: S. Norin and L.
Yepremyan, Turán number of generalized triangles, J. Combin. Theory Ser. A 146 (2017), 312-343,
arXiv:1501.01913, Theorem 1.1: there is n0 such that for all n ≥ n0, ex(n, 𝒯_r) = ex(n, Σ_r) for r =
5, 6, and the extremal graphs are blow-ups of the unique (11, 5, 4) and (12, 6, 5) Steiner systems;
the blow-ups are the Frankl-Füredi lower-bound constructions named in the AimPL problem,
https://doi.org/10.1016/j.jcta.2016.09.003.
-/
public theorem_wanted generalizedTriangleSixTuranNumber_holds : generalizedTriangleSixTuranNumber

end MathlibExt.Combinatorics.GeneralizedTriangleTuranNumberAIMCombinatoricsProblem151Wanted
