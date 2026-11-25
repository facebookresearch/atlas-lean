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

/-- **Generalized triangle $\mathcal{T}_r$.** Let $r, n \in \mathbb{N}$ and let $G$ be a family of
subsets of $\{0, \dots, n-1\}$, typically an $r$-uniform hypergraph. Then $G$ contains a
generalized triangle $\mathcal{T}_r$ (the book $B_{r,2}$) when there are edges
$D_1, D_2, D_3 \in G$, not necessarily distinct, with $|D_1 \cap D_2| + 1 = r$,
$D_1 \triangle D_2 \subseteq D_3$ and $D_3 \cap D_1 \cap D_2 = \emptyset$. -/
def ContainsGeneralizedTriangle {n : ℕ} (r : ℕ) (G : Finset (Finset (Fin n))) : Prop :=
  ∃ D₁ ∈ G, ∃ D₂ ∈ G, ∃ D₃ ∈ G,
    (D₁ ∩ D₂).card + 1 = r ∧ symmDiff D₁ D₂ ⊆ D₃ ∧ Disjoint D₃ (D₁ ∩ D₂)

/-- **Turán number of the generalized triangle.** For $r, n \in \mathbb{N}$, the Turán number
$\mathrm{ex}(n, \mathcal{T}_r)$ is the largest number of edges of an $r$-uniform hypergraph on the
vertex set $\{0, \dots, n-1\}$ that contains no generalized triangle $\mathcal{T}_r$. -/
noncomputable def generalizedTriangleTuranNumber (r n : ℕ) : ℕ :=
  sSup {m | ∃ G : Finset (Finset (Fin n)),
    SetFamily.IsUniform G r ∧ ¬ ContainsGeneralizedTriangle r G ∧ G.card = m}

/-- **Steiner system $S(t, r, m)$.** Let $t, r, m \in \mathbb{N}$ and let $D$ be a family of
subsets of $\{0, \dots, m-1\}$. Then $D$ is a Steiner system $S(t, r, m)$ when every block of $D$
has exactly $r$ elements and every $t$-element subset of $\{0, \dots, m-1\}$ is contained in
exactly one block of $D$. -/
def IsSteinerSystem (t r m : ℕ) (D : Finset (Finset (Fin m))) : Prop :=
  SetFamily.IsUniform D r ∧ ∀ T : Finset (Fin m), T.card = t → ∃! B, B ∈ D ∧ T ⊆ B

/-- **Blow-up of a hypergraph along a map.** Let $D$ be a family of subsets of
$\{0, \dots, m-1\}$, let $r \in \mathbb{N}$ and let $\varphi : \{0, \dots, n-1\} \to
\{0, \dots, m-1\}$. The $r$-uniform blow-up of $D$ along $\varphi$ is the family of $r$-element
subsets $e \subseteq \{0, \dots, n-1\}$ such that $\varphi$ is injective on $e$ and the image
$\varphi(e)$ is a block of $D$. -/
def blowUp {n m : ℕ} (D : Finset (Finset (Fin m))) (r : ℕ) (φ : Fin n → Fin m) :
    Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard r).filter fun e => (e.image φ).card = r ∧ e.image φ ∈ D

/-- **Largest blow-up of a hypergraph.** Let $D$ be a family of subsets of $\{0, \dots, m-1\}$
and let $r, n \in \mathbb{N}$. The largest blow-up size of $D$ is the maximum, over all maps
$\varphi : \{0, \dots, n-1\} \to \{0, \dots, m-1\}$, of the number of edges of the $r$-uniform
blow-up of $D$ along $\varphi$; it is $0$ when there is no such map. -/
def maxBlowUpSize {m : ℕ} (D : Finset (Finset (Fin m))) (r n : ℕ) : ℕ :=
  Finset.univ.sup fun φ : Fin n → Fin m => (blowUp D r φ).card

/-- **Turán number of $\mathcal{T}_5$ via blow-ups of $S(4, 5, 11)$.** There exist a Steiner system
$D$ of type $S(4, 5, 11)$ on $\{0, \dots, 10\}$ and an $n_0 \in \mathbb{N}$ such that for every
$n \ge n_0$, the Turán number $\mathrm{ex}(n, \mathcal{T}_5)$ of the generalized triangle
$\mathcal{T}_5$ (the book $B_{5,2}$) equals the largest number of edges of a $5$-uniform blow-up
of $D$ along a map $\{0, \dots, n-1\} \to \{0, \dots, 10\}$.

Source: AimPL Problem 2.1 (Hypergraph Turán problem), case `k = 5`. -/
def generalizedTriangleFiveTuranNumber : Prop :=
  ∃ D : Finset (Finset (Fin 11)), IsSteinerSystem 4 5 11 D ∧
    ∃ n₀ : ℕ, ∀ n ≥ n₀, generalizedTriangleTuranNumber 5 n = maxBlowUpSize D 5 n

/-- **Turán number of $\mathcal{T}_6$ via blow-ups of $S(5, 6, 12)$.** There exist a Steiner system
$D$ of type $S(5, 6, 12)$ on $\{0, \dots, 11\}$ and an $n_0 \in \mathbb{N}$ such that for every
$n \ge n_0$, the Turán number $\mathrm{ex}(n, \mathcal{T}_6)$ of the generalized triangle
$\mathcal{T}_6$ (the book $B_{6,2}$) equals the largest number of edges of a $6$-uniform blow-up
of $D$ along a map $\{0, \dots, n-1\} \to \{0, \dots, 11\}$.

Source: AimPL Problem 2.1 (Hypergraph Turán problem), case `k = 6`. -/
def generalizedTriangleSixTuranNumber : Prop :=
  ∃ D : Finset (Finset (Fin 12)), IsSteinerSystem 5 6 12 D ∧
    ∃ n₀ : ℕ, ∀ n ≥ n₀, generalizedTriangleTuranNumber 6 n = maxBlowUpSize D 6 n

/--
**Norin–Yepremyan theorem for $\mathcal{T}_5$.** There exist a Steiner system $D$ of type
$S(4, 5, 11)$ on $\{0, \dots, 10\}$ and an $n_0 \in \mathbb{N}$ such that for every $n \ge n_0$,
the Turán number $\mathrm{ex}(n, \mathcal{T}_5)$ of the generalized triangle $\mathcal{T}_5$ (the
book $B_{5,2}$) equals the largest number of edges of a $5$-uniform blow-up of $D$ along a map
$\{0, \dots, n-1\} \to \{0, \dots, 10\}$.

Norin and Yepremyan proved more: for all large $n$, every extremal $\mathcal{T}_5$-free
$5$-uniform hypergraph on $n$ vertices is a blow-up of $S(4, 5, 11)$ (the Frankl–Füredi
construction).

Source: AimPL: Hypergraph Turán problem,
Problem 2.1 (Frankl-Füredi), http://aimpl.org/hypergraphturan/2/; resolution: S. Norin and L.
Yepremyan, Turán number of generalized triangles, J. Combin. Theory Ser. A 146 (2017), 312-343,
arXiv:1501.01913, Theorem 1.1: there is n0 such that for all n ≥ n0, ex(n, 𝒯_r) = ex(n, Σ_r) for r =
5, 6, and the extremal graphs are blow-ups of the unique (11, 5, 4) and (12, 6, 5) Steiner systems;
the blow-ups are the Frankl-Füredi lower-bound constructions named in the AimPL problem,
https://doi.org/10.1016/j.jcta.2016.09.003.
-/
public theorem_wanted generalizedTriangleFiveTuranNumber_holds : generalizedTriangleFiveTuranNumber

/--
**Norin–Yepremyan theorem for $\mathcal{T}_6$.** There exist a Steiner system $D$ of type
$S(5, 6, 12)$ on $\{0, \dots, 11\}$ and an $n_0 \in \mathbb{N}$ such that for every $n \ge n_0$,
the Turán number $\mathrm{ex}(n, \mathcal{T}_6)$ of the generalized triangle $\mathcal{T}_6$ (the
book $B_{6,2}$) equals the largest number of edges of a $6$-uniform blow-up of $D$ along a map
$\{0, \dots, n-1\} \to \{0, \dots, 11\}$.

Norin and Yepremyan proved more: for all large $n$, every extremal $\mathcal{T}_6$-free
$6$-uniform hypergraph on $n$ vertices is a blow-up of $S(5, 6, 12)$ (the Frankl–Füredi
construction).

Source: AimPL: Hypergraph Turán problem,
Problem 2.1 (Frankl-Füredi), http://aimpl.org/hypergraphturan/2/; resolution: S. Norin and L.
Yepremyan, Turán number of generalized triangles, J. Combin. Theory Ser. A 146 (2017), 312-343,
arXiv:1501.01913, Theorem 1.1: there is n0 such that for all n ≥ n0, ex(n, 𝒯_r) = ex(n, Σ_r) for r =
5, 6, and the extremal graphs are blow-ups of the unique (11, 5, 4) and (12, 6, 5) Steiner systems;
the blow-ups are the Frankl-Füredi lower-bound constructions named in the AimPL problem,
https://doi.org/10.1016/j.jcta.2016.09.003.
-/
public theorem_wanted generalizedTriangleSixTuranNumber_holds : generalizedTriangleSixTuranNumber

end MathlibExt.Combinatorics.GeneralizedTriangleTuranNumberAIMCombinatoricsProblem151Wanted
