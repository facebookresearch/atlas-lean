/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Connectedness of the asymptotic spectrum of graphs (Oberwolfach Report 50/2018)

A. Schrijver (with S. Polak), Combinatorial Optimization, Oberwolfach Report 50/2018, p. 3005, open
problems: is the asymptotic spectrum of graphs `Δ` connected?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.GraphTheory.AsymptoticSpectrumGraphsConnectedOWR16633Problem008Wanted

/-!
Source: A. Schrijver (with S. Polak), abstract on the asymptotic spectrum of graphs and the Shannon
capacity, in Combinatorial Optimization, Oberwolfach Reports 15 (2018), no. 50, p. 3005, DOI
10.4171/OWR/2018/50. UnsolvedMath record UM-30003991 (`OWR-16633-008`), dataset ulamai/UnsolvedMath
v1.8.0.

`Δ` is Zuiddam's asymptotic spectrum of graphs: the graph parameters `f` with `f(G ⊔ H) = f(G) +
f(H)`, `f(G ⊠ H) = f(G) f(H)`, `f(G) ≤ f(H)` whenever `G ≤ H` (a map sending distinct non-adjacent
vertices to distinct non-adjacent vertices, the report's homomorphism), and `f(K₁) = 1`, with the
topology of pointwise convergence (the report: `Δ` is a metrizable compact space). Graphs are graphs
on `Fin n`; isomorphism invariance and nonnegativity follow from monotonicity and additivity. The
record's other questions (an explicit `f ∈ Δ` with `f(C₇) = Θ(C₇)`, limits of fractional Haemers
bounds over `F_p`, continuity of `n/k ↦ Θ(C_{k,n})` and `n/k ↦ ϑ(C_{k,n})`) are open and not
formalized here.
-/

/-- A finite simple graph, as a graph on `Fin n` for some `n`. -/
abbrev FinGraph : Type := Σ n : ℕ, SimpleGraph (Fin n)

/-- The disjoint union `G ⊔ H`, on `Fin (n + m)`. -/
def disjointUnion (G H : FinGraph) : FinGraph :=
  ⟨G.1 + H.1, (G.2.sum H.2).map finSumFinEquiv.toEmbedding⟩

/-- The strong product `G ⊠ H`, on `Fin (n * m)`: distinct pairs `(u, v)`, `(u', v')` are adjacent
when `u = u'` or `u u'` is an edge of `G`, and `v = v'` or `v v'` is an edge of `H`. -/
def strongProduct (G H : FinGraph) : FinGraph :=
  ⟨G.1 * H.1, (SimpleGraph.fromRel fun p q : Fin G.1 × Fin H.1 =>
      (p.1 = q.1 ∨ G.2.Adj p.1 q.1) ∧ (p.2 = q.2 ∨ H.2.Adj p.2 q.2)).map
    finProdFinEquiv.toEmbedding⟩

/-- `G ≤ H` in Zuiddam's preorder (Oberwolfach Report 50/2018, p. 3005): there is a map
`h : V(G) → V(H)` sending distinct non-adjacent vertices to distinct non-adjacent vertices. -/
def CohomLE (G H : FinGraph) : Prop :=
  ∃ h : Fin G.1 → Fin H.1, ∀ u v, u ≠ v → ¬ G.2.Adj u v → h u ≠ h v ∧ ¬ H.2.Adj (h u) (h v)

/-- The one-vertex graph `K₁`. -/
def oneVertex : FinGraph := ⟨1, ⊥⟩

/-- The asymptotic spectrum of graphs `Δ`: the graph parameters that are additive under disjoint
union, multiplicative under the strong product, monotone under `CohomLE` and normalized by
`f(K₁) = 1`, as a subspace of `FinGraph → ℝ` with the topology of pointwise convergence. -/
def asymptoticSpectrum : Set (FinGraph → ℝ) :=
  {f | (∀ G H, f (disjointUnion G H) = f G + f H) ∧ (∀ G H, f (strongProduct G H) = f G * f H) ∧
    (∀ G H, CohomLE G H → f G ≤ f H) ∧ f oneVertex = 1}

/-- The first open problem of Schrijver's abstract (Oberwolfach Report 50/2018, p. 3005): the
asymptotic spectrum of graphs `Δ` is connected. -/
def asymptoticSpectrumConnected : Prop :=
  IsConnected asymptoticSpectrum

/--
Resolved true: Vrana showed that every spectral point admits a probabilistic refinement, so that the
asymptotic spectrum can be parameterized by a convex set (abstract); Wigderson and Zuiddam record
that "the asymptotic spectrum of graphs is known to be connected [Vra21]" and that connectivity and
even log-convexity of the spectrum was proved by Vrana. Source: A. Schrijver (with S. Polak),
abstract on the asymptotic spectrum of graphs and the Shannon capacity, in Combinatorial
Optimization, Oberwolfach Reports 15 (2018), no. 50, p. 3005, DOI 10.4171/OWR/2018/50; resolution:
P. Vrana, Probabilistic refinement of the asymptotic spectrum of graphs, Combinatorica 41 (2021),
DOI 10.1007/s00493-020-4324-5, arXiv:1903.01857; A. Wigderson and J. Zuiddam, Asymptotic spectra:
theory, applications and extensions, Bull. Amer. Math. Soc. (2026), DOI 10.1090/bull/1880, Vrana,
abstract: the asymptotic spectrum can be parameterized with a convex set; Wigderson-Zuiddam: 'the
asymptotic spectrum of graphs is known to be connected [Vra21]' and 'connectivity and even
log-convexity of the spectrum was proved (by Vrana [Vra21])', https://arxiv.org/abs/1903.01857.
-/
public theorem_wanted asymptoticSpectrumConnected_holds : asymptoticSpectrumConnected

end MathlibExt.GraphTheory.AsymptoticSpectrumGraphsConnectedOWR16633Problem008Wanted
