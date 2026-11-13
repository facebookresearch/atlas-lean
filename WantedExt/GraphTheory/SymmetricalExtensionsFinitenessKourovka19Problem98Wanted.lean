/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finiteness of symmetrical extensions of graphs (Kourovka Notebook Problem 19.98)

Kourovka Notebook, Archive of Solved Problems, Problem 19.98 (V. I. Trofimov): a connected graph `Σ`
is a symmetrical extension of `Γ` by `Δ` if some vertex-transitive group `G` of automorphisms of `Σ`
has an imprimitivity system `σ` with `Σ / σ ≅ Γ` whose blocks span subgraphs isomorphic to `Δ`. (a)
Let `Γ` be a locally finite Cayley graph of a finitely presented group and `Δ` a finite graph. Are
there only finitely many symmetrical extensions of `Γ` by `Δ`? (b) The same for locally finite
`k`-contractible `Γ`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Group.End
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.GroupTheory.FinitelyPresentedGroup

@[expose] public section

namespace MathlibExt.GraphTheory.SymmetricalExtensionsFinitenessKourovka19Problem98Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.98 (V. I.
Trofimov). UnsolvedMath record UM-00701646 (`KOU-19.98`), dataset ulamai/UnsolvedMath v1.8.0.

Only part (a) is formalized: part (b) uses Trofimov's `k`-contractibility, which the problem only
cites. The imprimitivity system is a `G`-invariant setoid on the vertices; the quotient graph joins
distinct blocks connected by an edge; blocks span induced subgraphs. The Cayley graph is Mathlib's
`SimpleGraph.mulCayley S` for a finite generating set `S` (`x ≠ y` adjacent when `x⁻¹ y ∈ S ∪ S⁻¹`),
so it is locally finite. "Only finitely many" is up to graph isomorphism: finitely many graphs `Σᵢ`
with every symmetrical extension isomorphic to one of them.
-/

/-- The quotient graph `Σ / σ` of `Σ` by a partition `σ` of its vertex set (a setoid): two distinct
blocks are adjacent when some edge of `Σ` joins them. -/
def quotientGraph {V : Type*} (S : SimpleGraph V) (r : Setoid V) : SimpleGraph (Quotient r) :=
  SimpleGraph.fromRel fun a b => ∃ x y : V, Quotient.mk r x = a ∧ Quotient.mk r y = b ∧ S.Adj x y

/-- `Σ` is a symmetrical extension of `Γ` by `Δ` (Trofimov): `Σ` is connected and some
vertex-transitive group `G` of automorphisms of `Σ` has an imprimitivity system `σ` (a
`G`-invariant partition of the vertices) such that `Σ / σ ≅ Γ` and every block of `σ` spans in `Σ`
an induced subgraph isomorphic to `Δ`. -/
def IsSymmetricalExtension {V W U : Type*} (S : SimpleGraph V) (Γ : SimpleGraph W)
    (Δ : SimpleGraph U) : Prop :=
  S.Connected ∧ ∃ (G : Subgroup (S ≃g S)) (r : Setoid V),
    (∀ x y : V, ∃ g ∈ G, g x = y) ∧ (∀ g ∈ G, ∀ x y : V, r x y ↔ r (g x) (g y)) ∧
    Nonempty (quotientGraph S r ≃g Γ) ∧ ∀ x : V, Nonempty (S.induce {y | r x y} ≃g Δ)

/-- Kourovka 19.98(a) (V. I. Trofimov): for a locally finite Cayley graph `Γ` of a finitely
presented group (Mathlib's `SimpleGraph.mulCayley S` for a finite generating set `S`) and a finite
graph `Δ`, there are only finitely many symmetrical extensions of `Γ` by `Δ` up to isomorphism:
finitely many graphs `Σᵢ` such that every symmetrical extension is isomorphic to one of them. -/
def finitelyManySymmetricalExtensions : Prop :=
  ∀ (H : Type) [Group H], Group.IsFinitelyPresented H → ∀ S : Finset H,
    Subgroup.closure (S : Set H) = ⊤ → ∀ (U : Type) [Finite U] (Δ : SimpleGraph U),
      ∃ (k : ℕ) (V : Fin k → Type) (graphs : ∀ i, SimpleGraph (V i)),
        ∀ (V' : Type) (S' : SimpleGraph V'),
          IsSymmetricalExtension S' (SimpleGraph.mulCayley (S : Set H)) Δ →
            ∃ i, Nonempty (S' ≃g graphs i)

/--
Resolved false: the Kourovka Archive answers 19.98(a) "No, not always", as follows from the
construction in the proof of Theorem H of de la Salle and Tessera (and (b) likewise, since the
problem notes that every `Γ` in (a) is `k`-contractible). Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 19.98 (V. I. Trofimov); resolution: M. de la Salle and
R. Tessera, Characterizing a vertex-transitive graph by a large ball, J. Topology 12 (2019), 705-743
(arXiv:1508.02247), Theorem H: for a finitely presented H = G ⋊ Q with G finitely generated and
H²(G, ℤ/2ℤ) infinite (e.g. H = F₂ × F₂) and a suitable extension of H by ℤ/2ℤ, there are, for every
R, continuum many pairwise non-isometric vertex-transitive graphs that are R-locally one of its
Cayley graphs; Kourovka Archive, Problem 19.98: (a) No, not always, and (b) No, not always, as
follows from the construction in the proof of Theorem H, https://arxiv.org/abs/1508.02247.
-/
public theorem_wanted finitelyManySymmetricalExtensions_refuted :
    ¬ finitelyManySymmetricalExtensions

end MathlibExt.GraphTheory.SymmetricalExtensionsFinitenessKourovka19Problem98Wanted
