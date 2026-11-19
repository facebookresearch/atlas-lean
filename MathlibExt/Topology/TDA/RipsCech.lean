/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Nerves, Čech and Vietoris–Rips complexes

The simplicial complexes that topological data analysis builds from a metric space at a scale
`ε`, following G. Carlsson, *Topology and data*, Bull. Amer. Math. Soc. 46 (2009) 255–308, §2.2.
Complexes are Mathlib's `PreAbstractSimplicialComplex` (faces are nonempty finite sets, closed
under nonempty subsets), so that the complexes at a negative scale are allowed and empty.

* `nerve U`: the nerve of a family of sets (Def. 2.2).
* `cechComplex ε`: the Čech complex, the nerve of the closed `ε`-balls centred at the points
  (the construction `Č(X, ε)` before Thm. 2.4, with closed balls).
* `ripsComplex ε`: the Vietoris–Rips complex (Def. 2.5).
* `ripsGraph ε`: its one-skeleton, the `ε`-neighbourhood graph; the Vietoris–Rips complex is the
  clique (flag) complex of this graph (`mem_ripsComplex_iff_isClique`).
* `cechComplex_le_ripsComplex_two_mul`, `ripsComplex_le_cechComplex`: the inclusions
  `Č(X, ε) ⊆ VR(X, 2ε) ⊆ Č(X, 2ε)` of Prop. 2.6.
* `cechComplex_mono`, `ripsComplex_mono`: both are filtrations, that is, `ℝ`-persistence
  simplicial complexes in the sense of Def. 2.9.
-/

@[expose] public section

open Metric

namespace MathlibExt.Topology.TDA

/-- **Nerve of a family of sets.** For a family `U : ι → Set X` (for instance a covering of
`X`), the nerve is the abstract simplicial complex on the index set `ι` whose faces are the
nonempty finite sets of indices `s` with `⋂_{i ∈ s} U i ≠ ∅` (Carlsson, *Topology and data*,
Bull. AMS 2009, Def. 2.2). -/
def nerve {ι X : Type*} (U : ι → Set X) : PreAbstractSimplicialComplex ι where
  faces := {s | s.Nonempty ∧ ∃ x, ∀ i ∈ s, x ∈ U i}
  isRelLowerSet_faces := fun _ hs =>
    ⟨hs.1, fun _ hts htne => ⟨htne, hs.2.imp fun _ hx i hi => hx i (hts hi)⟩⟩

theorem mem_nerve {ι X : Type*} {U : ι → Set X} {s : Finset ι} :
    s ∈ nerve U ↔ s.Nonempty ∧ ∃ x, ∀ i ∈ s, x ∈ U i :=
  Iff.rfl

variable {M : Type*} [PseudoMetricSpace M]

/-- **Čech complex.** For a (pseudo)metric space `M` and a scale `ε`, the Čech complex
`Č(M, ε)` is the nerve of the family of closed balls `closedBall x ε`, `x ∈ M`: a nonempty
finite set of points spans a simplex exactly when the closed `ε`-balls around them have a common
point of `M` (Carlsson, *Topology and data*, Bull. AMS 2009, §2.2, the construction `Č(V, ε)`
with `V = M`, closed balls). The source does not say whether its balls are open or closed; closed
balls are what make the second inclusion of Prop. 2.6 hold: with open balls, two points at
distance exactly `2ε` span an edge of `VR(M, 2ε)` but not of `Č(M, 2ε)`. -/
def cechComplex (ε : ℝ) : PreAbstractSimplicialComplex M :=
  nerve fun x : M => closedBall x ε

theorem mem_cechComplex {ε : ℝ} {s : Finset M} :
    s ∈ cechComplex ε ↔ s.Nonempty ∧ ∃ z : M, ∀ x ∈ s, dist z x ≤ ε :=
  Iff.rfl

/-- **Vietoris–Rips complex.** For a (pseudo)metric space `M` and a scale `ε`, the
Vietoris–Rips complex `VR(M, ε)` has as faces the nonempty finite sets of points whose pairwise
distances are all at most `ε` (Carlsson, *Topology and data*, Bull. AMS 2009, Def. 2.5). -/
def ripsComplex (ε : ℝ) : PreAbstractSimplicialComplex M where
  faces := {s | s.Nonempty ∧ ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ ε}
  isRelLowerSet_faces := fun _ hs =>
    ⟨hs.1, fun _ hts htne => ⟨htne, fun x hx y hy => hs.2 x (hts hx) y (hts hy)⟩⟩

theorem mem_ripsComplex {ε : ℝ} {s : Finset M} :
    s ∈ ripsComplex ε ↔ s.Nonempty ∧ ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ ε :=
  Iff.rfl

/-- **The Čech complex is a filtration.** If `ε ≤ δ` then `Č(M, ε) ⊆ Č(M, δ)`, so the Čech
complexes form an `ℝ`-persistence simplicial complex (Carlsson, *Topology and data*,
Bull. AMS 2009, §2.3, the paragraph after Def. 2.9). -/
theorem cechComplex_mono {ε δ : ℝ} (h : ε ≤ δ) :
    (cechComplex ε : PreAbstractSimplicialComplex M) ≤ cechComplex δ :=
  fun _ hs => ⟨hs.1, hs.2.imp fun _ hz x hx => (hz x hx).trans h⟩

/-- **The Vietoris–Rips complex is a filtration.** If `ε ≤ δ` then `VR(M, ε) ⊆ VR(M, δ)`
(Carlsson, *Topology and data*, Bull. AMS 2009, §2.3, the paragraph after Def. 2.9). -/
theorem ripsComplex_mono {ε δ : ℝ} (h : ε ≤ δ) :
    (ripsComplex ε : PreAbstractSimplicialComplex M) ≤ ripsComplex δ :=
  fun _ hs => ⟨hs.1, fun x hx y hy => (hs.2 x hx y hy).trans h⟩

/-- **Čech inside Rips at twice the scale.** `Č(M, ε) ⊆ VR(M, 2ε)`: points whose closed
`ε`-balls share a point are pairwise at distance at most `2ε` (Carlsson, *Topology and data*,
Bull. AMS 2009, Prop. 2.6, first inclusion). -/
theorem cechComplex_le_ripsComplex_two_mul (ε : ℝ) :
    (cechComplex ε : PreAbstractSimplicialComplex M) ≤ ripsComplex (2 * ε) := by
  rintro s ⟨hne, z, hz⟩
  refine ⟨hne, fun x hx y hy => ?_⟩
  calc dist x y ≤ dist z x + dist z y := dist_triangle_left x y z
    _ ≤ ε + ε := add_le_add (hz x hx) (hz y hy)
    _ = 2 * ε := (two_mul ε).symm

/-- **Rips inside Čech at the same scale.** `VR(M, ε) ⊆ Č(M, ε)`: if the pairwise distances of
a nonempty finite set are at most `ε`, any of its points lies in all the closed `ε`-balls. With
`2ε` in place of `ε` this is the second inclusion `VR(M, 2ε) ⊆ Č(M, 2ε)` of Carlsson,
*Topology and data*, Bull. AMS 2009, Prop. 2.6. -/
theorem ripsComplex_le_cechComplex (ε : ℝ) :
    (ripsComplex ε : PreAbstractSimplicialComplex M) ≤ cechComplex ε := by
  rintro s ⟨hne, hs⟩
  obtain ⟨z, hz⟩ := hne
  exact ⟨⟨z, hz⟩, z, fun x hx => hs z hz x hx⟩

/-- **The Rips–Čech interleaving.** `Č(M, ε) ⊆ VR(M, 2ε) ⊆ Č(M, 2ε)` (Carlsson, *Topology and
data*, Bull. AMS 2009, Prop. 2.6). -/
theorem cechComplex_le_ripsComplex_le_cechComplex (ε : ℝ) :
    (cechComplex ε : PreAbstractSimplicialComplex M) ≤ ripsComplex (2 * ε) ∧
      (ripsComplex (2 * ε) : PreAbstractSimplicialComplex M) ≤ cechComplex (2 * ε) :=
  ⟨cechComplex_le_ripsComplex_two_mul ε, ripsComplex_le_cechComplex (2 * ε)⟩

/-- **The `ε`-neighbourhood graph.** Two distinct points are adjacent when their distance is at
most `ε`; this is the one-skeleton of the Vietoris–Rips complex `VR(M, ε)` (Carlsson,
*Topology and data*, Bull. AMS 2009, Def. 2.5 and §3.2). -/
def ripsGraph (ε : ℝ) : SimpleGraph M where
  Adj x y := x ≠ y ∧ dist x y ≤ ε
  symm := ⟨fun _ _ h => ⟨h.1.symm, (dist_comm _ _).trans_le h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem ripsGraph_adj {ε : ℝ} {x y : M} : (ripsGraph ε).Adj x y ↔ x ≠ y ∧ dist x y ≤ ε :=
  Iff.rfl

/-- **The Vietoris–Rips complex is the clique complex of its one-skeleton.** For `ε ≥ 0`, a
nonempty finite set of points is a face of `VR(M, ε)` exactly when it is a clique of the
`ε`-neighbourhood graph: the Vietoris–Rips complex is determined by its edges, which is the reason
Carlsson gives for preferring it to the Čech complex (Carlsson, *Topology and data*, Bull. AMS
2009, §2.2, the paragraph before Def. 2.5). -/
theorem mem_ripsComplex_iff_isClique {ε : ℝ} (hε : 0 ≤ ε) {s : Finset M} :
    s ∈ ripsComplex ε ↔ s.Nonempty ∧ (ripsGraph ε).IsClique (s : Set M) := by
  refine and_congr_right fun _ => ⟨fun h x hx y hy hxy => ⟨hxy, h x hx y hy⟩, fun h x hx y hy => ?_⟩
  by_cases hxy : x = y
  · subst hxy
    simpa using hε
  · exact (h hx hy hxy).2

end MathlibExt.Topology.TDA
