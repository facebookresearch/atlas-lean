/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoundaryConditions
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Probability.Configuration.WeakConvergence
public import PhyslibExt.StatisticalMechanics.RandomCluster.RandomCluster
/-!
# Finite- and infinite-volume FK measures on `ℤ^d`

Wired random-cluster measures on finite graphs, box measures on `ℤ^d`, and their weak limits.

## i. Overview

For a finite graph `G`, a boundary predicate `bdry`, `p ∈ (0, 1)` and `q > 0`, the wired
random-cluster (FK) measure gives a bond configuration `ω` the weight
`∏_e p^ω(e) (1 - p)^(1 - ω(e)) · q^k¹(ω)`, where `k¹(ω)` counts the open clusters after all
boundary vertices are wired into one vertex. The free measure (`fkPMF`) uses the ordinary
cluster count instead.

On `ℤ^d` we take the box `Λ_n = [-n, n]^d` with its nearest-neighbour edges and its vertex
boundary `Λ_n \ Λ_(n-1)`. Declaring every edge outside the box closed turns the free and wired
measures on `Λ_n` into probability measures `φ⁰_n` and `φ¹_n` on the configuration space of
`ℤ^d`. This space is compact, so both sequences have weakly convergent subsequences
(Prokhorov). `freeInfiniteVolume` and `wiredInfiniteVolume` are chosen subsequential limits; this
file does not claim that the whole sequence converges. Convergence of the whole sequence on
increasing cylinder events is proved for `q = 2` in `MonotoneWeakLimit` (wired) and
`FreeWeakLimit` (free).

## ii. Key results

- `wiredFkPMF` : the wired random-cluster measure on a finite graph.
- `freeFiniteMeasure`, `wiredFiniteMeasure` : the free and wired box measures on `ℤ^d`.
- `freeInfiniteVolume`, `wiredInfiniteVolume` : chosen weak subsequential limits, with
  `freeInfiniteVolume_isLimit` and `wiredInfiniteVolume_isLimit`.

## iii. Table of contents

- A. The wired random-cluster measure on a finite graph
- B. Boxes of `ℤ^d`
- C. Box measures on the configuration space of `ℤ^d`
- D. Infinite-volume measures

## iv. References

- G. R. Grimmett, *The Random-Cluster Model*, Springer, 2006.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (bdry : V → Prop) [DecidablePred bdry]

/-!
## A. The wired random-cluster measure on a finite graph
-/

/-- The unnormalized wired random-cluster weight `edgeProduct G p ω · q ^ k¹(ω)`, where `k¹` counts
clusters after wiring all boundary vertices together. -/
noncomputable def wiredFkWeight (p q : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  edgeProduct G p ω * q ^ numClustersWired G bdry ω

lemma wiredFkWeight_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : 0 < wiredFkWeight G bdry p q ω :=
  mul_pos (edgeProduct_pos G hp hp1 ω) (pow_pos hq _)

lemma wiredFkWeight_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : 0 ≤ wiredFkWeight G bdry p q ω :=
  (wiredFkWeight_pos G bdry hp hp1 hq ω).le

/-- The wired partition function: the sum of `wiredFkWeight` over all configurations. -/
noncomputable def wiredFkZ (p q : ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), wiredFkWeight G bdry p q ω

lemma wiredFkZ_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < wiredFkZ G bdry p q :=
  Finset.sum_pos (fun ω _ => wiredFkWeight_pos G bdry hp hp1 hq ω) Finset.univ_nonempty

lemma wiredFkZ_ne_zero {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    wiredFkZ G bdry p q ≠ 0 :=
  (wiredFkZ_pos G bdry hp hp1 hq).ne'

/-- The wired random-cluster probability of a configuration, `wiredFkWeight / wiredFkZ`. -/
noncomputable def wiredFkProb (p q : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  wiredFkWeight G bdry p q ω / wiredFkZ G bdry p q

lemma wiredFkProb_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : 0 ≤ wiredFkProb G bdry p q ω :=
  div_nonneg (wiredFkWeight_nonneg G bdry hp hp1 hq ω) (wiredFkZ_pos G bdry hp hp1 hq).le

lemma wiredFkProb_sum_eq_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ ω : ConfigSpace (Sym2 V), wiredFkProb G bdry p q ω = 1 := by
  unfold wiredFkProb
  rw [← Finset.sum_div]
  exact div_self (wiredFkZ_ne_zero G bdry hp hp1 hq)

/-- The wired random-cluster measure on a finite graph, as a probability mass function. -/
noncomputable def wiredFkPMF {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    PMF (ConfigSpace (Sym2 V)) :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (wiredFkProb G bdry p q ω)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg fun ω _ => wiredFkProb_nonneg G bdry hp hp1 hq ω,
      wiredFkProb_sum_eq_one G bdry hp hp1 hq]
    simp

/-!
## B. Boxes of `ℤ^d`
-/

/-- The vertices of the box `Λ_n = [-n, n]^d ⊆ ℤ^d`, as a subtype. -/
abbrev boxVerts (d n : ℕ) : Type := {x : Site d // x ∈ box d n}

/-- The box `Λ_n` is finite. -/
noncomputable instance instFintypeBoxVerts (d n : ℕ) : Fintype (boxVerts d n) :=
  (box_finite d n).fintype

/-- Decidable equality on box vertices, inherited from `ℤ^d`. -/
instance instDecidableEqBoxVerts (d n : ℕ) : DecidableEq (boxVerts d n) :=
  Subtype.instDecidableEq

/-- The nearest-neighbour graph on the box `Λ_n`, induced from the hypercubic lattice. -/
def boxGraph (d n : ℕ) : SimpleGraph (boxVerts d n) :=
  SimpleGraph.comap Subtype.val (hypercubicLattice d)

/-- Adjacency in the box graph is decidable (classically). -/
noncomputable instance instDecidableRelBoxGraph (d n : ℕ) :
    DecidableRel (boxGraph d n).Adj :=
  Classical.decRel _

/-- The vertex boundary of the box: sites of `Λ_n` that are not in `Λ_(n-1)`. -/
def boxBoundary (d n : ℕ) (x : boxVerts d n) : Prop := (x : Site d) ∈ vertexBoundary d n

/-- Membership in the box boundary is decidable (classically). -/
noncomputable instance instDecidablePredBoxBoundary (d n : ℕ) :
    DecidablePred (boxBoundary d n) :=
  fun _ => Classical.dec _

/-!
## C. Box measures on the configuration space of `ℤ^d`
-/

/-- The inclusion of edges of the box into edges of `ℤ^d`. -/
def edgeIncl (d n : ℕ) : Sym2 (boxVerts d n) → Sym2 (Site d) :=
  Sym2.map (Subtype.val : boxVerts d n → Site d)

lemma edgeIncl_injective (d n : ℕ) : Function.Injective (edgeIncl d n) :=
  Sym2.map.injective Subtype.val_injective

/-- Extend a configuration on the box to `ℤ^d` by declaring every edge outside the box closed. -/
noncomputable def extendEdge (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    ConfigSpace (Sym2 (Site d)) :=
  fun e => if h : e ∈ Set.range (edgeIncl d n) then ω h.choose else false

lemma measurable_extendEdge (d n : ℕ) : Measurable (extendEdge d n) :=
  Measurable.of_discrete

/-- The free random-cluster measure `φ⁰_n` on the box `Λ_n`, pushed to the configuration space of
`ℤ^d` by `extendEdge`. -/
noncomputable def freeFiniteMeasure (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  ⟨((fkPMF (boxGraph d n) hp hp1 hq).toMeasure).map (extendEdge d n),
    inferInstance⟩

/-- The wired random-cluster measure `φ¹_n` on the box `Λ_n` (boundary vertices wired), pushed to
the configuration space of `ℤ^d` by `extendEdge`. -/
noncomputable def wiredFiniteMeasure (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  ⟨((wiredFkPMF (boxGraph d n) (boxBoundary d n) hp hp1 hq).toMeasure).map (extendEdge d n),
    inferInstance⟩

/-!
## D. Infinite-volume measures
-/

/-- A free infinite-volume random-cluster measure on `ℤ^d`: a weak limit of a subsequence of
`freeFiniteMeasure d n`, chosen by Prokhorov compactness. -/
noncomputable def freeInfiniteVolume (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  (CompactSpace.tendsto_subseq (fun n => freeFiniteMeasure d n hp hp1 hq)).choose

/-- `freeInfiniteVolume` is the weak limit of `freeFiniteMeasure` along some strictly increasing
sequence of box sizes. -/
lemma freeInfiniteVolume_isLimit (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
        (freeInfiniteVolume d hp hp1 hq) := by
  obtain ⟨φ, hφ, htends⟩ :=
    (CompactSpace.tendsto_subseq (fun n => freeFiniteMeasure d n hp hp1 hq)).choose_spec
  exact ⟨φ, hφ, htends⟩

/-- A wired infinite-volume random-cluster measure on `ℤ^d`: a weak limit of a subsequence of
`wiredFiniteMeasure d n`, chosen by Prokhorov compactness. -/
noncomputable def wiredInfiniteVolume (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  (CompactSpace.tendsto_subseq (fun n => wiredFiniteMeasure d n hp hp1 hq)).choose

/-- `wiredInfiniteVolume` is the weak limit of `wiredFiniteMeasure` along some strictly increasing
sequence of box sizes. -/
lemma wiredInfiniteVolume_isLimit (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
        (wiredInfiniteVolume d hp hp1 hq) := by
  obtain ⟨φ, hφ, htends⟩ :=
    (CompactSpace.tendsto_subseq (fun n => wiredFiniteMeasure d n hp hp1 hq)).choose_spec
  exact ⟨φ, hφ, htends⟩

end FK

end StatMech
