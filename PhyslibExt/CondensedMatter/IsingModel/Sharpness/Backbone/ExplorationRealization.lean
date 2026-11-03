/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ExplorationSelector
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.P2CutResummation
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.P3Domain

/-!
# The random-current exploration and its realization hypotheses

The random-current backbone exploration: states are subgraphs with a set of active path
segments, a step deletes the edges of a segment, and the step amplitude is the support-ordered
backbone weight of the segment in the current subgraph. Under two resummation hypotheses this is
an exploration kernel, and a normalized fiber mass realizes its weight.

## i. Overview

An ambient segment is a path of the complete graph on `V`. A backbone exploration domain is a
subgraph `G` together with a finite set of active segments supported on `G`; it is preordered by
inclusion of graphs with equal active sets. Exploring a segment deletes its edges and keeps the
active segments disjoint from it. The step amplitude is `shb_segmentRho`, the value of
`shb_rhoSupport` on the segment in the current graph (zero for inactive segments).

The amplitude is antitone in the domain exactly when the P3 resummation inequality holds for
every pair of domains (`LocalDomainResummation`); under that hypothesis the amplitudes form an
exploration kernel. Given any fiber mass satisfying the cut resummation identities
`shb_LocalSelectorFiberCutResummation`, the fiber mass normalized by the sourceless partition
function equals the kernel weight, so it is an exploration `ρ`-realization and satisfies P2 and P3
(`ExplorationSelector`).

Headline fidelity:
- `shb_BackboneExplorationDomain.kernel` and `shb_randomCurrent_rho_eq_weight`,
  `shb_randomCurrentExplorationRealization` are conditional on `LocalDomainResummation β J`
  (P3 for the support-ordered backbone weight, for every pair of nested domains and every active
  segment; not proved for any graph here).
- `shb_randomCurrent_rho_eq_weight` is also conditional on
  `shb_LocalSelectorFiberCutResummation β J fiberMass`. These identities hold exactly for the
  generated fiber mass, a product of segment numerators and partition-function ratios
  (`shb_LocalSelectorFiberCutResummation_iff_eq_generated`, `ExplorationCutAdmissible`), so the
  realization does not by itself relate to the backbone weight of a concatenated path in a fixed
  graph; that connection is the backbone chain rule (P2), which is not proved here.
- `shb_segment_unrestricted_cut_factor` and `shb_segmentRho_eq_num_div` are unconditional.

## ii. Key results

- `shb_AmbientSegment` : paths of the complete graph, used as exploration steps
- `shb_BackboneExplorationDomain` : subgraphs with active segments
- `shb_BackboneExplorationDomain.kernel` : the exploration kernel (conditional on
  `LocalDomainResummation`)
- `shb_randomCurrent_rho_eq_weight` : the normalized fiber mass is the kernel weight
  (conditional on `LocalDomainResummation` and `shb_LocalSelectorFiberCutResummation`)
- `shb_randomCurrentExplorationRealization` : the resulting exploration `ρ`-realization

## iii. Table of contents

- A. Ambient segments
- B. The graph exploration
- C. Backbone exploration domains
- D. The exploration kernel
- E. Segment cuts and segment numerators
- F. The normalized fiber mass realization

## iv. References

- H. Duminil-Copin, V. Tassion, "A new proof of the sharpness of the phase transition for
  Bernoulli percolation and the Ising model", Comm. Math. Phys. 343 (2016) 725–745

-/

@[expose] public section

open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- Classical decidability of adjacency, used throughout this file. -/
local instance (H : SimpleGraph V) : DecidableRel H.Adj :=
  Classical.decRel _

/-! ## A. Ambient segments -/

/-- An ambient segment: a path `x → y` of the complete graph on `V`, with its endpoints. -/
abbrev shb_AmbientSegment (V : Type*) [Fintype V] [DecidableEq V] :=
  Σ x : V, Σ y : V, (⊤ : SimpleGraph V).Path x y

/-- Ambient segments form a finite type. -/
noncomputable instance : Fintype (shb_AmbientSegment V) := inferInstance

/-- Classical decidable equality on ambient segments. -/
noncomputable instance : DecidableEq (shb_AmbientSegment V) := Classical.decEq _

/-- The set of edges of a segment. -/
def shb_AmbientSegment.edgeSet (s : shb_AmbientSegment V) : Set (Sym2 V) :=
  {e | e ∈ s.2.2.1.edges}

/-- A segment is supported on `H` if all its edges are edges of `H`. -/
def shb_AmbientSegment.Supported (H : SimpleGraph V)
    (s : shb_AmbientSegment V) : Prop :=
  ∀ e ∈ s.2.2.1.edges, e ∈ H.edgeSet

/-- Classical decidability of support. -/
noncomputable instance (H : SimpleGraph V) (s : shb_AmbientSegment V) :
    Decidable (s.Supported H) := Classical.propDecidable _

/-- A segment supported on `H`, as a path of `H`. -/
noncomputable def shb_AmbientSegment.toPath
    (H : SimpleGraph V) (s : shb_AmbientSegment V) (h : s.Supported H) :
    H.Path s.1 s.2.1 :=
  ⟨s.2.2.1.transfer H h, s.2.2.2.transfer h⟩

@[simp] lemma shb_AmbientSegment.toPath_edges
    (H : SimpleGraph V) (s : shb_AmbientSegment V) (h : s.Supported H) :
    (s.toPath H h).1.edges = s.2.2.1.edges := by
  exact Walk.edges_transfer _ _

/-! ## B. The graph exploration -/

/-- Exploring a segment from a graph deletes the segment's edges. -/
def shb_explorationAdvance (H : SimpleGraph V) (s : shb_AmbientSegment V) :
    SimpleGraph V :=
  H.deleteEdges s.edgeSet

lemma shb_explorationAdvance_mono {H K : SimpleGraph V} (hHK : H ≤ K)
    (s : shb_AmbientSegment V) :
    shb_explorationAdvance H s ≤ shb_explorationAdvance K s := by
  exact SimpleGraph.deleteEdges_mono hHK

/-- The exploration on subgraphs that tries all segments in a fixed order and deletes the edges
of the explored segment. -/
noncomputable def shb_randomCurrentExploration :
    shb_DynamicEdgeExploration (SimpleGraph V) (shb_AmbientSegment V) where
  edgeOrder := fun _ => Finset.univ.toList
  edgeOrder_nodup := fun _ => Finset.nodup_toList _
  advance := shb_explorationAdvance

/-- The support-ordered backbone weight of a segment in `H` (zero if the segment is not
supported on `H`). -/
noncomputable def shb_segmentRho
    (β : ℝ) (J : Sym2 V → ℝ) (H : SimpleGraph V)
    (s : shb_AmbientSegment V) : ℝ := by
  letI : DecidableRel H.Adj := Classical.decRel _
  exact if h : s.Supported H then
    shb_rhoSupport H β J s.1 s.2.1 (s.toPath H h)
  else 0

lemma shb_segmentRho_nonneg
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (H : SimpleGraph V) (s : shb_AmbientSegment V) :
    0 ≤ shb_segmentRho β J H s := by
  let : DecidableRel H.Adj := Classical.decRel _
  unfold shb_segmentRho
  split
  · apply div_nonneg
    · exact shb_backboneNumSupport_nonneg H β J hβ hJ _ _ _
    · exact le_of_lt (StatMech.Ising.acr_currentSum_empty_pos H β J)
  · exact le_rfl

/-! ## C. Backbone exploration domains -/

/-- A backbone exploration domain: a subgraph together with a finite set of active segments
supported on it. -/
structure shb_BackboneExplorationDomain (V : Type*) [Fintype V]
    [DecidableEq V] where
  graph : SimpleGraph V
  active : Finset (shb_AmbientSegment V)
  active_supported : ∀ s ∈ active, s.Supported graph

namespace shb_BackboneExplorationDomain

variable (d : shb_BackboneExplorationDomain V)

/-- Domains are ordered by inclusion of graphs with equal active sets. -/
instance : LE (shb_BackboneExplorationDomain V) where
  le d k := d.graph ≤ k.graph ∧ d.active = k.active

/-- The preorder on domains. -/
instance : Preorder (shb_BackboneExplorationDomain V) where
  le_refl d := ⟨le_rfl, rfl⟩
  le_trans d k l hdk hkl := ⟨hdk.1.trans hkl.1, hdk.2.trans hkl.2⟩

/-- Two segments are compatible if they have no common edge. -/
def compatible (s t : shb_AmbientSegment V) : Prop :=
  Disjoint s.edgeSet t.edgeSet

/-- Classical decidability of compatibility. -/
noncomputable instance (s t : shb_AmbientSegment V) :
    Decidable (compatible s t) := Classical.propDecidable _

lemma supported_deleteEdges_of_compatible
    {H : SimpleGraph V} {s t : shb_AmbientSegment V}
    (ht : t.Supported H) (hst : compatible s t) :
    t.Supported (H.deleteEdges s.edgeSet) := by
  intro e he
  rw [SimpleGraph.edgeSet_deleteEdges]
  refine ⟨ht e he, ?_⟩
  intro hes
  exact Set.disjoint_left.1 hst hes he

/-- Exploring a segment: delete its edges and keep the active segments compatible with it. -/
noncomputable def advance (d : shb_BackboneExplorationDomain V)
    (s : shb_AmbientSegment V) : shb_BackboneExplorationDomain V where
  graph := d.graph.deleteEdges s.edgeSet
  active := d.active.filter (compatible s)
  active_supported := by
    intro t ht
    rw [Finset.mem_filter] at ht
    exact supported_deleteEdges_of_compatible (d.active_supported t ht.1) ht.2

lemma advance_mono {d k : shb_BackboneExplorationDomain V} (hdk : d ≤ k)
    (s : shb_AmbientSegment V) : advance d s ≤ advance k s := by
  refine ⟨SimpleGraph.deleteEdges_mono hdk.1, ?_⟩
  simp only [advance, hdk.2]

/-- The exploration on domains: the edge order lists the active segments. -/
noncomputable def exploration :
    shb_DynamicEdgeExploration (shb_BackboneExplorationDomain V)
      (shb_AmbientSegment V) where
  edgeOrder := fun d => d.active.toList
  edgeOrder_nodup := fun d => Finset.nodup_toList d.active
  advance := advance

/-! ## D. The exploration kernel -/

/-- The step amplitude: the backbone weight of an active segment in the current graph, zero for
inactive segments. -/
noncomputable def amplitude (β : ℝ) (J : Sym2 V → ℝ)
    (d : shb_BackboneExplorationDomain V) (s : shb_AmbientSegment V) : ℝ :=
  if s ∈ d.active then shb_segmentRho β J d.graph s else 0

lemma amplitude_nonneg (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (d : shb_BackboneExplorationDomain V) (s : shb_AmbientSegment V) :
    0 ≤ amplitude β J d s := by
  unfold amplitude
  split
  · exact shb_segmentRho_nonneg β J hβ hJ d.graph s
  · exact le_rfl

/-- The P3 resummation inequality `shb_P3DomainResummation` for every pair of nested domains and
every active segment. -/
noncomputable def LocalDomainResummation (β : ℝ) (J : Sym2 V → ℝ) : Prop := by
  classical
  exact ∀ (d k : shb_BackboneExplorationDomain V) (hdk : d ≤ k)
      (s : shb_AmbientSegment V) (hs : s ∈ d.active),
      let hd := d.active_supported s hs
      shb_P3DomainResummation d.graph k.graph hdk.1 β J (s.toPath d.graph hd)

lemma toPath_mapLe
    {H K : SimpleGraph V} (hHK : H ≤ K) (s : shb_AmbientSegment V)
    (hH : s.Supported H) (hK : s.Supported K) :
    shb_pathMapLe hHK (s.toPath H hH) = s.toPath K hK := by
  apply Subtype.ext
  apply Walk.support_injective
  change (Walk.mapLe hHK (s.toPath H hH).1).support =
    (s.toPath K hK).1.support
  rw [Walk.support_mapLe_eq_support]
  exact (Walk.support_transfer _ _).trans (Walk.support_transfer _ _).symm

/-- Under `LocalDomainResummation`, the amplitude is antitone in the domain. -/
lemma amplitude_antitone_of_domainResummation
    (β : ℝ) (J : Sym2 V → ℝ) (hresum : LocalDomainResummation β J)
    {d k : shb_BackboneExplorationDomain V} (hdk : d ≤ k)
    (s : shb_AmbientSegment V) :
    amplitude β J k s ≤ amplitude β J d s := by
  by_cases hs : s ∈ d.active
  · have hsk : s ∈ k.active := by simpa [← hdk.2] using hs
    let : DecidableRel d.graph.Adj := Classical.decRel _
    let : DecidableRel k.graph.Adj := Classical.decRel _
    simp only [amplitude, hs, hsk, ite_true]
    let hd := d.active_supported s hs
    let hk := k.active_supported s hsk
    unfold shb_segmentRho
    rw [dite_eq_left hd, dite_eq_left hk]
    have hp3 := shb_P3_support_of_domainResummation
      d.graph k.graph hdk.1 β J (s.toPath d.graph hd) (hresum d k hdk s hs)
    rw [toPath_mapLe hdk.1 s hd hk] at hp3
    exact hp3
  · have hsk : s ∉ k.active := by simpa [← hdk.2] using hs
    simp [amplitude, hs, hsk]

/-- The exploration kernel of backbone domains, assuming `LocalDomainResummation`. -/
noncomputable def kernel (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (hresum : LocalDomainResummation β J) :
    shb_ExplorationKernel (shb_BackboneExplorationDomain V)
      (shb_AmbientSegment V) where
  exploration := exploration
  amplitude := amplitude β J
  amplitude_nonneg := amplitude_nonneg β J hβ hJ
  amplitude_antitone := amplitude_antitone_of_domainResummation β J hresum
  advance_mono := advance_mono

end shb_BackboneExplorationDomain

/-! ## E. Segment cuts and segment numerators -/

/-- The edges of `H` that lie on the segment `s`. -/
def shb_segmentCut (H : SimpleGraph V) [DecidableRel H.Adj]
    (s : shb_AmbientSegment V)
    (e : H.edgeFinset) : Prop :=
  e.1 ∈ s.edgeSet

/-- Classical decidability of the segment cut. -/
noncomputable instance (H : SimpleGraph V) [DecidableRel H.Adj]
    (s : shb_AmbientSegment V) :
    DecidablePred (shb_segmentCut H s) := Classical.decPred _

/-- The total current weight mass of `H` factors along the edges of a segment. -/
lemma shb_segment_unrestricted_cut_factor
    (H : SimpleGraph V)
    (β : ℝ) (J : Sym2 V → ℝ) (s : shb_AmbientSegment V) :
    shb_fullWeightMass H β J =
      shb_cutLeftMass H β J (shb_segmentCut H s) *
        shb_cutRightMass H β J (shb_segmentCut H s) := by
  exact shb_tsum_weight_cut_factor H β J (shb_segmentCut H s)

/-- Exploration domains: backbone exploration domains. -/
abbrev shb_ExplorationDomain (V : Type*) [Fintype V] [DecidableEq V] :=
  shb_BackboneExplorationDomain V

/-- Exploration steps: ambient segments. -/
abbrev shb_ExplorationSegment (V : Type*) [Fintype V] [DecidableEq V] :=
  shb_AmbientSegment V

/-- The backbone numerator of an active segment in the current graph, zero for inactive segments. -/
noncomputable def shb_segmentNum
    (β : ℝ) (J : Sym2 V → ℝ) (d : shb_ExplorationDomain V)
    (s : shb_ExplorationSegment V) : ℝ := by
  letI : DecidableRel d.graph.Adj := Classical.decRel _
  exact if hs : s ∈ d.active then
    shb_backboneNumSupport d.graph β J s.1 s.2.1
      (s.toPath d.graph (d.active_supported s hs))
  else 0

/-- The amplitude is the segment numerator divided by the sourceless partition function. -/
lemma shb_segmentRho_eq_num_div
    (β : ℝ) (J : Sym2 V → ℝ) (d : shb_ExplorationDomain V)
    (s : shb_ExplorationSegment V) :
    shb_BackboneExplorationDomain.amplitude β J d s =
      shb_segmentNum β J d s / currentSum d.graph β J ∅ := by
  let : DecidableRel d.graph.Adj := Classical.decRel _
  by_cases hs : s ∈ d.active
  · rw [shb_BackboneExplorationDomain.amplitude, ite_eq_left hs,
      shb_segmentNum, dite_eq_left hs]
    unfold shb_segmentRho shb_rhoSupport
    rw [dite_eq_left (d.active_supported s hs)]
  · simp [shb_BackboneExplorationDomain.amplitude, shb_segmentNum, hs]

/-! ## F. The normalized fiber mass realization -/

/-- A fiber mass: a real number for each domain and word of segments. -/
abbrev shb_ExplorationFiberMass (V : Type*) [Fintype V] [DecidableEq V] :=
  shb_ExplorationDomain V → List (shb_ExplorationSegment V) → ℝ

/-- The cut resummation identities for a fiber mass: the empty word has mass `Z_d`, a word
starting with an active segment factors through the segment numerator and the residual domain, and
a word starting with an inactive segment has mass zero. -/
noncomputable def shb_LocalSelectorFiberCutResummation
    (β : ℝ) (J : Sym2 V → ℝ) (fiberMass : shb_ExplorationFiberMass V) : Prop := by
  classical
  exact (∀ d, fiberMass d [] = currentSum d.graph β J ∅) ∧
    (∀ d s ss, s ∈ d.active →
      fiberMass d (s :: ss) *
          currentSum (shb_BackboneExplorationDomain.advance d s).graph β J ∅ =
        shb_segmentNum β J d s *
          fiberMass (shb_BackboneExplorationDomain.advance d s) ss) ∧
    (∀ d s ss, s ∉ d.active → fiberMass d (s :: ss) = 0)

/-- The fiber mass normalized by the sourceless partition function of the domain graph. -/
noncomputable def shb_normalizedExplorationRho
    (β : ℝ) (J : Sym2 V → ℝ) (fiberMass : shb_ExplorationFiberMass V)
    (d : shb_ExplorationDomain V) (word : List (shb_ExplorationSegment V)) : ℝ :=
  fiberMass d word / currentSum d.graph β J ∅

lemma shb_normalizedExplorationRho_nil
    (β : ℝ) (J : Sym2 V → ℝ) (fiberMass : shb_ExplorationFiberMass V)
    (hcut : shb_LocalSelectorFiberCutResummation β J fiberMass)
    (d : shb_ExplorationDomain V) :
    shb_normalizedExplorationRho β J fiberMass d [] = 1 := by
  let : DecidableRel d.graph.Adj := Classical.decRel _
  rw [shb_normalizedExplorationRho, hcut.1 d]
  exact div_self (ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos d.graph β J))

lemma shb_normalizedExplorationRho_cons
    (β : ℝ) (J : Sym2 V → ℝ) (fiberMass : shb_ExplorationFiberMass V)
    (hcut : shb_LocalSelectorFiberCutResummation β J fiberMass)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) :
    shb_normalizedExplorationRho β J fiberMass d (s :: ss) =
      shb_BackboneExplorationDomain.amplitude β J d s *
        shb_normalizedExplorationRho β J fiberMass
          (shb_BackboneExplorationDomain.advance d s) ss := by
  let d' := shb_BackboneExplorationDomain.advance d s
  let : DecidableRel d.graph.Adj := Classical.decRel _
  let : DecidableRel d'.graph.Adj := Classical.decRel _
  by_cases hs : s ∈ d.active
  · have hZd : currentSum d.graph β J ∅ ≠ 0 :=
      ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos d.graph β J)
    have hZd' : currentSum d'.graph β J ∅ ≠ 0 :=
      ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos d'.graph β J)
    rw [shb_normalizedExplorationRho, shb_normalizedExplorationRho,
      shb_segmentRho_eq_num_div]
    field_simp [hZd]
    exact (eq_div_iff hZd').2 (hcut.2.1 d s ss hs)
  · rw [shb_normalizedExplorationRho, hcut.2.2 d s ss hs]
    simp [shb_BackboneExplorationDomain.amplitude, hs]

/-- Under `LocalDomainResummation` and the cut resummation identities, the normalized fiber mass
equals the weight of the backbone exploration kernel. -/
theorem shb_randomCurrent_rho_eq_weight
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (hdom : shb_BackboneExplorationDomain.LocalDomainResummation β J)
    (fiberMass : shb_ExplorationFiberMass V)
    (hcut : shb_LocalSelectorFiberCutResummation β J fiberMass)
    (d : shb_ExplorationDomain V) (word : List (shb_ExplorationSegment V)) :
    shb_normalizedExplorationRho β J fiberMass d word =
      (shb_BackboneExplorationDomain.kernel β J hβ hJ hdom).weight d word := by
  induction word generalizing d with
  | nil =>
      rw [shb_normalizedExplorationRho_nil β J fiberMass hcut]
      rfl
  | cons s ss ih =>
      rw [shb_normalizedExplorationRho_cons β J fiberMass hcut,
        shb_ExplorationKernel.weight_cons, ih]
      rfl

/-- The exploration `ρ`-realization given by the normalized fiber mass, under
`LocalDomainResummation` and the cut resummation identities. -/
noncomputable def shb_randomCurrentExplorationRealization
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (hdom : shb_BackboneExplorationDomain.LocalDomainResummation β J)
    (fiberMass : shb_ExplorationFiberMass V)
    (hcut : shb_LocalSelectorFiberCutResummation β J fiberMass) :
    shb_ExplorationRhoRealization (shb_ExplorationDomain V)
      (shb_ExplorationSegment V) where
  kernel := shb_BackboneExplorationDomain.kernel β J hβ hJ hdom
  rho := shb_normalizedExplorationRho β J fiberMass
  rho_eq_weight := shb_randomCurrent_rho_eq_weight β J hβ hJ hdom fiberMass hcut

end

end StatMech.Sharpness
