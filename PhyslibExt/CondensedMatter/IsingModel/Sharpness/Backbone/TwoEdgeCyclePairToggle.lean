/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeExhaustiveProgram

/-!
# The exhaustive program removes the odd-cycle obstruction

On the path-plus-triangle domain of `TwoEdgeCycleObstruction`, the exhaustive two-edge program
has a copy toggle for the current `superposition`: toggling the copy of the suffix edge
exchanges the full-run and residual-vacuum pair event with the active-segment and lifted-residual
pair event.

## i. Overview

For the exhaustive program, each of the four run events on a split of `superposition` depends only
on the parity pattern of the split (`completeEvent_congr_bits`, `activeSegmentFiber_congr_bits`),
and the relevant patterns are: two units on the path for the full run, the suffix unit for the
lifted residual run, and no odd edge for the residual vacuum. Toggling `suffixCopy` changes only
the parity of the suffix edge, so it maps each pattern on one side to the corresponding pattern on
the other (`profile_toggle_suffix_bits_iff`, `profile_compl_bits_iff`). This gives the pair-event
toggle `exhaustive_cycle_pair_toggle`, in contrast with the failure for the non-exhaustive program
(`no_residualVacuum_suffix_covariance`).

Headline fidelity: `exhaustive_cycle_pair_toggle` and `exhaustive_cycle_pair_toggle_exists` are
proved, conditional on the hypotheses `hfirst` (the scan admits the head edge first for the
two-unit flux) and `hpath` (the canonical segments of the head and suffix edges form a path). Both
depend on the canonical orientation of the edges chosen by `Sym2.out` and on the scan order, and
are not decided here. The results concern this single domain and current and do not give the
chain rule (P2) in general.

## ii. Key results

- `BackboneTwoEdgeCyclePairToggle.suffixCopy` : the labeled copy of the suffix edge
- `BackboneTwoEdgeCyclePairToggle.complete_pair_bits_eq_twoUnit` : a complete two-edge run has the
  parity pattern of the two-unit flux
- `BackboneTwoEdgeCyclePairToggle.exhaustive_cycle_pair_toggle` : the pair-event toggle by
  `suffixCopy` (conditional on `hfirst`, `hpath`)
- `BackboneTwoEdgeCyclePairToggle.exhaustive_cycle_pair_toggle_exists` : a toggling set of copies
  exists (conditional on `hfirst`, `hpath`)

## iii. Table of contents

- A. Events depend only on parity patterns
- B. Parity patterns of profiles and toggles
- C. The residual graph and the suffix unit
- D. Recognizing the run events from parity patterns
- E. The pair toggle

## iv. References

None beyond those in the imported modules.
-/
@[expose] public section

open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

namespace StatMech.Sharpness

noncomputable section

namespace BackboneTwoEdgeCyclePairToggle

open BackboneConcreteBondProgram
open BackboneConcreteSelector
open BackboneDeterminedCutSwitching
open BackboneLabeledSwitching
open BackbonePartialP2Reindex
open BackboneP2CoordinateReindex
open BackboneTwoEdgeBondProgram
open BackboneTwoEdgeBondToggle
open BackboneTwoEdgeCycleObstruction
open FluxEdgeCopy

/-- Adjacency is decided classically in this file. -/
noncomputable local instance pairToggleDecidableAdj
    (G : SimpleGraph (Fin 6)) : DecidableRel G.Adj := Classical.decRel _

/-- The labeled copy of the suffix edge in `superposition`. -/
def suffixCopy : Copy domain.graph superposition :=
  ⟨suffixEdge, ⟨0, by simp⟩⟩

/-! ## A. Events depend only on parity patterns -/
lemma completeEvent_congr_bits
    (P : BondwiseSegmentProgram (Fin 6))
    (d : shb_ExplorationDomain (Fin 6))
    (word : List (shb_ExplorationSegment (Fin 6)))
    (p q : d.graph.edgeFinset → Nat)
    (hbits : fluxBitConfig d.graph P.bit p =
      fluxBitConfig d.graph P.bit q) :
    P.CompleteEvent d word p ↔ P.CompleteEvent d word q := by
  unfold BondwiseSegmentProgram.CompleteEvent
    BondwiseSegmentProgram.TerminalEvent BondwiseSuffixEvent
  rw [hbits]

lemma activeSegmentFiber_congr_bits
    (d : shb_ExplorationDomain (Fin 6))
    (e : d.graph.edgeFinset)
    (he : canonicalEdgeSegment d.graph e ∈ d.active)
    (p q : d.graph.edgeFinset → Nat)
    (hbits : fluxBitConfig d.graph oddBit p =
      fluxBitConfig d.graph oddBit q) :
    shb_ActiveSegmentFiber d (canonicalEdgeSegment d.graph e) he p ↔
      shb_ActiveSegmentFiber d (canonicalEdgeSegment d.graph e) he q := by
  have hsources :
      sources d.graph (ofEdgeFun d.graph p) =
        sources d.graph (ofEdgeFun d.graph q) := by
    rw [← sources_boolCurrent_oddBit d.graph p,
      ← sources_boolCurrent_oddBit d.graph q, hbits]
  have hsets :
      shb_backboneSet d.graph (ofEdgeFun d.graph p)
          (canonicalEdgeSegment d.graph e).1
          (canonicalEdgeSegment d.graph e).2.1 =
        shb_backboneSet d.graph (ofEdgeFun d.graph q)
          (canonicalEdgeSegment d.graph e).1
          (canonicalEdgeSegment d.graph e).2.1 := by
    ext path
    simp only [shb_mem_backboneSet]
    unfold shb_IsBackboneOf
    constructor
    · intro hp g hg
      have hgG : g ∈ d.graph.edgeFinset := by
        exact SimpleGraph.mem_edgeFinset.mpr
          (path.1.edges_subset_edgeSet hg)
      have hb := congrFun hbits g
      simp only [fluxBitConfig, dite_eq_left hgG] at hb
      have hpq : Odd (p ⟨g, hgG⟩) ↔ Odd (q ⟨g, hgG⟩) := by
        rw [← oddBit_eq_true_iff, ← oddBit_eq_true_iff, hb]
      simpa [ofEdgeFun, hgG] using hpq.mp (by
        simpa [ofEdgeFun, hgG] using hp g hg)
    · intro hq g hg
      have hgG : g ∈ d.graph.edgeFinset := by
        exact SimpleGraph.mem_edgeFinset.mpr
          (path.1.edges_subset_edgeSet hg)
      have hb := congrFun hbits g
      simp only [fluxBitConfig, dite_eq_left hgG] at hb
      have hpq : Odd (p ⟨g, hgG⟩) ↔ Odd (q ⟨g, hgG⟩) := by
        rw [← oddBit_eq_true_iff, ← oddBit_eq_true_iff, hb]
      simpa [ofEdgeFun, hgG] using hpq.mpr (by
        simpa [ofEdgeFun, hgG] using hq g hg)
  have hselect :
      shb_backboneSelectSupport d.graph (ofEdgeFun d.graph p)
          (canonicalEdgeSegment d.graph e).1
          (canonicalEdgeSegment d.graph e).2.1 =
        shb_backboneSelectSupport d.graph (ofEdgeFun d.graph q)
          (canonicalEdgeSegment d.graph e).1
          (canonicalEdgeSegment d.graph e).2.1 := by
    unfold shb_backboneSelectSupport
    rw [hsets]
  unfold shb_ActiveSegmentFiber
  rw [hsources, hselect]

/-- A current completing the exhaustive two-edge run has the parity pattern of the two-unit flux on
the path. -/
theorem complete_pair_bits_eq_twoUnit
    (p : domain.graph.edgeFinset → Nat)
    (hcomplete :
      (BackboneTwoEdgeExhaustiveProgram.program (V := Fin 6)).CompleteEvent
        domain
        [canonicalEdgeSegment domain.graph headEdge,
          canonicalEdgeSegment domain.graph suffixEdge] p) :
    fluxBitConfig domain.graph oddBit p =
      fluxBitConfig domain.graph oddBit
        (twoUnitFlux domain.graph headEdge suffixEdge) := by
  have hbase :=
    BackboneTwoEdgeExhaustiveProgram.complete_implies_base domain _ p hcomplete
  obtain ⟨e, f, he, hf, hfirst, hsecond, hneVal, _, _, _, _⟩ :=
    program_complete_pair_data domain p
      (canonicalEdgeSegment domain.graph headEdge)
      (canonicalEdgeSegment domain.graph suffixEdge) hbase
  have he' : e = headEdge :=
    canonicalEdgeSegment_injective domain.graph he
  have hf' : f = suffixEdge :=
    canonicalEdgeSegment_injective domain.graph hf
  subst e
  subst f
  have hhead : fluxBitConfig domain.graph oddBit p headEdge.1 = true :=
    BackboneTwoEdgeBondProgram.scan.firstAdmissible_isAdmissible
      (fun _ b => fluxBitConfig domain.graph oddBit p b)
      ⟨domain, []⟩ headEdge.1 hfirst
  have hsuffix : fluxBitConfig domain.graph oddBit p suffixEdge.1 = true :=
    BackboneTwoEdgeBondProgram.scan.firstAdmissible_isAdmissible
      (fun _ b => fluxBitConfig domain.graph oddBit p b)
      ⟨domain, [headEdge.1]⟩ suffixEdge.1 hsecond
  have hnone :=
    BackboneTwoEdgeExhaustiveProgram.noFurtherOdd_of_complete_canonical_pair
      domain headEdge suffixEdge p hcomplete
  funext b
  by_cases hb : b ∈ domain.graph.edgeFinset
  · rcases edge_cases ⟨b, hb⟩ with hh | hs | hc₀ | hc₁ | hc₂
    · have hb' := congrArg Subtype.val hh
      change b = headEdge.1 at hb'
      subst b
      exact hhead.trans (by
        unfold fluxBitConfig
        rw [dite_eq_left hb, hh]
        simp only [twoUnitFlux, unitFlux]
        simp only [ite_true]
        rw [ite_eq_right (fun h => hneVal (congrArg Subtype.val h))]
        decide)
    · have hb' := congrArg Subtype.val hs
      change b = suffixEdge.1 at hb'
      subst b
      exact hsuffix.trans (by
        unfold fluxBitConfig
        rw [dite_eq_left hb, hs]
        simp only [twoUnitFlux, unitFlux]
        rw [ite_eq_right (fun h => hneVal (congrArg Subtype.val h).symm)]
        simp only [ite_true]
        decide)
    · have hz := hnone cycleEdge₀.1 cycleEdge₀.2
          (fun h => cycleEdge₀_ne_headEdge (Subtype.ext h))
          (fun h => cycleEdge₀_ne_suffixEdge (Subtype.ext h))
      have hb' := congrArg Subtype.val hc₀
      change b = cycleEdge₀.1 at hb'
      subst b
      simpa [fluxBitConfig, cycleEdge₀.2, twoUnitFlux, unitFlux, cycleEdge₀, headEdge,
        suffixEdge, oddBit] using hz
    · have hz := hnone cycleEdge₁.1 cycleEdge₁.2
          (fun h => cycleEdge₁_ne_headEdge (Subtype.ext h))
          (fun h => cycleEdge₁_ne_suffixEdge (Subtype.ext h))
      have hb' := congrArg Subtype.val hc₁
      change b = cycleEdge₁.1 at hb'
      subst b
      simpa [fluxBitConfig, cycleEdge₁.2, twoUnitFlux, unitFlux, cycleEdge₁, headEdge,
        suffixEdge, oddBit] using hz
    · have hz := hnone cycleEdge₂.1 cycleEdge₂.2
          (fun h => cycleEdge₂_ne_headEdge (Subtype.ext h))
          (fun h => cycleEdge₂_ne_suffixEdge (Subtype.ext h))
      have hb' := congrArg Subtype.val hc₂
      change b = cycleEdge₂.1 at hb'
      subst b
      simpa [fluxBitConfig, cycleEdge₂.2, twoUnitFlux, unitFlux, cycleEdge₂, headEdge,
        suffixEdge, oddBit] using hz
  · unfold fluxBitConfig
    rw [dite_eq_right hb, dite_eq_right hb]

/-! ## B. Parity patterns of profiles and toggles -/
lemma fluxBitConfig_oddBit_eq_iff
    (p q : domain.graph.edgeFinset → Nat) :
    fluxBitConfig domain.graph oddBit p =
        fluxBitConfig domain.graph oddBit q ↔
      ∀ e, Odd (p e) ↔ Odd (q e) := by
  constructor
  · intro h e
    have hb := congrFun h e.1
    unfold fluxBitConfig at hb
    rw [dite_eq_left e.2, dite_eq_left e.2] at hb
    rw [← oddBit_eq_true_iff, ← oddBit_eq_true_iff, hb]
  · intro h
    funext b
    by_cases hb : b ∈ domain.graph.edgeFinset
    · unfold fluxBitConfig
      rw [dite_eq_left hb, dite_eq_left hb]
      apply Bool.eq_iff_iff.mpr
      rw [oddBit_eq_true_iff, oddBit_eq_true_iff]
      exact h ⟨b, hb⟩
    · unfold fluxBitConfig
      rw [dite_eq_right hb, dite_eq_right hb]

lemma fluxBitConfig_oddBit_eq_iff_on
    {G : SimpleGraph (Fin 6)} [DecidableRel G.Adj]
    (p q : G.edgeFinset → Nat) :
    fluxBitConfig G oddBit p = fluxBitConfig G oddBit q ↔
      ∀ e, Odd (p e) ↔ Odd (q e) := by
  constructor
  · intro h e
    have hb := congrFun h e.1
    unfold fluxBitConfig at hb
    rw [dite_eq_left e.2, dite_eq_left e.2] at hb
    rw [← oddBit_eq_true_iff, ← oddBit_eq_true_iff, hb]
  · intro h
    funext b
    by_cases hb : b ∈ G.edgeFinset
    · unfold fluxBitConfig
      rw [dite_eq_left hb, dite_eq_left hb]
      apply Bool.eq_iff_iff.mpr
      rw [oddBit_eq_true_iff, oddBit_eq_true_iff]
      exact h ⟨b, hb⟩
    · unfold fluxBitConfig
      rw [dite_eq_right hb, dite_eq_right hb]

lemma filter_symmDiff_edge
    (S U : Finset (Copy domain.graph superposition))
    (g : domain.graph.edgeFinset) :
    (S ∆ U).filter (fun i : Copy domain.graph superposition => i.1 = g) =
      S.filter (fun i : Copy domain.graph superposition => i.1 = g) ∆
        U.filter (fun i : Copy domain.graph superposition => i.1 = g) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_symmDiff]
  tauto

lemma profile_toggle_suffix_odd_iff
    (T : Finset (Copy domain.graph superposition))
    (g : domain.graph.edgeFinset) :
    Odd (profileFlux domain.graph superposition (T ∆ {suffixCopy}) g) ↔
      if g = suffixEdge then
        ¬ Odd (profileFlux domain.graph superposition T g)
      else Odd (profileFlux domain.graph superposition T g) := by
  unfold profileFlux
  by_cases hgs : g = suffixEdge
  · subst g
    rw [ite_eq_left rfl, filter_symmDiff_edge]
    convert odd_card_symmDiff_singleton_iff_not
      (T.filter (fun i : Copy domain.graph superposition =>
        i.1 = suffixEdge)) suffixCopy using 1
    simp [Finset.filter_singleton, suffixCopy]
  · rw [ite_eq_right hgs]
    rw [filter_symmDiff_edge]
    have hset :
        T.filter (fun i : Copy domain.graph superposition => i.1 = g) ∆
            ({suffixCopy} : Finset (Copy domain.graph superposition)).filter
              (fun i => i.1 = g) =
          T.filter (fun i : Copy domain.graph superposition => i.1 = g) := by
      ext i
      simp only [Finset.mem_symmDiff, Finset.mem_filter,
        Finset.mem_singleton]
      constructor
      · intro hi
        rcases hi with hi | hi
        · exact hi.1
        · rcases hi.1 with ⟨his, hedge⟩
          subst i
          exact (hgs hedge.symm).elim
      · intro hi
        exact Or.inl ⟨hi, by
          rintro ⟨his, hedge⟩
          subst i
          exact hgs hedge.symm⟩
    rw [hset]

lemma profile_compl_odd_iff
    (T : Finset (Copy domain.graph superposition))
    (g : domain.graph.edgeFinset) :
    Odd (profileFlux domain.graph superposition (univ \ T) g) ↔
      if g = headEdge ∨ g = suffixEdge then
        ¬ Odd (profileFlux domain.graph superposition T g)
      else Odd (profileFlux domain.graph superposition T g) := by
  rw [profileFlux_compl]
  have hle := profileFlux_le domain.graph superposition T g
  rw [Nat.odd_sub hle]
  rcases edge_cases g with rfl | rfl | rfl | rfl | rfl
  · simp only [superposition_head, true_or, ite_true]
    have hone : Odd (1 : Nat) := by decide
    constructor
    · intro h
      exact Nat.not_odd_iff_even.mpr (h.mp hone)
    · intro hn
      exact ⟨fun _ => Nat.not_odd_iff_even.mp hn, fun _ => hone⟩
  · simp only [superposition_suffix, or_true, ite_true]
    have hone : Odd (1 : Nat) := by decide
    constructor
    · intro h
      exact Nat.not_odd_iff_even.mpr (h.mp hone)
    · intro hn
      exact ⟨fun _ => Nat.not_odd_iff_even.mp hn, fun _ => hone⟩
  all_goals
    simp only [superposition_cycle₀, superposition_cycle₁,
      superposition_cycle₂, headEdge_ne_cycleEdge₀,
      suffixEdge_ne_cycleEdge₀, headEdge_ne_cycleEdge₁,
      suffixEdge_ne_cycleEdge₁, headEdge_ne_cycleEdge₂,
      suffixEdge_ne_cycleEdge₂, false_or, ite_false]
    have htwo : ¬ Odd (2 : Nat) := by decide
    constructor
    · intro h
      have hn : ¬ Even (profileFlux domain.graph superposition T _) :=
        fun he => htwo (h.mpr he)
      exact Nat.not_even_iff_odd.mp hn
    · intro ho
      constructor
      · exact fun h => (htwo h).elim
      · exact fun he =>
          ((Nat.not_even_iff_odd.mpr ho) he).elim

lemma profile_toggle_suffix_bits_iff
    (T : Finset (Copy domain.graph superposition)) :
    fluxBitConfig domain.graph oddBit
          (profileFlux domain.graph superposition (T ∆ {suffixCopy})) =
        fluxBitConfig domain.graph oddBit
          (unitFlux domain.graph headEdge) ↔
      fluxBitConfig domain.graph oddBit
          (profileFlux domain.graph superposition T) =
        fluxBitConfig domain.graph oddBit
          (twoUnitFlux domain.graph headEdge suffixEdge) := by
  rw [fluxBitConfig_oddBit_eq_iff, fluxBitConfig_oddBit_eq_iff]
  constructor
  · intro h g
    have ht := profile_toggle_suffix_odd_iff T g
    have hg := h g
    rcases edge_cases g with rfl | rfl | rfl | rfl | rfl <;>
      (try simp only [ite_eq_left, ite_eq_right, headEdge_ne_suffixEdge,
        cycleEdge₀_ne_suffixEdge, cycleEdge₁_ne_suffixEdge,
        cycleEdge₂_ne_suffixEdge] at ht) <;>
      simp only [domain_graph, headEdge_ne_suffixEdge, ↓reduceIte, unitFlux, odd_one, iff_true,
          twoUnitFlux, add_zero, Nat.not_odd_iff_even, suffixEdge_ne_headEdge, Nat.not_odd_zero,
          iff_false, zero_add, cycleEdge₀_ne_suffixEdge, cycleEdge₀_ne_headEdge,
          cycleEdge₁_ne_suffixEdge, cycleEdge₁_ne_headEdge, cycleEdge₂_ne_suffixEdge,
          cycleEdge₂_ne_headEdge] at ht hg ⊢ <;>
        (try simp only [← Nat.not_odd_iff_even] at ht hg ⊢) <;> tauto
  · intro h g
    have ht := profile_toggle_suffix_odd_iff T g
    have hg := h g
    rcases edge_cases g with rfl | rfl | rfl | rfl | rfl <;>
      (try simp only [ite_eq_left, ite_eq_right, headEdge_ne_suffixEdge,
        cycleEdge₀_ne_suffixEdge, cycleEdge₁_ne_suffixEdge,
        cycleEdge₂_ne_suffixEdge] at ht) <;>
      simp only [domain_graph, headEdge_ne_suffixEdge, ↓reduceIte, twoUnitFlux, unitFlux, add_zero,
          odd_one, iff_true, Nat.not_odd_iff_even, suffixEdge_ne_headEdge, zero_add,
          Nat.not_odd_zero, iff_false, cycleEdge₀_ne_suffixEdge, cycleEdge₀_ne_headEdge,
          cycleEdge₁_ne_suffixEdge, cycleEdge₁_ne_headEdge, cycleEdge₂_ne_suffixEdge,
          cycleEdge₂_ne_headEdge] at ht hg ⊢ <;>
        (try simp only [← Nat.not_odd_iff_even] at ht hg ⊢) <;> tauto

lemma profile_compl_bits_iff
    (T : Finset (Copy domain.graph superposition)) :
    fluxBitConfig domain.graph oddBit
          (profileFlux domain.graph superposition (univ \ T)) =
        fluxBitConfig domain.graph oddBit
          (unitFlux domain.graph suffixEdge) ↔
      fluxBitConfig domain.graph oddBit
          (profileFlux domain.graph superposition T) =
        fluxBitConfig domain.graph oddBit
          (unitFlux domain.graph headEdge) := by
  rw [fluxBitConfig_oddBit_eq_iff, fluxBitConfig_oddBit_eq_iff]
  constructor
  · intro h g
    have hc := profile_compl_odd_iff T g
    have hg := h g
    rcases edge_cases g with rfl | rfl | rfl | rfl | rfl <;>
      (try simp only [ite_eq_left, ite_eq_right, true_or, or_true, false_or,
        headEdge_ne_suffixEdge, cycleEdge₀_ne_headEdge,
        cycleEdge₀_ne_suffixEdge, cycleEdge₁_ne_headEdge,
        cycleEdge₁_ne_suffixEdge, cycleEdge₂_ne_headEdge,
        cycleEdge₂_ne_suffixEdge] at hc) <;>
      simp only [domain_graph, Nat.not_odd_iff_even, unitFlux, headEdge_ne_suffixEdge, ↓reduceIte,
          Nat.not_odd_zero, iff_false, odd_one, iff_true, suffixEdge_ne_headEdge,
          cycleEdge₀_ne_headEdge, cycleEdge₀_ne_suffixEdge, or_self, cycleEdge₁_ne_headEdge,
          cycleEdge₁_ne_suffixEdge, cycleEdge₂_ne_headEdge, cycleEdge₂_ne_suffixEdge] at hc hg ⊢ <;>
        (try simp only [← Nat.not_odd_iff_even] at hc hg ⊢) <;> tauto
  · intro h g
    have hc := profile_compl_odd_iff T g
    have hg := h g
    rcases edge_cases g with rfl | rfl | rfl | rfl | rfl <;>
      (try simp only [ite_eq_left, ite_eq_right, true_or, or_true, false_or,
        headEdge_ne_suffixEdge, cycleEdge₀_ne_headEdge,
        cycleEdge₀_ne_suffixEdge, cycleEdge₁_ne_headEdge,
        cycleEdge₁_ne_suffixEdge, cycleEdge₂_ne_headEdge,
        cycleEdge₂_ne_suffixEdge] at hc) <;>
      simp only [domain_graph, Nat.not_odd_iff_even, unitFlux, ↓reduceIte, odd_one, iff_true,
          headEdge_ne_suffixEdge, Nat.not_odd_zero, iff_false, suffixEdge_ne_headEdge,
          cycleEdge₀_ne_headEdge, cycleEdge₀_ne_suffixEdge, or_self, cycleEdge₁_ne_headEdge,
          cycleEdge₁_ne_suffixEdge, cycleEdge₂_ne_headEdge, cycleEdge₂_ne_suffixEdge] at hc hg ⊢ <;>
        (try simp only [← Nat.not_odd_iff_even] at hc hg ⊢) <;> tauto

lemma profile_compl_zero_bits_iff
    (T : Finset (Copy domain.graph superposition)) :
    fluxBitConfig domain.graph oddBit
          (profileFlux domain.graph superposition (univ \ T)) =
        fluxBitConfig domain.graph oddBit 0 ↔
      fluxBitConfig domain.graph oddBit
          (profileFlux domain.graph superposition T) =
        fluxBitConfig domain.graph oddBit
          (twoUnitFlux domain.graph headEdge suffixEdge) := by
  rw [fluxBitConfig_oddBit_eq_iff, fluxBitConfig_oddBit_eq_iff]
  constructor
  · intro h g
    have hc := profile_compl_odd_iff T g
    have hg := h g
    rcases edge_cases g with rfl | rfl | rfl | rfl | rfl <;>
      (try simp only [ite_eq_left, ite_eq_right, true_or, or_true, false_or,
        headEdge_ne_suffixEdge, cycleEdge₀_ne_headEdge,
        cycleEdge₀_ne_suffixEdge, cycleEdge₁_ne_headEdge,
        cycleEdge₁_ne_suffixEdge, cycleEdge₂_ne_headEdge,
        cycleEdge₂_ne_suffixEdge] at hc) <;>
      simp only [domain_graph, Nat.not_odd_iff_even, Pi.zero_apply, Nat.not_odd_zero, iff_false,
          twoUnitFlux, unitFlux, ↓reduceIte, headEdge_ne_suffixEdge, add_zero, odd_one, iff_true,
          suffixEdge_ne_headEdge, zero_add, cycleEdge₀_ne_headEdge, cycleEdge₀_ne_suffixEdge,
          or_self, cycleEdge₁_ne_headEdge, cycleEdge₁_ne_suffixEdge, cycleEdge₂_ne_headEdge,
          cycleEdge₂_ne_suffixEdge] at hc hg ⊢ <;>
        (try simp only [← Nat.not_odd_iff_even] at hc hg ⊢) <;> tauto
  · intro h g
    have hc := profile_compl_odd_iff T g
    have hg := h g
    rcases edge_cases g with rfl | rfl | rfl | rfl | rfl <;>
      (try simp only [ite_eq_left, ite_eq_right, true_or, or_true, false_or,
        headEdge_ne_suffixEdge, cycleEdge₀_ne_headEdge,
        cycleEdge₀_ne_suffixEdge, cycleEdge₁_ne_headEdge,
        cycleEdge₁_ne_suffixEdge, cycleEdge₂_ne_headEdge,
        cycleEdge₂_ne_suffixEdge] at hc) <;>
      simp only [domain_graph, Nat.not_odd_iff_even, twoUnitFlux, unitFlux, ↓reduceIte,
          headEdge_ne_suffixEdge, add_zero, odd_one, iff_true, Pi.zero_apply, Nat.not_odd_zero,
          iff_false, suffixEdge_ne_headEdge, zero_add, cycleEdge₀_ne_headEdge,
          cycleEdge₀_ne_suffixEdge, or_self, cycleEdge₁_ne_headEdge, cycleEdge₁_ne_suffixEdge,
          cycleEdge₂_ne_headEdge, cycleEdge₂_ne_suffixEdge] at hc hg ⊢ <;>
        (try simp only [← Nat.not_odd_iff_even] at hc hg ⊢) <;> tauto

/-! ## C. The residual graph and the suffix unit -/
lemma restrictResidual_bits_eq
    (p q : domain.graph.edgeFinset → Nat)
    (hbits : fluxBitConfig domain.graph oddBit p =
      fluxBitConfig domain.graph oddBit q) :
    fluxBitConfig residualGraph oddBit (restrictResidual p) =
      fluxBitConfig residualGraph oddBit (restrictResidual q) := by
  have hpar := (fluxBitConfig_oddBit_eq_iff p q).mp hbits
  funext b
  unfold fluxBitConfig
  split
  · rename_i hp
    apply Bool.eq_iff_iff.mpr
    rw [oddBit_eq_true_iff, oddBit_eq_true_iff]
    let er : residualGraph.edgeFinset := ⟨b, hp⟩
    have hambSet : b ∈ domain.graph.edgeSet :=
      SimpleGraph.edgeSet_mono residualLe
        (SimpleGraph.mem_edgeFinset.mp hp)
    let ea : domain.graph.edgeFinset :=
      ⟨b, SimpleGraph.mem_edgeFinset.mpr hambSet⟩
    simpa [restrictResidual, er, ea] using hpar ea
  · rfl

lemma restrictResidual_unitSuffix :
    restrictResidual (unitFlux domain.graph suffixEdge) =
      unitFlux residualGraph residualSuffix := by
  apply extendFlux_injective residualLe
  rw [extendFlux_restrictResidual (unitFlux domain.graph suffixEdge)]
  · exact (extendFlux_residual_unitFlux domain headEdge suffixEdge
      headEdge_ne_suffixEdge).symm
  · change (if headEdge = suffixEdge then 1 else 0) = 0
    rw [ite_eq_right headEdge_ne_suffixEdge]

lemma profile_head_eq_zero_of_unitSuffix_bits
    (T : Finset (Copy domain.graph superposition))
    (hbits : fluxBitConfig domain.graph oddBit
        (profileFlux domain.graph superposition T) =
      fluxBitConfig domain.graph oddBit
        (unitFlux domain.graph suffixEdge)) :
    profileFlux domain.graph superposition T headEdge = 0 := by
  have hpar := (fluxBitConfig_oddBit_eq_iff _ _).mp hbits headEdge
  have hnot : ¬ Odd (profileFlux domain.graph superposition T headEdge) := by
    intro hodd
    have := hpar.mp hodd
    change Odd (if headEdge = suffixEdge then 1 else 0) at this
    rw [ite_eq_right headEdge_ne_suffixEdge] at this
    exact (by decide : ¬ Odd (0 : Nat)) this
  have hle : profileFlux domain.graph superposition T headEdge ≤ 1 := by
    simpa only [superposition_head] using
      (profileFlux_le domain.graph superposition T headEdge)
  have hne : profileFlux domain.graph superposition T headEdge ≠ 1 := by
    intro h
    apply hnot
    rw [h]
    decide
  omega

lemma exhaustive_suffix_of_unitSuffix_bits
    (T : Finset (Copy domain.graph superposition))
    (hbits : fluxBitConfig domain.graph oddBit
        (profileFlux domain.graph superposition T) =
      fluxBitConfig domain.graph oddBit
        (unitFlux domain.graph suffixEdge)) :
    ((BackboneTwoEdgeExhaustiveProgram.program
        (V := Fin 6)).liftedResidualRunSpec domain
      (canonicalEdgeSegment domain.graph headEdge)
      [canonicalEdgeSegment domain.graph suffixEdge]).Event domain.graph
      (profileFlux domain.graph superposition T) := by
  let p := profileFlux domain.graph superposition T
  have hp0 : p headEdge = 0 :=
    profile_head_eq_zero_of_unitSuffix_bits T hbits
  rw [BondwiseSegmentProgram.liftedResidualRunSpec_event]
  unfold BondwiseSegmentProgram.LiftedRunEvent
  refine ⟨restrictResidual p, extendFlux_restrictResidual p hp0, ?_⟩
  refine ((BackboneTwoEdgeExhaustiveProgram.program
    (V := Fin 6)).runSpec_event _ _ _).mpr ?_
  have hresBits :
      fluxBitConfig residualGraph oddBit (restrictResidual p) =
        fluxBitConfig residualGraph oddBit
          (unitFlux residualGraph residualSuffix) := by
    rw [← restrictResidual_unitSuffix]
    exact restrictResidual_bits_eq p
      (unitFlux domain.graph suffixEdge) hbits
  apply (completeEvent_congr_bits
    (BackboneTwoEdgeExhaustiveProgram.program (V := Fin 6))
    (shb_BackboneExplorationDomain.advance domain
      (canonicalEdgeSegment domain.graph headEdge))
    [canonicalEdgeSegment domain.graph suffixEdge]
    (restrictResidual p) (unitFlux residualGraph residualSuffix) hresBits).mpr
  apply (BackboneTwoEdgeExhaustiveProgram.program_complete_singleton_iff_base
    (shb_BackboneExplorationDomain.advance domain
      (canonicalEdgeSegment domain.graph headEdge))
    (canonicalEdgeSegment domain.graph suffixEdge)
    (unitFlux residualGraph residualSuffix)).mpr
  have hX := program_complete_canonical_singleton_unitFlux
      (shb_BackboneExplorationDomain.advance domain
        (canonicalEdgeSegment domain.graph headEdge)) residualSuffix
      (residualEdge_active_advance domain headEdge suffixEdge
        headEdge_ne_suffixEdge suffix_active)
  have hcan : canonicalEdgeSegment (shb_BackboneExplorationDomain.advance domain
        (canonicalEdgeSegment domain.graph headEdge)).graph residualSuffix =
      canonicalEdgeSegment domain.graph suffixEdge :=
    residualEdge_canonical_eq domain headEdge suffixEdge headEdge_ne_suffixEdge
  rw [hcan] at hX
  exact hX

/-! ## D. Recognizing the run events from parity patterns -/
lemma base_singleton_complete_bits_eq_unit
    (d : shb_ExplorationDomain (Fin 6))
    (e : d.graph.edgeFinset) (p : d.graph.edgeFinset → Nat)
    (hcomplete :
      (BackboneTwoEdgeBondProgram.program (V := Fin 6)).CompleteEvent d
        [canonicalEdgeSegment d.graph e] p) :
    fluxBitConfig d.graph oddBit p =
      fluxBitConfig d.graph oddBit (unitFlux d.graph e) := by
  obtain ⟨f, hf, hfirst, _, _, hfinished⟩ :=
    program_complete_singleton_data d p (canonicalEdgeSegment d.graph e)
      hcomplete
  have hfe : f = e := canonicalEdgeSegment_injective d.graph hf
  subst f
  have hselected : fluxBitConfig d.graph oddBit p e.1 = true :=
    BackboneTwoEdgeBondProgram.scan.firstAdmissible_isAdmissible
      (fun _ b => fluxBitConfig d.graph oddBit p b) ⟨d, []⟩ e.1 hfirst
  have hnone :
      (d.graph.edgeFinset.erase e.1).1.toList.find?
          (fun b => fluxBitConfig d.graph oddBit p b) = none := by
    simpa [BackboneTwoEdgeBondProgram.scan,
      shb_DynamicEdgeExploration.firstAdmissible] using hfinished
  funext b
  by_cases hb : b ∈ d.graph.edgeFinset
  · let g : d.graph.edgeFinset := ⟨b, hb⟩
    by_cases hge : g = e
    · have hb' := congrArg Subtype.val hge
      change b = e.1 at hb'
      subst b
      exact hselected.trans (by
        unfold fluxBitConfig
        rw [dite_eq_left hb]
        have heq : (⟨e.1, _⟩ : d.graph.edgeFinset) = e :=
          Subtype.ext rfl
        rw [heq]
        simp [unitFlux, oddBit])
    · have hmemList : b ∈ (d.graph.edgeFinset.erase e.1).1.toList := by
        apply Finset.mem_toList.mpr
        apply Finset.mem_erase.mpr
        exact ⟨fun h => hge (Subtype.ext h), hb⟩
      have hpFalse : fluxBitConfig d.graph oddBit p b = false := by
        have := (List.find?_eq_none.mp hnone) b hmemList
        simpa using this
      have hright :
          fluxBitConfig d.graph oddBit (unitFlux d.graph e) b = false := by
        unfold fluxBitConfig
        rw [dite_eq_left hb]
        unfold unitFlux
        rw [ite_eq_right (fun h =>
          hge (Subtype.ext (congrArg Subtype.val h)))]
        rfl
      exact hpFalse.trans hright.symm
  · unfold fluxBitConfig
    rw [dite_eq_right hb, dite_eq_right hb]

lemma extendFlux_bits_eq
    (r q : residualGraph.edgeFinset → Nat)
    (hbits : fluxBitConfig residualGraph oddBit r =
      fluxBitConfig residualGraph oddBit q) :
    fluxBitConfig domain.graph oddBit (extendFlux residualLe r) =
      fluxBitConfig domain.graph oddBit (extendFlux residualLe q) := by
  have hpar := (fluxBitConfig_oddBit_eq_iff_on r q).mp hbits
  funext b
  unfold fluxBitConfig
  split
  · rename_i hb
    unfold extendFlux
    split
    · rename_i hr
      apply Bool.eq_iff_iff.mpr
      rw [oddBit_eq_true_iff, oddBit_eq_true_iff]
      exact hpar ⟨b, hr⟩
    · rfl
  · rfl

lemma unitSuffix_bits_of_exhaustive_suffix
    (T : Finset (Copy domain.graph superposition))
    (hsuffix :
      ((BackboneTwoEdgeExhaustiveProgram.program
          (V := Fin 6)).liftedResidualRunSpec domain
        (canonicalEdgeSegment domain.graph headEdge)
        [canonicalEdgeSegment domain.graph suffixEdge]).Event domain.graph
        (profileFlux domain.graph superposition T)) :
    fluxBitConfig domain.graph oddBit
        (profileFlux domain.graph superposition T) =
      fluxBitConfig domain.graph oddBit
        (unitFlux domain.graph suffixEdge) := by
  rw [BondwiseSegmentProgram.liftedResidualRunSpec_event] at hsuffix
  obtain ⟨r, hrext, hrun⟩ := hsuffix
  replace hrun := ((BackboneTwoEdgeExhaustiveProgram.program
    (V := Fin 6)).runSpec_event _ _ _).mp hrun
  have hbase :
      (BackboneTwoEdgeBondProgram.program (V := Fin 6)).CompleteEvent
        (shb_BackboneExplorationDomain.advance domain
          (canonicalEdgeSegment domain.graph headEdge))
        [canonicalEdgeSegment domain.graph suffixEdge] r :=
    (BackboneTwoEdgeExhaustiveProgram.program_complete_singleton_iff_base
      (shb_BackboneExplorationDomain.advance domain
        (canonicalEdgeSegment domain.graph headEdge))
      (canonicalEdgeSegment domain.graph suffixEdge) r).mp hrun
  have hresBits :
      fluxBitConfig residualGraph oddBit r =
        fluxBitConfig residualGraph oddBit
          (unitFlux residualGraph residualSuffix) := by
    have hbase' :
        (BackboneTwoEdgeBondProgram.program (V := Fin 6)).CompleteEvent
          (shb_BackboneExplorationDomain.advance domain
            (canonicalEdgeSegment domain.graph headEdge))
          [canonicalEdgeSegment residualGraph residualSuffix] r := by
      have hcan : canonicalEdgeSegment residualGraph residualSuffix =
          canonicalEdgeSegment domain.graph suffixEdge :=
        residualEdge_canonical_eq domain headEdge suffixEdge headEdge_ne_suffixEdge
      rw [hcan]
      exact hbase
    exact base_singleton_complete_bits_eq_unit
      (shb_BackboneExplorationDomain.advance domain
        (canonicalEdgeSegment domain.graph headEdge)) residualSuffix r hbase'
  have hambBits := extendFlux_bits_eq r
    (unitFlux residualGraph residualSuffix) hresBits
  have hextUnit :
      extendFlux residualLe (unitFlux residualGraph residualSuffix) =
        unitFlux domain.graph suffixEdge := by
    simpa only [residualSuffix] using
      (extendFlux_residual_unitFlux domain headEdge suffixEdge
        headEdge_ne_suffixEdge)
  rw [hrext, hextUnit] at hambBits
  exact hambBits

lemma activeHead_of_unitHead_bits
    (T : Finset (Copy domain.graph superposition))
    (hbits : fluxBitConfig domain.graph oddBit
        (profileFlux domain.graph superposition T) =
      fluxBitConfig domain.graph oddBit
        (unitFlux domain.graph headEdge)) :
    (activeSegmentRunSpec domain
      (canonicalEdgeSegment domain.graph headEdge) head_active).Event
      domain.graph (profileFlux domain.graph superposition T) := by
  rw [activeSegmentRunSpec_event]
  exact (activeSegmentFiber_congr_bits domain headEdge head_active
    (profileFlux domain.graph superposition T)
    (unitFlux domain.graph headEdge) hbits).mpr
      (activeSegmentFiber_unitFlux domain headEdge head_active)

lemma exhaustive_full_of_twoUnit_bits
    (T : Finset (Copy domain.graph superposition))
    (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible
      (fun _ b => fluxBitConfig domain.graph oddBit
        (twoUnitFlux domain.graph headEdge suffixEdge) b)
      ⟨domain, []⟩ = some headEdge.1)
    (hpath : FormsTwoEdgePath
      (canonicalEdgeSegment domain.graph headEdge)
      (canonicalEdgeSegment domain.graph suffixEdge))
    (hbits : fluxBitConfig domain.graph oddBit
        (profileFlux domain.graph superposition T) =
      fluxBitConfig domain.graph oddBit
        (twoUnitFlux domain.graph headEdge suffixEdge)) :
    ((BackboneTwoEdgeExhaustiveProgram.program (V := Fin 6)).runSpec domain
      [canonicalEdgeSegment domain.graph headEdge,
        canonicalEdgeSegment domain.graph suffixEdge]).Event domain.graph
      (profileFlux domain.graph superposition T) := by
  rw [(BackboneTwoEdgeExhaustiveProgram.program
    (V := Fin 6)).runSpec_event]
  apply (completeEvent_congr_bits
    (BackboneTwoEdgeExhaustiveProgram.program (V := Fin 6)) domain
    [canonicalEdgeSegment domain.graph headEdge,
      canonicalEdgeSegment domain.graph suffixEdge]
    (profileFlux domain.graph superposition T)
    (twoUnitFlux domain.graph headEdge suffixEdge) hbits).mpr
  exact BackboneTwoEdgeExhaustiveProgram.program_complete_canonical_pair_twoUnitFlux
    domain headEdge suffixEdge headEdge_ne_suffixEdge hfirst head_active
      suffix_active hpath

lemma profile_head_eq_zero_of_zero_bits
    (T : Finset (Copy domain.graph superposition))
    (hbits : fluxBitConfig domain.graph oddBit
        (profileFlux domain.graph superposition T) =
      fluxBitConfig domain.graph oddBit 0) :
    profileFlux domain.graph superposition T headEdge = 0 := by
  have hpar := (fluxBitConfig_oddBit_eq_iff _ _).mp hbits headEdge
  have hnot : ¬ Odd (profileFlux domain.graph superposition T headEdge) := by
    intro hodd
    have := hpar.mp hodd
    exact (by decide : ¬ Odd (0 : Nat)) this
  have hle : profileFlux domain.graph superposition T headEdge ≤ 1 := by
    simpa only [superposition_head] using
      (profileFlux_le domain.graph superposition T headEdge)
  have hne : profileFlux domain.graph superposition T headEdge ≠ 1 := by
    intro h
    apply hnot
    rw [h]
    decide
  omega

lemma residualVacuum_of_zero_bits
    (T : Finset (Copy domain.graph superposition))
    (hbits : fluxBitConfig domain.graph oddBit
        (profileFlux domain.graph superposition T) =
      fluxBitConfig domain.graph oddBit 0) :
    (residualVacuumRunSpec domain
      (canonicalEdgeSegment domain.graph headEdge)).Event domain.graph
      (profileFlux domain.graph superposition T) := by
  let p := profileFlux domain.graph superposition T
  have hp0 : p headEdge = 0 := profile_head_eq_zero_of_zero_bits T hbits
  rw [residualVacuumRunSpec_event]
  unfold liftedResidualVacuum
  refine ⟨restrictResidual p, extendFlux_restrictResidual p hp0, ?_⟩
  have hresBits :
      fluxBitConfig residualGraph oddBit (restrictResidual p) =
        fluxBitConfig residualGraph oddBit 0 := by
    have h := restrictResidual_bits_eq p 0 hbits
    exact h
  calc
    sources residualGraph (ofEdgeFun residualGraph (restrictResidual p)) =
        sources residualGraph
          (boolCurrent (fluxBitConfig residualGraph oddBit
            (restrictResidual p))) :=
      (sources_boolCurrent_oddBit residualGraph (restrictResidual p)).symm
    _ = sources residualGraph
          (boolCurrent (fluxBitConfig residualGraph oddBit 0)) := by
      rw [hresBits]
    _ = sources residualGraph (ofEdgeFun residualGraph 0) :=
      sources_boolCurrent_oddBit residualGraph 0
    _ = ∅ := sources_ofEdgeFun_zero residualGraph

/-! ## E. The pair toggle -/

/-- On the path-plus-triangle domain, toggling `suffixCopy` maps the full-run and residual-vacuum
pair event to the active-segment and lifted-residual pair event, given `hfirst` and `hpath`. -/
theorem exhaustive_cycle_pair_toggle
    (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible
      (fun _ b => fluxBitConfig domain.graph oddBit
        (twoUnitFlux domain.graph headEdge suffixEdge) b)
      ⟨domain, []⟩ = some headEdge.1)
    (hpath : FormsTwoEdgePath
      (canonicalEdgeSegment domain.graph headEdge)
      (canonicalEdgeSegment domain.graph suffixEdge))
    (T : Finset (Copy domain.graph superposition)) :
    BondwisePairEvent
        ((BackboneTwoEdgeExhaustiveProgram.program (V := Fin 6)).runSpec
          domain [canonicalEdgeSegment domain.graph headEdge,
            canonicalEdgeSegment domain.graph suffixEdge])
        (residualVacuumRunSpec domain
          (canonicalEdgeSegment domain.graph headEdge))
        domain.graph superposition T ↔
      BondwisePairEvent
        (activeSegmentRunSpec domain
          (canonicalEdgeSegment domain.graph headEdge) head_active)
        ((BackboneTwoEdgeExhaustiveProgram.program
          (V := Fin 6)).liftedResidualRunSpec domain
          (canonicalEdgeSegment domain.graph headEdge)
          [canonicalEdgeSegment domain.graph suffixEdge])
        domain.graph superposition (T ∆ {suffixCopy}) := by
  unfold BondwisePairEvent
  constructor
  · rintro ⟨hfull, _⟩
    have htwo := complete_pair_bits_eq_twoUnit _
      (((BackboneTwoEdgeExhaustiveProgram.program
        (V := Fin 6)).runSpec_event _ _ _).mp hfull)
    have hheadBits := (profile_toggle_suffix_bits_iff T).mpr htwo
    have hsuffixBits := (profile_compl_bits_iff (T ∆ {suffixCopy})).mpr
      hheadBits
    exact ⟨activeHead_of_unitHead_bits (T ∆ {suffixCopy}) hheadBits,
      exhaustive_suffix_of_unitSuffix_bits
        (univ \ (T ∆ {suffixCopy})) hsuffixBits⟩
  · rintro ⟨_, hsuffix⟩
    have hsuffixBits := unitSuffix_bits_of_exhaustive_suffix
      (univ \ (T ∆ {suffixCopy})) hsuffix
    have hheadBits := (profile_compl_bits_iff (T ∆ {suffixCopy})).mp
      hsuffixBits
    have htwo := (profile_toggle_suffix_bits_iff T).mp hheadBits
    have hzero := (profile_compl_zero_bits_iff T).mpr htwo
    exact ⟨exhaustive_full_of_twoUnit_bits T hfirst hpath htwo,
      residualVacuum_of_zero_bits (univ \ T) hzero⟩

/-- A set of copies toggling the pair events exists, given `hfirst` and `hpath`. -/
theorem exhaustive_cycle_pair_toggle_exists
    (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible
      (fun _ b => fluxBitConfig domain.graph oddBit
        (twoUnitFlux domain.graph headEdge suffixEdge) b)
      ⟨domain, []⟩ = some headEdge.1)
    (hpath : FormsTwoEdgePath
      (canonicalEdgeSegment domain.graph headEdge)
      (canonicalEdgeSegment domain.graph suffixEdge)) :
    ∃ path : Finset (Copy domain.graph superposition), ∀ T,
      BondwisePairEvent
          ((BackboneTwoEdgeExhaustiveProgram.program (V := Fin 6)).runSpec
            domain [canonicalEdgeSegment domain.graph headEdge,
              canonicalEdgeSegment domain.graph suffixEdge])
          (residualVacuumRunSpec domain
            (canonicalEdgeSegment domain.graph headEdge))
          domain.graph superposition T ↔
        BondwisePairEvent
          (activeSegmentRunSpec domain
            (canonicalEdgeSegment domain.graph headEdge) head_active)
          ((BackboneTwoEdgeExhaustiveProgram.program
            (V := Fin 6)).liftedResidualRunSpec domain
            (canonicalEdgeSegment domain.graph headEdge)
            [canonicalEdgeSegment domain.graph suffixEdge])
          domain.graph superposition (T ∆ path) := by
  exact ⟨{suffixCopy}, exhaustive_cycle_pair_toggle hfirst hpath⟩

end BackboneTwoEdgeCyclePairToggle

end

end StatMech.Sharpness
