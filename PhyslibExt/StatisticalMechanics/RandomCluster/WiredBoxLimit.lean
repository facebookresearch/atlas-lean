/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.BoxCrossGraph
public import PhyslibExt.StatisticalMechanics.RandomCluster.BoxTailLimit
/-!
# One-step comparison of wired boundary-connection probabilities

At `q = 2`, the wired measure on `Λ_(n+1)` conditioned on all outer annulus edges closed gives
`{0 ↔ ∂Λ_n}` at most its probability under the wired measure on `Λ_n`.

## i. Overview

`crossExt d n ω` extends a configuration of `Λ_n` to `Λ_(n+1)` with all annulus edges closed.
Conditioning the wired measure of `Λ_(n+1)` on this annulus configuration and enlarging the
wiring to contain the clique on the inner boundary gives the wired measure of `Λ_n`
(`condBcProb_crossExt_eq_wiredFkProb_add` in `BoxCrossGraph`). Since enlarging the wiring
increases increasing events, the conditional probability of `{0 ↔ ∂Λ_n}` is at most
`φ¹_n(0 ↔ ∂Λ_n)`.

## ii. Key results

- `wiredFiniteMeasure_succ_real_boxBdryConnEvent` : `φ¹_(n+1)(0 ↔ ∂Λ_n)` as a finite sum.
- `condBcProb_add_sum_eq_smallerBox` : the conditional measure with an annulus wiring equals
  the wired measure on `Λ_n`, on any event.
- `condWiredSucc_le_smallerBox` : the one-step comparison.

## iii. Table of contents

- A. Extension and restriction across `Λ_n ⊆ Λ_(n+1)`
- B. Boundary-connection events
- C. Finite-sum formulas
- D. The conditional comparison

## iv. References

- G. R. Grimmett, *The Random-Cluster Model*, Springer, 2006.
-/

@[expose] public section

open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}

/-!
## A. Extension and restriction across `Λ_n ⊆ Λ_(n+1)`
-/

lemma extendEdge_crossExt (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    extendEdge d (n + 1) (crossExt d n ω) = extendEdge d n ω := by
  funext e
  change (if h : e ∈ Set.range (edgeIncl d (n + 1)) then crossExt d n ω h.choose else false)
      = (if h : e ∈ Set.range (edgeIncl d n) then ω h.choose else false)
  by_cases h1 : e ∈ Set.range (edgeIncl d n)
  · obtain ⟨eb, rfl⟩ := h1
    have hmemn : edgeIncl d n eb ∈ Set.range (edgeIncl d n) := ⟨eb, rfl⟩
    have h2 : edgeIncl d n eb ∈ Set.range (edgeIncl d (n + 1)) := by
      refine ⟨innerEdge d n eb, ?_⟩; rw [edgeIncl_innerEdge]
    rw [dite_eq_left h2, dite_eq_left hmemn]
    have hce : h2.choose = innerEdge d n eb := by
      apply edgeIncl_injective d (n + 1); rw [h2.choose_spec, edgeIncl_innerEdge]
    rw [hce, crossExt_innerEdge]
    have heb : hmemn.choose = eb := edgeIncl_injective d n hmemn.choose_spec
    rw [heb]
  · rw [dite_eq_right h1]
    by_cases h2 : e ∈ Set.range (edgeIncl d (n + 1))
    · rw [dite_eq_left h2]
      apply crossExt_eq_false_of_not_range
      intro hin
      obtain ⟨eb, heb⟩ := hin
      exact h1 ⟨eb, by rw [← edgeIncl_innerEdge, heb, h2.choose_spec]⟩
    · rw [dite_eq_right h2]

lemma boxRestrict_extendEdge_succ (d n : ℕ) (ρ : ConfigSpace (Sym2 (boxVerts d (n + 1)))) :
    boxRestrict d n (extendEdge d (n + 1) ρ) = innerRestrict d n ρ := by
  funext eb
  unfold boxRestrict innerRestrict
  rw [← edgeIncl_innerEdge d n eb]
  have : boxRestrict d (n + 1) (extendEdge d (n + 1) ρ) (innerEdge d n eb)
      = ρ (innerEdge d n eb) := by
    rw [boxRestrict_extendEdge]
  exact this

/-!
## B. Boundary-connection events
-/

/-- The event on `Λ_(n+1)` that the origin is connected to `∂Λ_n` by open edges of `Λ_n`. -/
def innerBdryFinEvent (d n : ℕ) : Set (ConfigSpace (Sym2 (boxVerts d (n + 1)))) :=
  innerRestrict d n ⁻¹'
    {ω : ConfigSpace (Sym2 (boxVerts d n)) |
      ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)}

lemma isIncreasing_innerBdryFinEvent (d n : ℕ) : IsIncreasing (innerBdryFinEvent d n) := by
  intro a b hab ha
  simp only [innerBdryFinEvent, Set.mem_preimage, Set.mem_ofPred_eq] at ha ⊢
  obtain ⟨y, hy, hconn⟩ := ha
  refine ⟨y, hy, ?_⟩
  have hmono : innerRestrict d n a ≤ innerRestrict d n b := fun e => hab (innerEdge d n e)
  exact hconn.mono (openSub_mono _ hmono)

lemma extendEdge_succ_preimage_boxBdryConnEvent (d n : ℕ) :
    extendEdge d (n + 1) ⁻¹' (boxBdryConnEvent d n) = innerBdryFinEvent d n := by
  ext ρ
  simp only [boxBdryConnEvent, innerBdryFinEvent, Set.mem_preimage, Set.mem_ofPred_eq,
    boxRestrict_extendEdge_succ]

lemma crossExt_preimage_innerBdryFinEvent (d n : ℕ) :
    crossExt d n ⁻¹' (innerBdryFinEvent d n)
      = {ω : ConfigSpace (Sym2 (boxVerts d n)) |
          ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)} := by
  ext ω
  simp only [innerBdryFinEvent, Set.mem_preimage, Set.mem_ofPred_eq, innerRestrict_crossExt]

/-!
## C. Finite-sum formulas
-/

lemma wiredFiniteMeasure_succ_real_boxBdryConnEvent (d n : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d (n + 1) hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)
      = ∑ ρ : ConfigSpace (Sym2 (boxVerts d (n + 1))),
          (innerBdryFinEvent d n).indicator (fun _ => (1 : ℝ)) ρ
            * wiredFkProb (boxGraph d (n + 1)) (boxBoundary d (n + 1)) p 2 ρ := by
  have hA : MeasurableSet (boxBdryConnEvent d n) := measurableSet_boxBdryConnEvent d n
  have hw : (wiredFiniteMeasure d (n + 1) hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _).real
        (boxBdryConnEvent d n)
      = ((wiredFkPMF (boxGraph d (n + 1)) (boxBoundary d (n + 1)) hp hp1
            (by norm_num : (0 : ℝ) < 2)).toMeasure
          (extendEdge d (n + 1) ⁻¹' (boxBdryConnEvent d n))).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d (n + 1)) hA]
  rw [hw, extendEdge_succ_preimage_boxBdryConnEvent,
    wiredFkPMF_toMeasure_toReal d (n + 1) hp hp1 (by norm_num : (0 : ℝ) < 2)]

lemma wiredFiniteMeasure_real_boxBdryConnEvent_sum (d n : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          {ω : ConfigSpace (Sym2 (boxVerts d n)) |
            ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)}.indicator
              (fun _ => (1 : ℝ)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
  have hA : MeasurableSet (boxBdryConnEvent d n) := measurableSet_boxBdryConnEvent d n
  have hw : (wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _).real
        (boxBdryConnEvent d n)
      = ((wiredFkPMF (boxGraph d n) (boxBoundary d n) hp hp1
            (by norm_num : (0 : ℝ) < 2)).toMeasure
          (extendEdge d n ⁻¹' (boxBdryConnEvent d n))).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d n) hA]
  rw [hw, extendEdge_preimage_boxBdryConnEvent,
    wiredFkPMF_toMeasure_toReal d n hp hp1 (by norm_num : (0 : ℝ) < 2)]

/-!
## D. The conditional comparison
-/

/-- With all annulus edges closed and a wiring made of the inner-boundary clique and an annulus
wiring `D`, the conditional measure on `Λ_(n+1)` equals the wired measure on `Λ_n`, on any event
pulled back by `crossExt`. -/
lemma condBcProb_add_sum_eq_smallerBox (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq0 : 0 < q)
    {D : SimpleGraph (boxVerts d (n + 1))} [DecidableRel D.Adj] (hD : IsAnnulusWiring d n D)
    (B : Set (ConfigSpace (Sym2 (boxVerts d (n + 1))))) :
    (∑ ρ, B.indicator (fun _ => (1 : ℝ)) ρ *
        condBcProb (boxGraph d (n + 1))
          (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n) ⊔ D) p q
          (innerEdgeFinset d n) (fun _ => false) ρ)
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (crossExt d n ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  classical
  have hsupp : ∀ ρ ∉ condFibre (innerEdgeFinset d n) (fun _ => false),
      B.indicator (fun _ => (1 : ℝ)) ρ *
        condBcProb (boxGraph d (n + 1))
          (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n) ⊔ D) p q
          (innerEdgeFinset d n) (fun _ => false) ρ = 0 := by
    intro ρ hρ
    rw [mem_condFibre] at hρ
    unfold condBcProb
    rw [ite_eq_right hρ, mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ (condFibre (innerEdgeFinset d n) (fun _ => false)))
    (fun ρ _ hρ => hsupp ρ hρ)]
  rw [condFibre_eq_image_crossExt]
  rw [Finset.sum_image (fun a _ b _ h => by
    have := congrArg (innerRestrict d n) h
    rwa [innerRestrict_crossExt, innerRestrict_crossExt] at this)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [condBcProb_crossExt_eq_wiredFkProb_add d n hp hp1 hq0 ω hD]
  have hind : B.indicator (fun _ => (1 : ℝ)) (crossExt d n ω)
      = (crossExt d n ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω := by
    by_cases hω : crossExt d n ω ∈ B
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_preimage.mpr hω)]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun h => hω (Set.mem_preimage.mp h))]
  rw [hind]

/-- At `q = 2`, the wired measure on `Λ_(n+1)` conditioned on all annulus edges closed gives `{0 ↔
∂Λ_n}` at most `φ¹_n(0 ↔ ∂Λ_n)`. -/
lemma condWiredSucc_le_smallerBox (d n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (∑ ρ, (innerBdryFinEvent d n).indicator (fun _ => (1 : ℝ)) ρ *
        condBcProb (boxGraph d (n + 1))
          (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n + 1))) p 2
          (innerEdgeFinset d n) (fun _ => false) ρ)
      ≤ (wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
  classical
  have hq : (1 : ℝ) ≤ 2 := by norm_num
  have hq0 : (0 : ℝ) < 2 := by norm_num
  have hinc : IsIncreasing (innerBdryFinEvent d n) := isIncreasing_innerBdryFinEvent d n
  have hD : IsAnnulusWiring d n (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n + 1))) :=
    isAnnulusWiring_boxBoundary_succ d n
  have hdom := wiredFkProb_inner_dominated_cond (boxGraph d (n + 1)) (boxBoundary d (n + 1))
    (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n) ⊔
      StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n + 1)))
    le_sup_right hp hp1 hq (innerEdgeFinset d n) (fun _ => false) hinc
  refine hdom.trans ?_
  rw [condBcProb_add_sum_eq_smallerBox d n hp hp1 hq0 hD (innerBdryFinEvent d n),
    crossExt_preimage_innerBdryFinEvent,
    wiredFiniteMeasure_real_boxBdryConnEvent_sum d n hp hp1]

end FK

end StatMech
