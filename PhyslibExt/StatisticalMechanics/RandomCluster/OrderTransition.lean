/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint
public import PhyslibExt.StatisticalMechanics.RandomCluster.IvProperties
public import PhyslibExt.StatisticalMechanics.RandomCluster.DlrSandwich
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.SelfDualValue
/-!
# First-order transitions of the random-cluster model

The free percolation probability `θ⁰(p, q)`, and the definition of a first-order transition at
`(p, q)` as `θ⁰ = 0 < θ¹`: free and wired infinite-volume measures then differ.

## i. Overview

For `q > 4` the planar random-cluster model has a discontinuous phase transition at the
self-dual point `p_sd(q) = √q / (1 + √q)`: the free measure does not percolate while the wired
measure does (Duminil-Copin, Gagnebin, Harel, Manolescu and Tassion). This file defines the
property and proves its elementary consequence, that the free and wired infinite-volume measures
differ. It does **not** prove that the transition is first order for `q > 4`:
`order_transition_q_large` and `order_transition_q_large_selfDual` take `θ⁰(p_sd, q) = 0` and
`θ¹(p_sd, q) > 0` as hypotheses (`hFree`, `hWired`), which together are the definition of
`IsFirstOrderTransition`. The assumption `4 < q` is not used in the proofs.

## ii. Key results

- `fkThetaFree` : the free percolation probability `θ⁰(p, q)`.
- `IsFirstOrderTransition` : `θ⁰(p, q) = 0 < θ¹(p, q)`.
- `freeInfiniteVolume_ne_wiredInfiniteVolume_of_firstOrder` : at a first-order transition the
  free and wired infinite-volume measures differ.
- `order_transition_q_large_selfDual` : the same at the self-dual point on `ℤ²`, given the
  first-order property as hypotheses.

## iii. Table of contents

- A. The free percolation probability
- B. First-order transitions

## iv. References

- H. Duminil-Copin, M. Gagnebin, M. Harel, I. Manolescu and V. Tassion, *Discontinuity of the
  phase transition for the planar random-cluster and Potts models with q > 4*,
  Ann. Sci. ENS 54 (2021).
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation

/-! ## A. The free percolation probability -/

/-- The free percolation probability `θ⁰(p, q)`: the free infinite-volume measure of the event that
the origin lies in an infinite open cluster. -/
noncomputable def fkThetaFree (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : ℝ :=
  ((freeInfiniteVolume d hp hp1 hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (percolationEvent d)

/-- `θ⁰(p, q) ≥ 0`. -/
lemma fkThetaFree_nonneg (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 ≤ fkThetaFree d hp hp1 hq (q := q) :=
  ENNReal.toReal_nonneg

/-- `θ⁰(p, q) ≤ 1`. -/
lemma fkThetaFree_le_one (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    fkThetaFree d hp hp1 hq (q := q) ≤ 1 := by
  unfold fkThetaFree
  rw [Measure.real]
  refine ENNReal.toReal_le_of_le_ofReal (by norm_num) ?_
  rw [ENNReal.ofReal_one]
  exact prob_le_one

/-! ## B. First-order transitions -/

/-- A first-order transition at `(p, q)`: the free measure does not percolate, `θ⁰(p, q) = 0`, while
the wired one does, `θ¹(p, q) > 0`. -/
def IsFirstOrderTransition (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : Prop :=
  fkThetaFree d hp hp1 hq (q := q) = 0 ∧ 0 < fkTheta d hp hp1 hq (q := q)

/-- Introduction rule for `IsFirstOrderTransition`. -/
lemma firstOrderTransition_of_contour (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hFree : fkThetaFree d hp hp1 hq (q := q) = 0)
    (hWired : 0 < fkTheta d hp hp1 hq (q := q)) :
    IsFirstOrderTransition d hp hp1 hq :=
  ⟨hFree, hWired⟩

/-- At a first-order transition, `θ⁰(p, q) ≠ θ¹(p, q)`. -/
lemma fkThetaFree_ne_fkTheta_of_firstOrder (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (h : IsFirstOrderTransition d hp hp1 hq) :
    fkThetaFree d hp hp1 hq (q := q) ≠ fkTheta d hp hp1 hq (q := q) := by
  obtain ⟨hFree, hWired⟩ := h
  rw [hFree]
  exact ne_of_lt hWired

/-- At a first-order transition, the free and wired infinite-volume measures differ. -/
lemma freeInfiniteVolume_ne_wiredInfiniteVolume_of_firstOrder (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (h : IsFirstOrderTransition d hp hp1 hq) :
    freeInfiniteVolume d hp hp1 hq ≠ wiredInfiniteVolume d hp hp1 hq := by
  intro heq
  refine fkThetaFree_ne_fkTheta_of_firstOrder d hp hp1 hq h ?_
  unfold fkThetaFree fkTheta
  rw [heq]

/-- At a point `p ∈ (0, 1)` given as the self-dual point on `ℤ²`, the hypotheses `θ⁰ = 0`
and `θ¹ > 0` give a first-order transition with distinct free and wired measures. The
first-order property for `q > 4` (Duminil-Copin et al., 2021) is assumed, not proved;
`4 < q` is only used to get `q > 0`. -/
lemma order_transition_q_large {q : ℝ} (hq : 4 < q)
    (hpos : 0 < BeffaraDC.selfDualPoint q)
    (hlt : BeffaraDC.selfDualPoint q < 1)
    (hFree : fkThetaFree 2 hpos hlt (by linarith : (0 : ℝ) < q) (q := q) = 0)
    (hWired : 0 < fkTheta 2 hpos hlt (by linarith : (0 : ℝ) < q) (q := q)) :
    IsFirstOrderTransition 2 hpos hlt (by linarith : (0 : ℝ) < q)
      ∧ freeInfiniteVolume 2 hpos hlt (by linarith : (0 : ℝ) < q)
          ≠ wiredInfiniteVolume 2 hpos hlt (by linarith : (0 : ℝ) < q) := by
  have hfo : IsFirstOrderTransition 2 hpos hlt (by linarith : (0 : ℝ) < q) :=
    firstOrderTransition_of_contour 2 hpos hlt _ hFree hWired
  exact ⟨hfo, freeInfiniteVolume_ne_wiredInfiniteVolume_of_firstOrder 2 hpos hlt _ hfo⟩

/-- `order_transition_q_large` at the self-dual point `p_sd(q) = √q / (1 + √q)` of `ℤ²`, with
`θ⁰(p_sd, q) = 0` and `θ¹(p_sd, q) > 0` assumed. -/
lemma order_transition_q_large_selfDual {q : ℝ} (hq : 4 < q)
    (hFree : fkThetaFree 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).2
        (by linarith : (0 : ℝ) < q) (q := q) = 0)
    (hWired : 0 < fkTheta 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).2
        (by linarith : (0 : ℝ) < q) (q := q)) :
    IsFirstOrderTransition 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).2
        (by linarith : (0 : ℝ) < q)
      ∧ freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).1
          (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).2
          (by linarith : (0 : ℝ) < q)
        ≠ wiredInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).1
            (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).2
            (by linarith : (0 : ℝ) < q) :=
  order_transition_q_large hq
    (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).1
    (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).2 hFree hWired

end FK

end StatMech
