/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint
public import PhyslibExt.StatisticalMechanics.RandomCluster.OrderTransition
public import MathlibExt.Probability.Percolation.SharpnessFromInputs
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneMerge
public import MathlibExt.Probability.StochasticOrder.StochasticDomination
public import PhyslibExt.StatisticalMechanics.RandomCluster.PcNontrivial
/-!
# Free percolation above the random-cluster critical point

Above `p_c(q, d)`, the free infinite-volume random-cluster measure percolates, provided the free
measures are monotone in `p` and the free and wired percolation probabilities agree off a
countable set of parameters.

## i. Overview

`p_c(q, d)` is defined through the wired percolation probability `θ¹`, so `θ¹(p, q) > 0` for
every `p > p_c(q, d)`. To transfer this to the free percolation probability `θ⁰`, pick `p'` in
`(p_c, p)` where `θ⁰(p', q) = θ¹(p', q)` and use stochastic monotonicity of the free measure in
`p`: `θ⁰(p, q) ≥ θ⁰(p', q) > 0`. Both inputs are hypotheses here:

- `hmono` : the free infinite-volume measure at `p'` is stochastically dominated by the one at
  `p`, for every `p' ∈ (p_c, p)`;
- `hagree` : `θ⁰(p', q) = θ¹(p', q)` for every `p' > p_c` outside a countable set `bad`.

In the literature both hold for `q ≥ 1` (the second because free and wired measures coincide
off a countable set of `p`), but neither is proved in this file.

## ii. Key results

- `frp_fkTheta_pos_of_gt_fkPc` : `θ¹(p, q) > 0` for `p > p_c(q, d)`.
- `frp_free_percolation_above_pc_of_countable_agreement` : `θ⁰(p, q) > 0` for `p > p_c(q, d)`,
  under the two hypotheses above.

## iii. Table of contents

- A. Wired percolation above the critical point
- B. Free percolation above the critical point

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Chapters 4 and 5.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation

/-! ## A. Wired percolation above the critical point -/

/-- Above the critical point the wired measure percolates: `θ¹(p, q) > 0` for `p > p_c(q, d)`. -/
lemma frp_fkTheta_pos_of_gt_fkPc (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hpc : fkPc d q < p) :
    0 < fkTheta d hp hp1 hq (q := q) := by
  rcases (fkTheta_nonneg d hp hp1 hq (q := q)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hmem : p ∈ fkSubcriticalSet d q := ⟨hp, hp1, hq, h.symm⟩
    have hle : p ≤ fkPc d q := le_csSup (fkSubcriticalSet_bddAbove d q) hmem
    exact absurd hle (not_le.mpr hpc)

/-- The percolation event is measurable. -/
lemma frp_measurableSet_percolationEvent (d : ℕ) :
    MeasurableSet (Percolation.percolationEvent d) := by
  rw [Percolation.percolationEvent_eq_iInter]
  exact MeasurableSet.iInter (fun n => Percolation.measurableSet_crossingEvent (n + 1))

/-- The percolation event is increasing. -/
lemma frp_isIncreasing_percolationEvent (d : ℕ) :
    IsIncreasing (Percolation.percolationEvent d) := by
  intro ω ω' h hω
  rw [Percolation.mem_percolationEvent] at hω ⊢
  exact hω.mono (Percolation.cluster_mono h (Percolation.origin d))

/-! ## B. Free percolation above the critical point -/

/-- If `p_c < p'`, the free measure at `p'` is dominated by the free measure at `p`, and `θ⁰(p', q)
= θ¹(p', q)`, then `θ⁰(p, q) > 0`. -/
lemma frp_free_percolation_above_pc (d : ℕ) {p p' q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hp' : 0 < p') (hp1' : p' < 1)
    (hpc' : fkPc d q < p')
    (hmono : (freeInfiniteVolume d hp' hp1' hq : Measure (ConfigSpace (Sym2 (Site d))))
        ≼ (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))))
    (huniq : fkThetaFree d hp' hp1' hq (q := q) = fkTheta d hp' hp1' hq (q := q)) :
    0 < fkThetaFree d hp hp1 hq (q := q) := by
  have hwired : 0 < fkTheta d hp' hp1' hq (q := q) :=
    frp_fkTheta_pos_of_gt_fkPc d hp' hp1' hq hpc'
  have hfree' : 0 < fkThetaFree d hp' hp1' hq (q := q) := huniq ▸ hwired
  have hmono' : fkThetaFree d hp' hp1' hq (q := q) ≤ fkThetaFree d hp hp1 hq (q := q) :=
    hmono (Percolation.percolationEvent d) (frp_measurableSet_percolationEvent d)
      (frp_isIncreasing_percolationEvent d)
  exact lt_of_lt_of_le hfree' hmono'

/-- For `p > p_c(q, d)`, the free measure percolates, `θ⁰(p, q) > 0`, assuming monotonicity of the
free measures in `p` on `(p_c, p)` (`hmono`) and `θ⁰ = θ¹` off a countable set (`hagree`). -/
lemma frp_free_percolation_above_pc_of_countable_agreement
    (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hpc : fkPc d q < p) (bad : Set ℝ) (hbad : bad.Countable)
    (hmono : ∀ {p' : ℝ} (hp' : 0 < p') (hp1' : p' < 1), fkPc d q < p' →
      (freeInfiniteVolume d hp' hp1' hq : Measure (ConfigSpace (Sym2 (Site d))))
        ≼ (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))))
    (hagree : ∀ {p' : ℝ} (hp' : 0 < p') (hp1' : p' < 1), fkPc d q < p' →
      p' ∉ bad →
      fkThetaFree d hp' hp1' hq (q := q) = fkTheta d hp' hp1' hq (q := q)) :
    0 < fkThetaFree d hp hp1 hq (q := q) := by
  let a := max (fkPc d q) 0
  have hap : a < p := max_lt hpc hp
  have hI : (Set.Ioo a p).Nonempty := Set.nonempty_Ioo.mpr hap
  obtain ⟨p', hp'bad, hp'I⟩ :=
    (hbad.dense_compl ℝ).exists_mem_open isOpen_Ioo hI
  have hp' : 0 < p' := lt_of_le_of_lt (le_max_right _ _) hp'I.1
  have hp1' : p' < 1 := hp'I.2.trans hp1
  have hpc' : fkPc d q < p' := lt_of_le_of_lt (le_max_left _ _) hp'I.1
  exact frp_free_percolation_above_pc d hp hp1 hq hp' hp1' hpc'
    (hmono hp' hp1' hpc') (hagree hp' hp1' hpc' hp'bad)

end FK

end StatMech
