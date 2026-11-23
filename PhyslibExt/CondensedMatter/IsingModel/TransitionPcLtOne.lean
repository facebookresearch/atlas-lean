/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Transition
public import PhyslibExt.StatisticalMechanics.RandomCluster.PcNontrivial

/-!
# The phase transition when the FK critical point is below one

The phase transition of `Transition` with the hypothesis `0 < p_c` discharged.

## i. Overview

The FK critical point is positive in every dimension, so the hypotheses of `Transition` reduce to
nonnegativity of the magnetization, the threshold identity, and `p_c < 1`.

The statements here are conditional: they take as hypotheses the identification of the Ising
magnetization with the FK percolation probability and the nontriviality of the FK critical point.
The unconditional phase transition for `d ≥ 2` is `ising_phase_transition_of_two_le` in
`FKRepresentation.PcUpperAllDimensions`.

## ii. Key results

- `StatMech.Ising.ising_transition_of_two_le` : the phase transition for `d ≥ 2`
- `StatMech.Ising.isingBetaC_eq_of_two_le` : `β_c = -½ log (1 - p_c)`
- `StatMech.Ising.isingBetaC_pos_of_two_le` : `β_c > 0`

## iii. Table of contents

- A. The phase transition

## iv. References

- H. Duminil-Copin, *Lectures on the Ising and Potts models on the hypercubic lattice*, PIMS–CRM
  Summer School in Probability (2017), arXiv:1707.00520
- G. Grimmett, *The Random-Cluster Model*, Springer (2006)
-/

@[expose] public section

open Real

namespace StatMech

namespace Ising

open StatMech.IsingFK

lemma fkPc_two_pos_of_two_le {d : ℕ} (hd : 2 ≤ d) : 0 < FK.fkPc d 2 :=
  FK.fkPc_pos_of_two_le hd (by norm_num)

/-! ## A. The phase transition -/

lemma ising_transition_of_two_le (d : ℕ) (hd : 2 ≤ d)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (htransition : ∀ β, 0 < β →
      (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
    (hpc1 : FK.fkPc d 2 < 1) :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧
      (∀ β, βc < β → 0 < magnetization d β) :=
  ising_transition d hmag_nonneg htransition (fkPc_two_pos_of_two_le hd) hpc1

lemma isingBetaC_eq_of_two_le (d : ℕ) (hd : 2 ≤ d)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (htransition : ∀ β, 0 < β →
      (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
    (hpc1 : FK.fkPc d 2 < 1) :
    IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) :=
  ising_betaC_eq d hmag_nonneg htransition (fkPc_two_pos_of_two_le hd) hpc1

lemma isingBetaC_pos_of_two_le (d : ℕ) (hd : 2 ≤ d)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (htransition : ∀ β, 0 < β →
      (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
    (hpc1 : FK.fkPc d 2 < 1) :
    0 < IsingFK.betaC (magnetization d) :=
  isingBetaC_pos d hmag_nonneg htransition (fkPc_two_pos_of_two_le hd) hpc1

end Ising

end StatMech
