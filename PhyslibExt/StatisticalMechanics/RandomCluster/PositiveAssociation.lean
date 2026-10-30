/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.HolleyFKG
public import PhyslibExt.StatisticalMechanics.RandomCluster.FKG
public import MathlibExt.Probability.CorrelationInequalities.IncreasingEvent

/-!
# Positive association of the random-cluster measure

For `q ≥ 1` the finite-volume random-cluster measure satisfies the FKG lattice condition, so
increasing functions and increasing events are positively correlated.

## i. Overview

The FK weight `p^{o(ω)} (1 - p)^{c(ω)} q^{k(ω)}`, viewed as a nonnegative weight, satisfies the FKG
lattice condition for `q ≥ 1` because the cluster count is supermodular. The FKG inequality for
lattice-condition weights on a finite distributive lattice then gives positive association for
increasing functions, and for increasing events by taking indicators. All results are proved
unconditionally, under `0 < p < 1` and `1 ≤ q`. The positive-association statements themselves are
`fkProb_positively_associated` and `fkProb_positively_associated_events` in `FKG`.

## ii. Key results

- `fk_fkgCondition` : the nonnegative FK weight satisfies the FKG lattice condition.

## iii. Table of contents

- A. The FK weight as a lattice-condition weight

## iv. References

- C. M. Fortuin, P. W. Kasteleyn, and J. Ginibre, *Correlation inequalities on some partially
  ordered sets*, Comm. Math. Phys. 22 (1971).
- R. Holley, *Remarks on the FKG inequalities*, Comm. Math. Phys. 36 (1974).
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorem 3.8.
-/

@[expose] public section

open scoped BigOperators NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. The FK weight as a lattice-condition weight -/

/-- The FK weight `p^{o(ω)} (1 - p)^{c(ω)} q^{k(ω)}` as a nonnegative real number. -/
noncomputable def fkWeightNN (p q : ℝ) (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : ℝ≥0 :=
  ⟨fkWeight G p q ω, fkWeight_nonneg G hp hp1 hq ω⟩

@[simp]
lemma fkWeightNN_coe {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) :
    (fkWeightNN G p q hp hp1 hq ω : ℝ) = fkWeight G p q ω := rfl

/-- For `q ≥ 1` the nonnegative FK weight satisfies the FKG lattice condition. -/
lemma fk_fkgCondition {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Probability.FKGCondition (fkWeightNN G p q hp hp1 (lt_of_lt_of_le zero_lt_one hq)) := by
  intro a b
  rw [← NNReal.coe_le_coe]
  push_cast [fkWeightNN_coe]
  calc fkWeight G p q a * fkWeight G p q b
        ≤ fkWeight G p q (a ⊔ b) * fkWeight G p q (a ⊓ b) :=
        fkWeight_logSupermodular G hp hp1 hq a b
    _ = fkWeight G p q (a ⊓ b) * fkWeight G p q (a ⊔ b) := by ring

lemma fkProb_fkgLattice {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    fkProb G p q a * fkProb G p q b ≤ fkProb G p q (a ⊓ b) * fkProb G p q (a ⊔ b) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  
  have hcond := fk_fkgCondition G hp hp1 hq a b
  rw [← NNReal.coe_le_coe] at hcond
  push_cast [fkWeightNN_coe] at hcond
  
  have hZpos : 0 < fkZ G p q := fkZ_pos G hp hp1 hq0
  simp only [fkProb]
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right (mul_pos hZpos hZpos)).mpr hcond

end FK

end StatMech
