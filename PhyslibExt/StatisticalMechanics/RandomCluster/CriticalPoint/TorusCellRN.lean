/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellFKDuality
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellDefectClassify
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.SelfDualValue

/-!
# Radon–Nikodym bounds for torus self-duality

At the self-dual point, the torus random-cluster probability of a configuration and of its dual
differ by a factor `q ^ k` with `k ∈ {-1, 0, 1}`.

## i. Overview

Configurations on the torus edges (`TorusAmbientConfig`) carry the random-cluster weight
`torusAmbientFKWeight` and probability `torusAmbientProbability`. The duality bijection maps the
defect `δ` to `2 - δ`, and at `p_sd(q)` the weight ratio is `q ^ (δ - 1)`. Since `δ ∈ {0, 1, 2}`,
the probability ratio lies in `{q⁻¹, 1, q}` (`torusAmbientProbability_selfDual_ratio_mem`, `q ≥ 1`).
All results are unconditional.

## ii. Key results

- `torusAmbientFKWeight_selfDual_relation`: weight relation at the self-dual point.
- `torusAmbientProbability_selfDual_ratio_mem`: the probability ratio is `q⁻¹`, `1` or `q`.

## iii. Table of contents

- A. Torus configurations and duality
- B. Weights and partition function
- C. Self-dual ratios

## iv. References

* V. Beffara, H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster model is
  critical for q ≥ 1*, Probab. Theory Related Fields 153 (2012).
-/

@[expose] public section

open SimpleGraph Set

namespace StatMech.BeffaraDC

open StatMech.Onsager

/-! ## A. Torus configurations and duality -/

/-- Configurations of the edges of the `L × L` torus. -/
abbrev TorusAmbientConfig (L : ℕ) [Fact (2 < L)] :=
  TorusAmbientEdge L → Bool

/-- The dual configuration on torus edges, transported along the cell crossing. -/
noncomputable def torusCellDualAmbientConfig (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) : TorusAmbientConfig L :=
  fun e => !(omega ((torusCellCrossing L).symm e))

/-- The duality of torus configurations, as an equivalence. -/
noncomputable def torusCellDualAmbientConfigEquiv (L : ℕ) [Fact (2 < L)] :
    TorusAmbientConfig L ≃ TorusAmbientConfig L where
  toFun := torusCellDualAmbientConfig L
  invFun eta := fun e => !(eta (torusCellCrossing L e))
  left_inv omega := by
    funext e
    simp [torusCellDualAmbientConfig]
  right_inv eta := by
    funext e
    simp [torusCellDualAmbientConfig]

/-- Extend a torus configuration to all pairs of torus sites, closed off the torus edges. -/
def torusAmbientConfigExtend (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) :
    ConfigSpace (Sym2 (ZMod L × ZMod L)) := fun e =>
  if he : e ∈ (onsTorusGraph L).edgeFinset then omega ⟨e, he⟩ else false

/-- Restrict a configuration on all pairs of torus sites to the torus edges. -/
def torusAmbientConfigRestrict (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    TorusAmbientConfig L := fun e => omega e.1

@[simp] lemma torusAmbientConfigRestrict_extend
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) :
    torusAmbientConfigRestrict L (torusAmbientConfigExtend L omega) = omega := by
  funext e
  simp [torusAmbientConfigRestrict, torusAmbientConfigExtend, e.2]

lemma torusAmbientConfigExtend_dual (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) :
    torusAmbientConfigExtend L (torusCellDualAmbientConfig L omega) =
      torusCellDualConfig L (torusAmbientConfigExtend L omega) := by
  funext e
  by_cases he : e ∈ (onsTorusGraph L).edgeFinset
  · have hp := torusCellPrimalOfDualEdge_mem L he
    have hp' : (((torusCellCrossing L).symm
        (⟨e, he⟩ : TorusAmbientEdge L) : TorusAmbientEdge L) :
        Sym2 (ZMod L × ZMod L)) ∈ (onsTorusGraph L).edgeFinset :=
      ((torusCellCrossing L).symm (⟨e, he⟩ : TorusAmbientEdge L)).2
    rw [torusAmbientConfigExtend, dite_eq_left he, torusCellDualConfig,
      dite_eq_left he, torusCellDualAmbientConfig]
    rw [torusCellPrimalOfDualEdge_of_mem L he]
    rw [torusAmbientConfigExtend, dite_eq_left hp']
  · rw [torusAmbientConfigExtend, dite_eq_right he, torusCellDualConfig, dite_eq_right he]

/-! ## B. Weights and partition function -/

/-- The random-cluster weight of a torus configuration. -/
noncomputable def torusAmbientFKWeight (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (omega : TorusAmbientConfig L) : ℝ :=
  FK.fkWeight (onsTorusGraph L) p q (torusAmbientConfigExtend L omega)

lemma torusAmbientFKWeight_duality_signed
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    torusAmbientFKWeight L p q omega *
        q ^ ((onsTorusGraph L).edgeFinset.card + 1) =
      (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
        q ^ Nat.card (ZMod L × ZMod L) *
        torusAmbientFKWeight L (dualParam p q) q
          (torusCellDualAmbientConfig L omega) *
        q ^ torusCellDefect L
          (FK.openSub (onsTorusGraph L) (torusAmbientConfigExtend L omega)) := by
  unfold torusAmbientFKWeight
  rw [torusAmbientConfigExtend_dual]
  exact torusCell_fkWeight_duality_signed L
    (torusAmbientConfigExtend L omega) hp hp1 hq

/-- The Euler defect of the open subgraph of a torus configuration. -/
noncomputable def torusAmbientDefect (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) : ℤ :=
  torusCellDefect L
    (FK.openSub (onsTorusGraph L) (torusAmbientConfigExtend L omega))

lemma torusAmbientDefect_classified (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) :
    torusAmbientDefect L omega = 0 ∨ torusAmbientDefect L omega = 1 ∨
      torusAmbientDefect L omega = 2 := by
  unfold torusAmbientDefect
  exact torusCellDefect_classified_unconditional L _
    (FK.openSub_le (onsTorusGraph L) (torusAmbientConfigExtend L omega))

lemma torusAmbientDefect_add_dual (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) :
    torusAmbientDefect L omega +
      torusAmbientDefect L (torusCellDualAmbientConfig L omega) = 2 := by
  unfold torusAmbientDefect
  rw [torusAmbientConfigExtend_dual]
  exact torusCellDefect_add_dualConfig L (torusAmbientConfigExtend L omega)

/-- The random-cluster partition function on the torus. -/
noncomputable def torusAmbientPartition (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) : ℝ :=
  ∑ omega : TorusAmbientConfig L, torusAmbientFKWeight L p q omega

lemma torusAmbientPartition_reindex_dual (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) :
    (∑ omega : TorusAmbientConfig L,
        torusAmbientFKWeight L p q (torusCellDualAmbientConfig L omega)) =
      torusAmbientPartition L p q := by
  unfold torusAmbientPartition
  exact Equiv.sum_comp (torusCellDualAmbientConfigEquiv L)
    (torusAmbientFKWeight L p q)

/-! ## C. Self-dual ratios -/

lemma selfDualPoint_odds {q : ℝ} (hq : 0 < q) :
    selfDualPoint q / (1 - selfDualPoint q) = Real.sqrt q := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  unfold selfDualPoint
  field_simp
  ring

lemma torusAmbient_selfDual_prefactor (L : ℕ) [Fact (2 < L)]
    {q : ℝ} (hq : 0 < q) :
    (selfDualPoint q /
          (1 - dualParam (selfDualPoint q) q)) ^
        (onsTorusGraph L).edgeFinset.card *
      q ^ Nat.card (ZMod L × ZMod L) =
        q ^ (onsTorusGraph L).edgeFinset.card := by
  rw [selfDualPoint_is_fixed hq, selfDualPoint_odds hq]
  have hedge : (onsTorusGraph L).edgeFinset.card = 2 * L ^ 2 :=
    onsTorus_card_edges L
  have hvert : Nat.card (ZMod L × ZMod L) = L ^ 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]
    ring
  rw [hedge, hvert, pow_mul, Real.sq_sqrt hq.le, ← pow_add]
  congr 2
  omega

lemma torusAmbientFKWeight_selfDual_relation
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L)
    {q : ℝ} (hq : 0 < q) :
    torusAmbientFKWeight L (selfDualPoint q) q omega * q =
      torusAmbientFKWeight L (selfDualPoint q) q
          (torusCellDualAmbientConfig L omega) *
        q ^ torusAmbientDefect L omega := by
  obtain ⟨hp, hp1⟩ := selfDualPoint_mem_Ioo hq
  have h := torusAmbientFKWeight_duality_signed L omega hp hp1 hq
  have hpref := torusAmbient_selfDual_prefactor L hq
  rw [selfDualPoint_is_fixed hq] at h hpref
  rw [hpref] at h
  rw [pow_succ] at h
  have hqm : q ^ (onsTorusGraph L).edgeFinset.card ≠ 0 :=
    ne_of_gt (pow_pos hq _)
  apply mul_left_cancel₀ hqm
  calc
    q ^ (onsTorusGraph L).edgeFinset.card *
        (torusAmbientFKWeight L (selfDualPoint q) q omega * q) =
      torusAmbientFKWeight L (selfDualPoint q) q omega *
        (q ^ (onsTorusGraph L).edgeFinset.card * q) := by ring
    _ = q ^ (onsTorusGraph L).edgeFinset.card *
        (torusAmbientFKWeight L (selfDualPoint q) q
          (torusCellDualAmbientConfig L omega) *
          q ^ torusAmbientDefect L omega) := by
      simpa only [torusAmbientDefect, mul_assoc] using h

lemma torusAmbientFKWeight_pos (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < torusAmbientFKWeight L p q omega := by
  unfold torusAmbientFKWeight
  exact FK.fkWeight_pos (onsTorusGraph L) hp hp1 hq _

lemma torusAmbientPartition_pos (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < torusAmbientPartition L p q := by
  unfold torusAmbientPartition
  exact Finset.sum_pos
    (fun omega _ => torusAmbientFKWeight_pos L omega hp hp1 hq)
    Finset.univ_nonempty

/-- The random-cluster probability of a torus configuration. -/
noncomputable def torusAmbientProbability (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (omega : TorusAmbientConfig L) : ℝ :=
  torusAmbientFKWeight L p q omega / torusAmbientPartition L p q

lemma torusAmbientProbability_sum_one (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ omega : TorusAmbientConfig L, torusAmbientProbability L p q omega = 1 := by
  have hZ : torusAmbientPartition L p q ≠ 0 :=
    ne_of_gt (torusAmbientPartition_pos L hp hp1 hq)
  have hZ' : (∑ omega : TorusAmbientConfig L,
      torusAmbientFKWeight L p q omega) ≠ 0 := by
    simpa [torusAmbientPartition] using hZ
  unfold torusAmbientProbability torusAmbientPartition
  rw [← Finset.sum_div, div_self hZ']

lemma torusAmbientProbability_ratio_eq_weight_ratio
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    torusAmbientProbability L p q omega /
        torusAmbientProbability L p q (torusCellDualAmbientConfig L omega) =
      torusAmbientFKWeight L p q omega /
        torusAmbientFKWeight L p q (torusCellDualAmbientConfig L omega) := by
  have hZ : torusAmbientPartition L p q ≠ 0 :=
    ne_of_gt (torusAmbientPartition_pos L hp hp1 hq)
  have hWD : torusAmbientFKWeight L p q
      (torusCellDualAmbientConfig L omega) ≠ 0 :=
    ne_of_gt (torusAmbientFKWeight_pos L _ hp hp1 hq)
  unfold torusAmbientProbability
  field_simp

lemma torusAmbientProbability_selfDual_ratio_eq_zpow
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L)
    {q : ℝ} (hq : 0 < q) :
    torusAmbientProbability L (selfDualPoint q) q omega /
        torusAmbientProbability L (selfDualPoint q) q
          (torusCellDualAmbientConfig L omega) =
      q ^ (torusAmbientDefect L omega - 1) := by
  obtain ⟨hp, hp1⟩ := selfDualPoint_mem_Ioo hq
  rw [torusAmbientProbability_ratio_eq_weight_ratio L omega hp hp1 hq]
  have hrel := torusAmbientFKWeight_selfDual_relation L omega hq
  have hqne : q ≠ 0 := ne_of_gt hq
  have hWD : torusAmbientFKWeight L (selfDualPoint q) q
      (torusCellDualAmbientConfig L omega) ≠ 0 :=
    ne_of_gt (torusAmbientFKWeight_pos L _ hp hp1 hq)
  rw [div_eq_iff hWD]
  apply mul_right_cancel₀ hqne
  calc
    torusAmbientFKWeight L (selfDualPoint q) q omega * q =
        torusAmbientFKWeight L (selfDualPoint q) q
          (torusCellDualAmbientConfig L omega) *
            q ^ torusAmbientDefect L omega := hrel
    _ = (q ^ (torusAmbientDefect L omega - 1) *
          torusAmbientFKWeight L (selfDualPoint q) q
            (torusCellDualAmbientConfig L omega)) * q := by
      have hpow : q ^ (torusAmbientDefect L omega - 1) * q =
          q ^ torusAmbientDefect L omega := by
        calc
          q ^ (torusAmbientDefect L omega - 1) * q =
              q ^ (torusAmbientDefect L omega - 1) * q ^ (1 : ℤ) := by
                rw [zpow_one]
          _ = q ^ ((torusAmbientDefect L omega - 1) + 1) := by
                rw [zpow_add₀ hqne]
          _ = q ^ torusAmbientDefect L omega := by ring_nf
      rw [← hpow]
      ring

lemma torusAmbientProbability_selfDual_ratio_values
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L)
    {q : ℝ} (hq : 0 < q) :
    let ratio := torusAmbientProbability L (selfDualPoint q) q omega /
      torusAmbientProbability L (selfDualPoint q) q
        (torusCellDualAmbientConfig L omega)
    ratio = q⁻¹ ∨ ratio = 1 ∨ ratio = q := by
  obtain ⟨hp, hp1⟩ := selfDualPoint_mem_Ioo hq
  rw [torusAmbientProbability_ratio_eq_weight_ratio L omega hp hp1 hq]
  have hrel := torusAmbientFKWeight_selfDual_relation L omega hq
  have hqne : q ≠ 0 := ne_of_gt hq
  have hWD : torusAmbientFKWeight L (selfDualPoint q) q
      (torusCellDualAmbientConfig L omega) ≠ 0 :=
    ne_of_gt (torusAmbientFKWeight_pos L _ hp hp1 hq)
  rcases torusAmbientDefect_classified L omega with hd | hd | hd
  · left
    rw [hd, zpow_zero, mul_one] at hrel
    field_simp [hqne, hWD]
    simpa [mul_comm] using hrel
  · right; left
    rw [hd, zpow_one] at hrel
    have hw := mul_right_cancel₀ hqne hrel
    rw [hw, div_self hWD]
  · right; right
    rw [hd, zpow_two] at hrel
    have hw : torusAmbientFKWeight L (selfDualPoint q) q omega =
        torusAmbientFKWeight L (selfDualPoint q) q
          (torusCellDualAmbientConfig L omega) * q := by
      apply mul_right_cancel₀ hqne
      simpa [mul_assoc] using hrel
    rw [hw, mul_div_cancel_left₀ _ hWD]

/-- The probability ratio is `q⁻¹`, `1` or `q`. -/
theorem torusAmbientProbability_selfDual_ratio_mem
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L)
    {q : ℝ} (hq1 : 1 ≤ q) :
    let ratio := torusAmbientProbability L (selfDualPoint q) q omega /
      torusAmbientProbability L (selfDualPoint q) q
        (torusCellDualAmbientConfig L omega)
    q⁻¹ ≤ ratio ∧ ratio ≤ q := by
  have hq : 0 < q := lt_of_lt_of_le one_pos hq1
  have hinv : q⁻¹ ≤ 1 := (inv_le_one₀ hq).2 hq1
  have hinvq : q⁻¹ ≤ q := hinv.trans hq1
  rcases torusAmbientProbability_selfDual_ratio_values L omega hq with
    hratio | hratio | hratio
  · rw [hratio]
    exact ⟨le_rfl, hinvq⟩
  · rw [hratio]
    exact ⟨hinv, hq1⟩
  · rw [hratio]
    exact ⟨hinvq, le_rfl⟩

end StatMech.BeffaraDC
