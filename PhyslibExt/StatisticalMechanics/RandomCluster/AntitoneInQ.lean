/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.ComparisonHolley

/-!
# Monotonicity of the random-cluster measure in `q`

For `1 ≤ q₁ ≤ q₂` the random-cluster measure with parameter `q₂` is stochastically dominated by the
one with parameter `q₁`.

## i. Overview

The cluster count is antitone in the configuration and supermodular, so for `1 ≤ q₁ ≤ q₂` the
factors `q₂^{k(a)} q₁^{k(b)}` satisfy the cross inequality `q₂^{k(a)} q₁^{k(b)} ≤ q₂^{k(a ⊓ b)}
q₁^{k(a ⊔ b)}`. The Bernoulli edge product is log-modular, so the two normalized measures satisfy
Holley's condition `μ₂(a) μ₁(b) ≤ μ₂(a ⊓ b) μ₁(a ⊔ b)`, and Holley's inequality gives stochastic
domination.

The headline `fk_antitone_in_q` is proved unconditionally, under only `0 < p < 1` and `1 ≤ q₁ ≤ q₂`.

## ii. Key results

- `fkProb_cross_q` : Holley's cross condition between the measures at `q₂` and `q₁`.
- `fk_antitone_in_q` : the measure at `q₂` is stochastically dominated by the measure at `q₁`.

## iii. Table of contents

- A. The cross inequality for cluster factors
- B. Holley's condition and stochastic domination

## iv. References

- R. Holley, *Remarks on the FKG inequalities*, Comm. Math. Phys. 36 (1974).
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorem 3.21.
-/

@[expose] public section

open MeasureTheory SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. The cross inequality for cluster factors -/

lemma qFactor_cross {q₁ q₂ : ℝ} (hq₁ : 1 ≤ q₁) (hq₁₂ : q₁ ≤ q₂)
    (a b : ConfigSpace (Sym2 V)) :
    q₂ ^ numClusters G a * q₁ ^ numClusters G b
      ≤ q₂ ^ numClusters G (a ⊓ b) * q₁ ^ numClusters G (a ⊔ b) := by
  let ka := numClusters G a
  let kb := numClusters G b
  let ki := numClusters G (a ⊓ b)
  let ku := numClusters G (a ⊔ b)
  have hai : ka ≤ ki := numClusters_antitone G inf_le_left
  have hub : ku ≤ kb := numClusters_antitone G le_sup_right
  have hsuper : ka + kb ≤ ku + ki := by
    simpa only [ka, kb, ki, ku, add_comm] using numClusters_supermodular G a b
  let di := ki - ka
  let db := kb - ku
  have hdbdi : db ≤ di := by
    dsimp only [db, di]
    omega
  have hki : ki = ka + di := by
    dsimp only [di]
    omega
  have hkb : kb = ku + db := by
    dsimp only [db]
    omega
  have hq₂ : 1 ≤ q₂ := hq₁.trans hq₁₂
  have hpow : q₁ ^ db ≤ q₂ ^ di :=
    (pow_le_pow_left₀ (le_trans (by norm_num) hq₁) hq₁₂ db).trans
      (pow_le_pow_right₀ hq₂ hdbdi)
  change q₂ ^ ka * q₁ ^ kb ≤ q₂ ^ ki * q₁ ^ ku
  rw [hki, hkb, pow_add, pow_add]
  calc
    q₂ ^ ka * (q₁ ^ ku * q₁ ^ db) = q₂ ^ ka * q₁ ^ ku * q₁ ^ db := by ring
    _ ≤ q₂ ^ ka * q₁ ^ ku * q₂ ^ di := by gcongr
    _ = (q₂ ^ ka * q₂ ^ di) * q₁ ^ ku := by ring

/-! ## B. Holley's condition and stochastic domination -/

lemma fkWeight_cross_q {p q₁ q₂ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq₁ : 1 ≤ q₁) (hq₁₂ : q₁ ≤ q₂) (a b : ConfigSpace (Sym2 V)) :
    fkWeight G p q₂ a * fkWeight G p q₁ b
      ≤ fkWeight G p q₂ (a ⊓ b) * fkWeight G p q₁ (a ⊔ b) := by
  have hedge := (edgeProduct_logModular G p a b).trans (mul_comm _ _)
  have hcluster := qFactor_cross G hq₁ hq₁₂ a b
  have hedge_nonneg :
      0 ≤ edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b) :=
    mul_nonneg (edgeProduct_pos G hp hp1 _).le (edgeProduct_pos G hp hp1 _).le
  unfold fkWeight
  calc
    edgeProduct G p a * q₂ ^ numClusters G a
          * (edgeProduct G p b * q₁ ^ numClusters G b)
        = (edgeProduct G p a * edgeProduct G p b)
            * (q₂ ^ numClusters G a * q₁ ^ numClusters G b) := by ring
    _ = (edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b))
          * (q₂ ^ numClusters G a * q₁ ^ numClusters G b) := by rw [hedge]
    _ ≤ (edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b))
          * (q₂ ^ numClusters G (a ⊓ b) * q₁ ^ numClusters G (a ⊔ b)) :=
        mul_le_mul_of_nonneg_left hcluster hedge_nonneg
    _ = edgeProduct G p (a ⊓ b) * q₂ ^ numClusters G (a ⊓ b)
          * (edgeProduct G p (a ⊔ b) * q₁ ^ numClusters G (a ⊔ b)) := by ring

/-- Holley's cross condition: `μ_{q₂}(a) μ_{q₁}(b) ≤ μ_{q₂}(a ⊓ b) μ_{q₁}(a ⊔ b)` for `1 ≤ q₁ ≤ q₂`.
-/
lemma fkProb_cross_q {p q₁ q₂ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq₁ : 1 ≤ q₁) (hq₁₂ : q₁ ≤ q₂) (a b : ConfigSpace (Sym2 V)) :
    fkProb G p q₂ a * fkProb G p q₁ b
      ≤ fkProb G p q₂ (a ⊓ b) * fkProb G p q₁ (a ⊔ b) := by
  have hq₁0 : 0 < q₁ := lt_of_lt_of_le one_pos hq₁
  have hq₂0 : 0 < q₂ := lt_of_lt_of_le one_pos (hq₁.trans hq₁₂)
  have hZ₂ : 0 < fkZ G p q₂ := fkZ_pos G hp hp1 hq₂0
  have hZ₁ : 0 < fkZ G p q₁ := fkZ_pos G hp hp1 hq₁0
  unfold fkProb
  rw [div_mul_div_comm, div_mul_div_comm,
    div_le_div_iff_of_pos_right (mul_pos hZ₂ hZ₁)]
  exact fkWeight_cross_q G hp hp1 hq₁ hq₁₂ a b

/-- For `1 ≤ q₁ ≤ q₂` the random-cluster measure at `q₂` is stochastically dominated by the one at
`q₁`. -/
theorem fk_antitone_in_q {p q₁ q₂ : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq₁ : 1 ≤ q₁) (hq₁₂ : q₁ ≤ q₂) :
    measOfMass (fkProb G p q₂) ≼ measOfMass (fkProb G p q₁) := by
  have hq₁0 : 0 < q₁ := lt_of_lt_of_le one_pos hq₁
  have hq₂0 : 0 < q₂ := lt_of_lt_of_le one_pos (hq₁.trans hq₁₂)
  refine holley_stochasticallyDominated
    (fun ω => fkProb_nonneg G hp hp1 hq₂0 ω)
    (fun ω => fkProb_nonneg G hp hp1 hq₁0 ω) ?_ ?_
  · rw [fkProb_sum_eq_one G hp hp1 hq₂0, fkProb_sum_eq_one G hp hp1 hq₁0]
  · exact fun a b => fkProb_cross_q G hp hp1 hq₁ hq₁₂ a b

end StatMech.FK
