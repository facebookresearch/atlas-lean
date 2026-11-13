/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































import Code.Probability.HolleyFKG
import Code.FK.FKG
import Code.Inequalities.IncreasingEvent

open scoped BigOperators NNReal

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]











noncomputable def fkWeightNN (p q : ℝ) (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : ℝ≥0 :=
  ⟨fkWeight G p q ω, fkWeight_nonneg G hp hp1 hq ω⟩

@[simp]
theorem fkWeightNN_coe {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) :
    (fkWeightNN G p q hp hp1 hq ω : ℝ) = fkWeight G p q ω := rfl













theorem fk_fkgCondition {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Probability.FKGCondition (fkWeightNN G p q hp hp1 (lt_of_lt_of_le zero_lt_one hq)) := by
  intro a b
  rw [← NNReal.coe_le_coe]
  push_cast [fkWeightNN_coe]
  calc fkWeight G p q a * fkWeight G p q b
        ≤ fkWeight G p q (a ⊔ b) * fkWeight G p q (a ⊓ b) :=
        fkWeight_logSupermodular G hp hp1 hq a b
    _ = fkWeight G p q (a ⊓ b) * fkWeight G p q (a ⊔ b) := by ring












theorem fkProb_fkgLattice {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
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











theorem fk_positively_associated {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {f g : ConfigSpace (Sym2 V) → ℝ} (hf : Monotone f) (hg : Monotone g) :
    (∑ ω, fkProb G p q ω * f ω) * (∑ ω, fkProb G p q ω * g ω)
      ≤ ∑ ω, fkProb G p q ω * (f ω * g ω) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact Probability.fkg_inequality
    (fun ω => fkProb_nonneg G hp hp1 hq0 ω)
    (fkProb_sum_eq_one G hp hp1 hq0)
    (fkProb_fkgLattice G hp hp1 hq) hf hg








theorem fk_positively_associated_events {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A B : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (∑ ω, fkProb G p q ω * A.indicator (fun _ => (1 : ℝ)) ω)
        * (∑ ω, fkProb G p q ω * B.indicator (fun _ => (1 : ℝ)) ω)
      ≤ ∑ ω, fkProb G p q ω * (A ∩ B).indicator (fun _ => (1 : ℝ)) ω := by
  have hAB : (A ∩ B).indicator (fun _ => (1 : ℝ))
      = fun ω => A.indicator (fun _ => (1 : ℝ)) ω * B.indicator (fun _ => (1 : ℝ)) ω := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;>
      simp [Set.indicator, ha, hb, Set.mem_inter_iff]
  rw [hAB]
  exact fk_positively_associated G hp hp1 hq hA.indicator_monotone hB.indicator_monotone

end FK

end StatMech
