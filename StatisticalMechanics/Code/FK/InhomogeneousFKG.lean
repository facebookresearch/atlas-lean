/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.RussoDerivativeBeta
import Code.FK.FKG
import Code.OSSS.Monotonic
import Code.OSSS.HBridgeClose

open scoped BigOperators

namespace StatMech
namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem edgeProductW_logModular (pf : Sym2 V → ℝ)
    (a b : ConfigSpace (Sym2 V)) :
    edgeProductW G pf a * edgeProductW G pf b =
      edgeProductW G pf (a ⊔ b) * edgeProductW G pf (a ⊓ b) := by
  unfold edgeProductW
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  have hsup : (a ⊔ b) e = (a e || b e) := rfl
  have hinf : (a ⊓ b) e = (a e && b e) := rfl
  rw [hsup, hinf]
  cases a e <;> cases b e <;>
    simp only [Bool.or_self, Bool.or_false, Bool.or_true, Bool.and_self,
      Bool.and_false, Bool.and_true, if_true, mul_comm]

theorem fkWeightW_logSupermodular {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 1 ≤ q) (a b : ConfigSpace (Sym2 V)) :
    fkWeightW G pf q a * fkWeightW G pf q b ≤
      fkWeightW G pf q (a ⊔ b) * fkWeightW G pf q (a ⊓ b) := by
  have hcluster :
      q ^ numClusters G a * q ^ numClusters G b ≤
        q ^ numClusters G (a ⊔ b) * q ^ numClusters G (a ⊓ b) := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hq (numClusters_supermodular G a b)
  have hedge := edgeProductW_logModular G pf a b
  have hprod : 0 ≤ edgeProductW G pf (a ⊔ b) * edgeProductW G pf (a ⊓ b) :=
    mul_nonneg (edgeProductW_pos G hpf hpf1 _).le
      (edgeProductW_pos G hpf hpf1 _).le
  unfold fkWeightW
  calc
    edgeProductW G pf a * q ^ numClusters G a *
          (edgeProductW G pf b * q ^ numClusters G b) =
        (edgeProductW G pf a * edgeProductW G pf b) *
          (q ^ numClusters G a * q ^ numClusters G b) := by ring
    _ = (edgeProductW G pf (a ⊔ b) * edgeProductW G pf (a ⊓ b)) *
          (q ^ numClusters G a * q ^ numClusters G b) := by rw [hedge]
    _ ≤ (edgeProductW G pf (a ⊔ b) * edgeProductW G pf (a ⊓ b)) *
          (q ^ numClusters G (a ⊔ b) * q ^ numClusters G (a ⊓ b)) :=
      mul_le_mul_of_nonneg_left hcluster hprod
    _ = edgeProductW G pf (a ⊔ b) * q ^ numClusters G (a ⊔ b) *
          (edgeProductW G pf (a ⊓ b) * q ^ numClusters G (a ⊓ b)) := by ring

theorem fkProbW_sum_eq_one {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) :
    ∑ ω, fkProbW G pf q ω = 1 := by
  unfold fkProbW fkZW
  rw [← Finset.sum_div]
  exact div_self (fkZW_ne_zero G hpf hpf1 hq)

theorem fkProbW_FKGLatticeCondition {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 1 ≤ q) :
    FKGLatticeCondition (fkProbW G pf q) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hZ : 0 < fkZW G pf q := fkZW_pos G hpf hpf1 hq0
  intro a b
  unfold fkProbW
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right (mul_pos hZ hZ)).mpr
    (fkWeightW_logSupermodular G hpf hpf1 hq a b)

theorem fkProbW_isMonotonic {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 1 ≤ q) :
    OSSS.Monotonic.IsMonotonicMeasure (fkProbW G pf q) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact OSSS.Monotonic.fkg_implies_monotonic
    (fun ω => div_pos (fkWeightW_pos G hpf hpf1 hq0 ω)
      (fkZW_pos G hpf hpf1 hq0))
    (fkProbW_FKGLatticeCondition G hpf hpf1 hq)

theorem fkProbW_flipE_off (pf : Sym2 V → ℝ) (q : ℝ)
    {e : Sym2 V} (he : e ∉ G.edgeFinset) (ω : ConfigSpace (Sym2 V)) :
    fkProbW G pf q (OSSS.HBridgeClose.flipE e ω) = fkProbW G pf q ω := by
  unfold fkProbW fkWeightW edgeProductW
  congr 2
  · apply Finset.prod_congr rfl
    intro e' he'
    have hne : e' ≠ e := by rintro rfl; exact he he'
    rw [OSSS.HBridgeClose.flipE_of_ne hne]
  · rw [numClusters_congr_openSub G (OSSS.HBridgeClose.openSub_flipE G he ω)]

end FK
end StatMech
