/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.OSSS.FKSharpnessWeightedHighBeta










open scoped BigOperators Classical
open Finset Set

namespace StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem edgeProductW_nonneg_of_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {pf : Sym2 V -> Real} (hpf : forall e, 0 <= pf e)
    (hpf1 : forall e, pf e < 1)
    (omega : ConfigSpace (Sym2 V)) :
    0 <= edgeProductW G pf omega := by
  unfold edgeProductW
  apply Finset.prod_nonneg
  intro e he
  split
  · exact hpf e
  · linarith [hpf1 e]

theorem bcWeightW_nonneg_of_nonneg
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    {pf : Sym2 V -> Real} (hpf : forall e, 0 <= pf e)
    (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (omega : ConfigSpace (Sym2 V)) :
    0 <= bcWeightW G C pf q omega := by
  exact mul_nonneg (edgeProductW_nonneg_of_nonneg G hpf hpf1 omega)
    (pow_nonneg hq.le _)

theorem bcZW_pos_of_nonneg
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    {pf : Sym2 V -> Real} (hpf : forall e, 0 <= pf e)
    (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) :
    0 < bcZW G C pf q := by
  let closed : ConfigSpace (Sym2 V) := fun _ => false
  have hedge : 0 < edgeProductW G pf closed := by
    unfold edgeProductW
    apply Finset.prod_pos
    intro e he
    dsimp [closed]
    linarith [hpf1 e]
  have hclosed : 0 < bcWeightW G C pf q closed := by
    exact mul_pos hedge (pow_pos hq _)
  unfold bcZW
  apply Finset.sum_pos'
  · intro omega homega
    exact bcWeightW_nonneg_of_nonneg G C hpf hpf1 hq omega
  · exact ⟨closed, Finset.mem_univ _, hclosed⟩

theorem bcProbW_nonneg_of_nonneg
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    {pf : Sym2 V -> Real} (hpf : forall e, 0 <= pf e)
    (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) (omega : ConfigSpace (Sym2 V)) :
    0 <= bcProbW G C pf q omega := by
  exact div_nonneg (bcWeightW_nonneg_of_nonneg G C hpf hpf1 hq omega)
    (bcZW_pos_of_nonneg G C hpf hpf1 hq).le

theorem bcProbW_sum_eq_one_of_nonneg
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    {pf : Sym2 V -> Real} (hpf : forall e, 0 <= pf e)
    (hpf1 : forall e, pf e < 1)
    {q : Real} (hq : 0 < q) :
    (∑ omega, bcProbW G C pf q omega) = 1 := by
  unfold bcProbW bcZW
  rw [<- Finset.sum_div]
  exact div_self (bcZW_pos_of_nonneg G C hpf hpf1 hq).ne'

theorem edgeProductW_cross_params_of_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {pf1 pf2 : Sym2 V -> Real}
    (hpf1 : forall e, 0 <= pf1 e) (hpf1' : forall e, pf1 e < 1)
    (hpf2 : forall e, 0 <= pf2 e) (hpf2' : forall e, pf2 e < 1)
    (hle : forall e, pf1 e <= pf2 e)
    (a b : ConfigSpace (Sym2 V)) :
    edgeProductW G pf1 a * edgeProductW G pf2 b <=
      edgeProductW G pf1 (a ⊓ b) * edgeProductW G pf2 (a ⊔ b) := by
  unfold edgeProductW
  rw [<- Finset.prod_mul_distrib, <- Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro e he
    apply mul_nonneg
    · split
      · exact hpf1 e
      · linarith [hpf1' e]
    · split
      · exact hpf2 e
      · linarith [hpf2' e]
  · intro e he
    change (if a e then pf1 e else 1 - pf1 e) *
        (if b e then pf2 e else 1 - pf2 e) <=
      (if a e && b e then pf1 e else 1 - pf1 e) *
        (if a e || b e then pf2 e else 1 - pf2 e)
    cases ha : a e <;> cases hb : b e <;> simp <;>
      nlinarith [hle e]

theorem bcWeightW_cross_params_of_nonneg
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    {pf1 pf2 : Sym2 V -> Real}
    (hpf1 : forall e, 0 <= pf1 e) (hpf1' : forall e, pf1 e < 1)
    (hpf2 : forall e, 0 <= pf2 e) (hpf2' : forall e, pf2 e < 1)
    (hle : forall e, pf1 e <= pf2 e)
    {q : Real} (hq : 1 <= q) (a b : ConfigSpace (Sym2 V)) :
    bcWeightW G C pf1 q a * bcWeightW G C pf2 q b <=
      bcWeightW G C pf1 q (a ⊓ b) * bcWeightW G C pf2 q (a ⊔ b) := by
  have hcluster :
      q ^ numClustersBC G C a * q ^ numClustersBC G C b <=
        q ^ numClustersBC G C (a ⊓ b) * q ^ numClustersBC G C (a ⊔ b) := by
    rw [<- pow_add, <- pow_add]
    exact pow_le_pow_right₀ hq (mixed_supermodular_bc G C C le_rfl a b)
  have hedge := edgeProductW_cross_params_of_nonneg G
    hpf1 hpf1' hpf2 hpf2' hle a b
  have hedge0 : 0 <= edgeProductW G pf1 a * edgeProductW G pf2 b :=
    mul_nonneg (edgeProductW_nonneg_of_nonneg G hpf1 hpf1' a)
      (edgeProductW_nonneg_of_nonneg G hpf2 hpf2' b)
  have hcluster0 : 0 <=
      q ^ numClustersBC G C (a ⊓ b) * q ^ numClustersBC G C (a ⊔ b) := by
    positivity
  unfold bcWeightW
  calc
    _ = (edgeProductW G pf1 a * edgeProductW G pf2 b) *
          (q ^ numClustersBC G C a * q ^ numClustersBC G C b) := by ring
    _ <= (edgeProductW G pf1 a * edgeProductW G pf2 b) *
          (q ^ numClustersBC G C (a ⊓ b) *
            q ^ numClustersBC G C (a ⊔ b)) :=
      mul_le_mul_of_nonneg_left hcluster hedge0
    _ <= (edgeProductW G pf1 (a ⊓ b) * edgeProductW G pf2 (a ⊔ b)) *
          (q ^ numClustersBC G C (a ⊓ b) *
            q ^ numClustersBC G C (a ⊔ b)) :=
      mul_le_mul_of_nonneg_right hedge hcluster0
    _ = _ := by ring



theorem bcProbW_mono_params_of_nonneg
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    {pf1 pf2 : Sym2 V -> Real}
    (hpf1 : forall e, 0 <= pf1 e) (hpf1' : forall e, pf1 e < 1)
    (hpf2 : forall e, 0 <= pf2 e) (hpf2' : forall e, pf2 e < 1)
    (hle : forall e, pf1 e <= pf2 e)
    {q : Real} (hq : 1 <= q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW G C pf1 q omega) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        bcProbW G C pf2 q omega := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hZ1 := bcZW_pos_of_nonneg G C hpf1 hpf1' hq0
  have hZ2 := bcZW_pos_of_nonneg G C hpf2 hpf2' hq0
  have hcross : forall a b,
      bcProbW G C pf1 q a * bcProbW G C pf2 q b <=
        bcProbW G C pf1 q (a ⊓ b) * bcProbW G C pf2 q (a ⊔ b) := by
    intro a b
    unfold bcProbW
    rw [div_mul_div_comm, div_mul_div_comm,
      div_le_div_iff_of_pos_right (mul_pos hZ1 hZ2)]
    exact bcWeightW_cross_params_of_nonneg G C
      hpf1 hpf1' hpf2 hpf2' hle hq a b
  refine holley_dominates ?_ ?_ ?_ ?_ hA
  · exact bcProbW_nonneg_of_nonneg G C hpf1 hpf1' hq0
  · exact bcProbW_nonneg_of_nonneg G C hpf2 hpf2' hq0
  · rw [bcProbW_sum_eq_one_of_nonneg G C hpf1 hpf1' hq0,
      bcProbW_sum_eq_one_of_nonneg G C hpf2 hpf2' hq0]
  · exact hcross

end StatMech.FK
