/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































import Mathlib
import Code.Foundations.ConfigSpace
import Code.FK.RandomCluster
import Code.Inequalities.FKG
import Code.Foundations.StochasticDomination

open scoped BigOperators
open Matrix Module

set_option linter.style.show false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]












noncomputable def kerLap (ω : ConfigSpace (Sym2 V)) : Submodule ℝ (V → ℝ) :=
  LinearMap.ker (Matrix.toLin' ((openSub G ω).lapMatrix ℝ))




theorem mem_kerLap (ω : ConfigSpace (Sym2 V)) (x : V → ℝ) :
    x ∈ kerLap G ω ↔ ∀ i j, (openSub G ω).Adj i j → x i = x j := by
  unfold kerLap
  rw [LinearMap.mem_ker, Matrix.toLin'_apply]
  exact SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_adj (openSub G ω)



theorem numClusters_eq_finrank (ω : ConfigSpace (Sym2 V)) :
    numClusters G ω = Module.finrank ℝ (kerLap G ω) := by
  unfold numClusters kerLap
  exact SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix (openSub G ω)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem openSub_sup_adj (a b : ConfigSpace (Sym2 V)) (i j : V) :
    (openSub G (a ⊔ b)).Adj i j ↔ (openSub G a).Adj i j ∨ (openSub G b).Adj i j := by
  simp only [openSub_adj]
  constructor
  · rintro ⟨hadj, hopen⟩
    have h2 : (a ⊔ b) s(i, j) = (a s(i, j) || b s(i, j)) := rfl
    rw [h2, Bool.or_eq_true_iff] at hopen
    rcases hopen with h | h
    · exact Or.inl ⟨hadj, h⟩
    · exact Or.inr ⟨hadj, h⟩
  · rintro (⟨hadj, h⟩ | ⟨hadj, h⟩)
    · exact ⟨hadj, by
        show (a s(i, j) || b s(i, j)) = true; rw [Bool.or_eq_true_iff]; exact Or.inl h⟩
    · exact ⟨hadj, by
        show (a s(i, j) || b s(i, j)) = true; rw [Bool.or_eq_true_iff]; exact Or.inr h⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem openSub_inf_adj (a b : ConfigSpace (Sym2 V)) (i j : V) :
    (openSub G (a ⊓ b)).Adj i j ↔ (openSub G a).Adj i j ∧ (openSub G b).Adj i j := by
  simp only [openSub_adj]
  constructor
  · rintro ⟨hadj, hopen⟩
    have h2 : (a ⊓ b) s(i, j) = (a s(i, j) && b s(i, j)) := rfl
    rw [h2, Bool.and_eq_true_iff] at hopen
    exact ⟨⟨hadj, hopen.1⟩, ⟨hadj, hopen.2⟩⟩
  · rintro ⟨⟨hadj, ha⟩, ⟨_, hb⟩⟩
    exact ⟨hadj, by
      show (a s(i, j) && b s(i, j)) = true; rw [Bool.and_eq_true_iff]; exact ⟨ha, hb⟩⟩




theorem kerLap_sup (a b : ConfigSpace (Sym2 V)) :
    kerLap G (a ⊔ b) = kerLap G a ⊓ kerLap G b := by
  apply le_antisymm
  · intro x hx
    rw [mem_kerLap] at hx
    refine Submodule.mem_inf.mpr ⟨(mem_kerLap G a x).mpr ?_, (mem_kerLap G b x).mpr ?_⟩
    · intro i j hij; exact hx i j ((openSub_sup_adj G a b i j).mpr (Or.inl hij))
    · intro i j hij; exact hx i j ((openSub_sup_adj G a b i j).mpr (Or.inr hij))
  · intro x hx
    obtain ⟨hxa, hxb⟩ := Submodule.mem_inf.mp hx
    rw [mem_kerLap] at hxa hxb
    rw [mem_kerLap]
    intro i j hij
    rcases (openSub_sup_adj G a b i j).mp hij with h | h
    · exact hxa i j h
    · exact hxb i j h





theorem kerLap_inf_ge (a b : ConfigSpace (Sym2 V)) :
    kerLap G a ⊔ kerLap G b ≤ kerLap G (a ⊓ b) := by
  rw [sup_le_iff]
  refine ⟨fun x hx => (mem_kerLap G (a ⊓ b) x).mpr fun i j hij => ?_,
          fun x hx => (mem_kerLap G (a ⊓ b) x).mpr fun i j hij => ?_⟩
  · exact (mem_kerLap G a x).mp hx i j ((openSub_inf_adj G a b i j).mp hij).1
  · exact (mem_kerLap G b x).mp hx i j ((openSub_inf_adj G a b i j).mp hij).2





theorem numClusters_supermodular_lap (a b : ConfigSpace (Sym2 V)) :
    numClusters G a + numClusters G b ≤ numClusters G (a ⊔ b) + numClusters G (a ⊓ b) := by
  simp only [numClusters_eq_finrank]
  have hsup : Module.finrank ℝ (kerLap G (a ⊔ b))
      = Module.finrank ℝ (kerLap G a ⊓ kerLap G b : Submodule ℝ (V → ℝ)) := by
    rw [kerLap_sup]
  have hle : Module.finrank ℝ (kerLap G a ⊔ kerLap G b : Submodule ℝ (V → ℝ))
      ≤ Module.finrank ℝ (kerLap G (a ⊓ b)) :=
    Submodule.finrank_mono (kerLap_inf_ge G a b)
  have hkey := Submodule.finrank_sup_add_finrank_inf_eq (kerLap G a) (kerLap G b)
  rw [hsup]
  omega











theorem edgeFactor_cross (p1 p2 : ℝ) (hle : p1 ≤ p2) (α β : Bool) :
    (if α then p1 else 1 - p1) * (if β then p2 else 1 - p2)
      ≤ (if (α && β) then p1 else 1 - p1) * (if (α || β) then p2 else 1 - p2) := by
  cases α <;> cases β <;>
    · simp only [Bool.and_self, Bool.or_self, Bool.and_false, Bool.or_false, Bool.and_true,
        Bool.or_true, Bool.false_eq_true, if_true, if_false]
      nlinarith

omit [DecidableEq V] in




theorem edgeProduct_cross {p1 p2 : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1) (hp2 : 0 < p2)
    (hp2' : p2 < 1) (hle : p1 ≤ p2) (a b : ConfigSpace (Sym2 V)) :
    edgeProduct G p1 a * edgeProduct G p2 b
      ≤ edgeProduct G p1 (a ⊓ b) * edgeProduct G p2 (a ⊔ b) := by
  unfold edgeProduct
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro e _
    have h1 : (0 : ℝ) ≤ (if a e then p1 else 1 - p1) := by split <;> linarith
    have h2 : (0 : ℝ) ≤ (if b e then p2 else 1 - p2) := by split <;> linarith
    exact mul_nonneg h1 h2
  · intro e _
    have hinf : (a ⊓ b) e = (a e && b e) := rfl
    have hsup : (a ⊔ b) e = (a e || b e) := rfl
    rw [hinf, hsup]
    exact edgeFactor_cross p1 p2 hle (a e) (b e)








theorem fkWeight_cross {p1 p2 q : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1) (hp2 : 0 < p2)
    (hp2' : p2 < 1) (hle : p1 ≤ p2) (hq : 1 ≤ q) (a b : ConfigSpace (Sym2 V)) :
    fkWeight G p1 q a * fkWeight G p2 q b
      ≤ fkWeight G p1 q (a ⊓ b) * fkWeight G p2 q (a ⊔ b) := by
  
  set A1 := edgeProduct G p1 a with hA1
  set B1 := edgeProduct G p2 b with hB1
  set A2 := edgeProduct G p1 (a ⊓ b) with hA2
  set B2 := edgeProduct G p2 (a ⊔ b) with hB2
  
  have hedge : A1 * B1 ≤ A2 * B2 := edgeProduct_cross G hp1 hp1' hp2 hp2' hle a b
  
  have hclust : q ^ numClusters G a * q ^ numClusters G b
      ≤ q ^ numClusters G (a ⊓ b) * q ^ numClusters G (a ⊔ b) := by
    rw [← pow_add, ← pow_add]
    refine pow_le_pow_right₀ hq ?_
    have := numClusters_supermodular_lap G a b
    omega
  
  have hA1n : 0 ≤ A1 := (edgeProduct_pos G hp1 hp1' a).le
  have hB1n : 0 ≤ B1 := (edgeProduct_pos G hp2 hp2' b).le
  have hA2n : 0 ≤ A2 := (edgeProduct_pos G hp1 hp1' (a ⊓ b)).le
  have hB2n : 0 ≤ B2 := (edgeProduct_pos G hp2 hp2' (a ⊔ b)).le
  have hqa : (0 : ℝ) ≤ q ^ numClusters G a := pow_nonneg (by linarith) _
  have hqb : (0 : ℝ) ≤ q ^ numClusters G b := pow_nonneg (by linarith) _
  have hqab2 : (0 : ℝ) ≤ q ^ numClusters G (a ⊔ b) := pow_nonneg (by linarith) _
  
  unfold fkWeight
  have e1 : A1 * q ^ numClusters G a * (B1 * q ^ numClusters G b)
      = (A1 * B1) * (q ^ numClusters G a * q ^ numClusters G b) := by ring
  have e2 : A2 * q ^ numClusters G (a ⊓ b) * (B2 * q ^ numClusters G (a ⊔ b))
      = (A2 * B2) * (q ^ numClusters G (a ⊓ b) * q ^ numClusters G (a ⊔ b)) := by ring
  rw [e1, e2]
  exact mul_le_mul hedge hclust (mul_nonneg hqa hqb) (mul_nonneg hA2n hB2n)






theorem fkProb_cross {p1 p2 q : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1) (hp2 : 0 < p2)
    (hp2' : p2 < 1) (hle : p1 ≤ p2) (hq : 1 ≤ q) (a b : ConfigSpace (Sym2 V)) :
    fkProb G p1 q a * fkProb G p2 q b
      ≤ fkProb G p1 q (a ⊓ b) * fkProb G p2 q (a ⊔ b) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hZ1 : 0 < fkZ G p1 q := fkZ_pos G hp1 hp1' hq0
  have hZ2 : 0 < fkZ G p2 q := fkZ_pos G hp2 hp2' hq0
  unfold fkProb
  rw [div_mul_div_comm, div_mul_div_comm]
  rw [div_le_div_iff_of_pos_right (mul_pos hZ1 hZ2)]
  exact fkWeight_cross G hp1 hp1' hp2 hp2' hle hq a b












theorem fkProb_stochastically_increasing {p1 p2 q : ℝ} (hp1 : 0 < p1) (hp1' : p1 < 1)
    (hp2 : 0 < p2) (hp2' : p2 < 1) (hle : p1 ≤ p2) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fkProb G p1 q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fkProb G p2 q ω := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  refine holley_dominates ?_ ?_ ?_ ?_ hA
  · exact fun ω => fkProb_nonneg G hp1 hp1' hq0 ω
  · exact fun ω => fkProb_nonneg G hp2 hp2' hq0 ω
  · rw [fkProb_sum_eq_one G hp1 hp1' hq0, fkProb_sum_eq_one G hp2 hp2' hq0]
  · exact fun a b => fkProb_cross G hp1 hp1' hp2 hp2' hle hq a b

end FK

end StatMech
