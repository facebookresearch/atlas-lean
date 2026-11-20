/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































import Mathlib
import Code.Walls.gc85bthreereplicaswitch
import Code.Walls.gh3weightedcor3

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent
open StatMech.Walls.GhcEqGap

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {W : Type*} [DecidableEq W] [Fintype W]












noncomputable def gh4_bondCompOf (ends : ι → Sym2 W) (K : Finset ι) (u : W) : Finset ι :=
  K.filter (fun i => ∃ x ∈ ends i, connK ends K u x)

@[simp] lemma gh4_mem_bondCompOf {ends : ι → Sym2 W} {K : Finset ι} {u : W} {i : ι} :
    i ∈ gh4_bondCompOf ends K u ↔ i ∈ K ∧ ∃ x ∈ ends i, connK ends K u x := by
  simp [gh4_bondCompOf]


lemma gh4_bondCompOf_subset (ends : ι → Sym2 W) (K : Finset ι) (u : W) :
    gh4_bondCompOf ends K u ⊆ K := Finset.filter_subset _ _














noncomputable def gh4_compMass (ends : ι → Sym2 W) (m : Finset ι) (V₁ V₂ : Finset W) (u : W)
    (A : Finset ι) : ℕ :=
  #((m.powerset ×ˢ m.powerset).filter
      (fun KK => Disjoint KK.1 KK.2 ∧ sources ends KK.1 = V₁ ∧ sources ends KK.2 = V₂
        ∧ gh4_bondCompOf ends KK.1 u = A))













theorem gh4_compMass_partition (ends : ι → Sym2 W) (m : Finset ι) (V₁ V₂ : Finset W) (u : W) :
    gc85b_pcount ends m V₁ V₂ = ∑ A ∈ m.powerset, gh4_compMass ends m V₁ V₂ u A := by
  classical
  unfold gc85b_pcount gh4_compMass
  
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun KK : Finset ι × Finset ι => gh4_bondCompOf ends KK.1 u)
    (t := m.powerset)
    (by
      rintro ⟨K₁, K₂⟩ hKK
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product,
        Finset.mem_powerset] at hKK
      
      exact Finset.mem_coe.2 (Finset.mem_powerset.2
        (Finset.Subset.trans (gh4_bondCompOf_subset ends K₁ u) hKK.1.1)))]
  refine Finset.sum_congr rfl (fun A hA => ?_)
  congr 1
  ext ⟨K₁, K₂⟩
  constructor
  · intro hKK
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hKK ⊢
    tauto
  · intro hKK
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hKK ⊢
    tauto


















lemma gh4_bondCompOf_conn (ends : ι → Sym2 W) (K : Finset ι) (u : W)
    {i : ι} (hi : i ∈ gh4_bondCompOf ends K u) {x : W} (hx : x ∈ ends i) :
    connK ends K u x := by
  rw [gh4_mem_bondCompOf] at hi
  obtain ⟨hiK, y, hy, hconn⟩ := hi
  
  by_cases hxy : x = y
  · exact hxy ▸ hconn
  · exact hconn.tail ⟨i, hiK, hy, hx, fun h => hxy h.symm⟩





lemma gh4_mark_in_comp_iff_conn (ends : ι → Sym2 W) (K : Finset ι) (u w : W) :
    (∃ i ∈ gh4_bondCompOf ends K u, w ∈ ends i) ↔ (∃ i ∈ K, w ∈ ends i) ∧ connK ends K u w := by
  constructor
  · rintro ⟨i, hi, hw⟩
    exact ⟨⟨i, gh4_bondCompOf_subset ends K u hi, hw⟩, gh4_bondCompOf_conn ends K u hi hw⟩
  · rintro ⟨⟨i, hiK, hw⟩, hconn⟩
    exact ⟨i, gh4_mem_bondCompOf.2 ⟨hiK, w, hw, hconn⟩, hw⟩



















theorem gh4_drop_nonneg (ends : ι → Sym2 W) (m : Finset ι) (V₁ V₂ : Finset W) (u : W)
    (wgt diff : Finset ι → ℝ) (hwgt : ∀ A, 0 ≤ wgt A) (hdiff : ∀ A, 0 ≤ diff A) :
    0 ≤ ∑ A ∈ m.powerset,
        (gh4_compMass ends m V₁ V₂ u A : ℝ) * wgt A * diff A := by
  apply Finset.sum_nonneg
  intro A hA
  have hmass : (0 : ℝ) ≤ (gh4_compMass ends m V₁ V₂ u A : ℝ) := Nat.cast_nonneg _
  have := hwgt A
  have := hdiff A
  positivity















theorem gh4_eq22_decomposition_of_identity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V)
    (ends : ι → Sym2 W) (m : Finset ι) (V₁ V₂ V₁' V₂' : Finset W) (u u' : W)
    (wgtA diffA wgtB diffB : Finset ι → ℝ)
    (hwgtA : ∀ A, 0 ≤ wgtA A) (hdiffA : ∀ A, 0 ≤ diffA A)
    (hwgtB : ∀ B, 0 ≤ wgtB B) (hdiffB : ∀ B, 0 ≤ diffB B)
    (surv : ℝ)
    (hident : eg_ursell3 G β h o x y
      = surv
        - 2 * (∑ A ∈ m.powerset, (gh4_compMass ends m V₁ V₂ u A : ℝ) * wgtA A * diffA A)
        - 2 * (∑ B ∈ m.powerset, (gh4_compMass ends m V₁' V₂' u' B : ℝ) * wgtB B * diffB B)) :
    gh3_eq22_decomposition G β h o x y := by
  refine ⟨surv, _, _, hident, ?_, ?_⟩
  · exact gh4_drop_nonneg ends m V₁ V₂ u wgtA diffA hwgtA hdiffA
  · exact gh4_drop_nonneg ends m V₁' V₂' u' wgtB diffB hwgtB hdiffB





theorem gh4_compMass_le_pcount (ends : ι → Sym2 W) (m : Finset ι) (V₁ V₂ : Finset W) (u : W)
    (A : Finset ι) :
    gh4_compMass ends m V₁ V₂ u A ≤ gc85b_pcount ends m V₁ V₂ := by
  rw [gh4_compMass_partition ends m V₁ V₂ u]
  by_cases hA : A ∈ m.powerset
  · exact Finset.single_le_sum (f := fun A => gh4_compMass ends m V₁ V₂ u A)
      (fun i _ => Nat.zero_le _) hA
  · have : gh4_compMass ends m V₁ V₂ u A = 0 := by
      unfold gh4_compMass
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ⟨K1, K2⟩ hKK hcond
      simp only [Finset.mem_product, Finset.mem_powerset] at hKK
      exact hA (Finset.mem_powerset.2 (hcond.2.2.2 ▸ Finset.Subset.trans
        (gh4_bondCompOf_subset ends K1 u) hKK.1))
    omega



































theorem gh4_status : True := trivial

end StatMech.Walls
