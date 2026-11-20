/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib
import Code.Ising.InfiniteVolume
import Code.Ising.Pressure

open scoped BigOperators
open Finset Filter Topology

namespace StatMech

namespace Ising

open StatMech.Lattice














theorem logZ_dist_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] (β : ℝ) (E₁ E₂ : Ω → ℝ)
    (M : ℝ) (hM : ∀ s, |E₁ s - E₂ s| ≤ M) :
    |Real.log (Z β E₁) - Real.log (Z β E₂)| ≤ |β| * M := by
  have hZ1 : 0 < Z β E₁ := Z_pos β E₁
  have hZ2 : 0 < Z β E₂ := Z_pos β E₂
  
  have key : ∀ (Ea Eb : Ω → ℝ), (∀ s, |Ea s - Eb s| ≤ M) →
      Z β Ea ≤ Real.exp (|β| * M) * Z β Eb := by
    intro Ea Eb hab
    unfold Z
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : -β * (Ea s - Eb s) ≤ |β| * M := by
      calc -β * (Ea s - Eb s) ≤ |(-β) * (Ea s - Eb s)| := le_abs_self _
        _ = |β| * |Ea s - Eb s| := by rw [abs_mul, abs_neg]
        _ ≤ |β| * M := mul_le_mul_of_nonneg_left (hab s) (abs_nonneg _)
    nlinarith [h1]
  have hb1 : Z β E₁ ≤ Real.exp (|β| * M) * Z β E₂ := key E₁ E₂ hM
  have hb2 : Z β E₂ ≤ Real.exp (|β| * M) * Z β E₁ :=
    key E₂ E₁ (fun s => by rw [abs_sub_comm]; exact hM s)
  have hl1 : Real.log (Z β E₁) ≤ |β| * M + Real.log (Z β E₂) := by
    have := Real.log_le_log hZ1 hb1
    rwa [Real.log_mul (Real.exp_ne_zero _) hZ2.ne', Real.log_exp] at this
  have hl2 : Real.log (Z β E₂) ≤ |β| * M + Real.log (Z β E₁) := by
    have := Real.log_le_log hZ2 hb2
    rwa [Real.log_mul (Real.exp_ne_zero _) hZ1.ne', Real.log_exp] at this
  rw [abs_le]
  constructor <;> linarith



variable {d : ℕ}





theorem fvZ_eq_Z (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    fvZ η n B β h = Z β (fvEnergy η n B h) := rfl




lemma bond_abs_le_one (s : ConfigSpace (Site d)) (e : Sym2 (Site d)) : |bond s e| ≤ 1 := by
  induction e with
  | h x y =>
    rw [bond_mk, abs_mul]
    have hx := abs_spin_le_one s x
    have hy := abs_spin_le_one s y
    nlinarith [abs_nonneg (spin s x), abs_nonneg (spin s y)]




lemma fieldSum_indep (η₁ η₂ : ConfigSpace (Site d)) (n : ℕ)
    (τ : {x // x ∈ box d n} → Bool) :
    (∑ x ∈ boxFinset d n, spin (glue η₁ τ) x) = ∑ x ∈ boxFinset d n, spin (glue η₂ τ) x := by
  apply Finset.sum_congr rfl
  intro x hx
  rw [mem_boxFinset] at hx
  unfold spin; rw [glue_mem _ _ hx, glue_mem _ _ hx]




lemma bond_internal_indep (η₁ η₂ : ConfigSpace (Site d)) (n : ℕ)
    (τ : {x // x ∈ box d n} → Bool) {e : Sym2 (Site d)}
    (he : e ∈ bondFinsetInternal d n) :
    bond (glue η₁ τ) e = bond (glue η₂ τ) e := by
  unfold bondFinsetInternal bondPairsInternal at he
  rw [Finset.mem_image] at he
  obtain ⟨p, hp, rfl⟩ := he
  rw [Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hx, hy⟩, _⟩ := hp
  rw [mem_boxFinset] at hx hy
  rw [bond_mk, bond_mk]
  have e1 : spin (glue η₁ τ) p.1 = spin (glue η₂ τ) p.1 := by
    unfold spin; rw [glue_mem _ _ hx, glue_mem _ _ hx]
  have e2 : spin (glue η₁ τ) p.2 = spin (glue η₂ τ) p.2 := by
    unfold spin; rw [glue_mem _ _ hy, glue_mem _ _ hy]
  rw [e1, e2]














lemma fvEnergy_sub_abs_le
    (η_bc η_free : ConfigSpace (Site d)) (n : ℕ)
    (B_bc B_free : Finset (Sym2 (Site d))) (h : ℝ)
    (τ : {x // x ∈ box d n} → Bool)
    (hsub : B_free ⊆ B_bc)
    (hagree : ∀ e ∈ B_free, bond (glue η_bc τ) e = bond (glue η_free τ) e) :
    |fvEnergy η_bc n B_bc h τ - fvEnergy η_free n B_free h τ|
      ≤ (B_bc \ B_free).card := by
  have hfield := fieldSum_indep η_bc η_free n τ
  
  have hbond : (∑ e ∈ B_bc, bond (glue η_bc τ) e) - (∑ e ∈ B_free, bond (glue η_free τ) e)
      = ∑ e ∈ B_bc \ B_free, bond (glue η_bc τ) e := by
    have hsplit : ∑ e ∈ B_bc, bond (glue η_bc τ) e
        = (∑ e ∈ B_free, bond (glue η_bc τ) e) + ∑ e ∈ B_bc \ B_free, bond (glue η_bc τ) e := by
      rw [← Finset.sum_union (Finset.disjoint_sdiff)]
      congr 1
      rw [Finset.union_sdiff_of_subset hsub]
    rw [hsplit]
    have hfree : ∑ e ∈ B_free, bond (glue η_bc τ) e = ∑ e ∈ B_free, bond (glue η_free τ) e :=
      Finset.sum_congr rfl hagree
    rw [hfree]; ring
  have heq : fvEnergy η_bc n B_bc h τ - fvEnergy η_free n B_free h τ
      = -((∑ e ∈ B_bc, bond (glue η_bc τ) e) - (∑ e ∈ B_free, bond (glue η_free τ) e)) := by
    unfold fvEnergy
    rw [hfield]; ring
  calc |fvEnergy η_bc n B_bc h τ - fvEnergy η_free n B_free h τ|
      = |(∑ e ∈ B_bc, bond (glue η_bc τ) e) - (∑ e ∈ B_free, bond (glue η_free τ) e)| := by
        rw [heq, abs_neg]
    _ = |∑ e ∈ B_bc \ B_free, bond (glue η_bc τ) e| := by rw [hbond]
    _ ≤ ∑ e ∈ B_bc \ B_free, |bond (glue η_bc τ) e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ B_bc \ B_free, (1 : ℝ) := Finset.sum_le_sum (fun e _ => bond_abs_le_one _ e)
    _ = (B_bc \ B_free).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]







theorem logFvZ_sub_abs_le
    (η_bc η_free : ConfigSpace (Site d)) (n : ℕ)
    (B_bc B_free : Finset (Sym2 (Site d))) (β h : ℝ)
    (hsub : B_free ⊆ B_bc)
    (hagree : ∀ (τ : {x // x ∈ box d n} → Bool), ∀ e ∈ B_free,
      bond (glue η_bc τ) e = bond (glue η_free τ) e) :
    |Real.log (fvZ η_bc n B_bc β h) - Real.log (fvZ η_free n B_free β h)|
      ≤ |β| * (B_bc \ B_free).card := by
  rw [fvZ_eq_Z, fvZ_eq_Z]
  exact logZ_dist_le β (fvEnergy η_bc n B_bc h) (fvEnergy η_free n B_free h)
    ((B_bc \ B_free).card)
    (fun τ => fvEnergy_sub_abs_le η_bc η_free n B_bc B_free h τ hsub (hagree τ))







lemma bondFinsetInternal_subset_touch (n : ℕ) :
    bondFinsetInternal d n ⊆ bondFinsetTouch d n := by
  unfold bondFinsetInternal bondFinsetTouch bondPairsInternal bondPairsTouch
  intro e he
  rw [Finset.mem_image] at he ⊢
  obtain ⟨p, hp, rfl⟩ := he
  rw [Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hx, hy⟩, hadj⟩ := hp
  rw [mem_boxFinset] at hx hy
  refine ⟨p, ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨?_, ?_⟩, hadj, Or.inl hx⟩
  · rw [mem_boxFinset]; exact box_subset_succ d n hx
  · rw [mem_boxFinset]; exact box_subset_succ d n hy



lemma internal_bond_agree (n : ℕ) (τ : {x // x ∈ box d n} → Bool)
    (e : Sym2 (Site d)) (he : e ∈ bondFinsetInternal d n) :
    bond (glue (plusField d) τ) e = bond (glue (minusField d) τ) e :=
  bond_internal_indep (plusField d) (minusField d) n τ he




theorem plus_free_logFvZ_sub_abs_le (n : ℕ) (β h : ℝ) :
    |Real.log (fvZ (plusField d) n (bondFinsetTouch d n) β h)
        - Real.log (fvZ (minusField d) n (bondFinsetInternal d n) β h)|
      ≤ |β| * ((bondFinsetTouch d n) \ (bondFinsetInternal d n)).card :=
  logFvZ_sub_abs_le (plusField d) (minusField d) n
    (bondFinsetTouch d n) (bondFinsetInternal d n) β h
    (bondFinsetInternal_subset_touch n)
    (fun τ e he => internal_bond_agree n τ e he)










theorem normalized_diff_tendsto_zero (L₁ L₂ surf vol : ℕ → ℝ)
    (hbound : ∀ n, |L₁ n - L₂ n| ≤ surf n)
    (hvolpos : ∀ n, 0 < vol n)
    (hratio : Tendsto (fun n => surf n / vol n) atTop (𝓝 0)) :
    Tendsto (fun n => L₁ n / vol n - L₂ n / vol n) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n => -(surf n / vol n)) (h := fun n => surf n / vol n)
  · simpa using hratio.neg
  · exact hratio
  · intro n
    simp only [← sub_div]
    rw [le_div_iff₀ (hvolpos n), neg_mul, div_mul_cancel₀ _ (hvolpos n).ne']
    have := (abs_le.mp (hbound n)).1
    linarith
  · intro n
    simp only [← sub_div]
    rw [div_le_iff₀ (hvolpos n), div_mul_cancel₀ _ (hvolpos n).ne']
    have := (abs_le.mp (hbound n)).2
    linarith



lemma boxFinset_card_pos (n : ℕ) : 0 < ((boxFinset d n).card : ℝ) := by
  have : (boxFinset d n).Nonempty := by
    refine ⟨0, ?_⟩; rw [mem_boxFinset, mem_box]; intro i; simp
  exact_mod_cast Finset.card_pos.mpr this












theorem plus_free_pressure_indep (β h : ℝ)
    (hratio : Tendsto
      (fun n => (|β| * (((bondFinsetTouch d n) \ (bondFinsetInternal d n)).card : ℝ))
        / ((boxFinset d n).card : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n =>
        Real.log (fvZ (plusField d) n (bondFinsetTouch d n) β h) / ((boxFinset d n).card : ℝ)
      - Real.log (fvZ (minusField d) n (bondFinsetInternal d n) β h) / ((boxFinset d n).card : ℝ))
      atTop (𝓝 0) :=
  normalized_diff_tendsto_zero
    (fun n => Real.log (fvZ (plusField d) n (bondFinsetTouch d n) β h))
    (fun n => Real.log (fvZ (minusField d) n (bondFinsetInternal d n) β h))
    (fun n => |β| * (((bondFinsetTouch d n) \ (bondFinsetInternal d n)).card : ℝ))
    (fun n => ((boxFinset d n).card : ℝ))
    (fun n => plus_free_logFvZ_sub_abs_le n β h)
    (fun n => boxFinset_card_pos n)
    hratio

end Ising

end StatMech
