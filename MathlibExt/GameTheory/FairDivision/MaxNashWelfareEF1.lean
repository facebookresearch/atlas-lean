/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import MathlibExt.GameTheory.FairDivision.Indivisible
public import MathlibExt.GameTheory.FairDivision.MaxNashWelfare

import Mathlib.Logic.Function.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false

namespace MathlibExt.GameTheory.FairDivision.Indivisible

@[expose] public section

/-- The allocation obtained from `A` by moving good `g` to agent `i`. -/
def transfer {ι γ : Type*} [DecidableEq γ] (A : γ → ι) (g : γ) (i : ι) :
    γ → ι :=
  Function.update A g i

/-- Moving `g` to `i` when `g` was in `j`'s bundle: the new bundle of `i`
is the old one with `g` inserted (stated for `A g ≠ i`). -/
theorem bundle_transfer_self {ι γ : Type*} [Fintype γ] [DecidableEq γ]
    [DecidableEq ι] (A : γ → ι) {g : γ} {i : ι} (hgi : A g ≠ i) :
    bundle (transfer A g i) i = insert g (bundle A i) := by
  unfold bundle transfer
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases h : x = g
  · subst h
    simp [Function.update_self]
  · have hx : Function.update A g i x = A x := Function.update_of_ne h _ _
    simp [h]

/-- Moving `g` away from `j`: the new bundle of `j` is the old one with
`g` erased (stated for the owner `j = A g` moving to a different agent). -/
theorem bundle_transfer_owner {ι γ : Type*} [Fintype γ] [DecidableEq γ]
    [DecidableEq ι] (A : γ → ι) {g : γ} {i : ι} (hgi : A g ≠ i) :
    bundle (transfer A g i) (A g) = (bundle A (A g)).erase g := by
  unfold bundle transfer
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  by_cases h : x = g
  · subst h
    have hni : i ≠ A x := Ne.symm hgi
    have hself : Function.update A x i x = i := Function.update_self _ _ _
    simp [hni]
  · have hx : Function.update A g i x = A x := Function.update_of_ne h _ _
    simp [h]

/-- The single-good exchange inequality at a maximum Nash welfare allocation with nonnegative
single-good values: if `g` belongs to `j ≠ i`, `i` has positive value and `j` keeps positive
value without `g`, then moving `g` from `j` to `i` cannot increase the product of the two
bundle values. -/
theorem exchange_le {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    [DecidableEq ι] {v : ι → γ → ℝ} {A : γ → ι} (hA : IsMaxNashWelfare v A)
    (hv : ∀ i g, 0 ≤ v i g)
    {i j : ι} {g : γ} (hg : g ∈ bundle A j) (hij : i ≠ j)
    (hi : 0 < value v A i) (hj : 0 < value v A j - v j g) :
    (value v A i + v i g) * (value v A j - v j g) ≤ value v A i * value v A j := by
  have hAg : A g = j := by
    have h := hg
    unfold bundle at h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  have hgi : A g ≠ i := by
    rw [hAg]
    exact Ne.symm hij
  have hgAi : g ∉ bundle A i := by
    intro h
    unfold bundle at h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact hgi h
  have hvalBi : value v (transfer A g i) i = value v A i + v i g := by
    unfold value bundleValue
    rw [bundle_transfer_self A hgi, Finset.sum_insert hgAi]
    exact add_comm _ _
  have hBj : bundle (transfer A g i) j = (bundle A j).erase g := by
    have h := bundle_transfer_owner A hgi
    rwa [hAg] at h
  have hvalBj : value v (transfer A g i) j = value v A j - v j g := by
    unfold value bundleValue
    rw [hBj]
    have hmem : g ∉ (bundle A j).erase g :=
      fun h => (Finset.mem_erase.mp h).1 rfl
    have h1 : ∑ x ∈ insert g ((bundle A j).erase g), v j x
        = v j g + ∑ x ∈ (bundle A j).erase g, v j x :=
      Finset.sum_insert hmem
    have h2 : insert g ((bundle A j).erase g) = bundle A j :=
      Finset.insert_erase hg
    rw [h2] at h1
    rw [h1, add_sub_cancel_left]
  have hjA : 0 < value v A j := lt_of_le_of_lt (hv j g) (sub_pos.mp hj)
  have hbundle_other : ∀ k, k ≠ i → k ≠ j →
      bundle (transfer A g i) k = bundle A k := by
    intro k hki hkj
    unfold bundle transfer
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : x = g
    · rw [h, Function.update_self, hAg]
      exact ⟨fun hh => (hki hh.symm).elim, fun hh => (hkj hh.symm).elim⟩
    · have hx : Function.update A g i x = A x := Function.update_of_ne h _ _
      rw [hx]
  have hval_other : ∀ k, k ≠ i → k ≠ j →
      value v (transfer A g i) k = value v A k := by
    intro k hki hkj
    unfold value bundleValue
    rw [hbundle_other k hki hkj]
  have hpos : positiveAgents v (transfer A g i) = positiveAgents v A := by
    ext k
    simp only [positiveAgents, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hki : k = i
    · rw [hki]
      constructor
      · intro _
        exact hi
      · intro _
        rw [hvalBi]
        exact lt_of_lt_of_le hi (le_add_of_nonneg_right (hv i g))
    · by_cases hkj : k = j
      · rw [hkj]
        constructor
        · intro _
          exact hjA
        · intro _
          rw [hvalBj]
          exact hj
      · rw [hval_other k hki hkj]
  have hW := hA (transfer A g i)
  unfold positiveWelfare at hW
  rw [hpos] at hW
  have hiS : i ∈ positiveAgents v A := by
    simp only [positiveAgents, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi
  have hjS : j ∈ positiveAgents v A := by
    simp only [positiveAgents, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hjA
  have hijS : j ∈ (positiveAgents v A).erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hij, hjS⟩
  have hAf : ∏ k ∈ positiveAgents v A, value v A k = value v A i *
      (value v A j * ∏ k ∈ ((positiveAgents v A).erase i).erase j, value v A k) := by
    have e1 := Finset.mul_prod_erase (positiveAgents v A) (fun k => value v A k) hiS
    have e2 := Finset.mul_prod_erase ((positiveAgents v A).erase i) (fun k => value v A k) hijS
    rw [← e1, ← e2]
  have hBf : ∏ k ∈ positiveAgents v A, value v (transfer A g i) k =
      value v (transfer A g i) i * (value v (transfer A g i) j *
      ∏ k ∈ ((positiveAgents v A).erase i).erase j, value v (transfer A g i) k) := by
    have e1 := Finset.mul_prod_erase (positiveAgents v A)
      (fun k => value v (transfer A g i) k) hiS
    have e2 := Finset.mul_prod_erase ((positiveAgents v A).erase i)
      (fun k => value v (transfer A g i) k) hijS
    rw [← e1, ← e2]
  have hR : ∏ k ∈ ((positiveAgents v A).erase i).erase j, value v (transfer A g i) k
      = ∏ k ∈ ((positiveAgents v A).erase i).erase j, value v A k := by
    apply Finset.prod_congr rfl
    intro k hk
    simp only [Finset.mem_erase] at hk
    exact hval_other k hk.2.1 hk.1
  have hRpos : 0 < ∏ k ∈ ((positiveAgents v A).erase i).erase j, value v A k := by
    have hpp : ∀ s : Finset ι, (∀ k ∈ s, 0 < value v A k) →
        0 < ∏ k ∈ s, value v A k := by
      refine Finset.induction ?_ ?_
      · intro _
        rw [Finset.prod_empty]
        exact zero_lt_one
      · intro a s hna ih hf
        rw [Finset.prod_insert hna]
        exact mul_pos (hf a (Finset.mem_insert_self a s))
          (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))
    apply hpp
    intro k hk
    simp only [Finset.mem_erase] at hk
    have hkmem : k ∈ positiveAgents v A := hk.2.2
    simp only [positiveAgents, Finset.mem_filter, Finset.mem_univ, true_and] at hkmem
    exact hkmem
  rw [hAf, hBf, hR, hvalBi, hvalBj, ← mul_assoc, ← mul_assoc] at hW
  exact le_of_mul_le_mul_right (hW.2 rfl) hRpos

/-- **Maximum Nash welfare implies EF1.** For additive nonnegative
valuations, every refined maximum Nash welfare allocation is envy-free up
to one good. -/
theorem isEF1_of_isMaxNashWelfare {ι γ : Type*} [Fintype ι] [Fintype γ]
    [DecidableEq γ] [DecidableEq ι] {v : ι → γ → ℝ} {A : γ → ι}
    (hv : ∀ i g, 0 ≤ v i g) (hA : IsMaxNashWelfare v A) :
    IsEF1 v A := by
  classical
  unfold IsEF1
  intro i j hne
  by_cases hij : i = j
  · subst hij
    obtain ⟨g, hg⟩ := hne
    exact ⟨g, hg, Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun x _ _ => hv _ _)⟩
  · by_contra hcon
    have hcon' : ∀ g ∈ bundle A j,
        value v A i < bundleValue v i ((bundle A j).erase g) := by
      intro g hg
      apply not_le.mp
      intro hle
      exact hcon ⟨g, hg, hle⟩
    have herase : ∀ g ∈ bundle A j,
        bundleValue v i ((bundle A j).erase g)
          = bundleValue v i (bundle A j) - v i g := by
      intro g hg
      unfold bundleValue
      have hmem : g ∉ (bundle A j).erase g :=
        fun h => (Finset.mem_erase.mp h).1 rfl
      have h1 : ∑ x ∈ insert g ((bundle A j).erase g), v i x
          = v i g + ∑ x ∈ (bundle A j).erase g, v i x :=
        Finset.sum_insert hmem
      have h2 : insert g ((bundle A j).erase g) = bundle A j :=
        Finset.insert_erase hg
      rw [h2] at h1
      rw [h1, add_sub_cancel_left]
    have ⟨g0, hg0⟩ := hne
    have hx_nonneg : 0 ≤ value v A i := by
      unfold value bundleValue
      exact Finset.sum_nonneg (f := v i) (s := bundle A i) (fun g _ => hv i g)
    have hS_pos : 0 < bundleValue v i (bundle A j) := by
      have h := hcon' g0 hg0
      rw [herase g0 hg0] at h
      have h1 : 0 < bundleValue v i (bundle A j) - v i g0 :=
        lt_of_le_of_lt hx_nonneg h
      have h2 : v i g0 < bundleValue v i (bundle A j) := sub_pos.mp h1
      exact lt_of_le_of_lt (hv i g0) h2
    have hsum : ∑ x ∈ bundle A j,
        (v i x * value v A j - v j x * bundleValue v i (bundle A j)) = 0 := by
      have hstep : ∑ x ∈ bundle A j,
            (v i x * value v A j - v j x * bundleValue v i (bundle A j))
          = (∑ x ∈ bundle A j, v i x) * value v A j
            - (∑ x ∈ bundle A j, v j x) * bundleValue v i (bundle A j) := by
        calc ∑ x ∈ bundle A j,
                (v i x * value v A j - v j x * bundleValue v i (bundle A j))
            = ∑ x ∈ bundle A j, v i x * value v A j
              - ∑ x ∈ bundle A j, v j x * bundleValue v i (bundle A j) :=
              Finset.sum_sub_distrib _ _
          _ = (∑ x ∈ bundle A j, v i x) * value v A j
              - (∑ x ∈ bundle A j, v j x) * bundleValue v i (bundle A j) := by
              congr 1
              · exact (Finset.sum_mul _ _ _).symm
              · exact (Finset.sum_mul _ _ _).symm
      have eS : (∑ x ∈ bundle A j, v i x) = bundleValue v i (bundle A j) := rfl
      have ey : (∑ x ∈ bundle A j, v j x) = value v A j := rfl
      rw [hstep, eS, ey]
      ring
    obtain ⟨m0, hm0mem, hm0max⟩ := Finset.exists_max_image (bundle A j)
      (fun x => v i x * value v A j - v j x * bundleValue v i (bundle A j)) hne
    let M : Finset γ :=
      (bundle A j).filter (fun g => ∀ h ∈ bundle A j,
        v i h * value v A j - v j h * bundleValue v i (bundle A j)
          ≤ v i g * value v A j - v j g * bundleValue v i (bundle A j))
    have hm0M : m0 ∈ M := by
      simp only [M, Finset.mem_filter]
      exact ⟨hm0mem, hm0max⟩
    have hMne : M.Nonempty := ⟨m0, hm0M⟩
    obtain ⟨g, hgM, hgtie⟩ := Finset.exists_max_image M (v i) hMne
    simp only [M, Finset.mem_filter] at hgM
    obtain ⟨hgmem, hgmax⟩ := hgM
    have hscore_nonneg : 0 ≤ v i g * value v A j
        - v j g * bundleValue v i (bundle A j) := by
      by_contra hneg
      rw [not_le] at hneg
      have hall' : ∀ x ∈ bundle A j,
          v i x * value v A j - v j x * bundleValue v i (bundle A j) < 0 := by
        intro x hx
        exact lt_of_le_of_lt (hgmax x hx) hneg
      have hlt : (∑ x ∈ bundle A j,
            (v i x * value v A j - v j x * bundleValue v i (bundle A j)))
          < ∑ x ∈ bundle A j, (0 : ℝ) :=
        Finset.sum_lt_sum_of_nonempty hne hall'
      rw [hsum, Finset.sum_const_zero] at hlt
      exact (lt_irrefl 0) hlt
    have hS_sum : 0 < ∑ x ∈ bundle A j, v i x := hS_pos
    obtain ⟨h, hhmem, hhpos⟩ :=
      (Finset.sum_pos_iff_of_nonneg (f := v i) (s := bundle A j)
        (fun x _ => hv i x)).mp hS_sum
    have ha_pos : 0 < v i g := by
      by_cases hpos : 0 < v i g * value v A j
        - v j g * bundleValue v i (bundle A j)
      · by_contra ha0
        rw [not_lt] at ha0
        have ha_eq : v i g = 0 := le_antisymm ha0 (hv i g)
        rw [ha_eq, zero_mul, zero_sub] at hpos
        have hbj : 0 ≤ v j g * bundleValue v i (bundle A j) :=
          mul_nonneg (hv j g) (le_of_lt hS_pos)
        linarith [hpos, hbj]
      · have hzero : v i g * value v A j - v j g * bundleValue v i (bundle A j)
            = 0 :=
            le_antisymm (not_lt.mp hpos) hscore_nonneg
        have hle0 : ∀ x ∈ bundle A j,
            v i x * value v A j - v j x * bundleValue v i (bundle A j) ≤ 0 := by
          intro x hx
          have hle := hgmax x hx
          rw [hzero] at hle
          exact hle
        have hall0 : ∀ x ∈ bundle A j,
            v i x * value v A j - v j x * bundleValue v i (bundle A j) = 0 :=
          (Finset.sum_eq_zero_iff_of_nonpos (s := bundle A j)
            (f := fun x => v i x * value v A j
              - v j x * bundleValue v i (bundle A j)) hle0).mp hsum
        have hhM : h ∈ M := by
          simp only [M, Finset.mem_filter]
          refine ⟨hhmem, ?_⟩
          intro x hx
          have hx0 := hall0 x hx
          have hh0 := hall0 h hhmem
          linarith [hx0, hh0]
        exact lt_of_lt_of_le hhpos (hgtie h hhM)
    have hAg : A g = j := by
      have h := hgmem
      unfold bundle at h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h
    have hgi : A g ≠ i := by
      rw [hAg]
      exact Ne.symm hij
    have hgAi : g ∉ bundle A i := by
      intro h
      unfold bundle at h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact hgi h
    have hvalBi : value v (transfer A g i) i = value v A i + v i g := by
      unfold value bundleValue
      rw [bundle_transfer_self A hgi, Finset.sum_insert hgAi]
      exact add_comm _ _
    have hBj : bundle (transfer A g i) j = (bundle A j).erase g := by
      have h := bundle_transfer_owner A hgi
      rwa [hAg] at h
    have hvalBj : value v (transfer A g i) j = value v A j - v j g := by
      unfold value bundleValue
      rw [hBj]
      have hmem : g ∉ (bundle A j).erase g :=
        fun h => (Finset.mem_erase.mp h).1 rfl
      have h1 : ∑ x ∈ insert g ((bundle A j).erase g), v j x
          = v j g + ∑ x ∈ (bundle A j).erase g, v j x :=
        Finset.sum_insert hmem
      have h2 : insert g ((bundle A j).erase g) = bundle A j :=
        Finset.insert_erase hgmem
      rw [h2] at h1
      rw [h1, add_sub_cancel_left]
    have hbundle_other : ∀ k, k ≠ i → k ≠ j →
        bundle (transfer A g i) k = bundle A k := by
      intro k hki hkj
      unfold bundle transfer
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h : x = g
      · rw [h, Function.update_self, hAg]
        exact ⟨fun hh => (hki hh.symm).elim, fun hh => (hkj hh.symm).elim⟩
      · have hx : Function.update A g i x = A x := Function.update_of_ne h _ _
        rw [hx]
    have hval_other : ∀ k, k ≠ i → k ≠ j →
        value v (transfer A g i) k = value v A k := by
      intro k hki hkj
      unfold value bundleValue
      rw [hbundle_other k hki hkj]
    have hcontra : ∀ h ∈ bundle A j,
        value v A i + v i h < bundleValue v i (bundle A j) := by
      intro h hh
      have hc := hcon' h hh
      rw [herase h hh] at hc
      linarith [hc]
    have hy_nonneg : 0 ≤ value v A j := by
      unfold value bundleValue
      exact Finset.sum_nonneg (f := v j) (s := bundle A j) (fun g _ => hv j g)
    by_cases hypos : 0 < value v A j
    · have hyb : 0 < value v A j - v j g := by
        by_contra hle
        rw [not_lt] at hle
        have hbj_le : v j g ≤ value v A j :=
          Finset.single_le_sum (f := v j) (s := bundle A j)
            (fun x _ => hv j x) hgmem
        have hbj_eq : v j g = value v A j := by
          have hle' : value v A j ≤ v j g := by linarith [hle]
          exact le_antisymm hbj_le hle'
        have hai_le : v i g ≤ bundleValue v i (bundle A j) :=
          Finset.single_le_sum (f := v i) (s := bundle A j)
            (fun x _ => hv i x) hgmem
        have hscore_le : v i g * value v A j
            - v j g * bundleValue v i (bundle A j) ≤ 0 := by
          have hprod : 0 ≤ value v A j
              * (bundleValue v i (bundle A j) - v i g) :=
            mul_nonneg hy_nonneg (sub_nonneg.mpr hai_le)
          rw [hbj_eq]
          linarith [hprod]
        have hscore_eq : v i g * value v A j
            - v j g * bundleValue v i (bundle A j) = 0 :=
          le_antisymm hscore_le hscore_nonneg
        have ha_lt_S : v i g < bundleValue v i (bundle A j) := by
          have hc := hcontra g hgmem
          linarith [hc, hx_nonneg]
        have hlt1 : v i g * value v A j
            < bundleValue v i (bundle A j) * value v A j := by
          have hpos3 := mul_pos (sub_pos.mpr ha_lt_S) hypos
          linarith [hpos3]
        have heq : v i g * value v A j
            = bundleValue v i (bundle A j) * value v A j := by
          rw [hbj_eq] at hscore_eq
          linarith [hscore_eq]
        linarith [hlt1, heq]
      by_cases hxpos : 0 < value v A i
      · have hex := exchange_le hA hv hgmem hij hxpos hyb
        have hdiff : 0 < v i g * value v A j
            - v j g * (value v A i + v i g) := by
          have hc := hcontra g hgmem
          by_cases hbpos : 0 < v j g
          · have hmul : v j g * (value v A i + v i g)
                < v j g * bundleValue v i (bundle A j) := by
              have hpos2 := mul_pos hbpos (sub_pos.mpr hc)
              linarith [hpos2]
            linarith [hmul, hscore_nonneg]
          · have hb0 : v j g = 0 :=
              le_antisymm (not_lt.mp hbpos) (hv j g)
            rw [hb0, zero_mul, sub_zero]
            exact mul_pos ha_pos hypos
        have hlt : value v A i * value v A j
            < (value v A i + v i g) * (value v A j - v j g) := by
          have heq : (value v A i + v i g) * (value v A j - v j g)
              = value v A i * value v A j
                + (v i g * value v A j
                  - v j g * (value v A i + v i g)) := by ring
          rw [heq]
          linarith [hdiff]
        exact (not_le_of_gt hlt) hex
      · have hx0 : value v A i = 0 :=
          le_antisymm (not_lt.mp hxpos) hx_nonneg
        have hi_notmem : i ∉ positiveAgents v A := by
          intro hmem
          simp only [positiveAgents, Finset.mem_filter, Finset.mem_univ,
            true_and] at hmem
          rw [hx0] at hmem
          exact (lt_irrefl 0) hmem
        have hpos : positiveAgents v (transfer A g i)
            = insert i (positiveAgents v A) := by
          ext k
          simp only [positiveAgents, Finset.mem_filter, Finset.mem_univ,
            true_and, Finset.mem_insert]
          by_cases hki : k = i
          · subst hki
            constructor
            · intro _; exact Or.inl rfl
            · intro _
              rw [hvalBi, hx0, zero_add]
              exact ha_pos
          · by_cases hkj : k = j
            · subst hkj
              constructor
              · intro _; exact Or.inr hypos
              · intro _; rw [hvalBj]; exact hyb
            · rw [hval_other k hki hkj]
              simp [hki]
        have hcard : (positiveAgents v (transfer A g i)).card
            = (positiveAgents v A).card + 1 := by
          rw [hpos, Finset.card_insert_of_notMem hi_notmem]
        have hle := (hA (transfer A g i)).1
        omega
    · have hy0' : value v A j = 0 :=
        le_antisymm (not_lt.mp hypos) hy_nonneg
      have hb0_all : ∀ h ∈ bundle A j, v j h = 0 := by
        have hsum0 : ∑ h ∈ bundle A j, v j h = 0 := hy0'
        have h := (Finset.sum_eq_zero_iff_of_nonneg (f := v j)
          (s := bundle A j) (fun x _ => hv j x)).mp hsum0
        exact h
      have hb0 : v j g = 0 := hb0_all g hgmem
      have hvalBj0 : value v (transfer A g i) j = 0 := by
        rw [hvalBj, hy0', hb0, sub_self]
      by_cases hxpos : 0 < value v A i
      · have hpos : positiveAgents v (transfer A g i)
          = positiveAgents v A := by
          ext k
          simp only [positiveAgents, Finset.mem_filter, Finset.mem_univ,
            true_and]
          by_cases hki : k = i
          · subst hki
            rw [hvalBi]
            constructor
            · intro _; exact hxpos
            · intro _; linarith [hxpos, ha_pos]
          · by_cases hkj : k = j
            · subst hkj
              rw [hvalBj0, hy0']
            · rw [hval_other k hki hkj]
        have hcard : (positiveAgents v (transfer A g i)).card
            = (positiveAgents v A).card := by rw [hpos]
        have hle := (hA (transfer A g i)).2 hcard
        have hiS : i ∈ positiveAgents v A := by
          simp only [positiveAgents, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact hxpos
        have hAf : positiveWelfare v A
            = value v A i
              * ∏ k ∈ (positiveAgents v A).erase i, value v A k := by
          unfold positiveWelfare
          exact (Finset.mul_prod_erase (positiveAgents v A)
            (fun k => value v A k) hiS).symm
        have hBf : positiveWelfare v (transfer A g i)
            = value v (transfer A g i) i
              * ∏ k ∈ (positiveAgents v A).erase i,
                value v (transfer A g i) k := by
          unfold positiveWelfare
          rw [hpos]
          exact (Finset.mul_prod_erase (positiveAgents v A)
            (fun k => value v (transfer A g i) k) hiS).symm
        have hR : ∏ k ∈ (positiveAgents v A).erase i,
              value v (transfer A g i) k
            = ∏ k ∈ (positiveAgents v A).erase i, value v A k := by
          apply Finset.prod_congr rfl
          intro k hk
          simp only [Finset.mem_erase] at hk
          by_cases hkj : k = j
          · subst hkj
            rw [hvalBj0, hy0']
          · exact hval_other k hk.1 hkj
        have hRpos : 0 < ∏ k ∈ (positiveAgents v A).erase i,
            value v A k := by
          apply Finset.prod_pos
          intro k hk
          simp only [Finset.mem_erase] at hk
          have hkmem : k ∈ positiveAgents v A := hk.2
          simp only [positiveAgents, Finset.mem_filter, Finset.mem_univ,
            true_and] at hkmem
          exact hkmem
        have hlt : positiveWelfare v A
            < positiveWelfare v (transfer A g i) := by
          rw [hAf, hBf, hR, hvalBi]
          have hexpand : (value v A i + v i g)
                * ∏ k ∈ (positiveAgents v A).erase i, value v A k
              = value v A i * ∏ k ∈ (positiveAgents v A).erase i, value v A k
                + v i g * ∏ k ∈ (positiveAgents v A).erase i, value v A k := by
            ring
          rw [hexpand]
          have hapos := mul_pos ha_pos hRpos
          linarith [hapos]
        linarith [hle, hlt]
      · have hx0 : value v A i = 0 :=
          le_antisymm (not_lt.mp hxpos) hx_nonneg
        have hi_notmem : i ∉ positiveAgents v A := by
          intro hmem
          simp only [positiveAgents, Finset.mem_filter, Finset.mem_univ,
            true_and] at hmem
          rw [hx0] at hmem
          exact (lt_irrefl 0) hmem
        have hpos : positiveAgents v (transfer A g i)
            = insert i (positiveAgents v A) := by
          ext k
          simp only [positiveAgents, Finset.mem_filter, Finset.mem_univ,
            true_and, Finset.mem_insert]
          by_cases hki : k = i
          · subst hki
            constructor
            · intro _; exact Or.inl rfl
            · intro _
              rw [hvalBi, hx0, zero_add]
              exact ha_pos
          · by_cases hkj : k = j
            · subst hkj
              rw [hvalBj0, hy0']
              simp [Ne.symm hij]
            · rw [hval_other k hki hkj]
              simp [hki]
        have hcard : (positiveAgents v (transfer A g i)).card
            = (positiveAgents v A).card + 1 := by
          rw [hpos, Finset.card_insert_of_notMem hi_notmem]
        have hle := (hA (transfer A g i)).1
        omega

end

end MathlibExt.GameTheory.FairDivision.Indivisible
