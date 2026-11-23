/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic

import MathlibExt.Combinatorics.Schnirelmann
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.PSeries
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset
open scoped Pointwise

private lemma hw_card_fin_filter_modeq_le (b r v : ℕ) (hr : 0 < r) :
    #{x ∈ (Finset.univ : Finset (Fin b)) | x.val ≡ v [MOD r]} ≤ b / r + 1 := by
  have heq :
      #{x ∈ (Finset.univ : Finset (Fin b)) | x.val ≡ v [MOD r]} =
        #{x ∈ Finset.range b | x ≡ v [MOD r]} := by
    apply Finset.card_bij (fun x _ ↦ x.val)
    · simp
    · intro a _ b _ hab
      exact Fin.ext hab
    · intro x hx
      simp only [mem_filter, mem_range] at hx
      exact ⟨⟨x, hx.1⟩, by simp [hx.2]⟩
  rw [heq, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card b hr v]
  split <;> omega

private def hwCentered (M : ℕ) (x : Fin (2 * M + 1)) : ℤ :=
  x.val - M

private def hwToCentered (M : ℕ) (z : ℤ) (hz : z.natAbs ≤ M) : Fin (2 * M + 1) :=
  ⟨(z + M).toNat, by
    have hzle : z ≤ (z.natAbs : ℤ) := Int.le_natAbs
    have hnzle : -z ≤ ((-z).natAbs : ℤ) := Int.le_natAbs
    rw [Int.natAbs_neg] at hnzle
    have habs : (z.natAbs : ℤ) ≤ M := by exact_mod_cast hz
    have hlo : -(M : ℤ) ≤ z := by omega
    have hhi : z ≤ M := by omega
    have hz0 : 0 ≤ z + M := by omega
    have hz2 : z + M < 2 * M + 1 := by omega
    exact (Int.toNat_lt hz0).2 hz2⟩

private lemma hw_centered_toCentered (M : ℕ) (z : ℤ) (hz : z.natAbs ≤ M) :
    hwCentered M (hwToCentered M z hz) = z := by
  have hnzle : -z ≤ ((-z).natAbs : ℤ) := Int.le_natAbs
  rw [Int.natAbs_neg] at hnzle
  have habs : (z.natAbs : ℤ) ≤ M := by exact_mod_cast hz
  have hlo : -(M : ℤ) ≤ z := by omega
  have hz0 : 0 ≤ z + M := by omega
  simp [hwCentered, hwToCentered, Int.toNat_of_nonneg hz0]

private def hwPairFiber (M : ℕ) (h₁ h₂ n : ℤ) :
    Finset (Fin (2 * M + 1) × Fin (2 * M + 1)) :=
  Finset.univ.filter fun x ↦
    h₁ * hwCentered M x.1 + h₂ * hwCentered M x.2 = n

private lemma hw_pairFiber_card_le (M : ℕ) {h₁ h₂ n : ℤ} (hh₂ : h₂ ≠ 0) :
    #(hwPairFiber M h₁ h₂ n) ≤
      (2 * M + 1) / (h₂.natAbs / h₂.gcd h₁) + 1 := by
  let d := h₂.natAbs
  let g := d.gcd h₁.natAbs
  let r := d / g
  have hd : 0 < d := Int.natAbs_pos.mpr hh₂
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hd
  have hgd : g ∣ d := by
    dsimp [g, d]
    exact Nat.gcd_dvd_left _ _
  have hgle : g ≤ d := Nat.le_of_dvd hd hgd
  have hr : 0 < r := Nat.div_pos hgle hg
  by_cases hS : (hwPairFiber M h₁ h₂ n).Nonempty
  · let w := hS.choose
    have hw := hS.choose_spec
    have hproj : Set.InjOn Prod.fst {x | x ∈ hwPairFiber M h₁ h₂ n} := by
      intro x hx y hy hxy
      apply Prod.ext hxy
      have hx' : h₁ * hwCentered M x.1 + h₂ * hwCentered M x.2 = n := by
        simpa [hwPairFiber] using hx
      have hy' : h₁ * hwCentered M y.1 + h₂ * hwCentered M y.2 = n := by
        simpa [hwPairFiber] using hy
      rw [hxy] at hx'
      have hm : h₂ * hwCentered M x.2 = h₂ * hwCentered M y.2 := by
        linarith [hy']
      have hc := Int.eq_of_mul_eq_mul_left hh₂ hm
      apply Fin.ext
      dsimp [hwCentered] at hc
      omega
    have hcard : #(hwPairFiber M h₁ h₂ n) =
        #((hwPairFiber M h₁ h₂ n).image Prod.fst) := by
      exact (card_image_iff.mpr hproj).symm
    have hsub : (hwPairFiber M h₁ h₂ n).image Prod.fst ⊆
        (Finset.univ.filter fun x : Fin (2 * M + 1) ↦ x.val ≡ w.1.val [MOD r]) := by
      intro x hx
      rcases mem_image.mp hx with ⟨z, hz, rfl⟩
      simp only [hwPairFiber, mem_filter, mem_univ, true_and] at hz hw
      change h₁ * hwCentered M w.1 + h₂ * hwCentered M w.2 = n at hw
      simp only [mem_filter, mem_univ, true_and]
      have hmul : h₁ * hwCentered M z.1 ≡ h₁ * hwCentered M w.1 [ZMOD (d : ℤ)] := by
        rw [Int.modEq_iff_dvd]
        have heq : h₁ * hwCentered M w.1 - h₁ * hwCentered M z.1 =
            h₂ * (hwCentered M z.2 - hwCentered M w.2) := by
          linear_combination hw - hz
        rw [heq]
        exact dvd_mul_of_dvd_left (by simp [d]) _
      have hcancel := Int.ModEq.cancel_left_div_gcd (m := (d : ℤ))
        (a := hwCentered M z.1) (b := hwCentered M w.1) (c := h₁)
        (by exact_mod_cast hd) (by simpa [mul_comm] using hmul)
      have hmod : hwCentered M z.1 ≡ hwCentered M w.1 [ZMOD (r : ℤ)] := by
        simpa [r, d, g, Int.gcd_eq_natAbs, Int.natCast_ediv,
          Int.natCast_natAbs, Int.natAbs_abs] using hcancel
      have hmod' : (z.1.val : ℤ) ≡ w.1.val [ZMOD (r : ℤ)] := by
        simpa [hwCentered] using hmod.add_right (M : ℤ)
      exact Int.natCast_modEq_iff.mp hmod'
    rw [hcard]
    exact (card_le_card hsub).trans (hw_card_fin_filter_modeq_le _ _ _ hr)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, card_empty]
    exact Nat.zero_le _

private lemma hw_pairFiber_card_mul_le (M : ℕ) {h₁ h₂ n : ℤ} (hh₂ : h₂ ≠ 0)
    (hh₂M : h₂.natAbs ≤ M) :
    #(hwPairFiber M h₁ h₂ n) * h₂.natAbs ≤
      4 * (M + 1) * h₂.gcd h₁ := by
  let d := h₂.natAbs
  let g := d.gcd h₁.natAbs
  let r := d / g
  have hd : 0 < d := Int.natAbs_pos.mpr hh₂
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hd
  have hgd : g ∣ d := Nat.gcd_dvd_left _ _
  have hdr : r * g = d := by
    rw [mul_comm, Nat.mul_div_cancel' hgd]
  have hrle : r ≤ M := (Nat.div_le_self _ _).trans hh₂M
  have hdiv := Nat.div_mul_le_self (2 * M + 1) r
  have hcard := hw_pairFiber_card_le M (h₁ := h₁) (n := n) hh₂
  change #(hwPairFiber M h₁ h₂ n) * d ≤ 4 * (M + 1) * g
  change #(hwPairFiber M h₁ h₂ n) ≤ (2 * M + 1) / r + 1 at hcard
  nlinarith

private lemma hw_pairFiber_swap (M : ℕ) (h₁ h₂ n : ℤ) :
    #(hwPairFiber M h₁ h₂ n) = #(hwPairFiber M h₂ h₁ n) := by
  apply Finset.card_bij (fun p _ ↦ (p.2, p.1))
  · intro p hp
    simp only [hwPairFiber, mem_filter, mem_univ, true_and] at hp ⊢
    linarith
  · intro p hp q hq hpq
    exact Prod.ext (congrArg Prod.snd hpq) (congrArg Prod.fst hpq)
  · intro p hp
    refine ⟨(p.2, p.1), ?_, by simp⟩
    simp only [hwPairFiber, mem_filter, mem_univ, true_and] at hp ⊢
    linarith

private lemma hw_pairFiber_card_mul_max_le (M : ℕ) {h₁ h₂ n : ℤ}
    (hh₁ : h₁ ≠ 0) (hh₂ : h₂ ≠ 0) (hh₁M : h₁.natAbs ≤ M) (hh₂M : h₂.natAbs ≤ M) :
    #(hwPairFiber M h₁ h₂ n) * max h₁.natAbs h₂.natAbs ≤
      4 * (M + 1) * h₁.gcd h₂ := by
  rcases max_choice h₁.natAbs h₂.natAbs with h | h
  · rw [h, hw_pairFiber_swap]
    simpa [Int.gcd_comm] using
      hw_pairFiber_card_mul_le M (h₁ := h₂) (h₂ := h₁) (n := n) hh₁ hh₁M
  · rw [h]
    simpa [Int.gcd_comm] using
      hw_pairFiber_card_mul_le M (h₁ := h₁) (h₂ := h₂) (n := n) hh₂ hh₂M

private lemma hw_card_pairs_max_eq_le (L t : ℕ) :
    #({p ∈ (Finset.Icc 1 L).product (Finset.Icc 1 L) | max p.1 p.2 = t}) ≤ 2 * t := by
  let U := ({t} : Finset ℕ).product (Finset.Icc 1 t)
  let V := (Finset.Icc 1 t).product ({t} : Finset ℕ)
  have hsub : {p ∈ (Finset.Icc 1 L).product (Finset.Icc 1 L) | max p.1 p.2 = t} ⊆
      U ∪ V := by
    rintro ⟨a, b⟩ hp
    rcases mem_filter.mp hp with ⟨hpbox, hmax⟩
    rcases mem_product.mp hpbox with ⟨ha, hb⟩
    have ha' := mem_Icc.mp ha
    have hb' := mem_Icc.mp hb
    rcases max_choice a b with h | h
    · have hat : a = t := h.symm.trans hmax
      apply mem_union.mpr
      left
      apply mem_product.mpr
      exact ⟨by simp [hat], mem_Icc.mpr ⟨hb'.1, by omega⟩⟩
    · have hbt : b = t := h.symm.trans hmax
      apply mem_union.mpr
      right
      apply mem_product.mpr
      exact ⟨mem_Icc.mpr ⟨ha'.1, by omega⟩, by simp [hbt]⟩
  calc
    #({p ∈ (Finset.Icc 1 L).product (Finset.Icc 1 L) | max p.1 p.2 = t}) ≤ #(U ∪ V) :=
      card_le_card hsub
    _ ≤ #U + #V := card_union_le _ _
    _ = 2 * t := by simp [U, V, Nat.card_Icc]; omega

private lemma hw_sum_inv_max_le (L : ℕ) :
    (∑ a ∈ Finset.Icc 1 L, ∑ b ∈ Finset.Icc 1 L,
      ((max a b : ℕ) : ℝ)⁻¹) ≤ 2 * L := by
  let P := (Finset.Icc 1 L).product (Finset.Icc 1 L)
  have hmap : ∀ p ∈ P, max p.1 p.2 ∈ Finset.Icc 1 L := by
    rintro ⟨a, b⟩ hp
    have hp' := mem_product.mp (show (a, b) ∈
      (Finset.Icc 1 L).product (Finset.Icc 1 L) by simpa [P] using hp)
    rw [mem_Icc]
    have ha := mem_Icc.mp hp'.1
    have hb := mem_Icc.mp hp'.2
    omega
  rw [show (∑ a ∈ Finset.Icc 1 L, ∑ b ∈ Finset.Icc 1 L,
      ((max a b : ℕ) : ℝ)⁻¹) =
      ∑ p ∈ P, ((max p.1 p.2 : ℕ) : ℝ)⁻¹ by simp [P, Finset.sum_product]]
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun p : ℕ × ℕ ↦ ((max p.1 p.2 : ℕ) : ℝ)⁻¹)]
  calc
    (∑ t ∈ Finset.Icc 1 L, ∑ p ∈ P with max p.1 p.2 = t,
        ((max p.1 p.2 : ℕ) : ℝ)⁻¹) =
        ∑ t ∈ Finset.Icc 1 L,
          (#({p ∈ P | max p.1 p.2 = t}) : ℝ) / t := by
      apply sum_congr rfl
      intro t ht
      rw [sum_congr rfl (fun p hp ↦ by rw [(mem_filter.mp hp).2])]
      simp [div_eq_mul_inv]
    _ ≤ ∑ _t ∈ Finset.Icc 1 L, (2 : ℝ) := by
      gcongr with t ht
      have ht0 : (0 : ℝ) < t := by exact_mod_cast (mem_Icc.mp ht).1
      rw [div_le_iff₀ ht0]
      exact_mod_cast hw_card_pairs_max_eq_le L t
    _ = 2 * L := by simp [Nat.card_Icc]; ring

private lemma hw_sum_common_divisor_inv_max_le (H d : ℕ) (hd : 0 < d) :
    (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H,
      if d ∣ a ∧ d ∣ b then (d : ℝ) / max a b else 0) ≤
        2 * H * (d : ℝ)⁻¹ := by
  let P := (Finset.Icc 1 H).product (Finset.Icc 1 H)
  let S := P.filter fun p ↦ d ∣ p.1 ∧ d ∣ p.2
  let Q := (Finset.Icc 1 (H / d)).product (Finset.Icc 1 (H / d))
  let f : ℕ × ℕ → ℕ × ℕ := fun p ↦ (p.1 / d, p.2 / d)
  have hf_inj : Set.InjOn f {p | p ∈ S} := by
    intro p hp q hq hpq
    have hp' : d ∣ p.1 ∧ d ∣ p.2 := by simpa [S] using (mem_filter.mp hp).2
    have hq' : d ∣ q.1 ∧ d ∣ q.2 := by simpa [S] using (mem_filter.mp hq).2
    apply Prod.ext
    · simpa [f, Nat.mul_div_cancel' hp'.1, Nat.mul_div_cancel' hq'.1] using
        congrArg (fun z ↦ d * z.1) hpq
    · simpa [f, Nat.mul_div_cancel' hp'.2, Nat.mul_div_cancel' hq'.2] using
        congrArg (fun z ↦ d * z.2) hpq
  have hf_map : S.image f ⊆ Q := by
    intro q hq
    rcases mem_image.mp hq with ⟨p, hp, rfl⟩
    have hpP := (mem_filter.mp hp).1
    have hpD := (mem_filter.mp hp).2
    have hpbox := mem_product.mp hpP
    have hp1 := mem_Icc.mp hpbox.1
    have hp2 := mem_Icc.mp hpbox.2
    apply mem_product.mpr
    constructor <;> apply mem_Icc.mpr
    · exact ⟨Nat.div_pos (Nat.le_of_dvd hp1.1 hpD.1) hd,
        Nat.div_le_div_right hp1.2⟩
    · exact ⟨Nat.div_pos (Nat.le_of_dvd hp2.1 hpD.2) hd,
        Nat.div_le_div_right hp2.2⟩
  have hweight : ∀ p ∈ S,
      (d : ℝ) / max p.1 p.2 = ((max (f p).1 (f p).2 : ℕ) : ℝ)⁻¹ := by
    rintro ⟨a, b⟩ hp
    have hpD := (mem_filter.mp hp).2
    obtain ⟨u, rfl⟩ := hpD.1
    obtain ⟨v, rfl⟩ := hpD.2
    simp only [f]
    rw [Nat.mul_div_cancel_left _ hd, Nat.mul_div_cancel_left _ hd]
    rw [max_mul_mul_left]
    push_cast
    field_simp
  rw [show (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H,
      if d ∣ a ∧ d ∣ b then (d : ℝ) / max a b else 0) =
      ∑ p ∈ S, (d : ℝ) / max p.1 p.2 by
        rw [show S = P.filter (fun p ↦ d ∣ p.1 ∧ d ∣ p.2) from rfl, sum_filter]
        rw [show P = (Finset.Icc 1 H).product (Finset.Icc 1 H) from rfl]
        exact (Finset.sum_product (Finset.Icc 1 H) (Finset.Icc 1 H)
          (fun p ↦ if d ∣ p.1 ∧ d ∣ p.2 then (d : ℝ) / max p.1 p.2 else 0)).symm]
  calc
    (∑ p ∈ S, (d : ℝ) / max p.1 p.2) =
        ∑ q ∈ S.image f, ((max q.1 q.2 : ℕ) : ℝ)⁻¹ := by
      rw [Finset.sum_image hf_inj]
      exact sum_congr rfl hweight
    _ ≤ ∑ q ∈ Q, ((max q.1 q.2 : ℕ) : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hf_map (by
        intro q hq hnot
        exact inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ 2 * (H / d : ℕ) := by
      simpa [Q, Finset.sum_product] using hw_sum_inv_max_le (H / d)
    _ ≤ 2 * H * (d : ℝ)⁻¹ := by
      rw [mul_assoc, ← div_eq_mul_inv]
      gcongr
      exact Nat.cast_div_le

private noncomputable def hwSigmaInv (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (d : ℝ)⁻¹

private lemma hw_sum_gcd_inv_max_le (H n : ℕ) (hn : n ≠ 0) :
    (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H,
      if a.gcd b ∣ n then (a.gcd b : ℝ) / max a b else 0) ≤
        2 * H * hwSigmaInv n := by
  calc
    (∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H,
      if a.gcd b ∣ n then (a.gcd b : ℝ) / max a b else 0) ≤
        ∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H,
          ∑ d ∈ n.divisors,
            if d ∣ a ∧ d ∣ b then (d : ℝ) / max a b else 0 := by
      gcongr with a ha b hb
      split_ifs with hg
      · have ha0 : 0 < a := (mem_Icc.mp ha).1
        have hg0 : 0 < a.gcd b := Nat.gcd_pos_of_pos_left _ ha0
        have hgmem : a.gcd b ∈ n.divisors := Nat.mem_divisors.mpr ⟨hg, hn⟩
        simpa [Nat.gcd_dvd_left, Nat.gcd_dvd_right] using
          (Finset.single_le_sum (s := n.divisors)
            (f := fun d ↦ if d ∣ a ∧ d ∣ b then (d : ℝ) / max a b else 0)
            (fun d hd ↦ by positivity) hgmem)
      · positivity
    _ = ∑ d ∈ n.divisors, ∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H,
          if d ∣ a ∧ d ∣ b then (d : ℝ) / max a b else 0 := by
      simp_rw [Finset.sum_comm (s := Finset.Icc 1 H) (t := n.divisors)]
    _ ≤ ∑ d ∈ n.divisors, 2 * H * (d : ℝ)⁻¹ := by
      gcongr with d hd
      exact hw_sum_common_divisor_inv_max_le H d (Nat.pos_of_mem_divisors hd)
    _ = 2 * H * hwSigmaInv n := by
      simp [hwSigmaInv, Finset.mul_sum]

private lemma hw_summable_inv_sq : Summable (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) := by
  have h := Real.summable_one_div_nat_pow.mpr (show 1 < 2 by norm_num)
  simpa only [one_div] using h

private noncomputable def hwZetaTwo : ℝ :=
  ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹

private lemma hw_sum_inv_sq_le_zetaTwo (s : Finset ℕ) :
    (∑ n ∈ s, ((n : ℝ) ^ 2)⁻¹) ≤ hwZetaTwo := by
  exact hw_summable_inv_sq.sum_le_tsum s (by
    intro i hi
    exact inv_nonneg.mpr (sq_nonneg _))

private lemma hw_zetaTwo_nonneg : 0 ≤ hwZetaTwo := by
  exact tsum_nonneg fun _ ↦ by positivity

private lemma hw_sum_multiples_inv_sq_le (H g : ℕ) (hg : 0 < g) :
    (∑ d ∈ Finset.Icc 1 H with g ∣ d, ((d : ℝ) ^ 2)⁻¹) ≤
      ((g : ℝ) ^ 2)⁻¹ * hwZetaTwo := by
  let S := (Finset.Icc 1 H).filter fun d ↦ g ∣ d
  let Q := Finset.Icc 1 (H / g)
  let f : ℕ → ℕ := fun d ↦ d / g
  have hf_inj : Set.InjOn f {d | d ∈ S} := by
    intro d hd e he hde
    have hd' : d ∈ S := hd
    have he' : e ∈ S := he
    have hdd : g ∣ d := (mem_filter.mp hd').2
    have hed : g ∣ e := (mem_filter.mp he').2
    simpa [f, Nat.mul_div_cancel' hdd, Nat.mul_div_cancel' hed] using
      congrArg (fun z ↦ g * z) hde
  have hf_map : S.image f ⊆ Q := by
    intro q hq
    rcases mem_image.mp hq with ⟨d, hdS, rfl⟩
    have hdD := (mem_filter.mp hdS).2
    have hdI := mem_Icc.mp (mem_filter.mp hdS).1
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hdI.1 hdD) hg,
      Nat.div_le_div_right hdI.2⟩
  have hweight : ∀ d ∈ S,
      ((d : ℝ) ^ 2)⁻¹ = ((g : ℝ) ^ 2)⁻¹ * (((f d : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro d hdS
    have hdD := (mem_filter.mp hdS).2
    obtain ⟨u, rfl⟩ := hdD
    rw [show f (g * u) = u by simp [f, Nat.mul_div_cancel_left _ hg]]
    push_cast
    simp [mul_pow, mul_comm]
  change (∑ d ∈ S, ((d : ℝ) ^ 2)⁻¹) ≤ ((g : ℝ) ^ 2)⁻¹ * hwZetaTwo
  calc
    (∑ d ∈ S, ((d : ℝ) ^ 2)⁻¹) =
        ∑ q ∈ S.image f, ((g : ℝ) ^ 2)⁻¹ * ((q : ℝ) ^ 2)⁻¹ := by
      rw [Finset.sum_image hf_inj]
      exact sum_congr rfl hweight
    _ ≤ ∑ q ∈ Q, ((g : ℝ) ^ 2)⁻¹ * ((q : ℝ) ^ 2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hf_map (by
        intro q hq hnot
        positivity)
    _ = ((g : ℝ) ^ 2)⁻¹ * ∑ q ∈ Q, ((q : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ ((g : ℝ) ^ 2)⁻¹ * hwZetaTwo := by
      gcongr
      exact hw_sum_inv_sq_le_zetaTwo Q

private lemma hw_card_common_multiples (x d e : ℕ) :
    #({n ∈ Finset.Icc 1 x | d ∣ n ∧ e ∣ n}) = x / d.lcm e := by
  rw [← Nat.card_multiples' x (d.lcm e)]
  congr 1
  ext n
  simp only [Nat.lcm_dvd_iff, mem_filter, mem_Icc, mem_range, Nat.lt_succ_iff]
  omega

private lemma hw_sum_common_divisor_kernel (x g : ℕ) :
    (∑ d ∈ Finset.Icc 1 x, ∑ e ∈ Finset.Icc 1 x,
      if g ∣ d ∧ g ∣ e then
        (g : ℝ) * ((d : ℝ) ^ 2)⁻¹ * ((e : ℝ) ^ 2)⁻¹ else 0) =
      (g : ℝ) * (∑ d ∈ Finset.Icc 1 x with g ∣ d, ((d : ℝ) ^ 2)⁻¹) ^ 2 := by
  rw [pow_two, Finset.sum_mul_sum]
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_filter]
  apply sum_congr rfl
  intro d hd
  by_cases hdg : g ∣ d
  · simp only [hdg, true_and, ite_true]
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro e he
    by_cases heg : g ∣ e <;> simp [heg, mul_assoc]
  · simp [hdg]

private lemma hw_divisor_kernel_le (x : ℕ) :
    (∑ d ∈ Finset.Icc 1 x, ∑ e ∈ Finset.Icc 1 x,
      ((d : ℝ) * e * d.lcm e)⁻¹) ≤ hwZetaTwo ^ 3 := by
  let D := Finset.Icc 1 x
  calc
    (∑ d ∈ D, ∑ e ∈ D, ((d : ℝ) * e * d.lcm e)⁻¹) =
        ∑ d ∈ D, ∑ e ∈ D,
          (d.gcd e : ℝ) * ((d : ℝ) ^ 2)⁻¹ * ((e : ℝ) ^ 2)⁻¹ := by
      apply sum_congr rfl
      intro d hd
      apply sum_congr rfl
      intro e he
      have hdI : d ∈ Finset.Icc 1 x := by simpa [D] using hd
      have heI : e ∈ Finset.Icc 1 x := by simpa [D] using he
      have hdPos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hdI).1
      have hePos : 0 < e := lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp heI).1
      have hdNat : d ≠ 0 := hdPos.ne'
      have heNat : e ≠ 0 := hePos.ne'
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hdNat
      have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast heNat
      have hl0 : (d.lcm e : ℝ) ≠ 0 := by
        exact_mod_cast Nat.lcm_ne_zero hdNat heNat
      rw [pow_two, pow_two]
      field_simp [hd0, he0, hl0]
      exact_mod_cast (Nat.gcd_mul_lcm d e).symm.trans (mul_comm _ _)
    _ ≤ ∑ d ∈ D, ∑ e ∈ D, ∑ g ∈ D,
          if g ∣ d ∧ g ∣ e then
            (g : ℝ) * ((d : ℝ) ^ 2)⁻¹ * ((e : ℝ) ^ 2)⁻¹ else 0 := by
      gcongr with d hd e he
      have hg0 : 0 < d.gcd e := Nat.gcd_pos_of_pos_left _ (mem_Icc.mp hd).1
      have hgmem : d.gcd e ∈ D := mem_Icc.mpr ⟨hg0,
        (Nat.gcd_le_left _ (mem_Icc.mp hd).1).trans (mem_Icc.mp hd).2⟩
      simpa [Nat.gcd_dvd_left, Nat.gcd_dvd_right] using
        (Finset.single_le_sum (s := D)
          (f := fun g ↦ if g ∣ d ∧ g ∣ e then
            (g : ℝ) * ((d : ℝ) ^ 2)⁻¹ * ((e : ℝ) ^ 2)⁻¹ else 0)
          (fun g hg ↦ by positivity) hgmem)
    _ = ∑ g ∈ D, (g : ℝ) *
          (∑ d ∈ D with g ∣ d, ((d : ℝ) ^ 2)⁻¹) ^ 2 := by
      have hreorder :
          (∑ d ∈ D, ∑ e ∈ D, ∑ g ∈ D,
            if g ∣ d ∧ g ∣ e then
              (g : ℝ) * ((d : ℝ) ^ 2)⁻¹ * ((e : ℝ) ^ 2)⁻¹ else 0) =
          ∑ g ∈ D, ∑ d ∈ D, ∑ e ∈ D,
            if g ∣ d ∧ g ∣ e then
              (g : ℝ) * ((d : ℝ) ^ 2)⁻¹ * ((e : ℝ) ^ 2)⁻¹ else 0 := by
        calc
          _ = ∑ d ∈ D, ∑ g ∈ D, ∑ e ∈ D,
              if g ∣ d ∧ g ∣ e then
                (g : ℝ) * ((d : ℝ) ^ 2)⁻¹ * ((e : ℝ) ^ 2)⁻¹ else 0 := by
            apply sum_congr rfl
            intro d hd
            exact Finset.sum_comm
          _ = _ := Finset.sum_comm
      rw [hreorder]
      apply sum_congr rfl
      intro g hg
      simpa [D] using hw_sum_common_divisor_kernel x g
    _ ≤ ∑ g ∈ D, (g : ℝ) * (((g : ℝ) ^ 2)⁻¹ * hwZetaTwo) ^ 2 := by
      gcongr with g hg
      exact hw_sum_multiples_inv_sq_le x g (mem_Icc.mp hg).1
    _ ≤ ∑ g ∈ D, ((g : ℝ) ^ 2)⁻¹ * hwZetaTwo ^ 2 := by
      apply sum_le_sum
      intro g hg
      have hgI : g ∈ Finset.Icc 1 x := by simpa [D] using hg
      have hgPos : 0 < g := lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hgI).1
      have hgNat : g ≠ 0 := hgPos.ne'
      have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast hgNat
      have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (mem_Icc.mp hgI).1
      have heq : (g : ℝ) * (((g : ℝ) ^ 2)⁻¹ * hwZetaTwo) ^ 2 =
          (g : ℝ)⁻¹ * (((g : ℝ) ^ 2)⁻¹ * hwZetaTwo ^ 2) := by
        field_simp [hg0]
      rw [heq]
      calc
        (g : ℝ)⁻¹ * (((g : ℝ) ^ 2)⁻¹ * hwZetaTwo ^ 2) ≤
            1 * (((g : ℝ) ^ 2)⁻¹ * hwZetaTwo ^ 2) :=
          mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hg1) (by positivity)
        _ = ((g : ℝ) ^ 2)⁻¹ * hwZetaTwo ^ 2 := one_mul _
    _ ≤ hwZetaTwo * hwZetaTwo ^ 2 := by
      rw [← Finset.sum_mul]
      gcongr
      exact hw_sum_inv_sq_le_zetaTwo D
    _ = hwZetaTwo ^ 3 := by ring

private lemma hw_sigmaInv_eq_sum_dvd {x n : ℕ} (hn : n ∈ Finset.Icc 1 x) :
    hwSigmaInv n = ∑ d ∈ Finset.Icc 1 x, if d ∣ n then (d : ℝ)⁻¹ else 0 := by
  have hnPos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hn).1
  have hn0 : n ≠ 0 := hnPos.ne'
  have hdiv : n.divisors = (Finset.Icc 1 x).filter fun d ↦ d ∣ n := by
    ext d
    rw [Nat.mem_divisors]
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hnPos,
        (Nat.le_of_dvd hnPos hd).trans (mem_Icc.mp hn).2⟩, hd⟩
    · rintro ⟨⟨_, _⟩, hd⟩
      exact ⟨hd, hn0⟩
  rw [hwSigmaInv, hdiv, sum_filter]

private lemma hw_sigmaInv_sq_sum_le (x : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, hwSigmaInv n ^ 2) ≤ x * hwZetaTwo ^ 3 := by
  let D := Finset.Icc 1 x
  have hexpand :
      (∑ n ∈ D, hwSigmaInv n ^ 2) =
        ∑ d ∈ D, ∑ e ∈ D,
          (#({n ∈ D | d ∣ n ∧ e ∣ n}) : ℝ) *
            (d : ℝ)⁻¹ * (e : ℝ)⁻¹ := by
    have hnexpand : ∀ n ∈ D,
        hwSigmaInv n ^ 2 = ∑ d ∈ D, ∑ e ∈ D,
          (if d ∣ n then (d : ℝ)⁻¹ else 0) *
            (if e ∣ n then (e : ℝ)⁻¹ else 0) := by
      intro n hn
      rw [hw_sigmaInv_eq_sum_dvd hn, pow_two, Finset.sum_mul_sum]
    rw [sum_congr rfl hnexpand]
    have hreorder :
        (∑ n ∈ D, ∑ d ∈ D, ∑ e ∈ D,
          (if d ∣ n then (d : ℝ)⁻¹ else 0) *
            (if e ∣ n then (e : ℝ)⁻¹ else 0)) =
        ∑ d ∈ D, ∑ e ∈ D, ∑ n ∈ D,
          (if d ∣ n then (d : ℝ)⁻¹ else 0) *
            (if e ∣ n then (e : ℝ)⁻¹ else 0) := by
      calc
        _ = ∑ d ∈ D, ∑ n ∈ D, ∑ e ∈ D,
            (if d ∣ n then (d : ℝ)⁻¹ else 0) *
              (if e ∣ n then (e : ℝ)⁻¹ else 0) := Finset.sum_comm
        _ = _ := by
          apply sum_congr rfl
          intro d hd
          exact Finset.sum_comm
    rw [hreorder]
    apply sum_congr rfl
    intro d hd
    apply sum_congr rfl
    intro e he
    calc
      (∑ n ∈ D, (if d ∣ n then (d : ℝ)⁻¹ else 0) *
          (if e ∣ n then (e : ℝ)⁻¹ else 0)) =
          ∑ n ∈ D with d ∣ n ∧ e ∣ n, (d : ℝ)⁻¹ * (e : ℝ)⁻¹ := by
        rw [sum_filter]
        apply sum_congr rfl
        intro n hn
        by_cases hdvd : d ∣ n <;> by_cases hevd : e ∣ n <;> simp [hdvd, hevd]
      _ = (#({n ∈ D | d ∣ n ∧ e ∣ n}) : ℝ) *
          (d : ℝ)⁻¹ * (e : ℝ)⁻¹ := by simp; ring
  rw [hexpand]
  calc
    (∑ d ∈ D, ∑ e ∈ D,
      (#({n ∈ D | d ∣ n ∧ e ∣ n}) : ℝ) * (d : ℝ)⁻¹ * (e : ℝ)⁻¹) ≤
        ∑ d ∈ D, ∑ e ∈ D, (x : ℝ) * ((d : ℝ) * e * d.lcm e)⁻¹ := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro e he
      have hdI : d ∈ Finset.Icc 1 x := by simpa [D] using hd
      have heI : e ∈ Finset.Icc 1 x := by simpa [D] using he
      have hdPos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hdI).1
      have hePos : 0 < e := lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp heI).1
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hdPos.ne'
      have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast hePos.ne'
      have hl0 : (d.lcm e : ℝ) ≠ 0 := by
        exact_mod_cast Nat.lcm_ne_zero hdPos.ne' hePos.ne'
      rw [hw_card_common_multiples x d e]
      calc
        ((x / d.lcm e : ℕ) : ℝ) * (d : ℝ)⁻¹ * (e : ℝ)⁻¹ ≤
            ((x : ℝ) / d.lcm e) * (d : ℝ)⁻¹ * (e : ℝ)⁻¹ := by
          gcongr
          exact Nat.cast_div_le
        _ = (x : ℝ) * ((d : ℝ) * e * d.lcm e)⁻¹ := by
          field_simp [hd0, he0, hl0]
    _ = (x : ℝ) * (∑ d ∈ D, ∑ e ∈ D,
        ((d : ℝ) * e * d.lcm e)⁻¹) := by
      simp_rw [Finset.mul_sum]
    _ ≤ (x : ℝ) * hwZetaTwo ^ 3 := by
      gcongr
      simpa [D] using hw_divisor_kernel_le x

private lemma hw_sum_fin_succ {R : Type*} [AddCommMonoid R] (H : ℕ) (f : ℕ → R) :
    (∑ i : Fin H, f (i.val + 1)) = ∑ a ∈ Finset.Icc 1 H, f a := by
  rw [Fin.sum_univ_eq_sum_range (fun n ↦ f (n + 1)) H]
  rw [show Finset.range H = Finset.Ico 0 H by simp]
  rw [Finset.sum_Ico_add' f 0 H 1]
  congr 1

private abbrev hwSigned (H : ℕ) := Fin 2 × Fin H

private def hwSignedVal (H : ℕ) (h : hwSigned H) : ℤ :=
  if h.1 = 0 then (h.2.val + 1 : ℕ) else -((h.2.val + 1 : ℕ) : ℤ)

@[simp] private lemma hw_signedVal_natAbs (H : ℕ) (h : hwSigned H) :
    (hwSignedVal H h).natAbs = h.2.val + 1 := by
  rcases h with ⟨s, i⟩
  fin_cases s
  · change (((i.val + 1 : ℕ) : ℤ)).natAbs = i.val + 1
    exact Int.natAbs_natCast _
  · change (-((i.val + 1 : ℕ) : ℤ)).natAbs = i.val + 1
    rw [Int.natAbs_neg]
    exact Int.natAbs_natCast _

private lemma hw_signedVal_ne_zero (H : ℕ) (h : hwSigned H) : hwSignedVal H h ≠ 0 := by
  apply Int.natAbs_pos.mp
  rw [hw_signedVal_natAbs]
  omega

private lemma hw_signedVal_natAbs_le (H : ℕ) (h : hwSigned H) :
    (hwSignedVal H h).natAbs ≤ H := by
  rw [hw_signedVal_natAbs]
  omega

private def hwSignedToCentered (H : ℕ) (h : hwSigned H) : Fin (2 * H + 1) :=
  if h.1 = 0 then
    ⟨H + (h.2.val + 1), by omega⟩
  else
    ⟨H - (h.2.val + 1), by omega⟩

private lemma hw_centered_signedToCentered (H : ℕ) (h : hwSigned H) :
    hwCentered H (hwSignedToCentered H h) = hwSignedVal H h := by
  rcases h with ⟨s, i⟩
  fin_cases s <;> simp [hwSignedToCentered, hwSignedVal, hwCentered]

private def hwCenteredToSigned
    (H : ℕ) (x : {x : Fin (2 * H + 1) // hwCentered H x ≠ 0}) : hwSigned H :=
  if hx : H < x.1.val then
    (0, ⟨x.1.val - H - 1, by omega⟩)
  else
    (1, ⟨H - x.1.val - 1, by
      have hne : x.1.val ≠ H := by
        intro h
        apply x.2
        simp [hwCentered, h]
      omega⟩)

private def hwSignedEquivCentered (H : ℕ) :
    hwSigned H ≃ {x : Fin (2 * H + 1) // hwCentered H x ≠ 0} where
  toFun h := ⟨hwSignedToCentered H h, by
    rw [hw_centered_signedToCentered]
    exact hw_signedVal_ne_zero H h⟩
  invFun := hwCenteredToSigned H
  left_inv h := by
    rcases h with ⟨s, i⟩
    fin_cases s
    · apply Prod.ext
      · apply Fin.ext
        simp [hwCenteredToSigned, hwSignedToCentered]
      · apply Fin.ext
        simp [hwCenteredToSigned, hwSignedToCentered]
    · have hi := i.isLt
      have hnot : ¬H < H - (i.val + 1) := by omega
      apply Prod.ext
      · apply Fin.ext
        simp [hwCenteredToSigned, hwSignedToCentered, hnot]
      · apply Fin.ext
        simp [hwCenteredToSigned, hwSignedToCentered, hnot]
        omega
  right_inv x := by
    apply Subtype.ext
    apply Fin.ext
    by_cases hx : H < x.1.val
    · simp [hwCenteredToSigned, hwSignedToCentered, hx]
      omega
    · have hne : x.1.val ≠ H := by
        intro h
        apply x.2
        simp [hwCentered, h]
      simp [hwCenteredToSigned, hwSignedToCentered, hx]
      omega

private def hwLinearFiber (M : ℕ) (c : Fin 4 → ℤ) :
    Finset (Fin 4 → Fin (2 * M + 1)) :=
  Finset.univ.filter fun m ↦ ∑ i, c i * hwCentered M (m i) = 0

private lemma hw_linearFiber_card_le (M : ℕ) (c : Fin 4 → ℤ)
    {i : Fin 4} (hi : c i ≠ 0) : #(hwLinearFiber M c) ≤ (2 * M + 1) ^ 3 := by
  let proj : (Fin 4 → Fin (2 * M + 1)) → (Fin 3 → Fin (2 * M + 1)) :=
    fun m j ↦ m (i.succAbove j)
  have hinj : Set.InjOn proj {m | m ∈ hwLinearFiber M c} := by
    intro x hx y hy hxy
    funext j
    by_cases hji : j = i
    · subst j
      have hxsum : ∑ j, c j * hwCentered M (x j) = 0 := by
        simpa [hwLinearFiber] using hx
      have hysum : ∑ j, c j * hwCentered M (y j) = 0 := by
        simpa [hwLinearFiber] using hy
      rw [Fin.sum_univ_succAbove (fun j ↦ c j * hwCentered M (x j)) i] at hxsum
      rw [Fin.sum_univ_succAbove (fun j ↦ c j * hwCentered M (y j)) i] at hysum
      have htail :
          (∑ j : Fin 3, c (i.succAbove j) * hwCentered M (x (i.succAbove j))) =
            ∑ j : Fin 3, c (i.succAbove j) * hwCentered M (y (i.succAbove j)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [show x (i.succAbove j) = y (i.succAbove j) from congrFun hxy j]
      have hcenter : hwCentered M (x i) = hwCentered M (y i) := by
        apply Int.eq_of_mul_eq_mul_left hi
        linarith
      apply Fin.ext
      dsimp [hwCentered] at hcenter
      omega
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hji
      exact congrFun hxy j
  calc
    #(hwLinearFiber M c) = #((hwLinearFiber M c).image proj) :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ Fintype.card (Fin 3 → Fin (2 * M + 1)) := Finset.card_le_univ _
    _ = (2 * M + 1) ^ 3 := by simp

private def hwCoordZero (H : ℕ) (i : Fin 4) :
    Finset (Fin 4 → Fin (2 * H + 1)) :=
  Finset.univ.filter fun h ↦ hwCentered H (h i) = 0

private lemma hw_coordZero_card_le (H : ℕ) (i : Fin 4) :
    #(hwCoordZero H i) ≤ (2 * H + 1) ^ 3 := by
  let proj : (Fin 4 → Fin (2 * H + 1)) → (Fin 3 → Fin (2 * H + 1)) :=
    fun h j ↦ h (i.succAbove j)
  have hinj : Set.InjOn proj {h | h ∈ hwCoordZero H i} := by
    intro x hx y hy hxy
    funext j
    by_cases hji : j = i
    · subst j
      have hx0 : hwCentered H (x i) = 0 := by simpa [hwCoordZero] using hx
      have hy0 : hwCentered H (y i) = 0 := by simpa [hwCoordZero] using hy
      apply Fin.ext
      dsimp [hwCentered] at hx0 hy0
      omega
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hji
      exact congrFun hxy j
  calc
    #(hwCoordZero H i) = #((hwCoordZero H i).image proj) :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ Fintype.card (Fin 3 → Fin (2 * H + 1)) := Finset.card_le_univ _
    _ = (2 * H + 1) ^ 3 := by simp

private def hwHasZero (H : ℕ) : Finset (Fin 4 → Fin (2 * H + 1)) :=
  Finset.univ.filter fun h ↦ ∃ i, hwCentered H (h i) = 0

private lemma hw_hasZero_card_le (H : ℕ) :
    #(hwHasZero H) ≤ 4 * (2 * H + 1) ^ 3 := by
  have hsub : hwHasZero H ⊆ Finset.univ.biUnion (hwCoordZero H) := by
    intro h hh
    rcases (Finset.mem_filter.mp hh).2 with ⟨i, hi⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [hwCoordZero, hi]⟩
  calc
    #(hwHasZero H) ≤ #(Finset.univ.biUnion (hwCoordZero H)) := Finset.card_le_card hsub
    _ ≤ ∑ i : Fin 4, #(hwCoordZero H i) := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin 4, (2 * H + 1) ^ 3 := by
      gcongr with i
      exact hw_coordZero_card_le H i
    _ = 4 * (2 * H + 1) ^ 3 := by simp

private lemma hw_gcd_dvd_natAbs_of_pairFiber_nonempty (M : ℕ) {h₁ h₂ n : ℤ}
    (h : (hwPairFiber M h₁ h₂ n).Nonempty) : h₁.gcd h₂ ∣ n.natAbs := by
  obtain ⟨p, hp⟩ := h
  simp only [hwPairFiber, mem_filter, mem_univ, true_and] at hp
  rw [← Int.natCast_dvd]
  rw [← hp]
  exact Int.dvd_add (dvd_mul_of_dvd_left (Int.gcd_dvd_left h₁ h₂) _)
    (dvd_mul_of_dvd_left (Int.gcd_dvd_right h₁ h₂) _)

private lemma hw_pairFiber_card_real_le (H M : ℕ) (hHM : H ≤ M)
    (h₁ h₂ : hwSigned H) (n : ℤ) :
    (#(hwPairFiber M (hwSignedVal H h₁) (hwSignedVal H h₂) n) : ℝ) ≤
      4 * (M + 1) *
        (if (h₁.2.val + 1).gcd (h₂.2.val + 1) ∣ n.natAbs then
          ((h₁.2.val + 1).gcd (h₂.2.val + 1) : ℝ) /
            max (h₁.2.val + 1) (h₂.2.val + 1) else 0) := by
  let a := hwSignedVal H h₁
  let b := hwSignedVal H h₂
  have ha0 : a ≠ 0 := hw_signedVal_ne_zero H h₁
  have hb0 : b ≠ 0 := hw_signedVal_ne_zero H h₂
  have haM : a.natAbs ≤ M := (hw_signedVal_natAbs_le H h₁).trans hHM
  have hbM : b.natAbs ≤ M := (hw_signedVal_natAbs_le H h₂).trans hHM
  have hgcd : a.gcd b = (h₁.2.val + 1).gcd (h₂.2.val + 1) := by
    simp [a, b, Int.gcd_eq_natAbs]
  split_ifs with hdvd
  · have hmax0 : (0 : ℝ) < max a.natAbs b.natAbs := by positivity
    have hmax : max a.natAbs b.natAbs =
        max (h₁.2.val + 1) (h₂.2.val + 1) := by simp [a, b]
    rw [← hgcd, ← hmax]
    rw [show (4 : ℝ) * (M + 1) * ((a.gcd b : ℝ) / max a.natAbs b.natAbs) =
        (4 * (M + 1) * (a.gcd b : ℝ)) / max a.natAbs b.natAbs by ring]
    rw [le_div_iff₀ hmax0]
    exact_mod_cast hw_pairFiber_card_mul_max_le M ha0 hb0 haM hbM
  · have hempty : hwPairFiber M a b n = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro p hp
      apply hdvd
      rw [← hgcd]
      exact hw_gcd_dvd_natAbs_of_pairFiber_nonempty M ⟨p, hp⟩
    have hempty' : hwPairFiber M (hwSignedVal H h₁) (hwSignedVal H h₂) n = ∅ := by
      simpa [a, b] using hempty
    simp [hempty']

private lemma hw_sum_signed_gcd_inv_max_le (H n : ℕ) (hn : n ≠ 0) :
    (∑ h₁ : hwSigned H, ∑ h₂ : hwSigned H,
      if (h₁.2.val + 1).gcd (h₂.2.val + 1) ∣ n then
        ((h₁.2.val + 1).gcd (h₂.2.val + 1) : ℝ) /
          max (h₁.2.val + 1) (h₂.2.val + 1) else 0) ≤
      8 * H * hwSigmaInv n := by
  simp_rw [Fintype.sum_prod_type]
  rw [show (∑ _s₁ : Fin 2, ∑ i : Fin H, ∑ _s₂ : Fin 2, ∑ j : Fin H,
      if (i.val + 1).gcd (j.val + 1) ∣ n then
        ((i.val + 1).gcd (j.val + 1) : ℝ) / max (i.val + 1) (j.val + 1) else 0) =
      4 * (∑ i : Fin H, ∑ j : Fin H,
        if (i.val + 1).gcd (j.val + 1) ∣ n then
          ((i.val + 1).gcd (j.val + 1) : ℝ) /
            max (i.val + 1) (j.val + 1) else 0) by
    simp only [Fin.sum_univ_two]
    simp_rw [Finset.sum_add_distrib]
    ring]
  rw [show (∑ i : Fin H, ∑ j : Fin H,
      if (i.val + 1).gcd (j.val + 1) ∣ n then
        ((i.val + 1).gcd (j.val + 1) : ℝ) / max (i.val + 1) (j.val + 1) else 0) =
      ∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H,
        if a.gcd b ∣ n then (a.gcd b : ℝ) / max a b else 0 by
    rw [hw_sum_fin_succ H (fun a ↦ ∑ j : Fin H,
      if a.gcd (j.val + 1) ∣ n then (a.gcd (j.val + 1) : ℝ) /
        max a (j.val + 1) else 0)]
    apply sum_congr rfl
    intro a ha
    rw [hw_sum_fin_succ H (fun b ↦ if a.gcd b ∣ n then
      (a.gcd b : ℝ) / max a b else 0)]]
  nlinarith [hw_sum_gcd_inv_max_le H n hn]

private lemma hw_centered_natAbs_le (M : ℕ) (x : Fin (2 * M + 1)) :
    (hwCentered M x).natAbs ≤ M := by
  by_cases hx : x.val ≤ M
  · rw [hwCentered, Int.natAbs_natCast_sub_natCast_of_le hx]
    omega
  · rw [hwCentered, Int.natAbs_natCast_sub_natCast_of_ge (Nat.le_of_not_ge hx)]
    have hxlt := x.isLt
    omega

private abbrev hwPairData (H M : ℕ) :=
  (hwSigned H × hwSigned H) × (Fin (2 * M + 1) × Fin (2 * M + 1))

private def hwPairVal (H M : ℕ) (p : hwPairData H M) : ℤ :=
  hwSignedVal H p.1.1 * hwCentered M p.2.1 +
    hwSignedVal H p.1.2 * hwCentered M p.2.2

private def hwPairCount (H M : ℕ) (n : ℤ) : ℕ :=
  #((Finset.univ : Finset (hwPairData H M)).filter fun p ↦ hwPairVal H M p = n)

private def hwFourTermCount (H M : ℕ) : ℕ :=
  #((Finset.univ : Finset (hwPairData H M × hwPairData H M)).filter fun p ↦
    hwPairVal H M p.1 + hwPairVal H M p.2 = 0)

private def hwCenteredFourTerm (H M : ℕ) :
    Finset ((Fin 4 → Fin (2 * H + 1)) × (Fin 4 → Fin (2 * M + 1))) :=
  Finset.univ.filter fun p ↦
    ∑ i, hwCentered H (p.1 i) * hwCentered M (p.2 i) = 0

private def hwCenteredFourNonzero (H M : ℕ) :
    Finset ((Fin 4 → Fin (2 * H + 1)) × (Fin 4 → Fin (2 * M + 1))) :=
  Finset.univ.filter fun p ↦
    (∑ i, hwCentered H (p.1 i) * hwCentered M (p.2 i) = 0) ∧
      ∀ i, hwCentered H (p.1 i) ≠ 0

private lemma hw_centeredFourTerm_card_eq_sum (H M : ℕ) :
    #(hwCenteredFourTerm H M) =
      ∑ h : Fin 4 → Fin (2 * H + 1),
        #(hwLinearFiber M fun i ↦ hwCentered H (h i)) := by
  rw [hwCenteredFourTerm, Finset.card_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  rw [hwLinearFiber, Finset.card_filter]

private lemma hw_centeredFourNonzero_card_eq_sum (H M : ℕ) :
    #(hwCenteredFourNonzero H M) =
      ∑ h : Fin 4 → Fin (2 * H + 1),
        if ∀ i, hwCentered H (h i) ≠ 0 then
          #(hwLinearFiber M fun i ↦ hwCentered H (h i)) else 0 := by
  rw [hwCenteredFourNonzero, Finset.card_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  rw [hwLinearFiber, Finset.card_filter]
  by_cases hh : ∀ i, hwCentered H (h i) ≠ 0
  · rw [ite_eq_left hh]
    apply Finset.sum_congr rfl
    intro m _
    change (if (∑ i, hwCentered H (h i) * hwCentered M (m i) = 0) ∧
        ∀ i, hwCentered H (h i) ≠ 0 then 1 else 0) =
      if ∑ i, hwCentered H (h i) * hwCentered M (m i) = 0 then 1 else 0
    by_cases heq : ∑ i, hwCentered H (h i) * hwCentered M (m i) = 0 <;>
      simp [heq, hh]
  · rw [ite_eq_right hh]
    apply Finset.sum_eq_zero
    intro m _
    have hcond : ¬(∑ i, hwCentered H (h i) * hwCentered M (m i) = 0 ∧
        ∀ i, hwCentered H (h i) ≠ 0) := fun heq ↦ hh heq.2
    rw [ite_eq_right hcond]

private def hwPackCenteredNonzero (H M : ℕ)
    (p : {p // p ∈ hwCenteredFourNonzero H M}) :
    hwPairData H M × hwPairData H M :=
  let s : Fin 4 → hwSigned H := fun i ↦
    (hwSignedEquivCentered H).symm
      ⟨p.1.1 i, (Finset.mem_filter.mp p.2).2.2 i⟩
  (((s 0, s 1), (p.1.2 0, p.1.2 1)),
    ((s 2, s 3), (p.1.2 2, p.1.2 3)))

private lemma hw_packCenteredNonzero_mem (H M : ℕ)
    (p : {p // p ∈ hwCenteredFourNonzero H M}) :
    hwPackCenteredNonzero H M p ∈
      (Finset.univ : Finset (hwPairData H M × hwPairData H M)).filter fun q ↦
        hwPairVal H M q.1 + hwPairVal H M q.2 = 0 := by
  have hs (i : Fin 4) :
      hwSignedVal H ((hwSignedEquivCentered H).symm
        ⟨p.1.1 i, (Finset.mem_filter.mp p.2).2.2 i⟩) =
        hwCentered H (p.1.1 i) := by
    rw [← hw_centered_signedToCentered]
    have he := (hwSignedEquivCentered H).apply_symm_apply
      ⟨p.1.1 i, (Finset.mem_filter.mp p.2).2.2 i⟩
    exact congrArg (fun z ↦ hwCentered H z.1) he
  have hp := (Finset.mem_filter.mp p.2).2.1
  simp only [Fin.sum_univ_succ] at hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  dsimp [hwPackCenteredNonzero, hwPairVal]
  rw [hs, hs, hs, hs]
  ring_nf at hp ⊢
  exact hp

private lemma hw_packCenteredNonzero_injective (H M : ℕ) :
    Function.Injective (hwPackCenteredNonzero H M) := by
  intro p q hpq
  apply Subtype.ext
  apply Prod.ext
  · funext i
    fin_cases i
    · have h := congrArg (fun z ↦ z.1.1.1) hpq
      dsimp [hwPackCenteredNonzero] at h
      exact congrArg Subtype.val ((hwSignedEquivCentered H).symm.injective h)
    · have h := congrArg (fun z ↦ z.1.1.2) hpq
      dsimp [hwPackCenteredNonzero] at h
      exact congrArg Subtype.val ((hwSignedEquivCentered H).symm.injective h)
    · have h := congrArg (fun z ↦ z.2.1.1) hpq
      dsimp [hwPackCenteredNonzero] at h
      exact congrArg Subtype.val ((hwSignedEquivCentered H).symm.injective h)
    · have h := congrArg (fun z ↦ z.2.1.2) hpq
      dsimp [hwPackCenteredNonzero] at h
      exact congrArg Subtype.val ((hwSignedEquivCentered H).symm.injective h)
  · funext i
    fin_cases i
    · exact congrArg (fun z ↦ z.1.2.1) hpq
    · exact congrArg (fun z ↦ z.1.2.2) hpq
    · exact congrArg (fun z ↦ z.2.2.1) hpq
    · exact congrArg (fun z ↦ z.2.2.2) hpq

private lemma hw_centeredFourNonzero_card_le (H M : ℕ) :
    #(hwCenteredFourNonzero H M) ≤ hwFourTermCount H M := by
  let S := {p // p ∈ hwCenteredFourNonzero H M}
  let f : S → hwPairData H M × hwPairData H M := hwPackCenteredNonzero H M
  have himage : (Finset.univ : Finset S).image f ⊆
      (Finset.univ : Finset (hwPairData H M × hwPairData H M)).filter fun q ↦
        hwPairVal H M q.1 + hwPairVal H M q.2 = 0 := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, _, rfl⟩
    exact hw_packCenteredNonzero_mem H M p
  calc
    #(hwCenteredFourNonzero H M) = Fintype.card S := by
      dsimp [S]
      rw [Fintype.card_subtype]
      simp
    _ = #((Finset.univ : Finset S).image f) := by
      calc
        Fintype.card S = #(Finset.univ : Finset S) := by simp
        _ = #((Finset.univ : Finset S).image f) :=
          (Finset.card_image_of_injective Finset.univ
            (hw_packCenteredNonzero_injective H M)).symm
    _ ≤ #((Finset.univ : Finset (hwPairData H M × hwPairData H M)).filter fun q ↦
        hwPairVal H M q.1 + hwPairVal H M q.2 = 0) := Finset.card_le_card himage
    _ = hwFourTermCount H M := rfl

private lemma hw_centered_eq_zero_iff (H : ℕ) (x : Fin (2 * H + 1)) :
    hwCentered H x = 0 ↔ x = ⟨H, by omega⟩ := by
  constructor
  · intro hx
    apply Fin.ext
    change x.val = H
    dsimp [hwCentered] at hx
    omega
  · rintro rfl
    change ((H : ℕ) : ℤ) - H = 0
    simp

private lemma hw_centeredFourTerm_card_le (H M : ℕ) :
    #(hwCenteredFourTerm H M) ≤
      hwFourTermCount H M + (2 * M + 1) ^ 4 +
        4 * (2 * H + 1) ^ 3 * (2 * M + 1) ^ 3 := by
  let F : (Fin 4 → Fin (2 * H + 1)) → ℕ := fun h ↦
    #(hwLinearFiber M fun i ↦ hwCentered H (h i))
  let P : (Fin 4 → Fin (2 * H + 1)) → Prop := fun h ↦
    ∀ i, hwCentered H (h i) ≠ 0
  let Q : (Fin 4 → Fin (2 * H + 1)) → Prop := fun h ↦
    ∃ i, hwCentered H (h i) = 0
  have hpart (h : Fin 4 → Fin (2 * H + 1)) :
      F h = (if P h then F h else 0) + if Q h then F h else 0 := by
    by_cases hp : P h
    · have hq : ¬Q h := fun hq ↦ by
        obtain ⟨i, hi⟩ := hq
        exact hp i hi
      simp [hp, hq]
    · have hq : Q h := by
        simp only [P, not_forall, not_ne_iff] at hp
        exact hp
      simp [hp, hq]
  have hzeroSum :
      (∑ h : Fin 4 → Fin (2 * H + 1),
        if ∀ i, hwCentered H (h i) = 0 then (2 * M + 1) ^ 4 else 0) =
          (2 * M + 1) ^ 4 := by
    let z : Fin (2 * H + 1) := ⟨H, by omega⟩
    have hall (h : Fin 4 → Fin (2 * H + 1)) :
        (∀ i, hwCentered H (h i) = 0) ↔ h = fun _ ↦ z := by
      constructor
      · intro hh
        funext i
        simpa [z] using (hw_centered_eq_zero_iff H (h i)).mp (hh i)
      · rintro rfl i
        simp [z, hwCentered]
    simp_rw [hall]
    simp
  have hhasZeroSum :
      (∑ h : Fin 4 → Fin (2 * H + 1),
        if Q h then (2 * M + 1) ^ 3 else 0) =
          #(hwHasZero H) * (2 * M + 1) ^ 3 := by
    change (∑ h : Fin 4 → Fin (2 * H + 1),
      if ∃ i, hwCentered H (h i) = 0 then (2 * M + 1) ^ 3 else 0) = _
    rw [← Finset.sum_filter]
    simp [hwHasZero]
  have hbad :
      (∑ h : Fin 4 → Fin (2 * H + 1), if Q h then F h else 0) ≤
        (2 * M + 1) ^ 4 + #(hwHasZero H) * (2 * M + 1) ^ 3 := by
    calc
      (∑ h : Fin 4 → Fin (2 * H + 1), if Q h then F h else 0) ≤
          ∑ h : Fin 4 → Fin (2 * H + 1),
            ((if ∀ i, hwCentered H (h i) = 0 then (2 * M + 1) ^ 4 else 0) +
              if Q h then (2 * M + 1) ^ 3 else 0) := by
        apply Finset.sum_le_sum
        intro h _
        by_cases hq : Q h
        · rw [ite_eq_left hq, ite_eq_left hq]
          by_cases hall : ∀ i, hwCentered H (h i) = 0
          · rw [ite_eq_left hall]
            exact (Finset.card_le_univ _).trans (by simp)
          · rw [ite_eq_right hall, zero_add]
            simp only [not_forall] at hall
            obtain ⟨i, hi⟩ := hall
            exact hw_linearFiber_card_le M (fun i ↦ hwCentered H (h i)) hi
        · rw [ite_eq_right hq]
          omega
      _ = (2 * M + 1) ^ 4 + #(hwHasZero H) * (2 * M + 1) ^ 3 := by
        rw [Finset.sum_add_distrib, hzeroSum, hhasZeroSum]
  rw [hw_centeredFourTerm_card_eq_sum]
  calc
    (∑ h : Fin 4 → Fin (2 * H + 1), F h) =
        (∑ h : Fin 4 → Fin (2 * H + 1), if P h then F h else 0) +
          ∑ h : Fin 4 → Fin (2 * H + 1), if Q h then F h else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro h _
      exact hpart h
    _ ≤ #(hwCenteredFourNonzero H M) +
        ((2 * M + 1) ^ 4 + #(hwHasZero H) * (2 * M + 1) ^ 3) := by
      rw [hw_centeredFourNonzero_card_eq_sum]
      exact Nat.add_le_add le_rfl hbad
    _ ≤ hwFourTermCount H M + (2 * M + 1) ^ 4 +
        4 * (2 * H + 1) ^ 3 * (2 * M + 1) ^ 3 := by
      have hnonzero := hw_centeredFourNonzero_card_le H M
      have hzero := Nat.mul_le_mul_right ((2 * M + 1) ^ 3) (hw_hasZero_card_le H)
      omega

private lemma hw_pairCount_eq (H M : ℕ) (n : ℤ) :
    hwPairCount H M n = ∑ h₁ : hwSigned H, ∑ h₂ : hwSigned H,
      #(hwPairFiber M (hwSignedVal H h₁) (hwSignedVal H h₂) n) := by
  rw [hwPairCount, Finset.card_filter]
  simp_rw [Fintype.sum_prod_type]
  simp only [hwPairFiber, Finset.card_filter, Fintype.sum_prod_type, hwPairVal]
  rfl

private lemma hw_pairVal_natAbs_le (H M : ℕ) (p : hwPairData H M) :
    (hwPairVal H M p).natAbs ≤ 2 * H * M := by
  calc
    (hwPairVal H M p).natAbs ≤
        (hwSignedVal H p.1.1 * hwCentered M p.2.1).natAbs +
          (hwSignedVal H p.1.2 * hwCentered M p.2.2).natAbs := by
      exact Int.natAbs_add_le _ _
    _ = (hwSignedVal H p.1.1).natAbs * (hwCentered M p.2.1).natAbs +
          (hwSignedVal H p.1.2).natAbs * (hwCentered M p.2.2).natAbs := by
      simp only [Int.natAbs_mul]
    _ ≤ H * M + H * M := by
      gcongr
      · exact hw_signedVal_natAbs_le H p.1.1
      · exact hw_centered_natAbs_le M p.2.1
      · exact hw_signedVal_natAbs_le H p.1.2
      · exact hw_centered_natAbs_le M p.2.2
    _ = 2 * H * M := by ring

private lemma hw_fourTermCount_eq (H M : ℕ) :
    hwFourTermCount H M =
      ∑ n ∈ Finset.Icc (-(2 * H * M : ℕ) : ℤ) (2 * H * M : ℕ),
        hwPairCount H M n * hwPairCount H M (-n) := by
  let D := (Finset.univ : Finset (hwPairData H M))
  let T := Finset.Icc (-(2 * H * M : ℕ) : ℤ) (2 * H * M : ℕ)
  have hmap : ∀ p ∈ D, hwPairVal H M p ∈ T := by
    intro p hp
    simp only [T, Finset.mem_Icc]
    have h := hw_pairVal_natAbs_le H M p
    omega
  rw [hwFourTermCount, Finset.card_filter, Fintype.sum_prod_type]
  change (∑ p ∈ D, ∑ q ∈ D,
    if hwPairVal H M p + hwPairVal H M q = 0 then 1 else 0) = _
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun p ↦ ∑ q ∈ D, if hwPairVal H M p + hwPairVal H M q = 0 then 1 else 0)]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    (∑ p ∈ D with hwPairVal H M p = n,
        ∑ q ∈ D, if hwPairVal H M p + hwPairVal H M q = 0 then 1 else 0) =
        ∑ _p ∈ D with hwPairVal H M _p = n, hwPairCount H M (-n) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
      change (∑ q : hwPairData H M,
        if n + hwPairVal H M q = 0 then 1 else 0) = hwPairCount H M (-n)
      rw [hwPairCount, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs <;> omega
    _ = hwPairCount H M n * hwPairCount H M (-n) := by
      simp [hwPairCount, D]

private lemma hw_pairFiber_card_le_fin (M : ℕ) {h₁ h₂ n : ℤ} (hh₁ : h₁ ≠ 0) :
    #(hwPairFiber M h₁ h₂ n) ≤ 2 * M + 1 := by
  have hproj : Set.InjOn Prod.snd {x | x ∈ hwPairFiber M h₁ h₂ n} := by
    intro x hx y hy hxy
    apply Prod.ext
    · have hx' : h₁ * hwCentered M x.1 + h₂ * hwCentered M x.2 = n := by
        simpa [hwPairFiber] using hx
      have hy' : h₁ * hwCentered M y.1 + h₂ * hwCentered M y.2 = n := by
        simpa [hwPairFiber] using hy
      rw [hxy] at hx'
      have hm : h₁ * hwCentered M x.1 = h₁ * hwCentered M y.1 := by
        linarith [hy']
      have hc := Int.eq_of_mul_eq_mul_left hh₁ hm
      apply Fin.ext
      dsimp [hwCentered] at hc
      omega
    · exact hxy
  have hcard : #(hwPairFiber M h₁ h₂ n) =
      #((hwPairFiber M h₁ h₂ n).image Prod.snd) :=
    (card_image_iff.mpr hproj).symm
  rw [hcard]
  exact (card_le_univ _).trans_eq (Fintype.card_fin _)

private lemma hw_pairCount_zero_le (H M : ℕ) :
    hwPairCount H M 0 ≤ 4 * H ^ 2 * (2 * M + 1) := by
  rw [hw_pairCount_eq]
  calc
    (∑ h₁ : hwSigned H, ∑ h₂ : hwSigned H,
        #(hwPairFiber M (hwSignedVal H h₁) (hwSignedVal H h₂) 0)) ≤
        ∑ _h₁ : hwSigned H, ∑ _h₂ : hwSigned H, (2 * M + 1) := by
      gcongr with h₁ h₂
      exact hw_pairFiber_card_le_fin M (hw_signedVal_ne_zero H h₁)
    _ = 4 * H ^ 2 * (2 * M + 1) := by
      simp [hwSigned]
      ring

private lemma hw_pairCount_real_le (H M : ℕ) (hHM : H ≤ M) {n : ℤ} (hn : n ≠ 0) :
    (hwPairCount H M n : ℝ) ≤
      32 * H * (M + 1) * hwSigmaInv n.natAbs := by
  have hnabs : n.natAbs ≠ 0 := (Int.natAbs_pos.mpr hn).ne'
  calc
    (hwPairCount H M n : ℝ) =
        ∑ h₁ : hwSigned H, ∑ h₂ : hwSigned H,
          (#(hwPairFiber M (hwSignedVal H h₁) (hwSignedVal H h₂) n) : ℝ) := by
      rw [hw_pairCount_eq]
      push_cast
      rfl
    _ ≤ ∑ h₁ : hwSigned H, ∑ h₂ : hwSigned H,
        4 * (M + 1) *
          (if (h₁.2.val + 1).gcd (h₂.2.val + 1) ∣ n.natAbs then
            ((h₁.2.val + 1).gcd (h₂.2.val + 1) : ℝ) /
              max (h₁.2.val + 1) (h₂.2.val + 1) else 0) := by
      gcongr with h₁ h₂
      exact hw_pairFiber_card_real_le H M hHM h₁ h₂ n
    _ = 4 * (M + 1) * (∑ h₁ : hwSigned H, ∑ h₂ : hwSigned H,
        if (h₁.2.val + 1).gcd (h₂.2.val + 1) ∣ n.natAbs then
          ((h₁.2.val + 1).gcd (h₂.2.val + 1) : ℝ) /
            max (h₁.2.val + 1) (h₂.2.val + 1) else 0) := by
      simp_rw [Finset.mul_sum]
    _ ≤ 4 * (M + 1) * (8 * H * hwSigmaInv n.natAbs) := by
      gcongr
      exact hw_sum_signed_gcd_inv_max_le H n.natAbs hnabs
    _ = 32 * H * (M + 1) * hwSigmaInv n.natAbs := by ring

private lemma hw_sum_int_natAbs_le (B : ℕ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) :
    (∑ n ∈ Finset.Icc (-(B : ℤ)) (B : ℤ) with n ≠ 0, F n.natAbs) ≤
      2 * ∑ a ∈ Finset.Icc 1 B, F a := by
  let S := (Finset.Icc (-(B : ℤ)) (B : ℤ)).filter fun n ↦ n ≠ 0
  let T := Finset.Icc 1 B
  have hmap : ∀ n ∈ S, n.natAbs ∈ T := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hbounds := Finset.mem_Icc.mp hn'.1
    change n.natAbs ∈ Finset.Icc 1 B
    rw [Finset.mem_Icc]
    constructor
    · exact Int.natAbs_pos.mpr hn'.2
    · rcases Int.natAbs_eq n with h | h
      · omega
      · omega
  change (∑ n ∈ S, F n.natAbs) ≤ 2 * ∑ a ∈ T, F a
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun n ↦ F n.natAbs)]
  calc
    (∑ a ∈ T, ∑ n ∈ S with n.natAbs = a, F n.natAbs) =
        ∑ a ∈ T, (#({n ∈ S | n.natAbs = a}) : ℝ) * F a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_congr rfl (fun n hn ↦ by rw [(Finset.mem_filter.mp hn).2])]
      simp
    _ ≤ ∑ a ∈ T, 2 * F a := by
      gcongr with a ha
      · exact hF a
      · have hsub : {n ∈ S | n.natAbs = a} ⊆ ({(a : ℤ), -(a : ℤ)} : Finset ℤ) := by
          intro n hn
          have hnabs := (Finset.mem_filter.mp hn).2
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases Int.natAbs_eq n with h | h
          · left
            simpa only [hnabs] using h
          · right
            simpa only [hnabs] using h
        have hc₁ := card_insert_le (a : ℤ) ({-(a : ℤ)} : Finset ℤ)
        have hc₂ : #({-(a : ℤ)} : Finset ℤ) = 1 := card_singleton _
        exact_mod_cast (card_le_card hsub).trans (by omega)
    _ = 2 * ∑ a ∈ T, F a := by rw [Finset.mul_sum]

private lemma hw_sigmaInv_nonneg (n : ℕ) : 0 ≤ hwSigmaInv n := by
  exact sum_nonneg fun d _ ↦ inv_nonneg.mpr (Nat.cast_nonneg d)

private lemma hw_fourTermCount_real_le (H M : ℕ) (hH : 0 < H) (hHM : H ≤ M) :
    (hwFourTermCount H M : ℝ) ≤
      (144 + 16384 * hwZetaTwo ^ 3) * (H * M) ^ 3 := by
  let B := 2 * H * M
  let T := Finset.Icc (-(B : ℤ)) (B : ℤ)
  have hM : 0 < M := hH.trans_le hHM
  have hcast : (hwFourTermCount H M : ℝ) =
      ∑ n ∈ T, (hwPairCount H M n : ℝ) * hwPairCount H M (-n) := by
    rw [hw_fourTermCount_eq]
    push_cast
    rfl
  have hz : {n ∈ T | n = 0} = {0} := by
    ext n
    simp only [mem_filter, mem_singleton, T, mem_Icc]
    constructor
    · exact fun h ↦ h.2
    · intro h
      subst n
      constructor <;> omega
  have hsplit :
      (∑ n ∈ T, (hwPairCount H M n : ℝ) * hwPairCount H M (-n)) =
        (hwPairCount H M 0 : ℝ) ^ 2 +
          ∑ n ∈ T with n ≠ 0,
            (hwPairCount H M n : ℝ) * hwPairCount H M (-n) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := T) (p := fun n ↦ n ≠ 0)]
    simp only [not_ne_iff]
    rw [hz]
    simp [add_comm, pow_two]
  have hzeroBase : (hwPairCount H M 0 : ℝ) ≤ 12 * H ^ 2 * M := by
    have hnat : 4 * H ^ 2 * (2 * M + 1) ≤ 12 * H ^ 2 * M := by
      calc
        4 * H ^ 2 * (2 * M + 1) ≤ 4 * H ^ 2 * (3 * M) := by
          gcongr
          omega
        _ = 12 * H ^ 2 * M := by ring
    exact_mod_cast (hw_pairCount_zero_le H M).trans hnat
  have hzero : (hwPairCount H M 0 : ℝ) ^ 2 ≤ 144 * (H * M) ^ 3 := by
    calc
      (hwPairCount H M 0 : ℝ) ^ 2 ≤ (12 * H ^ 2 * M : ℝ) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) hzeroBase 2
      _ = (144 * (H : ℝ) ^ 3 * M ^ 2) * H := by ring
      _ ≤ (144 * (H : ℝ) ^ 3 * M ^ 2) * M := by
        gcongr
      _ = 144 * (H * M) ^ 3 := by ring
  have hpair (n : ℤ) (hn : n ≠ 0) :
      (hwPairCount H M n : ℝ) ≤
        64 * H * M * hwSigmaInv n.natAbs := by
    calc
      (hwPairCount H M n : ℝ) ≤
          32 * H * (M + 1) * hwSigmaInv n.natAbs :=
        hw_pairCount_real_le H M hHM hn
      _ ≤ 32 * H * (2 * M) * hwSigmaInv n.natAbs := by
        apply mul_le_mul_of_nonneg_right _ (hw_sigmaInv_nonneg n.natAbs)
        gcongr
        exact_mod_cast (by omega : M + 1 ≤ 2 * M)
      _ = 64 * H * M * hwSigmaInv n.natAbs := by ring
  have hpoint (n : ℤ) (hn : n ≠ 0) :
      (hwPairCount H M n : ℝ) * hwPairCount H M (-n) ≤
        4096 * H ^ 2 * M ^ 2 * hwSigmaInv n.natAbs ^ 2 := by
    have hnneg : -n ≠ 0 := by simpa using hn
    have h₁ := hpair n hn
    have h₂ := hpair (-n) hnneg
    rw [Int.natAbs_neg] at h₂
    calc
      (hwPairCount H M n : ℝ) * hwPairCount H M (-n) ≤
          (64 * H * M * hwSigmaInv n.natAbs) *
            (64 * H * M * hwSigmaInv n.natAbs) := by
        exact mul_le_mul h₁ h₂ (by positivity)
          (mul_nonneg (by positivity) (hw_sigmaInv_nonneg n.natAbs))
      _ = 4096 * H ^ 2 * M ^ 2 * hwSigmaInv n.natAbs ^ 2 := by ring
  have hnonzero :
      (∑ n ∈ T with n ≠ 0,
        (hwPairCount H M n : ℝ) * hwPairCount H M (-n)) ≤
          16384 * (H * M) ^ 3 * hwZetaTwo ^ 3 := by
    calc
      (∑ n ∈ T with n ≠ 0,
        (hwPairCount H M n : ℝ) * hwPairCount H M (-n)) ≤
          ∑ n ∈ T with n ≠ 0,
            4096 * H ^ 2 * M ^ 2 * hwSigmaInv n.natAbs ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact hpoint n (mem_filter.mp hn).2
      _ = 4096 * H ^ 2 * M ^ 2 *
          (∑ n ∈ T with n ≠ 0, hwSigmaInv n.natAbs ^ 2) := by
        rw [Finset.mul_sum]
      _ ≤ 4096 * H ^ 2 * M ^ 2 *
          (2 * ∑ a ∈ Finset.Icc 1 B, hwSigmaInv a ^ 2) := by
        gcongr
        simpa [T] using hw_sum_int_natAbs_le B (fun a ↦ hwSigmaInv a ^ 2)
          (fun a ↦ sq_nonneg _)
      _ ≤ 4096 * H ^ 2 * M ^ 2 * (2 * (B * hwZetaTwo ^ 3)) := by
        gcongr
        exact hw_sigmaInv_sq_sum_le B
      _ = 16384 * (H * M) ^ 3 * hwZetaTwo ^ 3 := by
        dsimp [B]
        push_cast
        ring
  rw [hcast, hsplit]
  calc
    (hwPairCount H M 0 : ℝ) ^ 2 +
        ∑ n ∈ T with n ≠ 0,
          (hwPairCount H M n : ℝ) * hwPairCount H M (-n) ≤
      144 * (H * M) ^ 3 + 16384 * (H * M) ^ 3 * hwZetaTwo ^ 3 :=
        add_le_add hzero hnonzero
    _ = (144 + 16384 * hwZetaTwo ^ 3) * (H * M) ^ 3 := by ring

private lemma hw_exists_fourTermCount_bound :
    ∃ C : ℕ, 0 < C ∧ ∀ H M : ℕ, 0 < H → H ≤ M →
      hwFourTermCount H M ≤ C * (H * M) ^ 3 := by
  let R : ℝ := 144 + 16384 * hwZetaTwo ^ 3
  let C := ⌈R⌉₊
  have hR : 0 < R := by
    dsimp [R]
    have hz3 : 0 ≤ hwZetaTwo ^ 3 := pow_nonneg hw_zetaTwo_nonneg 3
    nlinarith
  refine ⟨C, Nat.ceil_pos.mpr hR, ?_⟩
  intro H M hH hHM
  have hmain := hw_fourTermCount_real_le H M hH hHM
  have hceil : R ≤ (C : ℝ) := Nat.le_ceil R
  have hpow : (0 : ℝ) ≤ (H * M : ℕ) ^ 3 := by positivity
  have hbound : (hwFourTermCount H M : ℝ) ≤ (C : ℝ) * ((H * M : ℕ) : ℝ) ^ 3 := by
    calc
      (hwFourTermCount H M : ℝ) ≤ R * ((H * M : ℕ) : ℝ) ^ 3 := by
        simpa [R] using hmain
      _ ≤ (C : ℝ) * ((H * M : ℕ) : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right hceil hpow
  exact_mod_cast hbound

private lemma hw_char_sum (P : ℕ) [NeZero P] (z : ℤ) :
    (∑ a : ZMod P, ZMod.stdAddChar (a * (z : ZMod P))) =
      if (z : ZMod P) = 0 then (P : ℂ) else 0 := by
  by_cases hz : (z : ZMod P) = 0
  · simp [hz]
  · have hp := ZMod.isPrimitive_stdAddChar P hz
    simp only [hz, ite_false]
    simpa [mul_comm] using AddChar.sum_eq_zero_of_ne_one hp

private lemma hw_dvd_eq_zero_of_abs_lt (P : ℕ) {z : ℤ}
    (hz : z.natAbs < P) (hd : (P : ℤ) ∣ z) : z = 0 := by
  obtain ⟨c, rfl⟩ := hd
  by_cases hc : c = 0
  · simp [hc]
  have hcabs : 1 ≤ c.natAbs := Int.natAbs_pos.mpr hc
  rw [Int.natAbs_mul] at hz
  have hle : P ≤ P * c.natAbs := Nat.le_mul_of_pos_right P (Int.natAbs_pos.mpr hc)
  have hcast : (P : ℤ).natAbs = P := by simp
  rw [hcast] at hz
  omega

private lemma hw_char_sum_eq_indicator (P : ℕ) [NeZero P] (z : ℤ)
    (hz : z.natAbs < P) :
    (∑ a : ZMod P, ZMod.stdAddChar (a * (z : ZMod P))) =
      if z = 0 then (P : ℂ) else 0 := by
  rw [hw_char_sum]
  have hiff : (z : ZMod P) = 0 ↔ z = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · exact hw_dvd_eq_zero_of_abs_lt P hz
    · rintro rfl
      simp
  simp only [hiff]

private def hwTupleSum (r N : ℕ) (f : ℕ → ℤ) (x : Fin r → Fin (N + 1)) : ℤ :=
  ∑ i, f (x i)

private noncomputable def hwWeylSum (P N : ℕ) [NeZero P]
    (f : ℕ → ℤ) (a : ZMod P) : ℂ :=
  ∑ n : Fin (N + 1), ZMod.stdAddChar (a * (f n : ZMod P))

private lemma hw_addChar_map_sum {A M ι : Type*} [AddCommMonoid A] [CommMonoid M]
    (ψ : AddChar A M) (s : Finset ι) (v : ι → A) :
    ψ (∑ i ∈ s, v i) = ∏ i ∈ s, ψ (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, AddChar.map_add_eq_mul]

private lemma hw_prod_char_eq_char_sum (P r N : ℕ) [NeZero P] (f : ℕ → ℤ)
    (a : ZMod P) (x : Fin r → Fin (N + 1)) :
    (∏ i, ZMod.stdAddChar (a * (f (x i) : ZMod P))) =
      ZMod.stdAddChar (a * (hwTupleSum r N f x : ZMod P)) := by
  rw [show a * (hwTupleSum r N f x : ZMod P) =
      ∑ i, a * (f (x i) : ZMod P) by simp [hwTupleSum, mul_sum]]
  exact (hw_addChar_map_sum ZMod.stdAddChar Finset.univ _).symm

private lemma hw_prod_neg_char_eq_char_neg_sum (P r N : ℕ) [NeZero P] (f : ℕ → ℤ)
    (a : ZMod P) (x : Fin r → Fin (N + 1)) :
    (∏ i, ZMod.stdAddChar (-(a * (f (x i) : ZMod P)))) =
      ZMod.stdAddChar (-(a * (hwTupleSum r N f x : ZMod P))) := by
  simpa only [neg_mul] using hw_prod_char_eq_char_sum P r N f (-a) x

private lemma hw_conj_weylSum (P N : ℕ) [NeZero P] (f : ℕ → ℤ) (a : ZMod P) :
    (starRingEnd ℂ) (hwWeylSum P N f a) =
      ∑ n : Fin (N + 1), ZMod.stdAddChar (-(a * (f n : ZMod P))) := by
  simp only [hwWeylSum, map_sum, AddChar.map_neg_eq_conj]

private lemma hw_absSq_pow_expand (P r N : ℕ) [NeZero P]
    (f : ℕ → ℤ) (a : ZMod P) :
    (hwWeylSum P N f a * (starRingEnd ℂ) (hwWeylSum P N f a)) ^ r =
      ∑ x : Fin r → Fin (N + 1), ∑ y : Fin r → Fin (N + 1),
        ZMod.stdAddChar
          (a * ((hwTupleSum r N f x - hwTupleSum r N f y : ℤ) : ZMod P)) := by
  rw [mul_pow, hw_conj_weylSum]
  unfold hwWeylSum
  rw [Finset.sum_pow' Finset.univ, Finset.sum_pow' Finset.univ]
  simp only [Fintype.piFinset_univ, Int.cast_sub, hw_prod_char_eq_char_sum,
    hw_prod_neg_char_eq_char_neg_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [← AddChar.map_add_eq_mul]
  congr 2
  ring

private def hwMomentFinset (r N : ℕ) (f : ℕ → ℤ) :
    Finset ((Fin r → Fin (N + 1)) × (Fin r → Fin (N + 1))) :=
  Finset.univ.filter fun xy ↦ hwTupleSum r N f xy.1 = hwTupleSum r N f xy.2

private def hwFinLift {A B : ℕ} (hAB : A ≤ B) (x : Fin (A + 1)) : Fin (B + 1) :=
  ⟨x.val, by omega⟩

private def hwMomentLift (r A B : ℕ) (hAB : A ≤ B) :
    ((Fin r → Fin (A + 1)) × (Fin r → Fin (A + 1))) →
      ((Fin r → Fin (B + 1)) × (Fin r → Fin (B + 1))) :=
  fun p ↦ (fun i ↦ hwFinLift hAB (p.1 i), fun i ↦ hwFinLift hAB (p.2 i))

private lemma hw_momentLift_injective (r A B : ℕ) (hAB : A ≤ B) :
    Function.Injective (hwMomentLift r A B hAB) := by
  intro p q hpq
  apply Prod.ext <;> funext i
  · have h := congrFun (congrArg Prod.fst hpq) i
    apply Fin.ext
    simpa [hwMomentLift, hwFinLift] using congrArg Fin.val h
  · have h := congrFun (congrArg Prod.snd hpq) i
    apply Fin.ext
    simpa [hwMomentLift, hwFinLift] using congrArg Fin.val h

private def hwTupleImage (r N : ℕ) (f : ℕ → ℤ) : Finset ℤ :=
  (Finset.univ : Finset (Fin r → Fin (N + 1))).image (hwTupleSum r N f)

private def hwValueFiber (r N : ℕ) (f : ℕ → ℤ) (t : ℤ) :
    Finset (Fin r → Fin (N + 1)) :=
  Finset.univ.filter fun x ↦ hwTupleSum r N f x = t

private def hwDiffFiber (r N : ℕ) (f : ℕ → ℤ) (m : ℤ) :
    Finset ((Fin r → Fin (N + 1)) × (Fin r → Fin (N + 1))) :=
  Finset.univ.filter fun p ↦ hwTupleSum r N f p.1 - hwTupleSum r N f p.2 = m

private lemma hw_diffFiber_card_eq_sum (r N : ℕ) (f : ℕ → ℤ) (m : ℤ) :
    #(hwDiffFiber r N f m) =
      ∑ t ∈ hwTupleImage r N f,
        #(hwValueFiber r N f t) * #(hwValueFiber r N f (t - m)) := by
  let X := (Finset.univ : Finset (Fin r → Fin (N + 1)))
  have hmap : ∀ x ∈ X, hwTupleSum r N f x ∈ hwTupleImage r N f := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [hwDiffFiber, Finset.card_filter, Fintype.sum_prod_type]
  change (∑ x ∈ X, ∑ y ∈ X,
    if hwTupleSum r N f x - hwTupleSum r N f y = m then 1 else 0) = _
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun x ↦ ∑ y ∈ X, if hwTupleSum r N f x - hwTupleSum r N f y = m then 1 else 0)]
  apply Finset.sum_congr rfl
  intro t _
  calc
    (∑ x ∈ X with hwTupleSum r N f x = t,
        ∑ y ∈ X, if hwTupleSum r N f x - hwTupleSum r N f y = m then 1 else 0) =
        ∑ _x ∈ X with hwTupleSum r N f _x = t, #(hwValueFiber r N f (t - m)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
      rw [hwValueFiber, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> omega
    _ = #(hwValueFiber r N f t) * #(hwValueFiber r N f (t - m)) := by
      simp [hwValueFiber, X]

private lemma hw_moment_card_eq_value_sq_sum (r N : ℕ) (f : ℕ → ℤ) :
    #(hwMomentFinset r N f) =
      ∑ t ∈ hwTupleImage r N f, #(hwValueFiber r N f t) ^ 2 := by
  have heq : hwMomentFinset r N f = hwDiffFiber r N f 0 := by
    ext p
    simp only [hwMomentFinset, hwDiffFiber, Finset.mem_filter, Finset.mem_univ,
      true_and, sub_eq_zero]
  rw [heq, hw_diffFiber_card_eq_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp [pow_two]

private lemma hw_valueFiber_ne_zero_mem_image (r N : ℕ) (f : ℕ → ℤ) {t : ℤ}
    (ht : #(hwValueFiber r N f t) ≠ 0) : t ∈ hwTupleImage r N f := by
  have hnonempty : (hwValueFiber r N f t).Nonempty := Finset.card_ne_zero.mp ht
  obtain ⟨x, hx⟩ := hnonempty
  have hx' := (Finset.mem_filter.mp hx).2
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx'⟩

private lemma hw_diffFiber_card_le_moment (r N : ℕ) (f : ℕ → ℤ) (m : ℤ) :
    #(hwDiffFiber r N f m) ≤ #(hwMomentFinset r N f) := by
  let T := hwTupleImage r N f
  let R : ℤ → ℕ := fun t ↦ #(hwValueFiber r N f t)
  have hshift : (∑ t ∈ T, R (t - m) ^ 2) ≤ ∑ t ∈ T, R t ^ 2 := by
    let S := T.image fun t ↦ t - m
    have hinj : Set.InjOn (fun t : ℤ ↦ t - m) (↑T) :=
      sub_left_injective.injOn
    have hsum : (∑ t ∈ T, R (t - m) ^ 2) = ∑ u ∈ S, R u ^ 2 := by
      dsimp only [S]
      rw [Finset.sum_image hinj]
    rw [hsum]
    apply Finset.sum_le_sum_of_ne_zero
    intro u hu hRu
    apply hw_valueFiber_ne_zero_mem_image r N f
    intro hzero
    apply hRu
    simp [R, hzero]
  have hamgm :
      2 * (∑ t ∈ T, R t * R (t - m)) ≤
        (∑ t ∈ T, R t ^ 2) + ∑ t ∈ T, R (t - m) ^ 2 := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t _
    simpa [mul_assoc] using two_mul_le_add_sq (R t) (R (t - m))
  rw [hw_diffFiber_card_eq_sum, hw_moment_card_eq_value_sq_sum]
  change (∑ t ∈ T, R t * R (t - m)) ≤ ∑ t ∈ T, R t ^ 2
  apply Nat.le_of_mul_le_mul_left (c := 2)
  · exact hamgm.trans (Nat.add_le_add_left hshift _ |>.trans_eq (by omega))
  · omega

private def hwSumFiber (r N : ℕ) (f : ℕ → ℤ) (m : ℤ) :
    Finset ((Fin r → Fin (N + 1)) × (Fin r → Fin (N + 1))) :=
  Finset.univ.filter fun p ↦ hwTupleSum r N f p.1 + hwTupleSum r N f p.2 = m

private lemma hw_sumFiber_card_eq_sum (r N : ℕ) (f : ℕ → ℤ) (m : ℤ) :
    #(hwSumFiber r N f m) =
      ∑ t ∈ hwTupleImage r N f,
        #(hwValueFiber r N f t) * #(hwValueFiber r N f (m - t)) := by
  let X := (Finset.univ : Finset (Fin r → Fin (N + 1)))
  have hmap : ∀ x ∈ X, hwTupleSum r N f x ∈ hwTupleImage r N f := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [hwSumFiber, Finset.card_filter, Fintype.sum_prod_type]
  change (∑ x ∈ X, ∑ y ∈ X,
    if hwTupleSum r N f x + hwTupleSum r N f y = m then 1 else 0) = _
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun x ↦ ∑ y ∈ X, if hwTupleSum r N f x + hwTupleSum r N f y = m then 1 else 0)]
  apply Finset.sum_congr rfl
  intro t _
  calc
    (∑ x ∈ X with hwTupleSum r N f x = t,
        ∑ y ∈ X, if hwTupleSum r N f x + hwTupleSum r N f y = m then 1 else 0) =
        ∑ _x ∈ X with hwTupleSum r N f _x = t, #(hwValueFiber r N f (m - t)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
      rw [hwValueFiber, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> omega
    _ = #(hwValueFiber r N f t) * #(hwValueFiber r N f (m - t)) := by
      simp [hwValueFiber, X]

private lemma hw_sumFiber_card_le_moment (r N : ℕ) (f : ℕ → ℤ) (m : ℤ) :
    #(hwSumFiber r N f m) ≤ #(hwMomentFinset r N f) := by
  let T := hwTupleImage r N f
  let R : ℤ → ℕ := fun t ↦ #(hwValueFiber r N f t)
  have hshift : (∑ t ∈ T, R (m - t) ^ 2) ≤ ∑ t ∈ T, R t ^ 2 := by
    let S := T.image fun t ↦ m - t
    have hsum : (∑ t ∈ T, R (m - t) ^ 2) = ∑ u ∈ S, R u ^ 2 := by
      dsimp only [S]
      rw [Finset.sum_image sub_right_injective.injOn]
    rw [hsum]
    apply Finset.sum_le_sum_of_ne_zero
    intro u hu hRu
    apply hw_valueFiber_ne_zero_mem_image r N f
    intro hzero
    apply hRu
    simp [R, hzero]
  have hamgm :
      2 * (∑ t ∈ T, R t * R (m - t)) ≤
        (∑ t ∈ T, R t ^ 2) + ∑ t ∈ T, R (m - t) ^ 2 := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t _
    simpa [mul_assoc] using two_mul_le_add_sq (R t) (R (m - t))
  rw [hw_sumFiber_card_eq_sum, hw_moment_card_eq_value_sq_sum]
  change (∑ t ∈ T, R t * R (m - t)) ≤ ∑ t ∈ T, R t ^ 2
  apply Nat.le_of_mul_le_mul_left (c := 2)
  · exact hamgm.trans (Nat.add_le_add_left hshift _ |>.trans_eq (by omega))
  · omega

private def hwPolyEval (k : ℕ) (a : Fin (k + 1) → ℤ) (n : ℕ) : ℤ :=
  ∑ j, a j * (n : ℤ) ^ j.val

private def hwCoeffBound (k c N : ℕ) (a : Fin (k + 1) → ℤ) : Prop :=
  ∀ j, (a j).natAbs ≤ c * N ^ (k - j.val)

private lemma hw_polyEval_natAbs_le (k c N n : ℕ) (hn : n ≤ N)
    (a : Fin (k + 1) → ℤ) (ha : hwCoeffBound k c N a) :
    (hwPolyEval k a n).natAbs ≤ (k + 1) * c * N ^ k := by
  calc
    (hwPolyEval k a n).natAbs ≤
        ∑ j : Fin (k + 1), (a j * (n : ℤ) ^ j.val).natAbs := by
      exact Int.natAbs_sum_le Finset.univ _
    _ ≤ ∑ _j : Fin (k + 1), c * N ^ k := by
      gcongr with j
      simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
      calc
        (a j).natAbs * n ^ j.val ≤
            (c * N ^ (k - j.val)) * N ^ j.val := by
          gcongr
          exact ha j
        _ = c * N ^ k := by
          rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega : j.val ≤ k)]
    _ = (k + 1) * c * N ^ k := by simp [mul_assoc]

private lemma hw_fin_sub_natAbs_le (N : ℕ) (x y : Fin (N + 1)) :
    ((x.val : ℤ) - y.val).natAbs ≤ N := by
  by_cases hxy : x.val ≤ y.val
  · rw [Int.natAbs_natCast_sub_natCast_of_le hxy]
    have hy := y.isLt
    omega
  · rw [Int.natAbs_natCast_sub_natCast_of_ge (Nat.le_of_not_ge hxy)]
    have hx := x.isLt
    omega

private lemma hw_quadratic_linear_natAbs_le (c N : ℕ) (a : Fin 3 → ℤ)
    (ha : hwCoeffBound 2 c N a) (x y : Fin (N + 1)) :
    (a 2 * ((x.val : ℤ) + y.val) + a 1).natAbs ≤ 3 * c * N := by
  have ha₂ : (a 2).natAbs ≤ c := by
    simpa [hwCoeffBound] using ha (2 : Fin 3)
  have ha₁ : (a 1).natAbs ≤ c * N := by
    simpa [hwCoeffBound] using ha (1 : Fin 3)
  have hxy : (((x.val : ℤ) + y.val).natAbs) ≤ 2 * N := by
    rw [show (x.val : ℤ) + y.val = ((x.val + y.val : ℕ) : ℤ) by norm_num,
      Int.natAbs_natCast]
    omega
  calc
    (a 2 * ((x.val : ℤ) + y.val) + a 1).natAbs ≤
        (a 2 * ((x.val : ℤ) + y.val)).natAbs + (a 1).natAbs :=
      Int.natAbs_add_le _ _
    _ = (a 2).natAbs * ((x.val : ℤ) + y.val).natAbs + (a 1).natAbs := by
      rw [Int.natAbs_mul]
    _ ≤ c * (2 * N) + c * N := Nat.add_le_add (Nat.mul_le_mul ha₂ hxy) ha₁
    _ = 3 * c * N := by ring

private def hwQuadraticMap (c N : ℕ) (a : Fin 3 → ℤ)
    (ha : hwCoeffBound 2 c N a)
    (p : {p // p ∈ hwMomentFinset 4 N (hwPolyEval 2 a)}) :
    (Fin 4 → Fin (2 * N + 1)) × (Fin 4 → Fin (2 * (3 * c * N) + 1)) :=
  (fun i ↦ hwToCentered N ((p.1.1 i).val - (p.1.2 i).val)
      (hw_fin_sub_natAbs_le N (p.1.1 i) (p.1.2 i)),
    fun i ↦ hwToCentered (3 * c * N)
      (a 2 * ((p.1.1 i).val + (p.1.2 i).val) + a 1)
      (hw_quadratic_linear_natAbs_le c N a ha (p.1.1 i) (p.1.2 i)))

private lemma hw_quadraticMap_mem (c N : ℕ) (a : Fin 3 → ℤ)
    (ha : hwCoeffBound 2 c N a)
    (p : {p // p ∈ hwMomentFinset 4 N (hwPolyEval 2 a)}) :
    hwQuadraticMap c N a ha p ∈ hwCenteredFourTerm N (3 * c * N) := by
  have hfactor (i : Fin 4) :
      hwPolyEval 2 a (p.1.1 i) - hwPolyEval 2 a (p.1.2 i) =
        ((p.1.1 i).val - (p.1.2 i).val) *
          (a 2 * ((p.1.1 i).val + (p.1.2 i).val) + a 1) := by
    simp [hwPolyEval, Fin.sum_univ_succ]
    ring
  have hsum : ∑ i,
      (hwPolyEval 2 a (p.1.1 i) - hwPolyEval 2 a (p.1.2 i)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have hp := (Finset.mem_filter.mp p.2).2
    simpa [hwTupleSum] using sub_eq_zero.mpr hp
  simp only [hwCenteredFourTerm, Finset.mem_filter, Finset.mem_univ, true_and]
  dsimp [hwQuadraticMap]
  simp_rw [hw_centered_toCentered]
  simp_rw [← hfactor]
  exact hsum

private lemma hw_quadraticMap_injective (c N : ℕ) (a : Fin 3 → ℤ)
    (ha : hwCoeffBound 2 c N a) (ha₂ : a 2 ≠ 0) :
    Function.Injective (hwQuadraticMap c N a ha) := by
  intro p q hpq
  apply Subtype.ext
  apply Prod.ext <;> funext i
  · have hhenc := congrFun (congrArg Prod.fst hpq) i
    have hmenc := congrFun (congrArg Prod.snd hpq) i
    have hh := congrArg (hwCentered N) hhenc
    have hm := congrArg (hwCentered (3 * c * N)) hmenc
    simp only [hwQuadraticMap, hw_centered_toCentered] at hh hm
    have hmul : a 2 * ((p.1.1 i).val + (p.1.2 i).val) =
        a 2 * ((q.1.1 i).val + (q.1.2 i).val) := by linarith
    have hs := Int.eq_of_mul_eq_mul_left ha₂ hmul
    apply Fin.ext
    omega
  · have hhenc := congrFun (congrArg Prod.fst hpq) i
    have hmenc := congrFun (congrArg Prod.snd hpq) i
    have hh := congrArg (hwCentered N) hhenc
    have hm := congrArg (hwCentered (3 * c * N)) hmenc
    simp only [hwQuadraticMap, hw_centered_toCentered] at hh hm
    have hmul : a 2 * ((p.1.1 i).val + (p.1.2 i).val) =
        a 2 * ((q.1.1 i).val + (q.1.2 i).val) := by linarith
    have hs := Int.eq_of_mul_eq_mul_left ha₂ hmul
    apply Fin.ext
    omega

private lemma hw_quadratic_moment_le_centered (c N : ℕ) (a : Fin 3 → ℤ)
    (ha : hwCoeffBound 2 c N a) (ha₂ : a 2 ≠ 0) :
    #(hwMomentFinset 4 N (hwPolyEval 2 a)) ≤ #(hwCenteredFourTerm N (3 * c * N)) := by
  let S := {p // p ∈ hwMomentFinset 4 N (hwPolyEval 2 a)}
  let f : S → (Fin 4 → Fin (2 * N + 1)) ×
      (Fin 4 → Fin (2 * (3 * c * N) + 1)) := hwQuadraticMap c N a ha
  have himage : (Finset.univ : Finset S).image f ⊆ hwCenteredFourTerm N (3 * c * N) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, _, rfl⟩
    exact hw_quadraticMap_mem c N a ha p
  calc
    #(hwMomentFinset 4 N (hwPolyEval 2 a)) = Fintype.card S := by
      dsimp [S]
      rw [Fintype.card_subtype]
      simp
    _ = #((Finset.univ : Finset S).image f) := by
      calc
        Fintype.card S = #(Finset.univ : Finset S) := by simp
        _ = #((Finset.univ : Finset S).image f) :=
          (Finset.card_image_of_injective Finset.univ
            (hw_quadraticMap_injective c N a ha ha₂)).symm
    _ ≤ #(hwCenteredFourTerm N (3 * c * N)) := Finset.card_le_card himage

private lemma hw_quadratic_moment_bound (c : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (N : ℕ) (a : Fin 3 → ℤ), 0 < N →
      hwCoeffBound 2 c N a → a 2 ≠ 0 →
        #(hwMomentFinset 4 N (hwPolyEval 2 a)) ≤ C * N ^ 6 := by
  obtain ⟨C₀, hC₀, hfour⟩ := hw_exists_fourTermCount_bound
  let D := 3 * c
  let E := 2 * D + 1
  let C := C₀ * D ^ 3 + E ^ 4 + 108 * E ^ 3
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N a hN ha ha₂
  have hc : 0 < c := by
    have hbound := ha (2 : Fin 3)
    have hpos := Int.natAbs_pos.mpr ha₂
    norm_num at hbound
    omega
  have hD : 0 < D := by dsimp [D]; positivity
  have hNM : N ≤ D * N := by
    apply Nat.le_mul_of_pos_left
    exact hD
  have htwoN : 2 * N + 1 ≤ 3 * N := by omega
  have htwoM : 2 * (D * N) + 1 ≤ E * N := by
    rw [show E * N = 2 * (D * N) + N by dsimp [E]; ring]
    omega
  have hfour' : hwFourTermCount N (D * N) ≤ C₀ * D ^ 3 * N ^ 6 := by
    calc
      hwFourTermCount N (D * N) ≤ C₀ * (N * (D * N)) ^ 3 :=
        hfour N (D * N) hN hNM
      _ = C₀ * D ^ 3 * N ^ 6 := by ring
  have hquartic : (2 * (D * N) + 1) ^ 4 ≤ E ^ 4 * N ^ 6 := by
    calc
      (2 * (D * N) + 1) ^ 4 ≤ (E * N) ^ 4 := Nat.pow_le_pow_left htwoM 4
      _ = E ^ 4 * N ^ 4 := by ring
      _ ≤ E ^ 4 * N ^ 6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN (by omega))
  have hcubic : 4 * (2 * N + 1) ^ 3 * (2 * (D * N) + 1) ^ 3 ≤
      108 * E ^ 3 * N ^ 6 := by
    calc
      4 * (2 * N + 1) ^ 3 * (2 * (D * N) + 1) ^ 3 ≤
          4 * (3 * N) ^ 3 * (E * N) ^ 3 := by
        gcongr
      _ = 108 * E ^ 3 * N ^ 6 := by ring
  have hcenter := hw_centeredFourTerm_card_le N (D * N)
  have hcenter' : #(hwCenteredFourTerm N (D * N)) ≤ C * N ^ 6 := by
    calc
      #(hwCenteredFourTerm N (D * N)) ≤
          hwFourTermCount N (D * N) + (2 * (D * N) + 1) ^ 4 +
            4 * (2 * N + 1) ^ 3 * (2 * (D * N) + 1) ^ 3 := hcenter
      _ ≤ C₀ * D ^ 3 * N ^ 6 + E ^ 4 * N ^ 6 + 108 * E ^ 3 * N ^ 6 :=
        Nat.add_le_add (Nat.add_le_add hfour' hquartic) hcubic
      _ = C * N ^ 6 := by dsimp [C]; ring
  calc
    #(hwMomentFinset 4 N (hwPolyEval 2 a)) ≤
        #(hwCenteredFourTerm N (3 * c * N)) :=
      hw_quadratic_moment_le_centered c N a ha ha₂
    _ = #(hwCenteredFourTerm N (D * N)) := by rfl
    _ ≤ C * N ^ 6 := hcenter'

private def hwDiffCoeff (k : ℕ) (a : Fin (k + 1) → ℤ) (h : ℕ) : Fin k → ℤ :=
  fun i ↦ ∑ j : Fin (k + 1), if i.val < j.val then
    a j * (j.val.choose i.val : ℤ) * (h : ℤ) ^ (j.val - i.val - 1) else 0

private lemma hw_choose_sum_lt (k j n h : ℕ) (hj : j ≤ k) :
    (∑ i : Fin k, if i.val < j then
      (j.choose i.val : ℤ) * (h : ℤ) ^ (j - i.val) * (n : ℤ) ^ i.val else 0) =
      ((n + h : ℕ) : ℤ) ^ j - (n : ℤ) ^ j := by
  change (∑ i : Fin k, (fun m : ℕ ↦ if m < j then
    (j.choose m : ℤ) * (h : ℤ) ^ (j - m) * (n : ℤ) ^ m else 0) i.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun m : ℕ ↦ if m < j then
    (j.choose m : ℤ) * (h : ℤ) ^ (j - m) * (n : ℤ) ^ m else 0) k]
  have hsub : Finset.range j ⊆ Finset.range k := Finset.range_mono hj
  rw [← Finset.sum_subset hsub]
  · rw [show (((n + h : ℕ) : ℤ) : ℤ) = (n : ℤ) + h by norm_num]
    rw [add_pow, Finset.sum_range_succ]
    norm_num
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range.mp hi, ↓reduceIte]
    ring
  · intro i hik hij
    simp only [Finset.mem_range] at hik hij
    simp only [show ¬i < j by omega, ↓reduceIte]

private lemma hw_diffCoeff_identity (k n h : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ) :
    (h : ℤ) * hwPolyEval (k - 1)
        (fun i ↦ hwDiffCoeff k a h ⟨i.val, by omega⟩) n =
      hwPolyEval k a (n + h) - hwPolyEval k a n := by
  have hkeq : k - 1 + 1 = k := by omega
  rw [show hwPolyEval (k - 1) (fun i ↦ hwDiffCoeff k a h ⟨i.val, by omega⟩) n =
      ∑ i : Fin k, hwDiffCoeff k a h i * (n : ℤ) ^ i.val by
    unfold hwPolyEval
    apply Fintype.sum_equiv (Fin.castOrderIso hkeq).toEquiv
    intro i
    rfl]
  rw [Finset.mul_sum]
  simp only [hwDiffCoeff]
  conv_lhs =>
    enter [2, i]
    rw [← mul_assoc, Finset.mul_sum]
    rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [show hwPolyEval k a (n + h) - hwPolyEval k a n =
      ∑ j : Fin (k + 1), a j *
        (((n + h : ℕ) : ℤ) ^ j.val - (n : ℤ) ^ j.val) by
    simp [hwPolyEval, Finset.sum_sub_distrib, mul_sub]]
  apply Finset.sum_congr rfl
  intro j _
  rw [show ∑ i : Fin k,
      (h : ℤ) * (if i.val < j.val then
        a j * (j.val.choose i.val : ℤ) * (h : ℤ) ^ (j.val - i.val - 1) else 0) *
          (n : ℤ) ^ i.val =
      a j * ∑ i : Fin k, if i.val < j.val then
        (j.val.choose i.val : ℤ) * (h : ℤ) ^ (j.val - i.val) *
          (n : ℤ) ^ i.val else 0 by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · have hp : (h : ℤ) * (h : ℤ) ^ (j.val - i.val - 1) =
          (h : ℤ) ^ (j.val - i.val) := by
        rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ j.val - i.val)]
      calc
        (h : ℤ) * (a j * (j.val.choose i.val : ℤ) *
            (h : ℤ) ^ (j.val - i.val - 1)) * (n : ℤ) ^ i.val =
            ((h : ℤ) * (h : ℤ) ^ (j.val - i.val - 1)) * a j *
              (j.val.choose i.val : ℤ) * (n : ℤ) ^ i.val := by ring
        _ = a j * ((j.val.choose i.val : ℤ) * (h : ℤ) ^ (j.val - i.val) *
              (n : ℤ) ^ i.val) := by rw [hp]; ring
    · simp]
  rw [hw_choose_sum_lt k j.val n h (by omega)]

private lemma hw_diffCoeff_bound (k c N h : ℕ) (hh : h ≤ N)
    (a : Fin (k + 1) → ℤ) (ha : hwCoeffBound k c N a) (i : Fin k) :
    (hwDiffCoeff k a h i).natAbs ≤
      ((k + 1) * c * 2 ^ k) * N ^ (k - 1 - i.val) := by
  let B := c * 2 ^ k * N ^ (k - 1 - i.val)
  calc
    (hwDiffCoeff k a h i).natAbs ≤ ∑ j : Fin (k + 1),
        (if i.val < j.val then
          a j * (j.val.choose i.val : ℤ) * (h : ℤ) ^ (j.val - i.val - 1) else 0).natAbs := by
      exact Int.natAbs_sum_le Finset.univ _
    _ ≤ ∑ _j : Fin (k + 1), B := by
      gcongr with j
      split_ifs with hij
      · simp only [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow]
        have haj := ha j
        have hjk : j.val ≤ k := by omega
        have hpowtwo : 2 ^ j.val ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hjk
        have hchoose := (Nat.choose_le_two_pow j.val i.val).trans hpowtwo
        have hhpow : h ^ (j.val - i.val - 1) ≤ N ^ (j.val - i.val - 1) :=
          Nat.pow_le_pow_left hh _
        calc
          (a j).natAbs * j.val.choose i.val * h ^ (j.val - i.val - 1) ≤
              (c * N ^ (k - j.val)) * (2 ^ k) * N ^ (j.val - i.val - 1) := by
            gcongr
          _ = c * 2 ^ k * (N ^ (k - j.val) * N ^ (j.val - i.val - 1)) := by ring
          _ = B := by
            dsimp [B]
            rw [← pow_add]
            congr 2
            omega
      · simp [B]
    _ = ((k + 1) * c * 2 ^ k) * N ^ (k - 1 - i.val) := by
      simp [B]
      ring

private lemma hw_diffCoeff_top (k h : ℕ) (hk : 0 < k) (a : Fin (k + 1) → ℤ) :
    hwDiffCoeff k a h ⟨k - 1, by omega⟩ = (k : ℤ) * a ⟨k, by omega⟩ := by
  let top : Fin (k + 1) := ⟨k, by omega⟩
  change (∑ j : Fin (k + 1), if k - 1 < j.val then
    a j * (j.val.choose (k - 1) : ℤ) * (h : ℤ) ^ (j.val - (k - 1) - 1) else 0) =
      (k : ℤ) * a ⟨k, by omega⟩
  rw [Finset.sum_eq_single top]
  · dsimp [top]
    simp only [show k - 1 < k by omega, ↓reduceIte]
    have hchoose : k.choose (k - 1) = k := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right] using
        Nat.choose_succ_self_right d
    rw [hchoose, show k - (k - 1) - 1 = 0 by omega]
    norm_num
    ring
  · intro j _ hj
    have hnot : ¬k - 1 < j.val := by
      intro hlt
      apply hj
      apply Fin.ext
      dsimp [top]
      omega
    simp only [hnot, ↓reduceIte]
  · intro htop
    exact (htop (Finset.mem_univ top)).elim

private def hwDiffCoeffs (k : ℕ) (hk : 0 < k) (a : Fin (k + 1) → ℤ) (h : ℕ) :
    Fin (k - 1 + 1) → ℤ :=
  fun i ↦ hwDiffCoeff k a h ⟨i.val, by omega⟩

private lemma hw_diffCoeffs_bound (k c N h : ℕ) (hk : 0 < k) (hh : h ≤ N)
    (a : Fin (k + 1) → ℤ) (ha : hwCoeffBound k c N a) :
    hwCoeffBound (k - 1) ((k + 1) * c * 2 ^ k) N (hwDiffCoeffs k hk a h) := by
  intro i
  simpa [hwDiffCoeffs] using hw_diffCoeff_bound k c N h hh a ha ⟨i.val, by omega⟩

private lemma hw_tupleSum_sub_natAbs_le (r N V : ℕ) (f : ℕ → ℤ)
    (hf : ∀ n ≤ N, (f n).natAbs ≤ V)
    (x y : Fin r → Fin (N + 1)) :
    (hwTupleSum r N f x - hwTupleSum r N f y).natAbs ≤ 2 * r * V := by
  have hx : (hwTupleSum r N f x).natAbs ≤ r * V := by
    calc
      (hwTupleSum r N f x).natAbs ≤ ∑ i, (f (x i)).natAbs :=
        Int.natAbs_sum_le Finset.univ fun i ↦ f (x i)
      _ ≤ ∑ _i : Fin r, V := by
        gcongr with i
        exact hf _ (Nat.le_of_lt_succ (x i).isLt)
      _ = r * V := by simp
  have hy : (hwTupleSum r N f y).natAbs ≤ r * V := by
    calc
      (hwTupleSum r N f y).natAbs ≤ ∑ i, (f (y i)).natAbs :=
        Int.natAbs_sum_le Finset.univ fun i ↦ f (y i)
      _ ≤ ∑ _i : Fin r, V := by
        gcongr with i
        exact hf _ (Nat.le_of_lt_succ (y i).isLt)
      _ = r * V := by simp
  calc
    (hwTupleSum r N f x - hwTupleSum r N f y).natAbs ≤
        (hwTupleSum r N f x).natAbs + (hwTupleSum r N f y).natAbs :=
      Int.natAbs_sub_le _ _
    _ ≤ r * V + r * V := Nat.add_le_add hx hy
    _ = 2 * r * V := by ring

private lemma hw_character_moment_eq_card_of_lt (P r N V : ℕ) [NeZero P]
    (f : ℕ → ℤ) (hf : ∀ n ≤ N, (f n).natAbs ≤ V)
    (hP : 2 * r * V < P) :
    ∑ a : ZMod P,
      (hwWeylSum P N f a * (starRingEnd ℂ) (hwWeylSum P N f a)) ^ r =
        (P : ℂ) * #(hwMomentFinset r N f) := by
  simp_rw [hw_absSq_pow_expand]
  rw [sum_comm]
  conv_lhs =>
    enter [2, x]
    rw [sum_comm]
  conv_lhs =>
    enter [2, x, 2, y]
    rw [hw_char_sum_eq_indicator P _
      ((hw_tupleSum_sub_natAbs_le r N V f hf x y).trans_lt hP)]
  simp only [sub_eq_zero]
  rw [show (∑ x : Fin r → Fin (N + 1), ∑ y : Fin r → Fin (N + 1),
      if hwTupleSum r N f x = hwTupleSum r N f y then (P : ℂ) else 0) =
      (P : ℂ) * #(hwMomentFinset r N f) by
    rw [← Fintype.sum_prod_type (fun xy :
      (Fin r → Fin (N + 1)) × (Fin r → Fin (N + 1)) ↦
        if hwTupleSum r N f xy.1 = hwTupleSum r N f xy.2 then (P : ℂ) else 0)]
    rw [hwMomentFinset, Finset.card_filter]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro xy _
    split_ifs <;> simp_all]

private abbrev hwOffDiag (N : ℕ) :=
  {p : Fin (N + 1) × Fin (N + 1) // p.1 ≠ p.2}

private def hwPairSignedDiff (N : ℕ) (p : hwOffDiag N) : hwSigned N :=
  if hp : p.1.2 < p.1.1 then
    (0, ⟨p.1.1.val - p.1.2.val - 1, by
      have hx := p.1.1.isLt
      have hpv : p.1.2.val < p.1.1.val := hp
      omega⟩)
  else
    (1, ⟨p.1.2.val - p.1.1.val - 1, by
      have hy := p.1.2.isLt
      have hne := p.2
      omega⟩)

private def hwPairBase (N : ℕ) (p : hwOffDiag N) : Fin (N + 1) :=
  if p.1.2 < p.1.1 then p.1.2 else p.1.1

private lemma hw_pair_eq_of_signedDiff_eq_of_base_eq (N : ℕ) {p q : hwOffDiag N}
    (hh : hwPairSignedDiff N p = hwPairSignedDiff N q)
    (hb : hwPairBase N p = hwPairBase N q) : p = q := by
  apply Subtype.ext
  have hnep : p.1.1.val ≠ p.1.2.val := fun h ↦ p.2 (Fin.ext h)
  have hneq : q.1.1.val ≠ q.1.2.val := fun h ↦ q.2 (Fin.ext h)
  by_cases hp : p.1.2 < p.1.1 <;> by_cases hq : q.1.2 < q.1.1
  · have hmag := congrArg (fun h : hwSigned N ↦ h.2.val) hh
    have hbase := congrArg Fin.val hb
    simp [hwPairSignedDiff, hwPairBase, hp, hq] at hmag hbase
    apply Prod.ext <;> apply Fin.ext <;> omega
  · have hsign := congrArg (fun h : hwSigned N ↦ h.1.val) hh
    simp [hwPairSignedDiff, hp, hq] at hsign
  · have hsign := congrArg (fun h : hwSigned N ↦ h.1.val) hh
    simp [hwPairSignedDiff, hp, hq] at hsign
  · have hmag := congrArg (fun h : hwSigned N ↦ h.2.val) hh
    have hbase := congrArg Fin.val hb
    simp [hwPairSignedDiff, hwPairBase, hp, hq] at hmag hbase
    apply Prod.ext <;> apply Fin.ext <;> omega

private def hwOffDiagFiber (N : ℕ) (h : hwSigned N) : Finset (hwOffDiag N) :=
  Finset.univ.filter fun p ↦ hwPairSignedDiff N p = h

private noncomputable def hwDiffBlock (P N : ℕ) [NeZero P] (f : ℕ → ℤ)
    (h : hwSigned N) (a : ZMod P) : ℂ :=
  ∑ p ∈ hwOffDiagFiber N h,
    ZMod.stdAddChar (a * ((f p.1.1 - f p.1.2 : ℤ) : ZMod P))

private lemma hw_weyl_absSq_eq_diag_add_blocks (P N : ℕ) [NeZero P]
    (f : ℕ → ℤ) (a : ZMod P) :
    hwWeylSum P N f a * (starRingEnd ℂ) (hwWeylSum P N f a) =
      (N + 1 : ℕ) + ∑ h : hwSigned N, hwDiffBlock P N f h a := by
  rw [hw_conj_weylSum]
  unfold hwWeylSum
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp_rw [← AddChar.map_add_eq_mul]
  simp_rw [show ∀ x y : Fin (N + 1),
      a * (f x : ZMod P) + -(a * (f y : ZMod P)) =
        a * ((f x - f y : ℤ) : ZMod P) by
    intro x y
    push_cast
    ring]
  rw [← Fintype.sum_prod_type (fun p : Fin (N + 1) × Fin (N + 1) ↦
    ZMod.stdAddChar (a * ((f p.1 - f p.2 : ℤ) : ZMod P)))]
  let diag := fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 = p.2
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := diag)]
  have hdiag : (∑ p ∈ (Finset.univ.filter diag),
      ZMod.stdAddChar (a * ((f p.1 - f p.2 : ℤ) : ZMod P))) = (N + 1 : ℕ) := by
    have heq : (Finset.univ.filter diag) =
        (Finset.univ : Finset (Fin (N + 1))).image fun x ↦ (x, x) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, diag]
      constructor
      · intro hp
        rcases p with ⟨x, y⟩
        dsimp at hp
        subst y
        exact ⟨x, rfl⟩
      · rintro ⟨x, rfl⟩
        rfl
    rw [heq, Finset.sum_image]
    · simp
    · intro x _ y _ hxy
      exact congrArg Prod.fst hxy
  rw [hdiag]
  congr 1
  rw [← Finset.sum_subtype_eq_sum_filter
    (s := (Finset.univ : Finset (Fin (N + 1) × Fin (N + 1))))
    (p := fun p ↦ ¬diag p)
    (f := fun p ↦ ZMod.stdAddChar (a * ((f p.1 - f p.2 : ℤ) : ZMod P)))]
  rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset (hwSigned N)))
    (g := hwPairSignedDiff N) (f := fun p : hwOffDiag N ↦
      ZMod.stdAddChar (a * ((f p.1.1 - f p.1.2 : ℤ) : ZMod P))) (by simp)]
  apply Finset.sum_congr rfl
  intro h _
  simp [hwDiffBlock, hwOffDiagFiber, diag]

private def hwBlockLength (N : ℕ) (h : hwSigned N) : ℕ :=
  N - (h.2.val + 1)

private def hwPairOfBase (N : ℕ) (h : hwSigned N)
    (y : Fin (hwBlockLength N h + 1)) : hwOffDiag N :=
  if hs : h.1 = 0 then
    ⟨(⟨y.val + h.2.val + 1, by
        have hy := y.isLt
        dsimp [hwBlockLength] at hy
        omega⟩, ⟨y.val, by
        have hy := y.isLt
        dsimp [hwBlockLength] at hy
        omega⟩), by
      intro heq
      have heqval : y.val + h.2.val + 1 = y.val :=
        congrArg (fun z : Fin (N + 1) ↦ z.val) heq
      omega⟩
  else
    ⟨(⟨y.val, by
        have hy := y.isLt
        dsimp [hwBlockLength] at hy
        omega⟩, ⟨y.val + h.2.val + 1, by
        have hy := y.isLt
        dsimp [hwBlockLength] at hy
        omega⟩), by
      intro heq
      have heqval : y.val = y.val + h.2.val + 1 :=
        congrArg (fun z : Fin (N + 1) ↦ z.val) heq
      omega⟩

private lemma hw_pairOfBase_signedDiff (N : ℕ) (h : hwSigned N)
    (y : Fin (hwBlockLength N h + 1)) :
    hwPairSignedDiff N (hwPairOfBase N h y) = h := by
  rcases h with ⟨s, d⟩
  fin_cases s
  · have hlt : y.val < y.val + d.val + 1 := by omega
    apply Prod.ext <;> apply Fin.ext
    · simp [hwPairOfBase, hwPairSignedDiff, hlt]
    · simp [hwPairOfBase, hwPairSignedDiff, hlt]
      omega
  · have hnot : ¬y.val + d.val + 1 < y.val := by omega
    apply Prod.ext <;> apply Fin.ext
    · simp [hwPairOfBase, hwPairSignedDiff, hnot]
    · simp [hwPairOfBase, hwPairSignedDiff, hnot]
      omega

private lemma hw_pairOfBase_base (N : ℕ) (h : hwSigned N)
    (y : Fin (hwBlockLength N h + 1)) :
    (hwPairBase N (hwPairOfBase N h y)).val = y.val := by
  rcases h with ⟨s, d⟩
  fin_cases s
  · have hlt : y.val < y.val + d.val + 1 := by omega
    simp [hwPairOfBase, hwPairBase, hlt]
  · have hnot : ¬y.val + d.val + 1 < y.val := by omega
    simp [hwPairOfBase, hwPairBase, hnot]

private lemma hw_pairBase_lt (N : ℕ) (h : hwSigned N) (p : hwOffDiag N)
    (hp : hwPairSignedDiff N p = h) :
    (hwPairBase N p).val < hwBlockLength N h + 1 := by
  have hmag := congrArg (fun z : hwSigned N ↦ z.2.val) hp
  by_cases hxy : p.1.2 < p.1.1
  · simp [hwPairSignedDiff, hwPairBase, hxy] at hmag ⊢
    have hx := p.1.1.isLt
    dsimp [hwBlockLength]
    omega
  · have hne : p.1.1.val ≠ p.1.2.val := fun h ↦ p.2 (Fin.ext h)
    have hy := p.1.2.isLt
    simp [hwPairSignedDiff, hwPairBase, hxy] at hmag ⊢
    dsimp [hwBlockLength]
    omega

private lemma hw_offDiagFiber_eq_image_pairOfBase (N : ℕ) (h : hwSigned N) :
    hwOffDiagFiber N h =
      (Finset.univ : Finset (Fin (hwBlockLength N h + 1))).image (hwPairOfBase N h) := by
  ext p
  constructor
  · intro hp
    have hdiff : hwPairSignedDiff N p = h := (Finset.mem_filter.mp hp).2
    let y : Fin (hwBlockLength N h + 1) :=
      ⟨(hwPairBase N p).val, hw_pairBase_lt N h p hdiff⟩
    apply Finset.mem_image.mpr
    refine ⟨y, Finset.mem_univ _, ?_⟩
    apply hw_pair_eq_of_signedDiff_eq_of_base_eq N
    · rw [hw_pairOfBase_signedDiff, hdiff]
    · apply Fin.ext
      exact hw_pairOfBase_base N h y
  · rintro hp
    rcases Finset.mem_image.mp hp with ⟨y, _, rfl⟩
    simp [hwOffDiagFiber, hw_pairOfBase_signedDiff]

private lemma hw_pairOfBase_injective (N : ℕ) (h : hwSigned N) :
    Function.Injective (hwPairOfBase N h) := by
  intro x y hxy
  apply Fin.ext
  have := congrArg (fun p ↦ (hwPairBase N p).val) hxy
  simpa [hw_pairOfBase_base] using this

private lemma hw_pairOfBase_polyDiff (k N : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ) (h : hwSigned N)
    (y : Fin (hwBlockLength N h + 1)) :
    hwPolyEval k a (hwPairOfBase N h y).1.1 -
        hwPolyEval k a (hwPairOfBase N h y).1.2 =
      hwSignedVal N h * hwPolyEval (k - 1)
        (hwDiffCoeffs k hk a (h.2.val + 1)) y.val := by
  have hid := hw_diffCoeff_identity k y.val (h.2.val + 1) hk a
  change ((h.2.val + 1 : ℕ) : ℤ) *
      hwPolyEval (k - 1) (hwDiffCoeffs k hk a (h.2.val + 1)) y.val =
        hwPolyEval k a (y.val + (h.2.val + 1)) - hwPolyEval k a y.val at hid
  rcases h with ⟨s, d⟩
  fin_cases s
  · simp only [hwPairOfBase, hwSignedVal]
    norm_num
    simpa [add_assoc] using hid.symm
  · simp only [hwPairOfBase, hwSignedVal]
    norm_num
    change (((d.val + 1 : ℕ) : ℤ) *
        hwPolyEval (k - 1) (hwDiffCoeffs k hk a (d.val + 1)) y.val =
          hwPolyEval k a (y.val + (d.val + 1)) - hwPolyEval k a y.val) at hid
    rw [show y.val + d.val + 1 = y.val + (d.val + 1) by omega]
    calc
      hwPolyEval k a y.val - hwPolyEval k a (y.val + (d.val + 1)) =
          -(hwPolyEval k a (y.val + (d.val + 1)) - hwPolyEval k a y.val) := by ring
      _ = -(((d.val + 1 : ℕ) : ℤ) *
          hwPolyEval (k - 1) (hwDiffCoeffs k hk a (d.val + 1)) y.val) := by
        rw [← hid]
      _ = (-1 + -(d.val : ℤ)) *
          hwPolyEval (k - 1) (hwDiffCoeffs k hk a (d.val + 1)) y.val := by
        push_cast
        ring

private lemma hw_diffBlock_eq_weyl (P k N : ℕ) [NeZero P] (hk : 0 < k)
    (a : Fin (k + 1) → ℤ) (h : hwSigned N) (α : ZMod P) :
    hwDiffBlock P N (hwPolyEval k a) h α =
      hwWeylSum P (hwBlockLength N h)
        (hwPolyEval (k - 1) (hwDiffCoeffs k hk a (h.2.val + 1)))
        (α * (hwSignedVal N h : ZMod P)) := by
  rw [hwDiffBlock, hw_offDiagFiber_eq_image_pairOfBase,
    Finset.sum_image (hw_pairOfBase_injective N h).injOn]
  unfold hwWeylSum
  apply Finset.sum_congr rfl
  intro y _
  rw [hw_pairOfBase_polyDiff k N hk a h y]
  congr 1
  push_cast
  ring

private lemma hw_absSq_pow_eq_norm_pow (z : ℂ) (r : ℕ) :
    (z * (starRingEnd ℂ) z) ^ r = ((‖z‖ ^ (2 * r) : ℝ) : ℂ) := by
  rw [Complex.mul_conj']
  norm_cast
  rw [← pow_mul]

private abbrev hwBlockChoice (r N : ℕ) :=
  Σ h : hwSigned N,
    (Fin r → Fin (hwBlockLength N h + 1)) ×
      (Fin r → Fin (hwBlockLength N h + 1))

private def hwBlockChoiceDiff (k r N : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ) (z : hwBlockChoice r N) : ℤ :=
  hwTupleSum r (hwBlockLength N z.1)
      (hwPolyEval (k - 1) (hwDiffCoeffs k hk a (z.1.2.val + 1))) z.2.1 -
    hwTupleSum r (hwBlockLength N z.1)
      (hwPolyEval (k - 1) (hwDiffCoeffs k hk a (z.1.2.val + 1))) z.2.2

private def hwBlockChoiceFreq (k r N : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ) (z : hwBlockChoice r N) : ℤ :=
  hwSignedVal N z.1 * hwBlockChoiceDiff k r N hk a z

private lemma hw_diffBlock_absSq_pow_expand (P k r N : ℕ) [NeZero P]
    (hk : 0 < k) (a : Fin (k + 1) → ℤ) (h : hwSigned N) (α : ZMod P) :
    (hwDiffBlock P N (hwPolyEval k a) h α *
        (starRingEnd ℂ) (hwDiffBlock P N (hwPolyEval k a) h α)) ^ r =
      ∑ x : Fin r → Fin (hwBlockLength N h + 1),
        ∑ y : Fin r → Fin (hwBlockLength N h + 1),
          ZMod.stdAddChar (α *
            ((hwSignedVal N h *
              (hwTupleSum r (hwBlockLength N h)
                  (hwPolyEval (k - 1) (hwDiffCoeffs k hk a (h.2.val + 1))) x -
                hwTupleSum r (hwBlockLength N h)
                  (hwPolyEval (k - 1) (hwDiffCoeffs k hk a (h.2.val + 1))) y) : ℤ) :
              ZMod P)) := by
  rw [hw_diffBlock_eq_weyl P k N hk a h α]
  rw [hw_absSq_pow_expand]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  push_cast
  ring

private lemma hw_sum_block_absSq_pow_expand (P k r N : ℕ) [NeZero P]
    (hk : 0 < k) (a : Fin (k + 1) → ℤ) (α : ZMod P) :
    (∑ h : hwSigned N,
      (hwDiffBlock P N (hwPolyEval k a) h α *
        (starRingEnd ℂ) (hwDiffBlock P N (hwPolyEval k a) h α)) ^ r) =
      ∑ z : hwBlockChoice r N,
        ZMod.stdAddChar (α * (hwBlockChoiceFreq k r N hk a z : ZMod P)) := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro h _
  rw [hw_diffBlock_absSq_pow_expand P k r N hk a h α]
  rw [Fintype.sum_prod_type]
  rfl

private lemma hw_char_sum_four_expand {C : Type*} [Fintype C]
    (P : ℕ) [NeZero P] (v : C → ℤ) (α : ZMod P) :
    (∑ z : C, ZMod.stdAddChar (α * (v z : ZMod P))) ^ 4 =
      ∑ u : Fin 4 → C,
        ZMod.stdAddChar (α * ((∑ i, v (u i) : ℤ) : ZMod P)) := by
  rw [Finset.sum_pow' Finset.univ]
  simp only [Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro u _
  rw [show α * ((∑ i, v (u i) : ℤ) : ZMod P) =
      ∑ i, α * (v (u i) : ZMod P) by push_cast; rw [mul_sum]]
  exact (hw_addChar_map_sum ZMod.stdAddChar Finset.univ _).symm

private def hwZeroQuadruples {C : Type*} [Fintype C] (v : C → ℤ) :
    Finset (Fin 4 → C) :=
  Finset.univ.filter fun u ↦ ∑ i, v (u i) = 0

private lemma hw_sum_char_four_eq_zero_count_of_lt {C : Type*} [Fintype C]
    (P N M : ℕ) [NeZero P] (v : C → ℤ)
    (hv : ∀ z, (v z).natAbs ≤ N * M) (hP : 4 * N * M < P) :
    ∑ α : ZMod P, (∑ z : C, ZMod.stdAddChar (α * (v z : ZMod P))) ^ 4 =
      (P : ℂ) * #(hwZeroQuadruples v) := by
  simp_rw [hw_char_sum_four_expand]
  rw [sum_comm]
  conv_lhs =>
    enter [2, u]
    rw [hw_char_sum_eq_indicator P]
    · skip
    · calc
        ((∑ i, v (u i) : ℤ)).natAbs ≤ ∑ i, (v (u i)).natAbs :=
          Int.natAbs_sum_le Finset.univ _
        _ ≤ ∑ _i : Fin 4, N * M := by
          gcongr with i
          exact hv (u i)
        _ < P := by simpa [mul_assoc] using hP
  rw [hwZeroQuadruples, Finset.card_filter]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  split_ifs <;> simp_all

private lemma hw_blockChoiceDiff_natAbs_le (k c r N : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ) (ha : hwCoeffBound k c N a) (z : hwBlockChoice r N) :
    (hwBlockChoiceDiff k r N hk a z).natAbs ≤
      2 * r * (k * ((k + 1) * c * 2 ^ k) * N ^ (k - 1)) := by
  let D := (k + 1) * c * 2 ^ k
  let V := k * D * N ^ (k - 1)
  have hh : z.1.2.val + 1 ≤ N := by omega
  have hL : hwBlockLength N z.1 ≤ N := Nat.sub_le _ _
  have hcoeff : hwCoeffBound (k - 1) D N
      (hwDiffCoeffs k hk a (z.1.2.val + 1)) := by
    simpa [D] using hw_diffCoeffs_bound k c N (z.1.2.val + 1) hk hh a ha
  have hvalue : ∀ n ≤ hwBlockLength N z.1,
      (hwPolyEval (k - 1) (hwDiffCoeffs k hk a (z.1.2.val + 1)) n).natAbs ≤ V := by
    intro n hn
    have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
    simpa [V, D, hk', mul_assoc] using
      hw_polyEval_natAbs_le (k - 1) D N n (hn.trans hL)
        (hwDiffCoeffs k hk a (z.1.2.val + 1)) hcoeff
  simpa [hwBlockChoiceDiff, V, D] using
    hw_tupleSum_sub_natAbs_le r (hwBlockLength N z.1) V
      (hwPolyEval (k - 1) (hwDiffCoeffs k hk a (z.1.2.val + 1))) hvalue z.2.1 z.2.2

private def hwBlockQuadMap (k r N M : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ)
    (hm : ∀ z : hwBlockChoice r N, (hwBlockChoiceDiff k r N hk a z).natAbs ≤ M)
    (u : Fin 4 → hwBlockChoice r N) :
    (Fin 4 → Fin (2 * N + 1)) × (Fin 4 → Fin (2 * M + 1)) :=
  (fun i ↦ hwSignedToCentered N (u i).1,
    fun i ↦ hwToCentered M (hwBlockChoiceDiff k r N hk a (u i)) (hm (u i)))

private lemma hw_blockQuadMap_mem (k r N M : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ)
    (hm : ∀ z : hwBlockChoice r N, (hwBlockChoiceDiff k r N hk a z).natAbs ≤ M)
    {u : Fin 4 → hwBlockChoice r N}
    (hu : u ∈ hwZeroQuadruples (hwBlockChoiceFreq k r N hk a)) :
    hwBlockQuadMap k r N M hk a hm u ∈ hwCenteredFourNonzero N M := by
  have hzero : ∑ i, hwBlockChoiceFreq k r N hk a (u i) = 0 :=
    (Finset.mem_filter.mp hu).2
  simp only [hwCenteredFourNonzero, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · simp only [hwBlockQuadMap, hw_centered_signedToCentered, hw_centered_toCentered]
    simpa [hwBlockChoiceFreq] using hzero
  · intro i
    simp only [hwBlockQuadMap, hw_centered_signedToCentered]
    exact hw_signedVal_ne_zero N (u i).1

private lemma hw_blockQuadMap_image_card_le (k r N M : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ)
    (hm : ∀ z : hwBlockChoice r N, (hwBlockChoiceDiff k r N hk a z).natAbs ≤ M) :
    #((hwZeroQuadruples (hwBlockChoiceFreq k r N hk a)).image
        (hwBlockQuadMap k r N M hk a hm)) ≤ hwFourTermCount N M := by
  calc
    #((hwZeroQuadruples (hwBlockChoiceFreq k r N hk a)).image
        (hwBlockQuadMap k r N M hk a hm)) ≤ #(hwCenteredFourNonzero N M) := by
      apply Finset.card_le_card
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨u, hu, rfl⟩
      exact hw_blockQuadMap_mem k r N M hk a hm hu
    _ ≤ hwFourTermCount N M := hw_centeredFourNonzero_card_le N M

private def hwBlockChoiceEmbed (r N : ℕ) (z : hwBlockChoice r N) :
    hwSigned N ×
      ((Fin r → Fin (N + 1)) × (Fin r → Fin (N + 1))) :=
  (z.1, hwMomentLift r (hwBlockLength N z.1) N (Nat.sub_le _ _) z.2)

private lemma hw_blockChoiceEmbed_injective (r N : ℕ) :
    Function.Injective (hwBlockChoiceEmbed r N) := by
  rintro ⟨h, p⟩ ⟨h', p'⟩ heq
  have hh : h = h' := congrArg Prod.fst heq
  subst h'
  have hp : p = p' :=
    hw_momentLift_injective r (hwBlockLength N h) N (Nat.sub_le _ _)
      (congrArg Prod.snd heq)
  exact Sigma.ext rfl (heq_of_eq hp)

private lemma hw_blockChoiceEmbed_diff (k r N : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ) (z : hwBlockChoice r N) :
    (hwBlockChoiceEmbed r N z).2 ∈
      hwDiffFiber r N
        (hwPolyEval (k - 1) (hwDiffCoeffs k hk a (z.1.2.val + 1)))
        (hwBlockChoiceDiff k r N hk a z) := by
  simp only [hwDiffFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  simp [hwBlockChoiceEmbed, hwBlockChoiceDiff, hwMomentLift, hwTupleSum, hwFinLift]

private lemma hw_blockQuadMap_fiber_card_le (k r N M A : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ)
    (hm : ∀ z : hwBlockChoice r N, (hwBlockChoiceDiff k r N hk a z).natAbs ≤ M)
    (hA : ∀ h : hwSigned N,
      #(hwMomentFinset r N
        (hwPolyEval (k - 1) (hwDiffCoeffs k hk a (h.2.val + 1)))) ≤ A)
    (b : (Fin 4 → Fin (2 * N + 1)) × (Fin 4 → Fin (2 * M + 1))) :
    #({u ∈ hwZeroQuadruples (hwBlockChoiceFreq k r N hk a) |
        hwBlockQuadMap k r N M hk a hm u = b}) ≤ A ^ 4 := by
  let S := {u ∈ hwZeroQuadruples (hwBlockChoiceFreq k r N hk a) |
    hwBlockQuadMap k r N M hk a hm u = b}
  by_cases hS : S.Nonempty
  · obtain ⟨u₀, hu₀⟩ := hS
    let enc : (Fin 4 → hwBlockChoice r N) →
        (Fin 4 → hwSigned N ×
          ((Fin r → Fin (N + 1)) × (Fin r → Fin (N + 1)))) :=
      fun u i ↦ hwBlockChoiceEmbed r N (u i)
    let T : Fin 4 → Finset (hwSigned N ×
        ((Fin r → Fin (N + 1)) × (Fin r → Fin (N + 1)))) :=
      fun i ↦ ({(u₀ i).1} : Finset (hwSigned N)).product
        (hwDiffFiber r N
          (hwPolyEval (k - 1) (hwDiffCoeffs k hk a ((u₀ i).1.2.val + 1)))
          (hwBlockChoiceDiff k r N hk a (u₀ i)))
    have henc : Function.Injective enc := by
      intro u v huv
      funext i
      exact hw_blockChoiceEmbed_injective r N (congrFun huv i)
    have himage : S.image enc ⊆ Fintype.piFinset T := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
      rw [Fintype.mem_piFinset]
      intro i
      have humap : hwBlockQuadMap k r N M hk a hm u = b :=
        (Finset.mem_filter.mp hu).2
      have hu₀map : hwBlockQuadMap k r N M hk a hm u₀ = b :=
        (Finset.mem_filter.mp hu₀).2
      have hmap : hwBlockQuadMap k r N M hk a hm u =
          hwBlockQuadMap k r N M hk a hm u₀ := humap.trans hu₀map.symm
      have hhenc : hwSignedToCentered N (u i).1 =
          hwSignedToCentered N (u₀ i).1 := by
        exact congrFun (congrArg Prod.fst hmap) i
      have hh : (u i).1 = (u₀ i).1 := by
        apply (hwSignedEquivCentered N).injective
        apply Subtype.ext
        exact hhenc
      have hdenc := congrFun (congrArg Prod.snd hmap) i
      have hdcenter := congrArg (hwCentered M) hdenc
      have hd : hwBlockChoiceDiff k r N hk a (u i) =
          hwBlockChoiceDiff k r N hk a (u₀ i) := by
        simpa only [hwBlockQuadMap, hw_centered_toCentered] using hdcenter
      have hdiff := hw_blockChoiceEmbed_diff k r N hk a (u i)
      change hwBlockChoiceEmbed r N (u i) ∈
        ({(u₀ i).1} : Finset (hwSigned N)).product
          (hwDiffFiber r N
            (hwPolyEval (k - 1) (hwDiffCoeffs k hk a ((u₀ i).1.2.val + 1)))
            (hwBlockChoiceDiff k r N hk a (u₀ i)))
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_singleton.mpr hh,
        by simpa [hh, hd] using hdiff⟩
    change #S ≤ A ^ 4
    calc
      #S = #(S.image enc) :=
        (Finset.card_image_of_injective S henc).symm
      _ ≤ #(Fintype.piFinset T) := Finset.card_le_card himage
      _ = ∏ i, #(T i) := Fintype.card_piFinset T
      _ = ∏ i, #(hwDiffFiber r N
          (hwPolyEval (k - 1) (hwDiffCoeffs k hk a ((u₀ i).1.2.val + 1)))
          (hwBlockChoiceDiff k r N hk a (u₀ i))) := by
        apply Finset.prod_congr rfl
        intro i _
        simp [T]
      _ ≤ ∏ _i : Fin 4, A := by
        gcongr with i
        exact (hw_diffFiber_card_le_moment r N
          (hwPolyEval (k - 1) (hwDiffCoeffs k hk a ((u₀ i).1.2.val + 1)))
          (hwBlockChoiceDiff k r N hk a (u₀ i))).trans (hA (u₀ i).1)
      _ = A ^ 4 := by simp
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change #S ≤ A ^ 4
    simp [hzero]

private lemma hw_zeroQuadruples_card_le (k r N M A : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ)
    (hm : ∀ z : hwBlockChoice r N, (hwBlockChoiceDiff k r N hk a z).natAbs ≤ M)
    (hA : ∀ h : hwSigned N,
      #(hwMomentFinset r N
        (hwPolyEval (k - 1) (hwDiffCoeffs k hk a (h.2.val + 1)))) ≤ A) :
    #(hwZeroQuadruples (hwBlockChoiceFreq k r N hk a)) ≤
      hwFourTermCount N M * A ^ 4 := by
  let S := hwZeroQuadruples (hwBlockChoiceFreq k r N hk a)
  let f := hwBlockQuadMap k r N M hk a hm
  have hmap : Set.MapsTo f (↑S) (↑(S.image f)) := by
    intro u hu
    exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  change #S ≤ _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    (∑ b ∈ S.image f, #{u ∈ S | f u = b}) ≤
        ∑ _b ∈ S.image f, A ^ 4 := by
      gcongr with b
      exact hw_blockQuadMap_fiber_card_le k r N M A hk a hm hA b
    _ = #(S.image f) * A ^ 4 := by simp
    _ ≤ hwFourTermCount N M * A ^ 4 := by
      gcongr
      exact hw_blockQuadMap_image_card_le k r N M hk a hm

private lemma hw_real_character_moment_eq_card_of_lt (P r N V : ℕ) [NeZero P]
    (f : ℕ → ℤ) (hf : ∀ n ≤ N, (f n).natAbs ≤ V)
    (hP : 2 * r * V < P) :
    ∑ α : ZMod P, ‖hwWeylSum P N f α‖ ^ (2 * r) =
      (P : ℝ) * #(hwMomentFinset r N f) := by
  have h := hw_character_moment_eq_card_of_lt P r N V f hf hP
  have hre := congrArg Complex.re h
  simp_rw [hw_absSq_pow_eq_norm_pow] at hre
  rw [Complex.re_sum] at hre
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero] at hre
  simpa using hre

private lemma hw_add_pow_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    (x + y) ^ n ≤ 2 ^ n * (x ^ n + y ^ n) := by
  have hxy : x + y ≤ 2 * max x y := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]
      linarith
    · rw [max_eq_left h]
      linarith
  calc
    (x + y) ^ n ≤ (2 * max x y) ^ n :=
      pow_le_pow_left₀ (add_nonneg hx hy) hxy n
    _ = 2 ^ n * (max x y) ^ n := by rw [mul_pow]
    _ ≤ 2 ^ n * (x ^ n + y ^ n) := by
      gcongr
      rcases le_total x y with h | h
      · rw [max_eq_right h]
        exact le_add_of_nonneg_left (pow_nonneg hx n)
      · rw [max_eq_left h]
        exact le_add_of_nonneg_right (pow_nonneg hy n)

private lemma hw_weyl_pointwise_le (P k r N : ℕ) [NeZero P] (hr : 0 < r)
    (a : Fin (k + 1) → ℤ) (α : ZMod P) :
    ‖hwWeylSum P N (hwPolyEval k a) α‖ ^ (16 * r) ≤
      2 ^ (8 * r) *
        (((N + 1 : ℕ) : ℝ) ^ (8 * r) +
          ((2 * N : ℕ) : ℝ) ^ (8 * r - 4) *
            (∑ h : hwSigned N,
              ‖hwDiffBlock P N (hwPolyEval k a) h α‖ ^ (2 * r)) ^ 4) := by
  let W := hwWeylSum P N (hwPolyEval k a) α
  let X : hwSigned N → ℝ :=
    fun h ↦ ‖hwDiffBlock P N (hwPolyEval k a) h α‖
  let U := ∑ h : hwSigned N, X h ^ (2 * r)
  have hsq : ‖W‖ ^ 2 ≤ ((N + 1 : ℕ) : ℝ) + ∑ h : hwSigned N, X h := by
    calc
      ‖W‖ ^ 2 = ‖W * (starRingEnd ℂ) W‖ := by
        rw [norm_mul, Complex.norm_conj, pow_two]
      _ = ‖((N + 1 : ℕ) : ℂ) +
          ∑ h : hwSigned N, hwDiffBlock P N (hwPolyEval k a) h α‖ := by
        rw [hw_weyl_absSq_eq_diag_add_blocks]
      _ ≤ ‖((N + 1 : ℕ) : ℂ)‖ +
          ‖∑ h : hwSigned N, hwDiffBlock P N (hwPolyEval k a) h α‖ :=
        norm_add_le _ _
      _ ≤ ((N + 1 : ℕ) : ℝ) + ∑ h : hwSigned N, X h := by
        apply add_le_add
        · exact le_of_eq (Complex.norm_natCast (N + 1))
        · simpa [X] using
            norm_sum_le (Finset.univ : Finset (hwSigned N))
              (fun h ↦ hwDiffBlock P N (hwPolyEval k a) h α)
  have hmean : (∑ h : hwSigned N, X h) ^ (2 * r) ≤
      ((2 * N : ℕ) : ℝ) ^ (2 * r - 1) * U := by
    have hp := pow_sum_le_card_mul_sum_pow
      (s := (Finset.univ : Finset (hwSigned N)))
      (f := X) (fun h _ ↦ norm_nonneg _) (2 * r - 1)
    have hexp : 2 * r - 1 + 1 = 2 * r := by omega
    simpa [U, X, hwSigned, hexp] using hp
  have hblock : (∑ h : hwSigned N, X h) ^ (8 * r) ≤
      ((2 * N : ℕ) : ℝ) ^ (8 * r - 4) * U ^ 4 := by
    calc
      (∑ h : hwSigned N, X h) ^ (8 * r) =
          ((∑ h : hwSigned N, X h) ^ (2 * r)) ^ 4 := by
        rw [← pow_mul]
        congr 1
        omega
      _ ≤ (((2 * N : ℕ) : ℝ) ^ (2 * r - 1) * U) ^ 4 := by
        exact pow_le_pow_left₀ (pow_nonneg (sum_nonneg fun h _ ↦ norm_nonneg _) (2 * r))
          hmean 4
      _ = ((2 * N : ℕ) : ℝ) ^ (8 * r - 4) * U ^ 4 := by
        rw [mul_pow, ← pow_mul]
        congr 2
        omega
  calc
    ‖hwWeylSum P N (hwPolyEval k a) α‖ ^ (16 * r) =
        (‖W‖ ^ 2) ^ (8 * r) := by
      dsimp [W]
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ (((N + 1 : ℕ) : ℝ) + ∑ h : hwSigned N, X h) ^ (8 * r) :=
      pow_le_pow_left₀ (sq_nonneg _) hsq (8 * r)
    _ ≤ 2 ^ (8 * r) *
        (((N + 1 : ℕ) : ℝ) ^ (8 * r) +
          (∑ h : hwSigned N, X h) ^ (8 * r)) :=
      hw_add_pow_le _ _ (by positivity) (sum_nonneg fun h _ ↦ norm_nonneg _) _
    _ ≤ 2 ^ (8 * r) *
        (((N + 1 : ℕ) : ℝ) ^ (8 * r) +
          ((2 * N : ℕ) : ℝ) ^ (8 * r - 4) * U ^ 4) := by
      gcongr
    _ = _ := by rfl

private lemma hw_block_fourth_sum_eq_zero_count_of_lt
    (P k r N M : ℕ) [NeZero P] (hk : 0 < k) (a : Fin (k + 1) → ℤ)
    (hm : ∀ z : hwBlockChoice r N, (hwBlockChoiceDiff k r N hk a z).natAbs ≤ M)
    (hP : 4 * N * M < P) :
    ∑ α : ZMod P,
      (∑ h : hwSigned N,
        ‖hwDiffBlock P N (hwPolyEval k a) h α‖ ^ (2 * r)) ^ 4 =
      (P : ℝ) * #(hwZeroQuadruples (hwBlockChoiceFreq k r N hk a)) := by
  have hfreq : ∀ z : hwBlockChoice r N,
      (hwBlockChoiceFreq k r N hk a z).natAbs ≤ N * M := by
    intro z
    rw [hwBlockChoiceFreq, Int.natAbs_mul]
    exact Nat.mul_le_mul (hw_signedVal_natAbs_le N z.1) (hm z)
  have hchar := hw_sum_char_four_eq_zero_count_of_lt P N M
    (hwBlockChoiceFreq k r N hk a) hfreq hP
  have hpoint (α : ZMod P) :
      (∑ z : hwBlockChoice r N,
        ZMod.stdAddChar (α * (hwBlockChoiceFreq k r N hk a z : ZMod P))) =
        ((∑ h : hwSigned N,
          ‖hwDiffBlock P N (hwPolyEval k a) h α‖ ^ (2 * r) : ℝ) : ℂ) := by
    calc
      (∑ z : hwBlockChoice r N,
          ZMod.stdAddChar (α * (hwBlockChoiceFreq k r N hk a z : ZMod P))) =
          ∑ h : hwSigned N,
            (hwDiffBlock P N (hwPolyEval k a) h α *
              (starRingEnd ℂ) (hwDiffBlock P N (hwPolyEval k a) h α)) ^ r :=
        (hw_sum_block_absSq_pow_expand P k r N hk a α).symm
      _ = ((∑ h : hwSigned N,
          ‖hwDiffBlock P N (hwPolyEval k a) h α‖ ^ (2 * r) : ℝ) : ℂ) := by
        simp_rw [hw_absSq_pow_eq_norm_pow]
        push_cast
        rfl
  simp_rw [hpoint, ← Complex.ofReal_pow] at hchar
  have hre := congrArg Complex.re hchar
  rw [Complex.re_sum] at hre
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero] at hre
  simpa using hre

private def hwStepR (k : ℕ) : ℕ := 4 * 8 ^ (k - 3)

private def hwStepD (k c : ℕ) : ℕ := (k + 1) * c * 2 ^ k

private def hwStepV (k c N : ℕ) : ℕ :=
  k * hwStepD k c * N ^ (k - 1)

private def hwStepM (k c N : ℕ) : ℕ :=
  max N (2 * hwStepR k * hwStepV k c N)

private def hwStepE (k c : ℕ) : ℕ :=
  2 * hwStepR k * k * hwStepD k c + 1

private lemma hw_step_pow_relations (k : ℕ) (hk : 3 ≤ k) :
    2 * hwStepR k = 8 ^ (k - 2) ∧
      8 * hwStepR k = 8 ^ (k - 1) / 2 ∧
      16 * hwStepR k = 8 ^ (k - 1) ∧
      8 ^ (k - 2) / 2 = hwStepR k := by
  have h₁ : k - 2 = (k - 3) + 1 := by omega
  have h₂ : k - 1 = (k - 3) + 2 := by omega
  dsimp [hwStepR]
  rw [h₁, h₂, pow_succ, pow_succ, pow_succ]
  omega

private lemma hw_step_degree_bounds (k : ℕ) (hk : 3 ≤ k) :
    k - 1 ≤ 2 * hwStepR k ∧ k ≤ 8 * hwStepR k := by
  have haux : ∀ m : ℕ, 1 ≤ m → m + 1 ≤ 8 ^ m := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
        by_cases hm0 : m = 0
        · subst m
          norm_num
        · have ih' := ih (by omega : 1 ≤ m)
          rw [pow_succ]
          calc
            m + 1 + 1 ≤ 8 * (m + 1) := by omega
            _ ≤ 8 * 8 ^ m := Nat.mul_le_mul_left 8 ih'
            _ = 8 ^ m * 8 := by ac_rfl
  have hdegree : k - 1 ≤ 8 ^ (k - 2) := by
    have := haux (k - 2) (by omega)
    convert this using 1
    all_goals omega
  have hrel := (hw_step_pow_relations k hk).1
  rw [← hrel] at hdegree
  constructor
  · exact hdegree
  · have hr : 0 < hwStepR k := by
      exact Nat.mul_pos (by omega) (pow_pos (by omega) _)
    omega

private lemma hw_stepM_bounds (k c N : ℕ) (hk : 3 ≤ k) (_hN : 0 < N) :
    N ≤ hwStepM k c N ∧
      hwStepM k c N ≤ hwStepE k c * N ^ (k - 1) := by
  have hpow : N ≤ N ^ (k - 1) := Nat.le_pow (by omega)
  constructor
  · exact le_max_left _ _
  · apply max_le
    · exact hpow.trans (Nat.le_mul_of_pos_left _ (by simp [hwStepE]))
    · calc
        2 * hwStepR k * hwStepV k c N =
            (2 * hwStepR k * k * hwStepD k c) * N ^ (k - 1) := by
          simp [hwStepV]
          ring
        _ ≤ hwStepE k c * N ^ (k - 1) := by
          gcongr
          simp [hwStepE]

private lemma hw_step_zero_count_bound (k c Cᵢ C₄ N : ℕ) (hk : 3 ≤ k)
    (hN : 0 < N) (a : Fin (k + 1) → ℤ) (ha : hwCoeffBound k c N a)
    (haTop : a ⟨k, by omega⟩ ≠ 0)
    (hI : ∀ (N : ℕ) (b : Fin (k - 1 + 1) → ℤ), 0 < N →
      hwCoeffBound (k - 1) (hwStepD k c) N b → b ⟨k - 1, by omega⟩ ≠ 0 →
      #(hwMomentFinset (8 ^ (k - 2) / 2) N (hwPolyEval (k - 1) b)) ≤
        Cᵢ * N ^ (8 ^ (k - 2) - (k - 1)))
    (hfour : ∀ H M : ℕ, 0 < H → H ≤ M →
      hwFourTermCount H M ≤ C₄ * (H * M) ^ 3) :
    #(hwZeroQuadruples
        (hwBlockChoiceFreq k (hwStepR k) N (by omega) a)) ≤
      (C₄ * hwStepE k c ^ 3 * Cᵢ ^ 4) *
        N ^ (8 * hwStepR k - k + 4) := by
  let r := hwStepR k
  let D := hwStepD k c
  let V := hwStepV k c N
  let M := hwStepM k c N
  let A := Cᵢ * N ^ (2 * r - (k - 1))
  have hrel := hw_step_pow_relations k hk
  have hdegree := (hw_step_degree_bounds k hk).1
  have hm : ∀ z : hwBlockChoice r N,
      (hwBlockChoiceDiff k r N (by omega) a z).natAbs ≤ M := by
    intro z
    have hz := hw_blockChoiceDiff_natAbs_le k c r N (by omega) a ha z
    apply hz.trans
    change 2 * r * V ≤ M
    exact le_max_right _ _
  have hA : ∀ h : hwSigned N,
      #(hwMomentFinset r N
        (hwPolyEval (k - 1) (hwDiffCoeffs k (by omega) a (h.2.val + 1)))) ≤ A := by
    intro h
    have hh : h.2.val + 1 ≤ N := by omega
    have hcoeff : hwCoeffBound (k - 1) D N
        (hwDiffCoeffs k (by omega) a (h.2.val + 1)) := by
      simpa [D, hwStepD] using
        hw_diffCoeffs_bound k c N (h.2.val + 1) (by omega) hh a ha
    have htop : (hwDiffCoeffs k (by omega) a (h.2.val + 1)) ⟨k - 1, by omega⟩ =
        (k : ℤ) * a ⟨k, by omega⟩ := by
      simpa [hwDiffCoeffs] using
        hw_diffCoeff_top k (h.2.val + 1) (by omega) a
    have htopne : (hwDiffCoeffs k (by omega) a (h.2.val + 1))
        ⟨k - 1, by omega⟩ ≠ 0 := by
      rw [htop]
      exact mul_ne_zero (by exact_mod_cast (show k ≠ 0 by omega)) haTop
    have hi := hI N (hwDiffCoeffs k (by omega) a (h.2.val + 1)) hN hcoeff htopne
    change #(hwMomentFinset r N
      (hwPolyEval (k - 1) (hwDiffCoeffs k (by omega) a (h.2.val + 1)))) ≤ A
    dsimp [A, r]
    rw [hrel.2.2.2, ← hrel.1] at hi
    exact hi
  have hzero := hw_zeroQuadruples_card_le k r N M A (by omega) a hm hA
  have hM := hw_stepM_bounds k c N hk hN
  have hfour' : hwFourTermCount N M ≤
      C₄ * hwStepE k c ^ 3 * N ^ (3 * k) := by
    have hpow : N * N ^ (k - 1) = N ^ k := by
      calc
        N * N ^ (k - 1) = N ^ (k - 1) * N := by ac_rfl
        _ = N ^ ((k - 1) + 1) := (pow_succ N (k - 1)).symm
        _ = N ^ k := by
          congr 2
          all_goals omega
    have hNM : N * M ≤ hwStepE k c * N ^ k := by
      calc
        N * M ≤ N * (hwStepE k c * N ^ (k - 1)) :=
          Nat.mul_le_mul_left N hM.2
        _ = hwStepE k c * N ^ k := by
          rw [← hpow]
          ring
    calc
      hwFourTermCount N M ≤ C₄ * (N * M) ^ 3 := hfour N M hN hM.1
      _ ≤ C₄ * (hwStepE k c * N ^ k) ^ 3 := by gcongr
      _ = C₄ * hwStepE k c ^ 3 * N ^ (3 * k) := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm k 3]
        ring
  have hA₄ : A ^ 4 = Cᵢ ^ 4 * N ^ (4 * (2 * r - (k - 1))) := by
    dsimp [A]
    rw [mul_pow, ← pow_mul, Nat.mul_comm (2 * r - (k - 1)) 4]
  calc
    #(hwZeroQuadruples (hwBlockChoiceFreq k r N (by omega) a)) ≤
        hwFourTermCount N M * A ^ 4 := hzero
    _ = hwFourTermCount N M *
        (Cᵢ ^ 4 * N ^ (4 * (2 * r - (k - 1)))) := by rw [hA₄]
    _ ≤ (C₄ * hwStepE k c ^ 3 * N ^ (3 * k)) *
        (Cᵢ ^ 4 * N ^ (4 * (2 * r - (k - 1)))) := by
      exact Nat.mul_le_mul_right _ hfour'
    _ = (C₄ * hwStepE k c ^ 3 * Cᵢ ^ 4) *
        N ^ (3 * k + 4 * (2 * r - (k - 1))) := by
      rw [pow_add]
      ring
    _ = (C₄ * hwStepE k c ^ 3 * Cᵢ ^ 4) *
        N ^ (8 * r - k + 4) := by
      congr 2
      omega

private def hwStepK (k c Cᵢ C₄ : ℕ) : ℕ :=
  C₄ * hwStepE k c ^ 3 * Cᵢ ^ 4

private def hwStepC (k c Cᵢ C₄ : ℕ) : ℕ :=
  2 ^ (8 * hwStepR k) *
    (2 ^ (8 * hwStepR k) +
      2 ^ (8 * hwStepR k - 4) * hwStepK k c Cᵢ C₄)

private lemma hw_moment_induction_step (k c Cᵢ C₄ : ℕ) (hk : 3 ≤ k)
    (hI : ∀ (N : ℕ) (b : Fin (k - 1 + 1) → ℤ), 0 < N →
      hwCoeffBound (k - 1) (hwStepD k c) N b → b ⟨k - 1, by omega⟩ ≠ 0 →
      #(hwMomentFinset (8 ^ (k - 2) / 2) N (hwPolyEval (k - 1) b)) ≤
        Cᵢ * N ^ (8 ^ (k - 2) - (k - 1)))
    (hfour : ∀ H M : ℕ, 0 < H → H ≤ M →
      hwFourTermCount H M ≤ C₄ * (H * M) ^ 3) :
    ∀ (N : ℕ) (a : Fin (k + 1) → ℤ), 0 < N →
      hwCoeffBound k c N a → a ⟨k, by omega⟩ ≠ 0 →
      #(hwMomentFinset (8 ^ (k - 1) / 2) N (hwPolyEval k a)) ≤
        hwStepC k c Cᵢ C₄ * N ^ (8 ^ (k - 1) - k) := by
  intro N a hN ha haTop
  let r := hwStepR k
  let M := hwStepM k c N
  let Vₑ := (k + 1) * c * N ^ k
  let P := max (2 * (8 * r) * Vₑ) (4 * N * M) + 1
  let K := hwStepK k c Cᵢ C₄
  let C := hwStepC k c Cᵢ C₄
  let _ : NeZero P := ⟨by simp [P]⟩
  have hrel := hw_step_pow_relations k hk
  have hdegrees := hw_step_degree_bounds k hk
  have hr : 0 < r := by
    exact Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have hm : ∀ z : hwBlockChoice r N,
      (hwBlockChoiceDiff k r N (by omega) a z).natAbs ≤ M := by
    intro z
    have hz := hw_blockChoiceDiff_natAbs_le k c r N (by omega) a ha z
    apply hz.trans
    change 2 * r * hwStepV k c N ≤ M
    exact le_max_right _ _
  have hf : ∀ n ≤ N, (hwPolyEval k a n).natAbs ≤ Vₑ := by
    intro n hn
    simpa [Vₑ, mul_assoc] using hw_polyEval_natAbs_le k c N n hn a ha
  have hPmoment : 2 * (8 * r) * Vₑ < P := by
    dsimp [P]
    exact (le_max_left _ _).trans_lt (Nat.lt_succ_self _)
  have hPblock : 4 * N * M < P := by
    dsimp [P]
    exact (le_max_right _ _).trans_lt (Nat.lt_succ_self _)
  have hmoment := hw_real_character_moment_eq_card_of_lt
    P (8 * r) N Vₑ (hwPolyEval k a) hf hPmoment
  have hblock := hw_block_fourth_sum_eq_zero_count_of_lt
    P k r N M (by omega) a hm hPblock
  have hzero := hw_step_zero_count_bound k c Cᵢ C₄ N hk hN a ha haTop hI hfour
  have hpoint :
      (∑ α : ZMod P, ‖hwWeylSum P N (hwPolyEval k a) α‖ ^ (16 * r)) ≤
        ∑ α : ZMod P, 2 ^ (8 * r) *
          (((N + 1 : ℕ) : ℝ) ^ (8 * r) +
            ((2 * N : ℕ) : ℝ) ^ (8 * r - 4) *
              (∑ h : hwSigned N,
                ‖hwDiffBlock P N (hwPolyEval k a) h α‖ ^ (2 * r)) ^ 4) := by
    apply Finset.sum_le_sum
    intro α _
    exact hw_weyl_pointwise_le P k r N hr a α
  have hsum :
      (∑ α : ZMod P, 2 ^ (8 * r) *
        (((N + 1 : ℕ) : ℝ) ^ (8 * r) +
          ((2 * N : ℕ) : ℝ) ^ (8 * r - 4) *
            (∑ h : hwSigned N,
              ‖hwDiffBlock P N (hwPolyEval k a) h α‖ ^ (2 * r)) ^ 4)) =
        (P : ℝ) * 2 ^ (8 * r) *
          (((N + 1 : ℕ) : ℝ) ^ (8 * r) +
            ((2 * N : ℕ) : ℝ) ^ (8 * r - 4) *
              #(hwZeroQuadruples
                (hwBlockChoiceFreq k r N (by omega) a))) := by
    calc
      _ = (∑ _α : ZMod P,
            (2 ^ (8 * r) : ℝ) * (((N + 1 : ℕ) : ℝ) ^ (8 * r)) +
          ∑ α : ZMod P,
            (2 ^ (8 * r) : ℝ) * (((2 * N : ℕ) : ℝ) ^ (8 * r - 4)) *
              (∑ h : hwSigned N,
                ‖hwDiffBlock P N (hwPolyEval k a) h α‖ ^ (2 * r)) ^ 4) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro α _
        push_cast
        ring
      _ = (P : ℝ) * ((2 ^ (8 * r) : ℝ) * (((N + 1 : ℕ) : ℝ) ^ (8 * r))) +
          ((2 ^ (8 * r) : ℝ) * (((2 * N : ℕ) : ℝ) ^ (8 * r - 4))) *
            ∑ α : ZMod P, (∑ h : hwSigned N,
              ‖hwDiffBlock P N (hwPolyEval k a) h α‖ ^ (2 * r)) ^ 4 := by
        rw [Finset.mul_sum]
        simp [ZMod.card]
      _ = _ := by
        rw [hblock]
        push_cast
        ring
  have hdiag : (((N + 1 : ℕ) : ℝ) ^ (8 * r)) ≤
      2 ^ (8 * r) * (N : ℝ) ^ (16 * r - k) := by
    have hNtwo : N + 1 ≤ 2 * N := by omega
    have hexp : 8 * r ≤ 16 * r - k := by omega
    calc
      (((N + 1 : ℕ) : ℝ) ^ (8 * r)) ≤
          (((2 * N : ℕ) : ℝ) ^ (8 * r)) := by
        exact_mod_cast (Nat.pow_le_pow_left hNtwo (8 * r))
      _ = 2 ^ (8 * r) * (N : ℝ) ^ (8 * r) := by
        push_cast
        rw [mul_pow]
      _ ≤ 2 ^ (8 * r) * (N : ℝ) ^ (16 * r - k) := by
        have hpN : N ^ (8 * r) ≤ N ^ (16 * r - k) :=
          Nat.pow_le_pow_right hN hexp
        apply mul_le_mul_of_nonneg_left
        · exact_mod_cast hpN
        · positivity
  have hblockNat :
      (2 * N) ^ (8 * r - 4) *
          #(hwZeroQuadruples (hwBlockChoiceFreq k r N (by omega) a)) ≤
        2 ^ (8 * r - 4) * K * N ^ (16 * r - k) := by
    calc
      (2 * N) ^ (8 * r - 4) *
          #(hwZeroQuadruples (hwBlockChoiceFreq k r N (by omega) a)) ≤
        (2 * N) ^ (8 * r - 4) * (K * N ^ (8 * r - k + 4)) := by
          gcongr
          simpa [K, hwStepK] using hzero
      _ = 2 ^ (8 * r - 4) * K * N ^ (16 * r - k) := by
        rw [mul_pow]
        calc
          2 ^ (8 * r - 4) * N ^ (8 * r - 4) *
              (K * N ^ (8 * r - k + 4)) =
            2 ^ (8 * r - 4) * K *
              (N ^ (8 * r - 4) * N ^ (8 * r - k + 4)) := by ring
          _ = _ := by
            rw [← pow_add]
            congr 3
            omega
  have hbracket :
      (((N + 1 : ℕ) : ℝ) ^ (8 * r) +
        ((2 * N : ℕ) : ℝ) ^ (8 * r - 4) *
          #(hwZeroQuadruples (hwBlockChoiceFreq k r N (by omega) a))) ≤
      (2 ^ (8 * r) + 2 ^ (8 * r - 4) * K) *
        (N : ℝ) ^ (16 * r - k) := by
    calc
      _ ≤ 2 ^ (8 * r) * (N : ℝ) ^ (16 * r - k) +
          (2 ^ (8 * r - 4) * K : ℕ) * (N : ℝ) ^ (16 * r - k) := by
        exact add_le_add hdiag (by exact_mod_cast hblockNat)
      _ = _ := by push_cast; ring
  have hPpos : (0 : ℝ) < P := Nat.cast_pos.mpr (NeZero.pos P)
  have hcancel : (#(hwMomentFinset (8 * r) N (hwPolyEval k a)) : ℝ) ≤
      C * N ^ (16 * r - k) := by
    apply le_of_mul_le_mul_left (a := (P : ℝ)) _ hPpos
    calc
      (P : ℝ) * #(hwMomentFinset (8 * r) N (hwPolyEval k a)) =
          ∑ α : ZMod P,
            ‖hwWeylSum P N (hwPolyEval k a) α‖ ^ (16 * r) := by
        rw [← show 2 * (8 * r) = 16 * r by omega]
        exact hmoment.symm
      _ ≤ _ := hpoint
      _ = (P : ℝ) * 2 ^ (8 * r) *
          (((N + 1 : ℕ) : ℝ) ^ (8 * r) +
            ((2 * N : ℕ) : ℝ) ^ (8 * r - 4) *
              #(hwZeroQuadruples
                (hwBlockChoiceFreq k r N (by omega) a))) := hsum
      _ ≤ (P : ℝ) * 2 ^ (8 * r) *
          ((2 ^ (8 * r) + 2 ^ (8 * r - 4) * K) *
            (N : ℝ) ^ (16 * r - k)) := by gcongr
      _ = (P : ℝ) * (C * N ^ (16 * r - k)) := by
        simp [C, hwStepC, K]
        ring
  have hnat : #(hwMomentFinset (8 * r) N (hwPolyEval k a)) ≤
      C * N ^ (16 * r - k) := by exact_mod_cast hcancel
  dsimp [C, r] at hnat ⊢
  rw [← hrel.2.1, ← hrel.2.2.1]
  exact hnat

private theorem hw_exists_moment_bound (k c : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, 0 < C ∧ ∀ (N : ℕ) (a : Fin (k + 1) → ℤ), 0 < N →
      hwCoeffBound k c N a → a ⟨k, by omega⟩ ≠ 0 →
      #(hwMomentFinset (8 ^ (k - 1) / 2) N (hwPolyEval k a)) ≤
        C * N ^ (8 ^ (k - 1) - k) := by
  revert c
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro c
      by_cases hk₂ : k = 2
      · subst k
        simpa using hw_quadratic_moment_bound c
      · have hk₃ : 3 ≤ k := by omega
        obtain ⟨Cᵢ, _, hI₀⟩ :=
          ih (k - 1) (by omega) (by omega) (hwStepD k c)
        obtain ⟨C₄, _, hfour⟩ := hw_exists_fourTermCount_bound
        let C := hwStepC k c Cᵢ C₄
        have hI : ∀ (N : ℕ) (b : Fin (k - 1 + 1) → ℤ), 0 < N →
            hwCoeffBound (k - 1) (hwStepD k c) N b →
              b ⟨k - 1, by omega⟩ ≠ 0 →
            #(hwMomentFinset (8 ^ (k - 2) / 2) N (hwPolyEval (k - 1) b)) ≤
              Cᵢ * N ^ (8 ^ (k - 2) - (k - 1)) := by
          intro N b hN hb hbtop
          have hi := hI₀ N b hN hb hbtop
          rw [show k - 1 - 1 = k - 2 by omega] at hi
          exact hi
        refine ⟨C, ?_, ?_⟩
        · dsimp [C, hwStepC]
          exact Nat.mul_pos (pow_pos (by omega) _)
            (Nat.add_pos_left (pow_pos (by omega) _) _)
        · exact hw_moment_induction_step k c Cᵢ C₄ hk₃ hI hfour

private def hwPowerSumset (k s : ℕ) : Set ℕ :=
  {n | ∃ x : Fin s → ℕ, n = ∑ i, x i ^ k}

private lemma hwPowerSumset_zero_mem {k s : ℕ} (hk : 0 < k) :
    0 ∈ hwPowerSumset k s := by
  refine ⟨fun _ ↦ 0, ?_⟩
  simp [hk.ne']

private lemma hwPowerSumset_one_mem {k s : ℕ} (hk : 0 < k) (hs : 0 < s) :
    1 ∈ hwPowerSumset k s := by
  let i0 : Fin s := ⟨0, hs⟩
  let x : Fin s → ℕ := fun i ↦ if i = i0 then 1 else 0
  refine ⟨x, ?_⟩
  have hxval : ∀ i, x i ^ k = if i = i0 then 1 else 0 := by
    intro i
    by_cases hi : i = i0 <;> simp [x, hi, hk.ne']
  simp_rw [hxval]
  simp

private lemma hw_sum_flatten (h s k : ℕ) (x : Fin h → Fin s → ℕ) :
    ∃ y : Fin (h * s) → ℕ,
      ∑ i, y i ^ k = ∑ i, ∑ j, x i j ^ k := by
  refine ⟨fun i ↦ x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2, ?_⟩
  calc
    ∑ i, (x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) ^ k =
        ∑ ij : Fin h × Fin s, x ij.1 ij.2 ^ k :=
      finProdFinEquiv.symm.sum_comp fun ij ↦ x ij.1 ij.2 ^ k
    _ = ∑ i, ∑ j, x i j ^ k := Fintype.sum_prod_type _

private def hwPowerFiber (k s M n : ℕ) : Finset (Fin s → Fin (M + 1)) :=
  Finset.univ.filter fun x ↦ n = ∑ i, (x i : ℕ) ^ k

private def hwSplitTuple (r M : ℕ) (x : Fin (r + r) → Fin (M + 1)) :
    (Fin r → Fin (M + 1)) × (Fin r → Fin (M + 1)) :=
  (fun i ↦ x (Fin.castAdd r i), fun i ↦ x (Fin.natAdd r i))

private lemma hw_splitTuple_injective (r M : ℕ) :
    Function.Injective (hwSplitTuple r M) := by
  intro x y hxy
  funext i
  refine Fin.addCases (motive := fun i ↦ x i = y i) ?_ ?_ i
  · intro j
    simpa [hwSplitTuple] using congrFun (congrArg Prod.fst hxy) j
  · intro j
    simpa [hwSplitTuple] using congrFun (congrArg Prod.snd hxy) j

private lemma hw_powerFiber_card_le_sumFiber {k s r M n : ℕ} (hs : r + r = s) :
    #(hwPowerFiber k s M n) ≤
      #(hwSumFiber r M (fun x : ℕ ↦ (x : ℤ) ^ k) n) := by
  let e : Fin (r + r) ≃ Fin s := finCongr hs
  let g : (Fin s → Fin (M + 1)) →
      (Fin r → Fin (M + 1)) × (Fin r → Fin (M + 1)) :=
    fun x ↦ hwSplitTuple r M (fun i ↦ x (e i))
  apply Finset.card_le_card_of_injOn g
  · intro x hx
    have hxsum : n = ∑ i : Fin s, (x i : ℕ) ^ k := by
      simpa [hwPowerFiber] using hx
    have hxsum' : n = ∑ i : Fin (r + r), (x (e i) : ℕ) ^ k := by
      exact hxsum.trans (e.sum_comp (fun i ↦ (x i : ℕ) ^ k)).symm
    have htarget : hwTupleSum r M (fun z : ℕ ↦ (z : ℤ) ^ k) (g x).1 +
        hwTupleSum r M (fun z : ℕ ↦ (z : ℤ) ^ k) (g x).2 = n := by
      dsimp [g, hwSplitTuple, hwTupleSum]
      calc
        (∑ i : Fin r, (x (e (Fin.castAdd r i)) : ℤ) ^ k) +
            ∑ i : Fin r, (x (e (Fin.natAdd r i)) : ℤ) ^ k =
            ∑ i : Fin (r + r), (x (e i) : ℤ) ^ k :=
          (Fin.sum_univ_add (fun i : Fin (r + r) ↦ (x (e i) : ℤ) ^ k)).symm
        _ = n := by exact_mod_cast hxsum'.symm
    change g x ∈ hwSumFiber r M (fun z : ℕ ↦ (z : ℤ) ^ k) n
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htarget⟩
  · intro x _ y _ hxy
    have hcomp : (fun i ↦ x (e i)) = fun i ↦ y (e i) :=
      hw_splitTuple_injective r M hxy
    funext i
    simpa [e] using congrFun hcomp (e.symm i)

private def hwPowerCoeffs (k : ℕ) : Fin (k + 1) → ℤ :=
  fun j ↦ if j.val = k then 1 else 0

private lemma hw_polyEval_power (k n : ℕ) :
    hwPolyEval k (hwPowerCoeffs k) n = (n : ℤ) ^ k := by
  rw [hwPolyEval]
  let top : Fin (k + 1) := ⟨k, by omega⟩
  rw [Finset.sum_eq_single top]
  · simp [hwPowerCoeffs, top]
  · intro j _ hj
    have hj' : j.val ≠ k := by
      intro h
      apply hj
      exact Fin.ext h
    simp [hwPowerCoeffs, hj']
  · simp

private lemma hw_powerCoeffs_bound (k M : ℕ) :
    hwCoeffBound k 1 M (hwPowerCoeffs k) := by
  intro j
  by_cases hj : j.val = k
  · simp [hwPowerCoeffs, hj]
  · simp [hwPowerCoeffs, hj]

private theorem hw_exists_powerFiber_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, 0 < C ∧ ∀ M n : ℕ,
      #(hwPowerFiber k (8 ^ (k - 1)) M n) ≤
        C * (M + 1) ^ (8 ^ (k - 1) - k) := by
  obtain ⟨C, hC, hmoment⟩ := hw_exists_moment_bound k 1 hk
  refine ⟨C, hC, ?_⟩
  intro M n
  let s := 8 ^ (k - 1)
  let r := s / 2
  have hsEven : Even s := by
    rw [Nat.even_pow]
    exact ⟨by norm_num, by omega⟩
  have hrs : r + r = s := by
    have h := Nat.two_mul_div_two_of_even hsEven
    omega
  by_cases hM : M = 0
  · subst M
    calc
      #(hwPowerFiber k s 0 n) ≤
          #((Finset.univ : Finset (Fin s → Fin (0 + 1)))) := by
        exact Finset.card_filter_le _ _
      _ = 1 := by simp
      _ ≤ C * (0 + 1) ^ (s - k) := by simp; omega
  · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
    have htop : hwPowerCoeffs k ⟨k, by omega⟩ ≠ 0 := by
      simp [hwPowerCoeffs]
    have hmom := hmoment M (hwPowerCoeffs k) hMpos
      (hw_powerCoeffs_bound k M) htop
    have hpow : hwPolyEval k (hwPowerCoeffs k) = fun x : ℕ ↦ (x : ℤ) ^ k := by
      funext x
      exact hw_polyEval_power k x
    rw [hpow] at hmom
    calc
      #(hwPowerFiber k s M n) ≤
          #(hwSumFiber r M (fun x : ℕ ↦ (x : ℤ) ^ k) n) :=
        hw_powerFiber_card_le_sumFiber hrs
      _ ≤ #(hwMomentFinset r M (fun x : ℕ ↦ (x : ℤ) ^ k)) :=
        hw_sumFiber_card_le_moment r M _ n
      _ ≤ C * M ^ (s - k) := by
        simpa only [s, r] using hmom
      _ ≤ C * (M + 1) ^ (s - k) :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) (s - k))

private def hwPowerImage (k s M : ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Fin s → Fin (M + 1))).image fun x ↦ ∑ i, (x i : ℕ) ^ k

private lemma hwPowerImage_zero_mem {k s M : ℕ} (hk : 0 < k) :
    0 ∈ hwPowerImage k s M := by
  apply mem_image.mpr
  refine ⟨fun _ ↦ 0, mem_univ _, ?_⟩
  simp [hk.ne']

private lemma hwPowerImage_one_mem {k s M : ℕ} (hk : 0 < k) (hs : 0 < s) (hM : 0 < M) :
    1 ∈ hwPowerImage k s M := by
  let i0 : Fin s := ⟨0, hs⟩
  let x : Fin s → Fin (M + 1) := fun i ↦ if i = i0 then ⟨1, by omega⟩ else 0
  apply mem_image.mpr
  refine ⟨x, mem_univ _, ?_⟩
  have hxval : ∀ i, (x i : ℕ) ^ k = if i = i0 then 1 else 0 := by
    intro i
    by_cases hi : i = i0 <;> simp [x, hi, hk.ne']
  simp_rw [hxval]
  simp

private lemma hwPowerImage_sum_le {k s M n : ℕ} (hn : n ∈ hwPowerImage k s M) :
    n ≤ s * M ^ k := by
  rcases mem_image.mp hn with ⟨x, _, rfl⟩
  calc
    ∑ i, (x i : ℕ) ^ k ≤ ∑ _i : Fin s, M ^ k := by
      gcongr with i
      exact Nat.le_of_lt_succ (x i).isLt
    _ = s * M ^ k := by simp

private lemma hw_card_le_card_image_mul_of_fiber_le {α β : Type*}
    [Fintype α] [DecidableEq β] (f : α → β) (R : ℕ)
    (hR : ∀ b, #{a ∈ (Finset.univ : Finset α) | f a = b} ≤ R) :
    Fintype.card α ≤ #((Finset.univ : Finset α).image f) * R := by
  have hmap : Set.MapsTo f (↑(Finset.univ : Finset α))
      (↑((Finset.univ : Finset α).image f)) := by
    intro a ha
    exact mem_image.2 ⟨a, ha, rfl⟩
  rw [Fintype.card, card_eq_sum_card_fiberwise hmap]
  calc
    ∑ b ∈ (Finset.univ : Finset α).image f,
        #{a ∈ (Finset.univ : Finset α) | f a = b} ≤
        ∑ _b ∈ (Finset.univ : Finset α).image f, R := by
      gcongr with b
      exact hR b
    _ = #((Finset.univ : Finset α).image f) * R := by simp

private lemma hw_degree_le_moment {k : ℕ} (hk : 2 ≤ k) : k ≤ 8 ^ (k - 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => norm_num
  | succ d ih =>
      have ih' : 2 + d ≤ 8 ^ (d + 1) := by
        rw [show 2 + d - 1 = d + 1 by omega] at ih
        exact ih
      rw [show 2 + (d + 1) - 1 = d + 2 by omega, pow_succ]
      calc
        2 + (d + 1) ≤ 8 * (2 + d) := by omega
        _ ≤ 8 * 8 ^ (d + 1) := Nat.mul_le_mul_left 8 ih'
        _ = 8 ^ (d + 1) * 8 := Nat.mul_comm _ _

private lemma hw_power_image_mul_ge {k C : ℕ} (hk : 2 ≤ k)
    (hC : ∀ M n : ℕ, #(hwPowerFiber k (8 ^ (k - 1)) M n) ≤
      C * (M + 1) ^ (8 ^ (k - 1) - k)) (M : ℕ) :
    (M + 1) ^ k ≤ #(hwPowerImage k (8 ^ (k - 1)) M) * C := by
  let f : (Fin (8 ^ (k - 1)) → Fin (M + 1)) → ℕ :=
    fun x ↦ ∑ i, (x i : ℕ) ^ k
  have hfiber : ∀ n,
      #{x ∈ (Finset.univ : Finset (Fin (8 ^ (k - 1)) → Fin (M + 1))) | f x = n} ≤
        C * (M + 1) ^ (8 ^ (k - 1) - k) := by
    intro n
    simpa only [f, hwPowerFiber, eq_comm] using hC M n
  have hraw := hw_card_le_card_image_mul_of_fiber_le f
    (C * (M + 1) ^ (8 ^ (k - 1) - k)) hfiber
  simp only [Fintype.card_fun, Fintype.card_fin] at hraw
  have hdegree := hw_degree_le_moment hk
  have hfactor : 0 < (M + 1) ^ (8 ^ (k - 1) - k) := by positivity
  apply Nat.le_of_mul_le_mul_left (c := (M + 1) ^ (8 ^ (k - 1) - k))
  · calc
      (M + 1) ^ (8 ^ (k - 1) - k) * (M + 1) ^ k =
          (M + 1) ^ (8 ^ (k - 1)) := by
        rw [← pow_add, Nat.sub_add_cancel hdegree]
      _ ≤ #((Finset.univ : Finset (Fin (8 ^ (k - 1)) → Fin (M + 1))).image f) *
          (C * (M + 1) ^ (8 ^ (k - 1) - k)) := hraw
      _ = (M + 1) ^ (8 ^ (k - 1) - k) *
          (#((Finset.univ : Finset (Fin (8 ^ (k - 1)) → Fin (M + 1))).image f) * C) := by
        ac_rfl
  · exact hfactor

private lemma hw_exists_power_scale {s k N : ℕ} (hs : 0 < s) (hk : 0 < k) :
    ∃ M : ℕ, N < s * (M + 1) ^ k ∧ (M = 0 ∨ s * M ^ k ≤ N) := by
  have hex : ∃ M : ℕ, N < s * (M + 1) ^ k := by
    refine ⟨N, ?_⟩
    have hpow : N + 1 ≤ (N + 1) ^ k := Nat.le_pow hk
    have hmul : (N + 1) ^ k ≤ s * (N + 1) ^ k := Nat.le_mul_of_pos_left _ hs
    exact (Nat.lt_succ_self N).trans_le (hpow.trans hmul)
  let M := Nat.find hex
  refine ⟨M, Nat.find_spec hex, ?_⟩
  by_cases hM : M = 0
  · exact Or.inl hM
  · right
    have hpred : M - 1 < M := by omega
    have hnot := Nat.find_min hex hpred
    rw [show M - 1 + 1 = M by omega] at hnot
    omega

private theorem hw_power_sumset_density_pos_of_fiber_bound (k C : ℕ) (hk : 2 ≤ k) (hC : 0 < C)
    (hbound : ∀ M n : ℕ, #(hwPowerFiber k (8 ^ (k - 1)) M n) ≤
      C * (M + 1) ^ (8 ^ (k - 1) - k)) :
    0 < @schnirelmannDensity (hwPowerSumset k (8 ^ (k - 1)))
      (fun n ↦ Classical.propDecidable (n ∈ hwPowerSumset k (8 ^ (k - 1)))) := by
  let s := 8 ^ (k - 1)
  let A := hwPowerSumset k s
  let D := 2 * s * C
  have hk0 : 0 < k := by omega
  have hs : 0 < s := by positivity
  have hD : 0 < D := by positivity
  let _ : DecidablePred (· ∈ A) := fun n ↦ Classical.propDecidable (n ∈ A)
  have hA1 : 1 ∈ A := hwPowerSumset_one_mem hk0 hs
  have hmain : ∀ N : ℕ, 0 < N → N ≤ D * #{a ∈ Ioc 0 N | a ∈ A} := by
    intro N hN
    by_cases hsmall : N < s
    · have hmem : 1 ∈ {a ∈ Ioc 0 N | a ∈ A} :=
        mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨zero_lt_one, hN⟩, hA1⟩
      have hcard : 1 ≤ #{a ∈ Ioc 0 N | a ∈ A} := by
        have := card_pos.mpr ⟨1, hmem⟩
        simpa using this
      have hND : N ≤ D := by
        calc
          N ≤ s := by omega
          _ ≤ 2 * s := Nat.le_mul_of_pos_left s (by omega)
          _ ≤ (2 * s) * C := Nat.le_mul_of_pos_right (2 * s) hC
          _ = D := rfl
      exact hND.trans (by simpa using Nat.mul_le_mul_left D hcard)
    · have hsN : s ≤ N := by omega
      obtain ⟨M, hupper, hM⟩ := hw_exists_power_scale hs hk0 (N := N)
      have hMpos : 0 < M := by
        by_contra hMpos
        have hM0 : M = 0 := Nat.eq_zero_of_not_pos hMpos
        subst M
        have : N < s := by simpa using hupper
        exact hsmall this
      have hlower : s * M ^ k ≤ N := hM.resolve_left hMpos.ne'
      let I := hwPowerImage k s M
      have hI0 : 0 ∈ I := hwPowerImage_zero_mem hk0
      have hI1 : 1 ∈ I := hwPowerImage_one_mem hk0 hs hMpos
      have hIcard : 2 ≤ #I := by
        have hsub : ({0, 1} : Finset ℕ) ⊆ I := by
          intro a ha
          simp only [mem_insert, mem_singleton] at ha
          rcases ha with rfl | rfl
          · exact hI0
          · exact hI1
        have := card_le_card hsub
        norm_num at this ⊢
        exact this
      have herase : I.erase 0 ⊆ {a ∈ Ioc 0 N | a ∈ A} := by
        intro a ha
        have ha' := mem_erase.mp ha
        have ha_le : a ≤ N := (hwPowerImage_sum_le ha'.2).trans hlower
        have haA : a ∈ A := by
          rcases mem_image.mp ha'.2 with ⟨x, _, hxa⟩
          exact ⟨fun i ↦ (x i : ℕ), hxa.symm⟩
        exact mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, ha_le⟩, haA⟩
      have herase_card : #(I.erase 0) ≤ #{a ∈ Ioc 0 N | a ∈ A} := card_le_card herase
      have hI_le : #I ≤ 2 * #{a ∈ Ioc 0 N | a ∈ A} := by
        have herase_eq := card_erase_add_one hI0
        omega
      have himage : (M + 1) ^ k ≤ #I * C := by
        simpa only [I, s] using hw_power_image_mul_ge hk hbound M
      calc
        N ≤ s * (M + 1) ^ k := Nat.le_of_lt hupper
        _ ≤ s * (#I * C) := Nat.mul_le_mul_left s himage
        _ ≤ s * (2 * #{a ∈ Ioc 0 N | a ∈ A} * C) := by
          gcongr
        _ = D * #{a ∈ Ioc 0 N | a ∈ A} := by
          dsimp [D]
          ac_rfl
  have hlower : (D : ℝ)⁻¹ ≤ schnirelmannDensity A := by
    rw [le_schnirelmannDensity_iff]
    intro N hN
    rw [le_div_iff₀ (Nat.cast_pos.mpr hN), inv_mul_le_iff₀ (Nat.cast_pos.mpr hD)]
    exact_mod_cast hmain N hN
  have hinv : 0 < (D : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hD)
  simpa only [A, s] using hinv.trans_le hlower

/--
**Hilbert–Waring theorem.** For every integer $k \ge 1$ there is a natural number $g$ such that
every natural number $n$ is a sum of $g$ $k$-th powers of natural numbers, that is,
$n = x_1^k + \dots + x_g^k$ for some $x_1, \dots, x_g \in \mathbb{N}$.

Proves `Wanted` entry `hilbert_waring`.

Proof: We follow Linnik's elementary route as presented in Tim Jameson's notes: a mean-value
estimate gives positive Schnirelmann density for a bounded power sumset, which is then an additive
basis of finite order by Schnirelmann's inequality.

Source: D. Hilbert, Beweis für die Darstellbarkeit der ganzen
Zahlen durch eine feste Anzahl n-ter Potenzen (Waringsches Problem), Math. Ann. 67 (1909) 281–305;
textbook in Vaughan, The Hardy-Littlewood Method; general includes minimal g(k).
-/
public theorem hilbert_waring :
    ∀ k : ℕ, 0 < k → ∃ g : ℕ, ∀ n : ℕ, ∃ x : Fin g → ℕ,
      n = Finset.univ.sum fun i => (x i) ^ k := by
  intro k hk
  by_cases hk1 : k = 1
  · subst k
    refine ⟨1, fun n ↦ ⟨fun _ ↦ n, ?_⟩⟩
    simp
  · have hk2 : 2 ≤ k := by omega
    obtain ⟨C, hC, hbound⟩ := hw_exists_powerFiber_bound k hk2
    let s := 8 ^ (k - 1)
    let A := hwPowerSumset k s
    let _ : DecidablePred (· ∈ A) := fun n ↦ Classical.propDecidable (n ∈ A)
    have hs : 0 < s := by positivity
    have hA0 : 0 ∈ A := hwPowerSumset_zero_mem hk
    have hσ : 0 < schnirelmannDensity A := by
      simpa only [A, s] using
        hw_power_sumset_density_pos_of_fiber_bound k C hk2 hC hbound
    obtain ⟨h, hbasis⟩ := exists_additive_basis_of_pos_schnirelmannDensity hA0 hσ
    refine ⟨h * s, fun n ↦ ?_⟩
    obtain ⟨z, hzA, hzn⟩ := hbasis n
    have hrep : ∀ i, ∃ x : Fin s → ℕ, z i = ∑ j, x j ^ k := by
      intro i
      exact hzA i
    choose x hx using hrep
    obtain ⟨y, hy⟩ := hw_sum_flatten h s k x
    refine ⟨y, ?_⟩
    calc
      n = ∑ i, z i := hzn
      _ = ∑ i, ∑ j, x i j ^ k := by
        apply Finset.sum_congr rfl
        intro i _
        exact hx i
      _ = ∑ i, y i ^ k := hy.symm

end MathlibExt.NumberTheory.HilbertWaringWanted
