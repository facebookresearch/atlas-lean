/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Higher moments of the smallest cycle of a random permutation

`MetaMathlibExt.smallest_cycle_moment_asymp` gives a power-saving error bound for the
Buchstab integral approximation to each moment of order at least two.

Marking the cycle through a point gives a recurrence for the probability that all cycles
have length at least `k`. Comparing this recurrence with the integrated Buchstab equation
gives a pointwise estimate. Integrating the estimate against the moment weight yields
the exponent `1 / 4`.
-/

open Function Equiv Equiv.Perm Finset
open scoped BigOperators

namespace MetaMathlibExt.smallest_cycle_moment_asymp

private abbrev HasLongCycles (k : ℕ) {α : Type*} (σ : Perm α) := ∀ x, k ≤ minimalPeriod σ x

private theorem period_map {α β : Type*} {f : α → α} {g : β → β} {e : α → β}
    (he : Injective e) (h : Semiconj e f g) (x : α) :
    minimalPeriod f x = minimalPeriod g (e x) := by
  apply minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  change f^[n] x = x ↔ g^[n] (e x) = e x
  rw [← (h.iterate_right n x), he.eq_iff]

private theorem period_cycle {α : Type*} {σ : Perm α}
    {s : Finset α} (h : σ.IsCycleOn s) {x : α} (hx : x ∈ s) :
    minimalPeriod σ x = s.card := by
  apply Nat.dvd_antisymm
  · exact (isPeriodicPt_iff_minimalPeriod_dvd.mp ((h.pow_apply_eq hx).mpr dvd_rfl :
      (σ ^ s.card) x = x))
  · exact (h.pow_apply_eq hx).mp (isPeriodicPt_minimalPeriod σ x)

private def orbitSet {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α) (a : α) : Finset α :=
  univ.filter (σ.SameCycle a)

private theorem orbit_cycle {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α) (a : α) :
    σ.IsCycleOn (orbitSet σ a) := by
  refine ⟨σ.bijOn fun x ↦ ?_, ?_⟩
  · simp [orbitSet, sameCycle_apply_right]
  · intro x hx y hy
    simp only [orbitSet, mem_coe, mem_filter, mem_univ, true_and] at hx hy
    exact hx.symm.trans hy

private theorem orbit_eq {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α}
    {s : Finset α} (h : σ.IsCycleOn s) {x : α} (hx : x ∈ s) :
    orbitSet σ x = s := by
  ext y
  simp only [orbitSet, mem_filter, mem_univ, true_and]
  exact ⟨fun ⟨i, hi⟩ ↦ by
    rw [← hi]
    exact (h.1.perm_zpow _).mapsTo hx, fun hy ↦ h.2 hx hy⟩

private noncomputable def countLong (k : ℕ) (α : Type*) :=
  Nat.card {σ : Perm α // HasLongCycles k σ}

private theorem count_congr (k : ℕ) {α β : Type*} (e : α ≃ β) :
    countLong k α = countLong k β := by
  apply Nat.card_congr (e.permCongr.subtypeEquiv ?_)
  intro σ
  have hp (x : α) : minimalPeriod σ x = minimalPeriod (e.permCongr σ) (e x) :=
    period_map e.injective (fun z ↦ by simp) x
  exact ⟨fun h y ↦ by simpa using le_of_le_of_eq (h (e.symm y)) (hp _),
    fun h x ↦ (hp x) ▸ h (e x)⟩

private theorem long_iff {n k : ℕ} (hn : 0 < n) (σ : Perm (Fin n)) :
    HasLongCycles k σ ↔ k ≤ ⨅ x, minimalPeriod σ x := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact le_ciInf_iff (OrderBot.bddBelow _) |>.symm

private theorem cycle_count (α : Type*) [Fintype α] (hn : 0 < Fintype.card α) :
    Nat.card {σ : Perm α // σ.IsCycleOn Set.univ} = (Fintype.card α - 1).factorial := by
  classical
  by_cases h : 2 ≤ Fintype.card α
  · have hiff (σ : Perm α) : σ.IsCycleOn Set.univ ↔ σ.cycleType = {Fintype.card α} := by
      constructor
      · intro hs
        let : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp h
        have hnt : (Set.univ : Set α).Nontrivial := Set.nontrivial_univ
        have hm (x : α) : σ x ≠ x := hs.apply_ne hnt (Set.mem_univ x)
        have hc : σ.IsCycle := by
          obtain ⟨x⟩ := Fintype.card_pos_iff.mp hn
          exact ⟨x, hm x, fun y _ ↦ hs.2 (Set.mem_univ x) (Set.mem_univ y)⟩
        have hu : σ.support = univ := by ext x; simp [Perm.mem_support, hm]
        simp [hc.cycleType, hu]
      · intro ht
        have hc : σ.IsCycle := card_cycleType_eq_one.mp (by simp [ht])
        have hu : σ.support = univ := eq_univ_of_card _ (by
          simpa [ht] using σ.sum_cycleType.symm)
        exact ⟨σ.bijOn fun _ ↦ Iff.rfl, fun x _ y _ ↦ hc.sameCycle
          (Perm.mem_support.mp (hu ▸ mem_univ x)) (Perm.mem_support.mp (hu ▸ mem_univ y))⟩
    simpa [Nat.card_eq_fintype_card, Fintype.card_subtype, hiff] using
      card_of_cycleType_singleton (α := α) h le_rfl
  · have hc : Fintype.card α = 1 := by omega
    let : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp hc.le
    have : ∀ σ : Perm α, σ.IsCycleOn Set.univ := fun σ ↦ isCycleOn_of_subsingleton σ _
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype, this, hc]

private abbrev FullOn {α : Type*} (s : Finset α) :=
  {τ : Perm s // τ.IsCycleOn Set.univ}

/-- Restrict a permutation to a full cycle on `s` and a permutation of its complement. -/
private noncomputable def splitCycle {α : Type*} (s : Finset α) (k : ℕ)
    (hk : k ≤ s.card) :
    {σ : Perm α // σ.IsCycleOn s ∧ HasLongCycles k σ} ≃
      FullOn s × {τ : Perm {x // x ∉ s} // HasLongCycles k τ} := by
  classical
  let restrictC (σ : Perm α) (h : σ.IsCycleOn s) : Perm {x // x ∉ s} :=
    σ.subtypePerm (fun _ ↦ h.apply_mem_iff.not)
  let merge (p : FullOn s × {τ : Perm {x // x ∉ s} // HasLongCycles k τ}) : Perm α :=
    p.1.val.subtypeCongr p.2.val
  have hm (p) (x : s) : merge p x = (p.1.val x : s) :=
    Equiv.Perm.subtypeCongr.left_apply_subtype _ _ _
  have hc (p) (x : {j // j ∉ s}) : merge p x = (p.2.val x : {j // j ∉ s}) :=
    Equiv.Perm.subtypeCongr.right_apply_subtype _ _ _
  have hcycle (p) : (merge p).IsCycleOn s := by
    have hi (x : α) : merge p x ∈ s ↔ x ∈ s := by
      by_cases hx : x ∈ s
      · exact iff_of_true ((hm p ⟨x, hx⟩) ▸ (p.1.val ⟨x, hx⟩).property) hx
      · exact iff_of_false ((hc p ⟨x, hx⟩) ▸ (p.2.val ⟨x, hx⟩).property) hx
    refine ⟨(merge p).bijOn hi, fun x hx y hy ↦ ?_⟩
    let a : s := ⟨x, hx⟩
    let b : s := ⟨y, hy⟩
    have he : (merge p).subtypePerm hi = p.1.val := Equiv.ext fun z ↦ Subtype.ext (hm p z)
    exact (sameCycle_subtypePerm (h := hi) (x := a) (y := b)).mp
      (he ▸ p.1.property.2 (Set.mem_univ a) (Set.mem_univ b))
  refine ⟨fun σ ↦ (⟨σ.val.subtypePerm (fun _ ↦ σ.property.1.apply_mem_iff),
      σ.property.1.subtypePerm⟩, ⟨restrictC σ.val σ.property.1, fun z ↦ ?_⟩),
    fun p ↦ ⟨merge p, hcycle p, fun x ↦ ?_⟩, ?_, ?_⟩
  · have h := period_map (Subtype.val_injective (p := fun j ↦ j ∉ s))
        (f := (restrictC σ.val σ.property.1 : _ → _)) (g := (σ.val : α → α)) (fun _ ↦ rfl) z
    exact h ▸ σ.property.2 z
  · by_cases hx : x ∈ s
    · rwa [period_cycle (hcycle p) hx]
    · have h := period_map (Subtype.val_injective (p := fun j ↦ j ∉ s))
          (f := (p.2.val : _ → _)) (g := (merge p : α → α)) (fun z ↦ (hc p z).symm) ⟨x, hx⟩
      exact h ▸ p.2.property ⟨x, hx⟩
  · intro σ
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ s
    · exact hm _ ⟨x, hx⟩
    · exact hc _ ⟨x, hx⟩
  · intro p
    apply Prod.ext
    · apply Subtype.ext
      ext x
      exact hm p x
    · apply Subtype.ext
      ext x
      exact hc p x

private abbrev Marked (k : ℕ) (α : Type*) :=
  α × {σ : Perm α // HasLongCycles k σ}

private def markedOrbit {k : ℕ} {α : Type*} [DecidableEq α] [Fintype α]
    (p : Marked k α) : Finset α := orbitSet p.2.val p.1

private noncomputable def fiber (k : ℕ) {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) :
    {p : Marked k α // markedOrbit p = s} ≃
      s × {σ : Perm α // σ.IsCycleOn s ∧ HasLongCycles k σ} where
  toFun := fun ⟨p, hp⟩ ↦
    (⟨p.1, hp ▸ (mem_filter.mpr ⟨mem_univ _, SameCycle.rfl⟩ : p.1 ∈ markedOrbit p)⟩,
      ⟨p.2.val, hp ▸ orbit_cycle _ _, p.2.property⟩)
  invFun p := ⟨(p.1.val, ⟨p.2.val, p.2.property.2⟩), orbit_eq p.2.property.1 p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem fiber_count (k : ℕ) (hk : 0 < k) {n : ℕ} (s : Finset (Fin n)) :
    Nat.card {p : Marked k (Fin n) // markedOrbit p = s} =
      if k ≤ s.card then s.card.factorial * countLong k (Fin (n - s.card)) else 0 := by
  classical
  rw [Nat.card_congr (fiber k s), Nat.card_prod, Nat.card_eq_fintype_card (α := ↥s),
    Fintype.card_coe]
  split_ifs with h
  · rw [Nat.card_congr (splitCycle s k h), Nat.card_prod]
    have hs : 0 < Fintype.card s := by simpa using lt_of_lt_of_le hk h
    have hd : Fintype.card {i : Fin n // i ∉ s} = n - s.card := by
      rw [Fintype.card_subtype_compl (· ∈ s)]
      simp
    rw [show Nat.card (FullOn s) = (s.card - 1).factorial by simpa using cycle_count s hs,
      ← mul_assoc, Nat.mul_factorial_pred (by omega)]
    exact congrArg (_ * ·) (count_congr k (Fintype.equivFinOfCardEq hd))
  · obtain hs | hs := s.eq_empty_or_nonempty
    · simp [hs]
    obtain ⟨x, hx⟩ := hs
    have hem : IsEmpty {σ : Perm (Fin n) // σ.IsCycleOn s ∧ HasLongCycles k σ} := ⟨fun σ ↦
      h ((period_cycle σ.property.1 hx) ▸ σ.property.2 x)⟩
    rw [Nat.card_of_isEmpty, mul_zero]

/-- Count marked permutations by the size of the marked cycle. A set of size `d`
has `d!` choices of a full cycle together with a marked point on that cycle. -/
private theorem count_rec (k n : ℕ) (hk : 0 < k) :
    n * countLong k (Fin n) = ∑ d ∈ range (n + 1),
      if k ≤ d then n.choose d * d.factorial * countLong k (Fin (n - d)) else 0 := by
  classical
  let term (d : ℕ) := if k ≤ d then d.factorial * countLong k (Fin (n - d)) else 0
  calc
    _ = Nat.card (Marked k (Fin n)) := by simp [Marked, countLong]
    _ = ∑ s : Finset (Fin n), Nat.card {p : Marked k (Fin n) // markedOrbit p = s} := by
      rw [← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv _)]
    _ = ∑ s ∈ (univ : Finset (Fin n)).powerset, term s.card := by
      simp only [powerset_univ, term, fiber_count k hk]
    _ = _ := by
      rw [sum_powerset]
      simp only [card_univ, Fintype.card_fin, sum_powersetCard, nsmul_eq_mul]
      refine sum_congr rfl fun d _ ↦ ?_
      by_cases h : k ≤ d <;> simp [term, h, mul_assoc]

private noncomputable def tail (k n : ℕ) : ℝ := countLong k (Fin n) / (n.factorial : ℝ)

private theorem tail_rec (k n : ℕ) (hk : 0 < k) :
    n * tail k n = ∑ d ∈ range (n + 1), if k ≤ d then tail k (n - d) else 0 := by
  classical
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  simp only [tail, ← mul_div_assoc]
  rw [div_eq_iff hn, sum_mul]
  have h := congrArg (Nat.cast : ℕ → ℝ) (count_rec k n hk)
  push_cast at h
  rw [h]
  refine sum_congr rfl fun d hd ↦ ?_
  split_ifs with hkd
  · have hdn : d ≤ n := by simpa using mem_range.mp hd
    have he := Nat.choose_mul_factorial_mul_factorial hdn
    have he' : (n.choose d : ℝ) * d.factorial * (n - d).factorial = n.factorial := by
      exact_mod_cast he
    rw [← he']
    field_simp
  · simp

private theorem tail_lt (k n : ℕ) (hn : 0 < n) (hnk : n < k) : tail k n = 0 := by
  have hem : IsEmpty {σ : Perm (Fin n) // HasLongCycles k σ} := ⟨fun σ ↦ by
    let x : Fin n := ⟨0, hn⟩
    have hx := σ.property x
    have hp := minimalPeriod_le_card (f := (σ.val : _ → _)) (x := x)
    simp only [Fintype.card_fin] at hp
    omega⟩
  simp only [tail, countLong, Nat.card_of_isEmpty, Nat.cast_zero, zero_div]

private theorem tail_zero (k : ℕ) : tail k 0 = 1 := by
  classical
  simp [tail, countLong, Nat.card_eq_fintype_card, Fintype.card_subtype, HasLongCycles]

/-- The empty complement contributes one. A nonempty complement has at least `k` points. -/
private theorem tail_sum {k n : ℕ} (hk : 0 < k) (hn : k ≤ n) :
    n * tail k n = 1 + ∑ j ∈ Icc k (n - k), tail k j := by
  classical
  rw [tail_rec k n hk, ← sum_range_reflect]
  simp only [Nat.add_sub_cancel]
  calc
    _ = ∑ j ∈ range (n + 1), ((if j = 0 then 1 else 0) +
        (if j ∈ Icc k (n - k) then tail k j else 0)) := by
      refine sum_congr rfl fun j hj ↦ ?_
      have hjn : j ≤ n := by simpa using mem_range.mp hj
      rw [Nat.sub_sub_self hjn]
      by_cases h : j = 0
      · simp [h, hn, tail_zero, hk.ne']
      · by_cases h' : j < k
        · simp [h, tail_lt k j (by omega) h']
        · simp only [ite_eq_right h, zero_add, mem_Icc, Nat.le_of_not_gt h', true_and]
          by_cases hh : k ≤ n - j
          · simp [hh, show j ≤ n - k by omega]
          · simp [hh, show ¬j ≤ n - k by omega]
    _ = _ := by
      have hs : Icc k (n - k) ⊆ range (n + 1) := fun j hj ↦ mem_range.mpr (by
        have := (mem_Icc.mp hj).2
        omega)
      rw [sum_add_distrib, ← sum_filter, ← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hs]
      simp

private theorem tail_bound (k n : ℕ) (hk : 0 < k) (hn : k ≤ n) :
    tail k n ≤ 1 / k := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    have hn' : (0 : ℝ) < n := by exact_mod_cast hk.trans_le hn
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    apply (mul_le_mul_iff_right₀ hn').mp
    rw [tail_sum hk hn]
    have h := sum_le_sum (s := Icc k (n - k)) (g := fun _ ↦ 1 / (k : ℝ))
      (fun j hj ↦ ih j (by have := (mem_Icc.mp hj).2; omega) (mem_Icc.mp hj).1)
    simp only [sum_const, Nat.card_Icc, nsmul_eq_mul] at h
    calc
      _ ≤ 1 + ↑(n - k + 1 - k) * (1 / (k : ℝ)) := by linarith
      _ ≤ _ := by
        field_simp
        exact_mod_cast (show k + (n - k + 1 - k) ≤ n by omega)

open MeasureTheory Real

variable {ω : ℝ → ℝ}

private abbrev BuchstabInitial (ω : ℝ → ℝ) := ∀ x ∈ Set.Icc (1 : ℝ) 2, ω x = 1 / x
private abbrev BuchstabEquation (ω : ℝ → ℝ) :=
  ∀ x : ℝ, 2 ≤ x → x * ω x = 1 + ∫ t in (1 : ℝ)..(x - 1), ω t

private theorem primitive_eq (h₁ : BuchstabInitial ω) (h₂ : BuchstabEquation ω)
    {x : ℝ} (hx : 1 ≤ x) :
    x * ω x = 1 + ∫ t in (1 : ℝ)..max 1 (x - 1), ω t := by
  by_cases h : 2 ≤ x
  · rw [max_eq_right (by linarith : 1 ≤ x - 1), h₂ x h]
  · rw [max_eq_left (by linarith : x - 1 ≤ 1), h₁ x ⟨hx, by linarith⟩]
    simp [ne_of_gt (by linarith : 0 < x)]

/-- Extend continuity and the bound by one across each successive unit interval. -/
private theorem buchstab_regular (h₁ : BuchstabInitial ω) (h₂ : BuchstabEquation ω) (n : ℕ) :
    ContinuousOn ω (Set.Icc 1 (n + 1 : ℝ)) ∧
      ∀ x ∈ Set.Icc (1 : ℝ) (n + 1), |ω x| ≤ 1 := by
  induction n with
  | zero => simp [h₁ 1 (by norm_num)]
  | succ n ih =>
    have hn : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hi {x : ℝ} (hx : x ∈ Set.Icc (1 : ℝ) (↑(n + 1 : ℕ) + 1)) :
        max 1 (x - 1) ∈ Set.Icc (1 : ℝ) (n + 1) := by
      refine ⟨le_max_left _ _, max_le hn ?_⟩
      have := hx.2
      push_cast at this
      linarith
    have hc := intervalIntegral.continuousOn_primitive_interval'
      (μ := volume) (ih.1.intervalIntegrable_of_Icc hn) Set.left_mem_uIcc
    rw [Set.uIcc_of_le hn] at hc
    constructor
    · have H : ContinuousOn (fun x : ℝ ↦ ∫ t in (1 : ℝ)..max 1 (x - 1), ω t)
          (Set.Icc 1 (↑(n + 1 : ℕ) + 1)) :=
        hc.comp (by fun_prop) fun _ hx ↦ hi hx
      apply (((continuousOn_const (c := (1 : ℝ))).add H).div continuousOn_id ?_).congr
      · intro x hx
        exact (eq_div_iff (ne_of_gt (zero_lt_one.trans_le hx.1))).mpr
          ((mul_comm _ _).trans (primitive_eq h₁ h₂ hx.1))
      · intro x hx
        exact ne_of_gt (zero_lt_one.trans_le hx.1)
    · intro x hx
      have h1 := (hi hx).1
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const (f := ω)
        (C := 1) (a := 1) (b := max 1 (x - 1)) (fun t ht ↦ ih.2 t (by
          rw [Set.uIoc_of_le h1] at ht; exact ⟨ht.1.le, ht.2.trans (hi hx).2⟩))
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h1), one_mul] at hb
      have hs := abs_add_le (1 : ℝ) (∫ t in (1 : ℝ)..max 1 (x - 1), ω t)
      rw [← primitive_eq h₁ h₂ hx.1, abs_mul, abs_of_nonneg (zero_le_one.trans hx.1),
        abs_one] at hs
      have hmx : max 1 (x - 1) ≤ x := max_le hx.1 (by linarith)
      nlinarith [hx.1]

private theorem omega_bound (h₁ : BuchstabInitial ω) (h₂ : BuchstabEquation ω)
    {x : ℝ} (hx : 1 ≤ x) :
    |ω x| ≤ 1 := by
  obtain ⟨n, hn⟩ := exists_nat_ge x
  exact (buchstab_regular h₁ h₂ n).2 x ⟨hx, by linarith⟩

private theorem omega_cont (h₁ : BuchstabInitial ω) (h₂ : BuchstabEquation ω)
    {a b : ℝ} (ha : 1 ≤ a) :
    ContinuousOn ω (Set.Icc a b) := by
  obtain ⟨n, hn⟩ := exists_nat_ge b
  exact (buchstab_regular h₁ h₂ n).1.mono
    (Set.Icc_subset_Icc ha (by linarith))

private theorem buchstab_lip (h₁ : BuchstabInitial ω) (h₂ : BuchstabEquation ω) {x y : ℝ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |y * ω y - x * ω x| ≤ |y - x| := by
  have hint (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : IntervalIntegrable ω volume a b :=
    (omega_cont h₁ h₂ (le_min ha hb)).intervalIntegrable
  rw [primitive_eq h₁ h₂ hy, primitive_eq h₁ h₂ hx, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (hint _ _ le_rfl (le_max_left _ _))
      (hint _ _ le_rfl (le_max_left _ _))]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (f := ω)
    (a := max 1 (x - 1)) (b := max 1 (y - 1)) (C := 1) (fun t ht ↦ omega_bound h₁ h₂
      ((le_min (le_max_left _ _) (le_max_left _ _)).trans ht.1.le))
  rw [Real.norm_eq_abs, one_mul] at hb
  refine hb.trans ?_
  simpa [max_comm (1 : ℝ), sub_sub_sub_cancel_right] using
    abs_max_sub_max_le_abs (y - 1) (x - 1) 1

private theorem omega_lip (h₁ : BuchstabInitial ω) (h₂ : BuchstabEquation ω) {x y : ℝ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) : |ω y - ω x| ≤ 2 * |y - x| := by
  have hd : y * (ω y - ω x) = (y * ω y - x * ω x) - (y - x) * ω x := by ring
  have hb := abs_sub (y * ω y - x * ω x) ((y - x) * ω x)
  rw [← hd, abs_mul, abs_of_nonneg (zero_le_one.trans hy), abs_mul] at hb
  have := mul_le_of_le_one_right (abs_nonneg (y - x)) (omega_bound h₁ h₂ hx)
  nlinarith [buchstab_lip h₁ h₂ hx hy, abs_nonneg (ω y - ω x)]

private theorem grid_error (h₁ : BuchstabInitial ω) (h₂ : BuchstabEquation ω) (k j : ℕ) (hk : 0 < k)
    (hj : k ≤ j) :
    |ω (j / k) / k - ∫ t in (j / k : ℝ)..((j + 1 : ℕ) / k : ℝ), ω t| ≤ 2 / (k : ℝ) ^ 2 := by
  let a := (j / k : ℝ)
  let b := ((j + 1 : ℕ) / k : ℝ)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have ha : 1 ≤ a := (one_le_div hk').2 (by exact_mod_cast hj)
  have hd : b - a = 1 / k := by dsimp [a, b]; push_cast; ring
  have hab : a ≤ b := by linarith [one_div_pos.mpr hk']
  have hint : IntervalIntegrable ω volume a b :=
    (omega_cont h₁ h₂ (b := b) ha).intervalIntegrable_of_Icc hab
  have he : ω a / k = ∫ _ in a..b, ω a := by
    rw [intervalIntegral.integral_const, smul_eq_mul, hd]; ring
  change |ω a / k - ∫ t in a..b, ω t| ≤ _
  rw [he, ← intervalIntegral.integral_sub intervalIntegrable_const hint]
  have H := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun x ↦ ω a - ω x) (C := 2 / k) (fun x hx ↦ by
      rw [Set.uIoc_of_le hab] at hx
      rw [Real.norm_eq_abs, abs_sub_comm]
      apply (omega_lip h₁ h₂ ha (ha.trans hx.1.le)).trans
      rw [abs_of_nonneg (sub_nonneg.mpr hx.1.le)]
      linarith [show 2 / (k : ℝ) = 2 * (1 / k) by ring, hx.2])
  rw [Real.norm_eq_abs, hd, abs_of_pos (one_div_pos.mpr hk')] at H
  exact H.trans_eq (by ring)

/-- Compare the discrete recurrence with the integral on the mesh of width `1 / k`.
The last summand has no matching interval and is bounded separately by `1 / k`. -/
private theorem tail_error (h₁ : BuchstabInitial ω) (h₂ : BuchstabEquation ω)
    (k n : ℕ) (hk : 0 < k) (hn : k ≤ n) :
    |tail k n - ω (n / k) / k| ≤ 8 * n / (k : ℝ) ^ 3 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    have hn' : (0 : ℝ) < n := by exact_mod_cast hk.trans_le hn
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hn
    have hq : 1 ≤ (n / k : ℝ) := (one_le_div hk').2 hkn
    apply (mul_le_mul_iff_right₀ hn').mp
    rw [← abs_of_pos hn', ← abs_mul, abs_of_pos hn', mul_sub,
      show (n : ℝ) * (ω (n / k) / k) = n / k * ω (n / k) by ring, tail_sum hk hn]
    by_cases hl : 2 * k ≤ n
    · have hl' : 2 ≤ (n / k : ℝ) := (le_div_iff₀ hk').2 (by exact_mod_cast hl)
      let b := n - k
      have hb : k ≤ b := by dsimp [b]; omega
      have hb' : b < n := by dsimp [b]; omega
      have hbq : b / (k : ℝ) = n / k - 1 := by
        dsimp [b]; rw [Nat.cast_sub hn]; field_simp
      let G (j : ℕ) := ∫ t in (j / k : ℝ)..((j + 1 : ℕ) / k : ℝ), ω t
      have hG : ∑ j ∈ Ico k b, G j = ∫ t in (1 : ℝ)..(n / k - 1), ω t := by
        have H := intervalIntegral.sum_integral_adjacent_intervals_Ico
          (a := fun j : ℕ ↦ j / (k : ℝ)) (f := ω) (μ := volume) hb (fun j hj ↦ by
            have hjk : (1 : ℝ) ≤ j / k := (one_le_div hk').2 (by exact_mod_cast hj.1)
            exact (omega_cont h₁ h₂ hjk).intervalIntegrable_of_Icc
              (div_le_div_of_nonneg_right (by exact_mod_cast j.le_succ) hk'.le))
        simpa only [div_self hk'.ne', hbq, G] using H
      rw [h₂ _ hl', ← hG, add_sub_add_left_eq_sub]
      change |∑ j ∈ Icc k b, tail k j - _| ≤ _
      rw [← insert_right_Ico hb, sum_insert (by simp), add_sub_assoc,
        ← sum_sub_distrib]
      have hv : |tail k b| ≤ 1 / k := by
        rw [abs_of_nonneg (by unfold tail; positivity)]
        exact tail_bound _ _ hk hb
      have herr (j : ℕ) (hj : j ∈ Ico k b) :
          |tail k j - G j| ≤ 8 * j / (k : ℝ) ^ 3 + 2 / (k : ℝ) ^ 2 := by
        apply (abs_sub_le _ (ω (j / k) / k) _).trans
        exact add_le_add (ih j (lt_trans (mem_Ico.mp hj).2 hb') (mem_Ico.mp hj).1)
          (grid_error h₁ h₂ k j hk (mem_Ico.mp hj).1)
      have hs' : Ico k b ⊆ range n := fun j hj ↦ mem_range.mpr ((mem_Ico.mp hj).2.trans hb')
      have hs : (∑ j ∈ Ico k b, (8 * j / (k : ℝ) ^ 3 + 2 / (k : ℝ) ^ 2)) ≤
          ∑ j ∈ range n, (8 * j / (k : ℝ) ^ 3 + 2 / (k : ℝ) ^ 2) :=
        sum_le_sum_of_subset_of_nonneg hs' fun j _ _ ↦ by positivity
      have hsum : (∑ j ∈ range n, (j : ℝ)) * 2 ≤ (n : ℝ) ^ 2 := by
        have h := sum_range_id_mul_two n
        have H : (∑ i ∈ range n, i) * 2 ≤ n ^ 2 := by
          rw [h, sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        rw [← Nat.cast_sum]
        exact_mod_cast H
      calc
        _ ≤ |tail k b| + ∑ j ∈ Ico k b, |tail k j - G j| :=
          (abs_add_le _ _).trans (add_le_add le_rfl (abs_sum_le_sum_abs _ _))
        _ ≤ 1 / k + _ := add_le_add hv (sum_le_sum herr)
        _ ≤ 1 / k + ∑ j ∈ range n, (8 * j / (k : ℝ) ^ 3 + 2 / (k : ℝ) ^ 2) := add_le_add le_rfl hs
        _ ≤ _ := by
          rw [sum_add_distrib, ← sum_div, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
          field_simp
          nlinarith [mul_nonneg (sub_nonneg.mpr hkn) (by positivity : 0 ≤ (n : ℝ) + k),
            mul_nonneg (sub_nonneg.mpr hkn) hn'.le]
    · have hu : (n / k : ℝ) ≤ 2 := (div_le_iff₀ hk').2 (by exact_mod_cast (by omega : n ≤ 2 * k))
      rw [h₁ _ ⟨hq, hu⟩, mul_one_div_cancel (by positivity),
        Icc_eq_empty_of_lt (by omega : n - k < k)]
      simp only [sum_empty, add_zero, sub_self, abs_zero]
      positivity

/-- At threshold `⌈n / x⌉₊`, combine the counting bound with the mesh estimate. -/
private theorem scaled_tail_bounds (h₁ : BuchstabInitial ω) (h₂ : BuchstabEquation ω)
    {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx : 1 ≤ x) :
    |n * tail ⌈n / x⌉₊ n - x * ω x| ≤ min (2 * x) (9 * x ^ 3 / n) := by
  let k := ⌈n / x⌉₊
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx' : 0 < x := zero_lt_one.trans_le hx
  have hk : 0 < k := Nat.one_le_ceil_iff.mpr (by positivity)
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkn : k ≤ n := Nat.ceil_le.mpr (div_le_self hn'.le hx)
  have ht : 1 ≤ (n / k : ℝ) := (one_le_div hk').2 (by exact_mod_cast hkn)
  have hlow : (n : ℝ) ≤ k * x := (div_le_iff₀ hx').mp (Nat.le_ceil _)
  have hup : (k : ℝ) * x < n + x := by
    have h := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (a := (n / x : ℝ)) (by positivity)) hx'
    rwa [add_mul, div_mul_cancel₀ _ hx'.ne', one_mul] at h
  have hnx : (n / k : ℝ) ≤ x := (div_le_iff₀ hk').2 (by linarith)
  have hInv : 1 / (k : ℝ) ≤ x / n := by
    rw [div_le_div_iff₀ hk' hn']; linarith
  change |n * tail k n - _| ≤ _
  apply le_min
  · have htp : 0 ≤ tail k n := by unfold tail; positivity
    have hlin := mul_le_mul_of_nonneg_left (tail_bound _ _ hk hkn) hn'.le
    have homega := mul_le_mul_of_nonneg_left (omega_bound h₁ h₂ hx) hx'.le
    calc
      _ ≤ |n * tail k n| + |x * ω x| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_of_nonneg (by positivity), abs_mul, abs_of_pos hx']
        linarith [show (n : ℝ) * (1 / k) = n / k by ring]
  · calc
      _ ≤ |n * tail k n - (n / k : ℝ) * ω (n / k)| + |(n / k : ℝ) * ω (n / k) - x * ω x| :=
        abs_sub_le _ _ _
      _ ≤ n * (8 * n / (k : ℝ) ^ 3) + |n / k - x| := by
        apply add_le_add _ (buchstab_lip h₁ h₂ hx ht)
        rw [show (n / k : ℝ) * ω (n / k) = n * (ω (n / k) / k) by ring, ← mul_sub,
          abs_mul, abs_of_pos hn']
        exact mul_le_mul_of_nonneg_left (tail_error h₁ h₂ k n hk hkn) hn'.le
      _ ≤ _ := by
        have ha : (n : ℝ) * (8 * n / k ^ 3) = 8 * (n / k) ^ 3 / n := by field_simp
        have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ n / k) hnx 3
        have hsmall : x - n / k ≤ x * (1 / k) := by
          field_simp; linarith
        have hsm := (mul_le_mul_of_nonneg_left hInv hx'.le)
        have hx3 : x * x ≤ x ^ 3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg x)]
        rw [ha, abs_of_nonpos (sub_nonpos.mpr hnx)]
        calc
          _ ≤ 8 * x ^ 3 / n + x * x / n := add_le_add
            (div_le_div_of_nonneg_right (by linarith) hn'.le)
            (by linarith [show x * (x / n) = x * x / n by ring])
          _ ≤ _ := by rw [← add_div]; gcongr; linarith

private noncomputable def weight (ℓ : ℕ) (x : ℝ) := x ^ (-(ℓ : ℝ) - 1)

/-- Interpolate the two tail bounds to obtain an error integrable even at order two. -/
private theorem weighted_error (h₁ : BuchstabInitial ω) (h₂ : BuchstabEquation ω) {n ℓ : ℕ}
    (hn : 1 ≤ n) (hℓ : 2 ≤ ℓ) {x : ℝ} (hx : 1 ≤ x) :
    |n * tail ⌈n / x⌉₊ n * weight ℓ x - ω x / x ^ ℓ| ≤
      9 * (n : ℝ) ^ (-(1 / 4) : ℝ) * x ^ (-(3 / 2) : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx' : 0 < x := zero_lt_one.trans_le hx
  let u := x ^ 2 / n
  have hu : 0 < u := by dsimp [u]; positivity
  have H := scaled_tail_bounds h₁ h₂ hn hx
  have hu' : |n * tail ⌈n / x⌉₊ n - x * ω x| ≤ 9 * x * u ^ (1 / 4 : ℝ) := by
    by_cases hh : 1 ≤ u
    · have h := Real.one_le_rpow hh (by norm_num : (0 : ℝ) ≤ 1 / 4)
      nlinarith [mul_le_mul_of_nonneg_left h hx'.le, H.trans (min_le_left _ _)]
    · have h := Real.rpow_le_rpow_of_exponent_ge hu (le_of_not_ge hh)
          (by norm_num : (1 / 4 : ℝ) ≤ 1)
      rw [Real.rpow_one] at h
      calc
        _ ≤ 9 * x ^ 3 / n := H.trans (min_le_right _ _)
        _ = 9 * x * u := by dsimp [u]; ring
        _ ≤ _ := by gcongr
  have hw (t : ℝ) : x ^ t * weight ℓ x = x ^ (t + (-(ℓ : ℝ) - 1)) :=
    (Real.rpow_add hx' ..).symm
  have he : x * ω x * weight ℓ x = ω x / x ^ ℓ := by
    have H1 := hw 1
    rw [Real.rpow_one] at H1
    rw [mul_right_comm, H1, show 1 + (-(ℓ : ℝ) - 1) = -ℓ by ring,
      Real.rpow_neg hx'.le, Real.rpow_natCast]
    ring
  rw [← he, ← sub_mul, abs_mul, abs_of_nonneg (show 0 ≤ weight ℓ x from Real.rpow_nonneg hx'.le _)]
  refine (mul_le_mul_of_nonneg_right hu' (Real.rpow_nonneg hx'.le _)).trans ?_
  have hur : u ^ (1 / 4 : ℝ) = x ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 4) : ℝ) := by
    dsimp [u]
    rw [Real.rpow_neg hn'.le, ← div_eq_mul_inv, Real.div_rpow (sq_nonneg x) hn'.le]
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx'.le]
    norm_num
  rw [hur]
  calc
    _ = 9 * (n : ℝ) ^ (-(1 / 4) : ℝ) * ((x ^ (1 + (1 / 2) : ℝ)) * weight ℓ x) := by
      rw [Real.rpow_add hx', Real.rpow_one]; unfold weight; ring
    _ ≤ _ := by
      rw [hw]; gcongr
      have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
      linarith

/-- For a permutation with shortest cycle `X`, integrate the weight from `n / X` to infinity.
Summing these integrals gives an exact integral formula for the moment. -/
private theorem moment_integral {n ℓ : ℕ} (hn : 1 ≤ n) (hℓ : 2 ≤ ℓ) :
    IntegrableOn (fun x : ℝ ↦ n * tail ⌈n / x⌉₊ n * weight ℓ x) (Set.Ioi 1) ∧
    (∑ σ : Perm (Fin n), ((⨅ x, minimalPeriod σ x : ℕ) : ℝ) ^ ℓ) / (n.factorial : ℝ) =
      ℓ * (n : ℝ) ^ (ℓ - 1) *
        ∫ x in Set.Ioi (1 : ℝ), n * tail ⌈n / x⌉₊ n * weight ℓ x := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl' : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hexp : -(ℓ : ℝ) - 1 < -1 := by linarith
  let X (σ : Perm (Fin n)) := ⨅ x, minimalPeriod σ x
  have hX₁ (σ : Perm (Fin n)) : 0 < (X σ : ℝ) := by
    have h : HasLongCycles 1 σ := fun x ↦
      minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts x)
    exact_mod_cast (long_iff hn σ).mp h
  have hX₂ (σ : Perm (Fin n)) : (X σ : ℝ) ≤ n := by
    have h' : X σ ≤ n := (ciInf_le (OrderBot.bddBelow _) (⟨0, hn⟩ : Fin n)).trans (by
      simpa using (minimalPeriod_le_card (f := (σ : _ → _)) (x := (⟨0, hn⟩ : Fin n))))
    exact_mod_cast h'
  let K (σ : Perm (Fin n)) := (Set.Ici ((n : ℝ) / X σ)).indicator (weight ℓ)
  have hK (σ) : IntegrableOn (K σ) (Set.Ici 1) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      (integrableOn_Ioi_rpow_of_lt hexp zero_lt_one)).indicator measurableSet_Ici
  have hI (σ) : (∫ x in Set.Ici (1 : ℝ), K σ x) =
      (X σ : ℝ) ^ ℓ / ((n : ℝ) ^ ℓ * ℓ) := by
    have hNX : 1 ≤ (n : ℝ) / X σ := (one_le_div (hX₁ _)).2 (hX₂ _)
    rw [show (∫ x in Set.Ici (1 : ℝ), K σ x) = _ from setIntegral_indicator measurableSet_Ici,
      Set.Ici_inter_Ici, max_eq_right hNX, integral_Ici_eq_integral_Ioi]
    unfold weight
    rw [integral_Ioi_rpow_of_lt hexp (div_pos hn' (hX₁ σ)),
      sub_add_cancel, Real.rpow_neg (by positivity), Real.rpow_natCast, div_pow]
    field_simp
  have heq : Set.EqOn (fun x : ℝ ↦ ((n : ℝ) / n.factorial) * ∑ σ, K σ x)
      (fun x : ℝ ↦ n * tail ⌈n / x⌉₊ n * weight ℓ x) (Set.Ici 1) := by
    intro x hx
    have hx' : 0 < x := zero_lt_one.trans_le hx
    have hσ (σ : Perm (Fin n)) : K σ x = if HasLongCycles ⌈n / x⌉₊ σ then weight ℓ x else 0 := by
      have H := long_iff (k := ⌈n / x⌉₊) hn σ
      change HasLongCycles ⌈n / x⌉₊ σ ↔ ⌈n / x⌉₊ ≤ X σ at H
      simp only [Nat.ceil_le, div_le_iff₀ hx'] at H
      simp [K, Set.indicator_apply, H, div_le_iff₀ (hX₁ σ), mul_comm]
    simp_rw [hσ, ← sum_filter]
    simp [tail, countLong, Nat.card_eq_fintype_card, Fintype.card_subtype,
      mul_assoc, div_eq_mul_inv]
    ring_nf
    simp
  constructor
  · apply IntegrableOn.mono_set _ Set.Ioi_subset_Ici_self
    exact (integrableOn_congr_fun heq measurableSet_Ici).mp
      ((integrable_finsetSum univ (fun σ _ ↦ hK σ)).const_mul _)
  · rw [← integral_Ici_eq_integral_Ioi, ← setIntegral_congr_fun measurableSet_Ici heq,
      integral_const_mul, integral_finsetSum _ (fun σ _ ↦ hK σ)]
    simp_rw [hI]
    rw [← sum_div, show (n : ℝ) ^ ℓ = (n : ℝ) ^ (ℓ - 1) * n by
      conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ ℓ), pow_succ]]
    change (∑ σ, (X σ : ℝ) ^ ℓ) / _ = _
    field_simp

private theorem integral_error (h₁ : BuchstabInitial ω) (h₂ : BuchstabEquation ω) {n ℓ : ℕ}
    (hn : 1 ≤ n) (hℓ : 2 ≤ ℓ) :
    |(∫ x in Set.Ioi (1 : ℝ), n * tail ⌈n / x⌉₊ n * weight ℓ x) -
      ∫ x in Set.Ioi (1 : ℝ), ω x / x ^ ℓ| ≤ 18 * (n : ℝ) ^ (-(1 / 4) : ℝ) := by
  have hℓ' : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hc : LipschitzOnWith 2 ω (Set.Ioi 1) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro x hx y hy
    simpa [Real.dist_eq] using omega_lip h₁ h₂ hy.le hx.le
  have hi : IntegrableOn (fun x : ℝ ↦ ω x / x ^ ℓ) (Set.Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt (by linarith : -(ℓ : ℝ) < -1) zero_lt_one).mono' ?_ ?_
    · exact (hc.continuousOn.div (by fun_prop) (fun x hx ↦ pow_ne_zero _ (by
        have : 1 < x := hx
        positivity))).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
      have hx' : 0 < x := zero_lt_one.trans hx
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hx' _), Real.rpow_neg hx'.le,
        Real.rpow_natCast, ← one_div]
      exact div_le_div_of_nonneg_right (omega_bound h₁ h₂ hx.le) (pow_nonneg hx'.le _)
  rw [← integral_sub (moment_integral hn hℓ).1 hi]
  have H := norm_integral_le_of_norm_le
    (f := fun x : ℝ ↦ n * tail ⌈n / x⌉₊ n * weight ℓ x - ω x / x ^ ℓ)
    ((integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) zero_lt_one).const_mul
      (9 * (n : ℝ) ^ (-(1 / 4) : ℝ))) (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun x hx ↦ weighted_error h₁ h₂ hn hℓ hx.le))
  rw [Real.norm_eq_abs, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one] at H
  norm_num at H
  linarith

end MetaMathlibExt.smallest_cycle_moment_asymp

namespace MetaMathlibExt
open smallest_cycle_moment_asymp

/-- **Higher moments of the smallest cycle length.** Let $\omega$ be a real function with
$\omega(x) = 1/x$ for $1 \le x \le 2$ and $x\,\omega(x) = 1 + \int_1^{x-1} \omega(t)\,dt$ for
$x \ge 2$, and for $n \ge 1$ let $X_n$ be the length of the smallest cycle of a uniformly random
permutation of $\{1, \dots, n\}$. For every integer $\ell \ge 2$ there are real constants
$\varepsilon > 0$ and $C$ such that for every $n \ge 1$

$$\left| \mathbb{E}(X_n^\ell) - \ell\, n^{\ell-1} \int_1^\infty \frac{\omega(x)}{x^\ell}\,dx \right|
\le C\, n^{\ell-1} n^{-\varepsilon}.$$

Source: Claude Gravel and Daniel Panario, *Evaluating the Generalized Buchstab
Function and Revisiting the Variance of the Distribution of the Smallest
Components of Combinatorial Objects*, INTEGERS 24 (2024), Article A7, Theorem 1
(`integers-2024-A7-thm-1`). -/
public theorem smallest_cycle_moment_asymp (ω : ℝ → ℝ)
    (hω₁ : ∀ x ∈ Set.Icc (1 : ℝ) 2, ω x = 1 / x)
    (hω₂ : ∀ x : ℝ, 2 ≤ x → x * ω x = 1 + ∫ t in (1 : ℝ)..(x - 1), ω t)
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ∃ ε C : ℝ, 0 < ε ∧ ∀ n : ℕ, 1 ≤ n →
      |(∑ σ : Equiv.Perm (Fin n), ((⨅ x, Function.minimalPeriod σ x : ℕ) : ℝ) ^ ℓ) /
            (n.factorial : ℝ) -
          ℓ * (n : ℝ) ^ (ℓ - 1) * ∫ x in Set.Ioi (1 : ℝ), ω x / x ^ ℓ|
        ≤ C * (n : ℝ) ^ (ℓ - 1) * (n : ℝ) ^ (-ε) := by
  refine ⟨1 / 4, 18 * ℓ, by norm_num, fun n hn ↦ ?_⟩
  rw [(moment_integral hn hℓ).2, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ℓ * (n : ℝ) ^ (ℓ - 1) * (18 * (n : ℝ) ^ (-(1 / 4) : ℝ)) :=
      mul_le_mul_of_nonneg_left (integral_error hω₁ hω₂ hn hℓ) (by positivity)
    _ = _ := by ring

end MetaMathlibExt
