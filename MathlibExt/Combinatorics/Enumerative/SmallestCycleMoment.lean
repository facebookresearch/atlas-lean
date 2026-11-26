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
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Moments of the smallest cycle of a random permutation

`MetaMathlibExt.smallest_cycle_moment_asymp` gives a power-saving error bound for the
Buchstab integral approximation to each moment of order at least two, and
`MetaMathlibExt.smallest_cycle_mean_asymp` shows that the mean is asymptotic to
`e^{-γ} log n`.

Marking the cycle through a point gives a recurrence for the probability that all cycles
have length at least `k`. Comparing this recurrence with the integrated Buchstab equation
gives a pointwise estimate. Integrating the estimate against the moment weight yields
the exponent `1 / 4`.

The proof for the mean does not use the Buchstab function. For fixed `k`, the same
recurrence shows that the increments of the tail probabilities have generating function
`exp (-∑_{1 ≤ j < k} x^j / j)` on `(-1, 1)`, and Abel's limit theorem identifies the limit of
the tail probabilities with `e^{-H_{k-1}}`. The recurrence also bounds the `m`-th increment by
`e^3 e^{-m/k}`, so the convergence is fast as long as `k ≤ n / (3 log n)`; the remaining tail
probabilities are at most `1 / k`. Hence the mean differs from `∑_{k ≤ n} e^{-H_{k-1}}`, which is
asymptotic to `e^{-γ} log n`, by `O(log log n)`.
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

namespace MetaMathlibExt.smallest_cycle_mean_asymp

open MetaMathlibExt.smallest_cycle_moment_asymp
open Filter Topology Real Asymptotics

/-! ### A sequence satisfying the tail recurrence

Throughout, `p : ℕ → ℝ` takes values in `[0, 1]`, `p 0 = 1`, and
`n p(n) = ∑_{j ≤ n - k} p(j)` for some `k ≥ 1`. -/

/-- The increments of a sequence: `incr p 0 = p 0` and `incr p (n + 1) = p (n + 1) - p n`. -/
private noncomputable def incr (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => p 0
  | n + 1 => p (n + 1) - p n

private theorem sum_incr (p : ℕ → ℝ) (n : ℕ) : ∑ i ∈ range (n + 1), incr p i = p n := by
  induction n with
  | zero => simp [incr]
  | succ n ih => rw [sum_range_succ, ih, incr]; ring

variable {k : ℕ} {p : ℕ → ℝ}

/-- Differencing the recurrence `n p(n) = ∑_{j ≤ n - k} p(j)`. -/
private theorem rec_succ (hrec : ∀ n : ℕ, n * p n = ∑ j ∈ range (n + 1 - k), p j)
    (n : ℕ) :
    (n + 1 : ℝ) * p (n + 1) = n * p n + if k ≤ n + 1 then p (n + 1 - k) else 0 := by
  have h1 := hrec (n + 1)
  push_cast at h1
  rw [h1, hrec n]
  split_ifs with h
  · rw [show n + 1 + 1 - k = (n + 1 - k) + 1 by omega, sum_range_succ]
  · rw [show n + 1 + 1 - k = 0 by omega, show n + 1 - k = 0 by omega]; simp

private theorem incr_succ (hrec : ∀ n : ℕ, n * p n = ∑ j ∈ range (n + 1 - k), p j)
    (n : ℕ) :
    (n + 1 : ℝ) * incr p (n + 1) = (if k ≤ n + 1 then p (n + 1 - k) else 0) - p n := by
  rw [incr, mul_sub, rec_succ hrec n]; ring

/-- A window of `k - 1` consecutive increments telescopes. -/
private theorem window_sum (p : ℕ → ℝ) (n q : ℕ) :
    ∑ j ∈ range q, (if j ≤ n then incr p (n - j) else 0) =
      p n - if q ≤ n then p (n - q) else 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [sum_range_succ, ih]
    by_cases hq : q + 1 ≤ n
    · rw [ite_eq_left (by omega : q ≤ n), ite_eq_left (by omega : q ≤ n), ite_eq_left hq,
        show n - q = (n - (q + 1)) + 1 by omega, incr]
      ring
    · by_cases hq' : q ≤ n
      · obtain rfl : q = n := by omega
        simp [incr]
      · rw [ite_eq_right hq', ite_eq_right hq', ite_eq_right hq]; ring

/-- The increments satisfy `(n + 1) a(n + 1) = -∑_{j < k - 1, j ≤ n} a(n - j)`. -/
private theorem incr_rec (hk : 0 < k)
    (hrec : ∀ n : ℕ, n * p n = ∑ j ∈ range (n + 1 - k), p j) (n : ℕ) :
    (n + 1 : ℝ) * incr p (n + 1) =
      -∑ j ∈ range (k - 1), (if j ≤ n then incr p (n - j) else 0) := by
  rw [incr_succ hrec, window_sum]
  by_cases h : k ≤ n + 1
  · rw [ite_eq_left h, ite_eq_left (by omega), show n + 1 - k = n - (k - 1) by omega]; ring
  · rw [ite_eq_right h, ite_eq_right (by omega)]; ring

private theorem abs_incr_le (h0 : p 0 = 1) (hnn : ∀ n, 0 ≤ p n) (hle : ∀ n, p n ≤ 1)
    (m : ℕ) : |incr p m| ≤ 1 := by
  cases m with
  | zero => simp [incr, h0]
  | succ n =>
    simp only [incr]
    rw [abs_le]; constructor <;> linarith [hnn n, hnn (n + 1), hle n, hle (n + 1)]

/-- Strong induction on the recurrence: once `m` exceeds `N ≥ ∑_{j < k - 1} x^(j+1)`, the
weighted increments `|a(m)| x^m` cannot exceed their earlier maximum. -/
private theorem incr_bound (hk : 0 < k) (h0 : p 0 = 1) (hnn : ∀ n, 0 ≤ p n)
    (hle : ∀ n, p n ≤ 1) (hrec : ∀ n : ℕ, n * p n = ∑ j ∈ range (n + 1 - k), p j)
    {x : ℝ} (hx : 1 ≤ x) {N : ℕ} (hN : ∑ j ∈ range (k - 1), x ^ (j + 1) ≤ N) (m : ℕ) :
    |incr p m| * x ^ m ≤ x ^ N := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m < N ∨ m = 0
    · calc |incr p m| * x ^ m ≤ 1 * x ^ m := by
            gcongr; exact abs_incr_le h0 hnn hle m
        _ ≤ x ^ N := by
          rw [one_mul]
          rcases hm with hm | rfl
          · exact pow_le_pow_right₀ hx hm.le
          · simpa using one_le_pow₀ hx
    · have hNm : N ≤ m := by omega
      obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
      have hn1 : (0 : ℝ) < n + 1 := by positivity
      have key : (n + 1 : ℝ) * (|incr p (n + 1)| * x ^ (n + 1)) ≤ (n + 1 : ℝ) * x ^ N := by
        calc (n + 1 : ℝ) * (|incr p (n + 1)| * x ^ (n + 1))
            = |(n + 1 : ℝ) * incr p (n + 1)| * x ^ (n + 1) := by
              rw [abs_mul, abs_of_pos hn1]; ring
          _ = |∑ j ∈ range (k - 1), (if j ≤ n then incr p (n - j) else 0)| *
                x ^ (n + 1) := by
              rw [incr_rec hk hrec, abs_neg]
          _ ≤ (∑ j ∈ range (k - 1), |if j ≤ n then incr p (n - j) else 0|) *
                x ^ (n + 1) := by
              gcongr; exact abs_sum_le_sum_abs _ _
          _ = ∑ j ∈ range (k - 1), |if j ≤ n then incr p (n - j) else 0| *
                x ^ (n + 1) := by
              rw [sum_mul]
          _ ≤ ∑ j ∈ range (k - 1), x ^ N * x ^ (j + 1) := by
              apply sum_le_sum
              intro j _
              split_ifs with hj
              · calc |incr p (n - j)| * x ^ (n + 1)
                    = (|incr p (n - j)| * x ^ (n - j)) * x ^ (j + 1) := by
                      rw [mul_assoc, ← pow_add]; congr 2; omega
                  _ ≤ x ^ N * x ^ (j + 1) := by
                      gcongr
                      exact ih (n - j) (by omega)
              · simp only [abs_zero, zero_mul]; positivity
          _ = x ^ N * ∑ j ∈ range (k - 1), x ^ (j + 1) := by rw [mul_sum]
          _ ≤ x ^ N * N := by gcongr
          _ ≤ x ^ N * (n + 1) := by
              gcongr
              exact_mod_cast hNm
          _ = (n + 1 : ℝ) * x ^ N := by ring
      exact le_of_mul_le_mul_left key hn1

/-- With `x = e^{1/k}` and `N = 3k`: the increments decay like `e^{-m/k}`. -/
private theorem incr_exp_bound (hk : 0 < k) (h0 : p 0 = 1) (hnn : ∀ n, 0 ≤ p n)
    (hle : ∀ n, p n ≤ 1) (hrec : ∀ n : ℕ, n * p n = ∑ j ∈ range (n + 1 - k), p j) (m : ℕ) :
    |incr p m| ≤ exp 3 * exp (-1 / k) ^ m := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hx : 1 ≤ exp (1 / k) := one_le_exp (by positivity)
  have hN : ∑ j ∈ range (k - 1), exp (1 / k) ^ (j + 1) ≤ ((3 * k : ℕ) : ℝ) := by
    calc ∑ j ∈ range (k - 1), exp (1 / k) ^ (j + 1) ≤ ∑ j ∈ range (k - 1), (3 : ℝ) := by
          apply sum_le_sum
          intro j hj
          have hj' : j + 1 ≤ k := by simp only [mem_range] at hj; omega
          rw [← exp_nat_mul]
          calc exp (((j + 1 : ℕ) : ℝ) * (1 / k)) ≤ exp 1 := by
                apply exp_le_exp.mpr
                rw [mul_one_div, div_le_one hk']
                exact_mod_cast hj'
            _ ≤ 3 := by linarith [exp_one_lt_d9]
      _ ≤ ((3 * k : ℕ) : ℝ) := by
          rw [sum_const, card_range, nsmul_eq_mul]
          have : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
          push_cast; linarith
  have h := incr_bound hk h0 hnn hle hrec hx hN m
  have hx3 : exp (1 / k) ^ (3 * k) = exp 3 := by
    rw [← exp_nat_mul]; congr 1; push_cast; field_simp
  have hxm : exp (1 / k) ^ m * exp (-1 / k) ^ m = 1 := by
    rw [← mul_pow, ← exp_add, neg_div, add_neg_cancel, exp_zero, one_pow]
  rw [hx3] at h
  calc |incr p m| = |incr p m| * exp (1 / k) ^ m * exp (-1 / k) ^ m := by
        rw [mul_assoc, hxm, mul_one]
    _ ≤ exp 3 * exp (-1 / k) ^ m := by gcongr

private theorem hasSum_series (hnn : ∀ n, 0 ≤ p n) (hle : ∀ n, p n ≤ 1) {x : ℝ}
    (hx : |x| < 1) : HasSum (fun n ↦ p n * x ^ n) (∑' n, p n * x ^ n) := by
  apply Summable.hasSum
  refine Summable.of_norm_bounded (summable_geometric_of_lt_one (abs_nonneg x) hx) fun n ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have : |p n| ≤ 1 := abs_le.mpr ⟨by linarith [hnn n], hle n⟩
  calc |p n| * |x| ^ n ≤ 1 * |x| ^ n := by gcongr
    _ = |x| ^ n := one_mul _

private theorem hasSum_incr_series (h0 : p 0 = 1) (hnn : ∀ n, 0 ≤ p n)
    (hle : ∀ n, p n ≤ 1) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n ↦ incr p n * x ^ n) ((1 - x) * ∑' n, p n * x ^ n) := by
  have hF := hasSum_series hnn hle hx
  apply (hasSum_nat_add_iff' 1).mp
  have h1 := (hasSum_nat_add_iff' 1).mpr hF
  convert h1.sub (hF.mul_left x) using 1
  · ext n; simp only [incr]; ring
  · simp [incr, h0]; ring

/-- The derivative series of `∑ a(n) x^n` is `-(1 - x^(k-1)) ∑ p(n) x^n`. -/
private theorem hasSum_incr_deriv (hk : 0 < k) (hnn : ∀ n, 0 ≤ p n) (hle : ∀ n, p n ≤ 1)
    (hrec : ∀ n : ℕ, n * p n = ∑ j ∈ range (n + 1 - k), p j) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n ↦ incr p n * (n * x ^ (n - 1)))
      (-(1 - x ^ (k - 1)) * ∑' n, p n * x ^ n) := by
  have hF := hasSum_series hnn hle hx
  have hS : HasSum (fun n ↦ (if k ≤ n + 1 then p (n + 1 - k) else 0) * x ^ n)
      (x ^ (k - 1) * ∑' n, p n * x ^ n) := by
    apply (hasSum_nat_add_iff' (k - 1)).mp
    have hz : (∑ i ∈ range (k - 1), (if k ≤ i + 1 then p (i + 1 - k) else 0) * x ^ i) =
        0 := by
      apply sum_eq_zero
      intro i hi
      simp only [mem_range] at hi
      rw [ite_eq_right (by omega), zero_mul]
    rw [hz, sub_zero]
    convert hF.mul_left (x ^ (k - 1)) using 1
    ext n
    rw [ite_eq_left (by omega), show n + (k - 1) + 1 - k = n by omega, pow_add]
    ring
  apply (hasSum_nat_add_iff' 1).mp
  convert hS.sub hF using 1
  · ext n
    have h := incr_succ hrec n
    rw [show n + 1 - 1 = n by omega]
    push_cast
    rw [← mul_assoc, mul_comm (incr p (n + 1)), h]
    ring
  · simp; ring

/-- Termwise differentiation of a power series with bounded coefficients. -/
private theorem hasDerivAt_series {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) {x : ℝ}
    (hx : |x| < 1) : HasDerivAt (fun y ↦ ∑' n, c n * y ^ n) (∑' n, c n * (n * x ^ (n - 1))) x := by
  obtain ⟨r, hxr, hr1⟩ := exists_between hx
  have hr0 : 0 < r := (abs_nonneg x).trans_lt hxr
  have hsum : Summable (fun n : ℕ ↦ (n : ℝ) * r ^ (n - 1)) := by
    have := (summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
      (by rwa [Real.norm_eq_abs, abs_of_pos hr0])).mul_left r⁻¹
    refine this.congr (fun n ↦ ?_)
    rcases n with _ | n
    · simp
    · rw [pow_one, pow_succ, show n + 1 - 1 = n by omega]
      field_simp
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-r) r →
      ‖c n * ((n : ℝ) * y ^ (n - 1))‖ ≤ (n : ℝ) * r ^ (n - 1) := by
    intro n y hy
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    have hy' : |y| ≤ r := abs_le.mpr ⟨hy.1.le, hy.2.le⟩
    calc |c n| * (n * |y| ^ (n - 1)) ≤ 1 * (n * r ^ (n - 1)) := by gcongr; exact hc n
      _ = _ := one_mul _
  have hs0 : Summable (fun n : ℕ ↦ c n * (0 : ℝ) ^ n) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    simp only [mem_singleton] at hn
    simp [hn]
  exact hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
    (g := fun n z ↦ c n * z ^ n) (g' := fun n y ↦ c n * ((n : ℝ) * y ^ (n - 1)))
    (u := fun n : ℕ ↦ (n : ℝ) * r ^ (n - 1)) (t := Set.Ioo (-r) r) (y₀ := 0) (y := x)
    hsum isOpen_Ioo isPreconnected_Ioo (fun n y _ ↦ (hasDerivAt_pow n y).const_mul (c n))
    hbound ⟨by linarith, hr0⟩ hs0
    ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

/-- The polynomial `∑_{j < k - 1} x^(j+1)/(j+1)`; its value at `1` is the harmonic number
`H_{k-1}`. -/
private noncomputable def poly (k : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (k - 1), x ^ (j + 1) / (j + 1)

private theorem hasDerivAt_poly (k : ℕ) (x : ℝ) :
    HasDerivAt (poly k) (∑ j ∈ range (k - 1), x ^ j) x := by
  unfold poly
  apply HasDerivAt.fun_sum
  intro j _
  convert (hasDerivAt_pow (j + 1) x).div_const ((j : ℝ) + 1) using 1
  push_cast
  field_simp

/-- On `(-1, 1)` the increments have generating function `exp (-poly k x)`: the product
`(∑ a(n) y^n) exp (poly k y)` has derivative zero. -/
private theorem incr_series_eq (hk : 0 < k) (h0 : p 0 = 1) (hnn : ∀ n, 0 ≤ p n)
    (hle : ∀ n, p n ≤ 1) (hrec : ∀ n : ℕ, n * p n = ∑ j ∈ range (n + 1 - k), p j)
    {x : ℝ} (hx : |x| < 1) :
    ∑' n, incr p n * x ^ n = exp (-poly k x) := by
  let G : ℝ → ℝ := fun y ↦ (∑' n, incr p n * y ^ n) * exp (poly k y)
  have hG : ∀ y ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt G 0 y := by
    intro y hy
    have hy' : |y| < 1 := abs_lt.mpr hy
    have h1 := hasDerivAt_series (abs_incr_le h0 hnn hle) hy'
    rw [(hasSum_incr_deriv hk hnn hle hrec hy').tsum_eq] at h1
    have h3 := h1.mul (hasDerivAt_poly k y).exp
    convert h3 using 1
    rw [(hasSum_incr_series h0 hnn hle hy').tsum_eq]
    have hgeom := mul_neg_geom_sum y (k - 1)
    linear_combination (-(∑' n, p n * y ^ n) * exp (poly k y)) * hgeom
  have hconst : G x = G 0 :=
    IsOpen.is_const_of_deriv_eq_zero isOpen_Ioo isPreconnected_Ioo
      (fun y hy ↦ (hG y hy).differentiableAt.differentiableWithinAt)
      (fun y hy ↦ (hG y hy).deriv) (abs_lt.mp hx) ⟨by norm_num, by norm_num⟩
  have hA0 : ∑' n, incr p n * (0 : ℝ) ^ n = 1 := by
    rw [tsum_eq_single 0 (fun n hn ↦ by simp [hn])]
    simp [incr, h0]
  have hP0 : poly k 0 = 0 := by simp [poly]
  simp only [G, hA0, hP0, exp_zero, mul_one] at hconst
  rw [exp_neg]
  exact eq_inv_of_mul_eq_one_left hconst

private theorem summable_abs_incr (hk : 0 < k) (h0 : p 0 = 1) (hnn : ∀ n, 0 ≤ p n)
    (hle : ∀ n, p n ≤ 1) (hrec : ∀ n : ℕ, n * p n = ∑ j ∈ range (n + 1 - k), p j) :
    Summable (fun m ↦ |incr p m|) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hr : exp (-1 / k) < 1 :=
    exp_lt_one_iff.mpr (by rw [neg_div]; exact neg_neg_of_pos (by positivity))
  refine Summable.of_nonneg_of_le (fun m ↦ abs_nonneg _) (incr_exp_bound hk h0 hnn hle hrec) ?_
  exact (summable_geometric_of_lt_one (exp_pos _).le hr).mul_left _

/-- Abel's limit theorem identifies the sum of the increments, the limit of `p`, with
`e^{-H_{k-1}}`. -/
private theorem hasSum_incr_limit (hk : 0 < k) (h0 : p 0 = 1) (hnn : ∀ n, 0 ≤ p n)
    (hle : ∀ n, p n ≤ 1) (hrec : ∀ n : ℕ, n * p n = ∑ j ∈ range (n + 1 - k), p j) :
    HasSum (incr p) (exp (-(harmonic (k - 1) : ℝ))) := by
  have hs : Summable (incr p) := (summable_abs_incr hk h0 hnn hle hrec).of_abs
  have hL := hs.hasSum
  have habel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hL.tendsto_sum_nat
  have hev : (fun x : ℝ ↦ ∑' n, incr p n * x ^ n) =ᶠ[𝓝[<] 1] fun x ↦ exp (-poly k x) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact incr_series_eq hk h0 hnn hle hrec (abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩)
  have hcont : Tendsto (fun x ↦ exp (-poly k x)) (𝓝[<] 1) (𝓝 (exp (-poly k 1))) := by
    have : Continuous (fun x ↦ exp (-poly k x)) := by unfold poly; fun_prop
    exact this.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have heq := tendsto_nhds_unique (habel.congr' hev) hcont
  have hP1 : poly k 1 = harmonic (k - 1) := by
    simp [poly, harmonic]
  rw [heq, hP1] at hL
  exact hL

/-- The rate of convergence of `p(n)` to `e^{-H_{k-1}}`, uniform in `k`. -/
private theorem limit_rate (hk : 0 < k) (h0 : p 0 = 1) (hnn : ∀ n, 0 ≤ p n)
    (hle : ∀ n, p n ≤ 1) (hrec : ∀ n : ℕ, n * p n = ∑ j ∈ range (n + 1 - k), p j) (n : ℕ) :
    |p n - exp (-(harmonic (k - 1) : ℝ))| ≤ exp 3 * k * exp (-(n / k : ℝ)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hL := hasSum_incr_limit hk h0 hnn hle hrec
  have hsplit := hL.summable.sum_add_tsum_nat_add (n + 1)
  rw [hL.tsum_eq, sum_incr] at hsplit
  set r := exp (-1 / k) with hr
  have hr0 : 0 ≤ r := (exp_pos _).le
  have hr1 : r < 1 :=
    exp_lt_one_iff.mpr (by rw [neg_div]; exact neg_neg_of_pos (by positivity))
  have hb := incr_exp_bound hk h0 hnn hle hrec
  have habs : Summable (fun i ↦ |incr p (i + (n + 1))|) :=
    (summable_nat_add_iff (n + 1)).mpr (summable_abs_incr hk h0 hnn hle hrec)
  have hgeo : Summable (fun i : ℕ ↦ exp 3 * r ^ (i + (n + 1))) := by
    simp_rw [pow_add]
    exact ((summable_geometric_of_lt_one hr0 hr1).mul_right _).mul_left _
  have h1 : |p n - exp (-(harmonic (k - 1) : ℝ))| = |∑' i, incr p (i + (n + 1))| := by
    rw [← hsplit, sub_add_cancel_left, abs_neg]
  rw [h1]
  have hrn : r ^ n = exp (-(n / k : ℝ)) := by
    rw [hr, ← exp_nat_mul]; congr 1; ring
  have hkey : r * (1 - r)⁻¹ ≤ k := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
    have h2 : r * exp (1 / k) = 1 := by rw [hr, ← exp_add, neg_div, neg_add_cancel, exp_zero]
    have h3 : r * (1 + 1 / k) ≤ 1 := by
      calc r * (1 + 1 / k) ≤ r * exp (1 / k) := by
            gcongr; linarith [add_one_le_exp (1 / (k : ℝ))]
        _ = 1 := h2
    have h4 : r * (k + 1) = k * (r * (1 + 1 / k)) := by field_simp
    nlinarith
  have habs' : Summable (fun i ↦ ‖incr p (i + (n + 1))‖) := by
    simpa only [Real.norm_eq_abs] using habs
  calc |∑' i, incr p (i + (n + 1))| ≤ ∑' i, |incr p (i + (n + 1))| := by
        have := norm_tsum_le_tsum_norm (f := fun i ↦ incr p (i + (n + 1))) habs'
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' i, exp 3 * r ^ (i + (n + 1)) :=
        habs.tsum_le_tsum (fun i ↦ hb (i + (n + 1))) hgeo
    _ = exp 3 * r ^ (n + 1) * (1 - r)⁻¹ := by
        simp_rw [pow_add]
        rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1]; ring
    _ = exp 3 * r ^ n * (r * (1 - r)⁻¹) := by ring
    _ ≤ exp 3 * r ^ n * k := by gcongr
    _ = exp 3 * k * exp (-(n / k : ℝ)) := by rw [hrn]; ring

/-- The asymptotic for any family `P k n` with the properties of the tail probabilities: the mean
`∑_{k ≤ n} P k n` differs from `∑_{k ≤ n} e^{-H_{k-1}}` by `O(log log n)`. -/
private theorem mean_asymp_of_tails (P : ℕ → ℕ → ℝ) (E : ℕ → ℝ)
    (hE : ∀ n, 1 ≤ n → E n = ∑ j ∈ range n, P (j + 1) n)
    (h0 : ∀ k, 0 < k → P k 0 = 1)
    (hnn : ∀ k n, 0 < k → 0 ≤ P k n) (hle : ∀ k n, 0 < k → P k n ≤ 1)
    (hbd : ∀ k n, 0 < k → k ≤ n → P k n ≤ 1 / k)
    (hrec : ∀ k n : ℕ, 0 < k → (n : ℝ) * P k n = ∑ j ∈ range (n + 1 - k), P k j) :
    Tendsto (fun n ↦ E n / (exp (-eulerMascheroniConstant) * log n)) atTop (𝓝 1) := by
  set c := exp (-eulerMascheroniConstant) with hc
  have hc0 : 0 < c := exp_pos _
  have hlog : Tendsto (fun n : ℕ ↦ log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- Two bounds for each term.
  have hterm : ∀ n j, j < n → |P (j + 1) n - exp (-(harmonic j : ℝ))| ≤
      min (exp 3 * (j + 1) * exp (-(n / (j + 1) : ℝ))) (1 / (j + 1)) := by
    intro n j hj
    have hj1 : 0 < j + 1 := Nat.succ_pos j
    apply le_min
    · have := limit_rate (k := j + 1) (p := P (j + 1)) hj1 (h0 _ hj1)
        (fun m ↦ hnn _ m hj1) (fun m ↦ hle _ m hj1) (fun m ↦ hrec _ m hj1) n
      simpa using this
    · have hb := hbd (j + 1) n hj1 hj
      have hp := hnn (j + 1) n hj1
      have he : exp (-(harmonic j : ℝ)) ≤ 1 / (j + 1) := by
        rw [exp_neg, one_div]
        apply inv_anti₀ (by positivity)
        have := log_add_one_le_harmonic j
        push_cast at this
        calc ((j : ℝ) + 1) = exp (log (j + 1)) := (exp_log (by positivity)).symm
          _ ≤ exp (harmonic j) := exp_le_exp.mpr this
      have he0 : 0 < exp (-(harmonic j : ℝ)) := exp_pos _
      push_cast at hb
      rw [abs_le]; constructor <;> linarith
  -- The error bound, splitting at `n / (3 log n)`.
  have herr : ∀ n : ℕ, 3 ≤ n → |E n - ∑ j ∈ range n, exp (-(harmonic j : ℝ))| ≤
      exp 3 + 1 + log 3 + log (log n) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by positivity
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hlogn : 1 ≤ log (n : ℝ) := by
      rw [le_log_iff_exp_le hn0]; linarith [exp_one_lt_d9]
    set K : ℝ := n / (3 * log n) with hK
    have hK0 : 0 < K := by positivity
    have hKn : K ≤ n := by
      rw [hK, div_le_iff₀ (by positivity)]; nlinarith
    set M := ⌊K⌋₊ with hM
    have hMK' : (M : ℝ) ≤ K := Nat.floor_le hK0.le
    have hMn : M ≤ n := by exact_mod_cast hMK'.trans hKn
    have hMK : K < M + 1 := Nat.lt_floor_add_one K
    have hbound : ∀ j ∈ range n, |P (j + 1) n - exp (-(harmonic j : ℝ))| ≤
        exp 3 / (n : ℝ) ^ 2 + if M ≤ j then 1 / ((j : ℝ) + 1) else 0 := by
      intro j hj
      rw [mem_range] at hj
      have ht := hterm n j hj
      split_ifs with hjM
      · have := ht.trans (min_le_right _ _)
        linarith [show 0 ≤ exp 3 / (n : ℝ) ^ 2 by positivity]
      · have hj1 : ((j : ℝ) + 1) ≤ K := by
          have : ((j + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast (by omega : j + 1 ≤ M)
          push_cast at this
          linarith
        have hj0 : (0 : ℝ) < j + 1 := by positivity
        have hexp : exp (-(n / (j + 1) : ℝ)) ≤ 1 / (n : ℝ) ^ 3 := by
          have h1 : 3 * log n ≤ n / (j + 1) := by
            rw [le_div_iff₀ hj0]
            calc 3 * log n * (j + 1) ≤ 3 * log n * K := by gcongr
              _ = n := by rw [hK]; field_simp
          calc exp (-(n / (j + 1) : ℝ)) ≤ exp (-(3 * log n)) := exp_le_exp.mpr (by linarith)
            _ = 1 / (n : ℝ) ^ 3 := by
              rw [exp_neg, show 3 * log (n : ℝ) = log ((n : ℝ) ^ 3) by
                  rw [log_pow]; push_cast; ring, exp_log (by positivity), one_div]
        have hjn : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
        calc |P (j + 1) n - exp (-(harmonic j : ℝ))|
            ≤ exp 3 * (j + 1) * exp (-(n / (j + 1) : ℝ)) := ht.trans (min_le_left _ _)
          _ ≤ exp 3 * n * (1 / (n : ℝ) ^ 3) := by gcongr
          _ = exp 3 / (n : ℝ) ^ 2 + 0 := by field_simp; ring
    have hH : ∀ m, (harmonic m : ℝ) = ∑ j ∈ range m, 1 / ((j : ℝ) + 1) := by
      intro m; simp [harmonic]
    have hsum_ite : ∑ j ∈ range n, (if M ≤ j then 1 / ((j : ℝ) + 1) else 0) =
        (harmonic n : ℝ) - harmonic M := by
      rw [hH, hH, ← sum_range_add_sum_Ico _ hMn, ← sum_range_add_sum_Ico _ hMn]
      have h1 : ∑ j ∈ range M, (if M ≤ j then 1 / ((j : ℝ) + 1) else 0) = 0 :=
        sum_eq_zero (fun j hj ↦ ite_eq_right (by rw [mem_range] at hj; omega))
      have h2 : ∑ j ∈ Ico M n, (if M ≤ j then 1 / ((j : ℝ) + 1) else 0) =
          ∑ j ∈ Ico M n, 1 / ((j : ℝ) + 1) :=
        sum_congr rfl (fun j hj ↦ ite_eq_left (mem_Ico.mp hj).1)
      rw [h1, h2]
      ring
    have hHn := harmonic_le_one_add_log n
    have hHM := log_add_one_le_harmonic M
    have hlogM : log K ≤ log ((M + 1 : ℕ) : ℝ) := by
      apply log_le_log hK0; push_cast; linarith
    have hlogK : log K = log n - log 3 - log (log n) := by
      rw [hK, log_div (by positivity) (by positivity), log_mul (by norm_num) (by positivity)]
      ring
    calc |E n - ∑ j ∈ range n, exp (-(harmonic j : ℝ))|
        = |∑ j ∈ range n, (P (j + 1) n - exp (-(harmonic j : ℝ)))| := by
          rw [hE n (by omega), sum_sub_distrib]
      _ ≤ ∑ j ∈ range n, |P (j + 1) n - exp (-(harmonic j : ℝ))| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range n,
            (exp 3 / (n : ℝ) ^ 2 + if M ≤ j then 1 / ((j : ℝ) + 1) else 0) :=
          sum_le_sum hbound
      _ = exp 3 / n + ((harmonic n : ℝ) - harmonic M) := by
          rw [sum_add_distrib, hsum_ite, sum_const, card_range, nsmul_eq_mul]
          field_simp
      _ ≤ exp 3 + 1 + log 3 + log (log n) := by
          have : exp 3 / n ≤ exp 3 := div_le_self (exp_pos _).le (by linarith)
          linarith
  -- The error is `o(log n)`.
  have hi : (fun n : ℕ ↦ E n - ∑ j ∈ range n, exp (-(harmonic j : ℝ))) =o[atTop]
      (fun n : ℕ ↦ log (n : ℝ)) := by
    have hB : (fun n : ℕ ↦ exp 3 + 1 + log 3 + log (log (n : ℝ))) =o[atTop]
        (fun n : ℕ ↦ log (n : ℝ)) := by
      have h1 : (fun _ : ℕ ↦ exp 3 + 1 + log 3) =o[atTop] (fun n : ℕ ↦ log (n : ℝ)) :=
        isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp hlog))
      have h2 : (fun n : ℕ ↦ log (log (n : ℝ))) =o[atTop] (fun n : ℕ ↦ log (n : ℝ)) :=
        isLittleO_log_id_atTop.comp_tendsto hlog
      exact h1.add h2
    refine IsBigO.trans_isLittleO ?_ hB
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 3] with n hn
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (herr n hn).trans (le_abs_self _)
  -- `∑ exp (-H_j)` is asymptotic to `e^{-γ} H_n`.
  have hii : (fun n : ℕ ↦ ∑ j ∈ range n, exp (-(harmonic j : ℝ)) - c * harmonic n)
      =o[atTop] (fun n : ℕ ↦ (harmonic n : ℝ)) := by
    have hratio : Tendsto (fun j : ℕ ↦ ((j : ℝ) + 1) * exp (-(harmonic j : ℝ)) - c)
        atTop (𝓝 0) := by
      have h := (continuous_exp.tendsto _).comp (Real.tendsto_harmonic_sub_log_add_one.neg)
      rw [← sub_self c]
      apply Tendsto.sub_const
      refine h.congr (fun j ↦ ?_)
      simp only [Function.comp_apply]
      rw [neg_sub, exp_sub, exp_log (by positivity), exp_neg, div_eq_mul_inv]
    have hf : (fun j : ℕ ↦ exp (-(harmonic j : ℝ)) - c * (1 / ((j : ℝ) + 1))) =o[atTop]
        (fun j : ℕ ↦ 1 / ((j : ℝ) + 1)) := by
      have := ((isLittleO_one_iff ℝ).mpr hratio).mul_isBigO
        (isBigO_refl (fun j : ℕ ↦ 1 / ((j : ℝ) + 1)) atTop)
      refine this.congr' ?_ ?_
      · filter_upwards with j
        field_simp
      · filter_upwards with j
        simp
    have hH : ∀ m, (harmonic m : ℝ) = ∑ j ∈ range m, 1 / ((j : ℝ) + 1) := by
      intro m; simp [harmonic]
    have htend : Tendsto (fun n ↦ ∑ i ∈ range n, 1 / ((i : ℝ) + 1)) atTop atTop := by
      refine tendsto_atTop_mono (fun n ↦ ?_)
        (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))
      rw [← hH]
      exact log_add_one_le_harmonic n
    have hs := hf.sum_range (fun j ↦ by positivity) htend
    refine hs.congr' ?_ ?_
    · filter_upwards with n
      rw [sum_sub_distrib, ← mul_sum, hH]
    · filter_upwards with n
      rw [hH]
  -- `H_n` is asymptotic to `log n`.
  have hiii : (fun n : ℕ ↦ (harmonic n : ℝ) - log n) =o[atTop]
      (fun n : ℕ ↦ log (n : ℝ)) :=
    (Real.tendsto_harmonic_sub_log.isBigO_one ℝ).trans_isLittleO
      ((isLittleO_one_left_iff ℝ).mpr (tendsto_norm_atTop_atTop.comp hlog))
  have hHO : (fun n : ℕ ↦ (harmonic n : ℝ)) =O[atTop] (fun n : ℕ ↦ log (n : ℝ)) := by
    have := hiii.isBigO.add (isBigO_refl (fun n : ℕ ↦ log (n : ℝ)) atTop)
    exact this.congr_left (fun n ↦ by ring)
  have hiv : (fun n : ℕ ↦ E n - c * log n) =o[atTop] (fun n : ℕ ↦ log (n : ℝ)) := by
    have := (hi.add (hii.trans_isBigO hHO)).add (hiii.const_mul_left c)
    exact this.congr_left (fun n ↦ by ring)
  have hdiv := hiv.tendsto_div_nhds_zero
  have hlim : Tendsto (fun n : ℕ ↦ 1 + ((E n - c * log n) / log n) / c) atTop
      (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hdiv.div_const c)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlogpos : 0 < log (n : ℝ) := log_pos (by exact_mod_cast hn)
  field_simp
  ring

/-! ### The tail probabilities of the smallest cycle -/

/-- The tail recurrence `n p(n) = ∑_{j ≤ n - k} p(j)`, read off from `tail_rec`. -/
private theorem tail_rec_range (k n : ℕ) (hk : 0 < k) :
    (n : ℝ) * tail k n = ∑ j ∈ range (n + 1 - k), tail k j := by
  have h := sum_range_reflect (fun d ↦ if k ≤ d then tail k (n - d) else 0) (n + 1)
  rw [tail_rec k n hk, ← h, ← sum_range_add_sum_Ico _ (Nat.sub_le (n + 1) k)]
  rw [sum_eq_zero (s := Ico (n + 1 - k) (n + 1)) (fun j hj ↦ ?_), add_zero]
  · refine sum_congr rfl (fun j hj ↦ ?_)
    rw [mem_range] at hj
    rw [ite_eq_left (by omega)]
    congr 1
    omega
  · rw [mem_Ico] at hj
    exact ite_eq_right (by omega)

private theorem tail_nonneg (k n : ℕ) : 0 ≤ tail k n := by
  unfold tail
  positivity

private theorem tail_le_one (k n : ℕ) (hk : 0 < k) : tail k n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [tail_zero]
  by_cases hkn : k ≤ n
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact (tail_bound k n hk hkn).trans (by rw [div_le_one (by positivity)]; exact hk')
  · rw [tail_lt k n hn (by omega)]
    norm_num

/-- The mean of the smallest cycle length is the sum of the tail probabilities. -/
private theorem mean_eq_sum_tail (n : ℕ) (hn : 1 ≤ n) :
    (∑ σ : Perm (Fin n), ((⨅ x, minimalPeriod σ x : ℕ) : ℝ)) / (n.factorial : ℝ) =
      ∑ j ∈ range n, tail (j + 1) n := by
  classical
  have hX (σ : Perm (Fin n)) : ((⨅ x, minimalPeriod σ x : ℕ) : ℝ) =
      ∑ j ∈ range n, if HasLongCycles (j + 1) σ then (1 : ℝ) else 0 := by
    have h1 : 1 ≤ ⨅ x, minimalPeriod σ x := (long_iff hn σ).mp fun x ↦
      minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts x)
    have h2 : ⨅ x, minimalPeriod σ x ≤ n :=
      (ciInf_le (OrderBot.bddBelow _) (⟨0, hn⟩ : Fin n)).trans (by
        simpa using (minimalPeriod_le_card (f := (σ : _ → _)) (x := (⟨0, hn⟩ : Fin n))))
    have hc (j : ℕ) : (if HasLongCycles (j + 1) σ then (1 : ℝ) else 0) =
        if j + 1 ≤ ⨅ x, minimalPeriod σ x then 1 else 0 := by
      by_cases h : j + 1 ≤ ⨅ x, minimalPeriod σ x
      · rw [ite_eq_left ((long_iff hn σ).mpr h), ite_eq_left h]
      · rw [ite_eq_right (fun h' ↦ h ((long_iff hn σ).mp h')), ite_eq_right h]
    rw [sum_congr rfl fun j _ ↦ hc j, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have hf : (range n).filter (fun j ↦ j + 1 ≤ ⨅ x, minimalPeriod σ x) =
        range (⨅ x, minimalPeriod σ x) := by
      ext j
      simp only [mem_filter, mem_range]
      omega
    rw [hf, card_range]
  simp_rw [hX]
  rw [sum_comm, sum_div]
  refine sum_congr rfl fun j _ ↦ ?_
  simp [tail, countLong, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The mean smallest cycle length, with `e^{-γ} log n` in the denominator. -/
private theorem mean_tendsto :
    Tendsto (fun n : ℕ ↦
      ((∑ σ : Perm (Fin n), ((⨅ x, minimalPeriod σ x : ℕ) : ℝ)) /
          (n.factorial : ℝ)) / (exp (-eulerMascheroniConstant) * log n)) atTop (𝓝 1) :=
  mean_asymp_of_tails (fun k n ↦ tail k n) _ mean_eq_sum_tail (fun k _ ↦ tail_zero k)
    (fun k n _ ↦ tail_nonneg k n) (fun k n hk ↦ tail_le_one k n hk)
    (fun k n hk hkn ↦ tail_bound k n hk hkn) (fun k n hk ↦ tail_rec_range k n hk)

end MetaMathlibExt.smallest_cycle_mean_asymp

namespace MetaMathlibExt
open smallest_cycle_mean_asymp

open Real

/-- **Mean length of the smallest cycle of a random permutation.** For $n \ge 1$ let $X_n$ be the
length of the smallest cycle of a uniformly random permutation of $\{1, \dots, n\}$. Then
$\mathbb{E}(X_n) / (e^{-\gamma} \log n) \to 1$ as $n \to \infty$, where $\gamma$ is the
Euler–Mascheroni constant.

The paper states this as $\mathbb{E}(X_n) = e^{-\gamma} \log n \, (1 + O(h(n)/\log n))$ for some
$h(n) = o(\log n)$, which is equivalent.

Source: Claude Gravel and Daniel Panario, *Evaluating the Generalized Buchstab
Function and Revisiting the Variance of the Distribution of the Smallest
Components of Combinatorial Objects*, INTEGERS 24 (2024), Article A7, Theorem 1
(`integers-2024-A7-thm-1`). -/
public theorem smallest_cycle_mean_asymp :
    Filter.Tendsto (fun n : ℕ =>
      ((∑ σ : Equiv.Perm (Fin n), ((⨅ x, Function.minimalPeriod σ x : ℕ) : ℝ)) /
          (n.factorial : ℝ)) / (Real.exp (-eulerMascheroniConstant) * Real.log n))
      Filter.atTop (nhds 1) :=
  mean_tendsto

end MetaMathlibExt
