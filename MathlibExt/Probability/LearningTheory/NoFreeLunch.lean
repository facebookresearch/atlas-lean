/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # No free lunch: averaging over targets on a finite domain

A learner `L` maps a labelled sample to a hypothesis `X → Bool`. Fix `m` distinct sample points
`x` in a finite domain `X`; `sampleOf x f` labels them with the target `f`, and
`errCount x f h` counts the points outside the sample where `h` disagrees with `f`. This is
the finite-domain core of roadmap package ML-05 of the Atlas TCS canon roadmap.

* `nfl_average`: summed over all `2 ^ card X` targets, the learner trained on `sampleOf x f`
  errs on exactly half of the (target, unseen point) pairs. This is the averaging step in the
  proof of the No-Free-Lunch theorem below: the targets are paired so that the two targets of a
  pair differ only at one unseen point `v`, the learner sees the same sample for both, and so it
  errs at `v` on exactly one of them.
* `nfl_tail`: if `card X = 2 * m`, then for at least a `1/7` fraction of the targets the learner
  errs on more than a `1/8` fraction of the domain outside its sample.

The No-Free-Lunch theorem (Theorem 5.1 in the source) uses the same constants on a different
probability space. There the learner is given `m < |X| / 2` training points, the proof works on
a `2m`-point subset `C` of the domain, the target is a fixed worst case, the sample is drawn
i.i.d. from the uniform distribution on `C` labelled by that target, and the conclusion is that
the true error is at least `1/8` with probability at least `1/7` over the sample. Here the domain
plays the role of `C`, the `m` sample points are fixed and distinct, the probability is over a
uniformly random target, and the error counts only unseen points, divided by `2m`, which is at
most the true error under the uniform distribution on `X`. The threshold `1/8` is strict here,
a smaller event than the theorem's `≥ 1/8`, so the bound on the number of targets is slightly
stronger.

Source: Shalev-Shwartz and Ben-David, Understanding Machine Learning (2014), Section 5.1,
Theorem 5.1 (No-Free-Lunch) and its proof.
-/

variable {X : Type*} [Fintype X] [DecidableEq X] {m : ℕ}

@[expose] public section

open Finset

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {m : ℕ}

/-- The sample obtained by labelling the inputs `x` with
the target `f`. -/
def sampleOf (x : Fin m → X) (f : X → Bool) : Fin m → X × Bool :=
  fun i => (x i, f (x i))

/-- The number of points outside the sample where the
hypothesis `h` disagrees with the target `f`. -/
def errCount (x : Fin m → X) (f : X → Bool) (h : X → Bool) : ℕ :=
  (Finset.univ.filter
    (fun t => t ∉ Set.range x ∧ h t ≠ f t)).card

/-- No-free-lunch, averaging form: summed over all targets,
the number of errors a learner makes outside its sample is
exactly half of all (target, unseen point) pairs. -/
theorem nfl_average (L : (Fin m → X × Bool) → X → Bool)
    (x : Fin m → X) (hx : Function.Injective x) :
    (∑ f : X → Bool, errCount x f (L (sampleOf x f)))
      = (Fintype.card X - m) * 2 ^ (Fintype.card X - 1) := by
  have hcard_fun : Fintype.card (X → Bool) = 2 ^ Fintype.card X := by
    rw [Fintype.card_pi]
    simp [Fintype.card_bool, Finset.prod_const, Finset.card_univ]
  have hinner : ∀ t : X, t ∉ Set.range x →
      (∑ f : X → Bool, (if L (sampleOf x f) t ≠ f t then (1 : ℕ) else 0))
        = 2 ^ (Fintype.card X - 1) := by
    intro t ht
    set flip : (X → Bool) → (X → Bool) := fun f => Function.update f t (!f t) with hflip
    have hinv : Function.Involutive flip := by
      intro f
      funext s
      by_cases hs : s = t
      · subst hs
        simp [hflip, Function.update_self]
      · simp [hflip, Function.update_of_ne hs]
    have hsample : ∀ f : X → Bool, sampleOf x (flip f) = sampleOf x f := by
      intro f
      funext i
      simp only [sampleOf, hflip]
      have hxi : x i ≠ t := fun h => ht ⟨i, h⟩
      rw [Function.update_of_ne hxi]
    have hpair : ∀ f : X → Bool,
        (if L (sampleOf x f) t ≠ f t then (1 : ℕ) else 0) +
        (if L (sampleOf x (flip f)) t ≠ (flip f) t then (1 : ℕ) else 0) = 1 := by
      intro f
      have h1 : L (sampleOf x (flip f)) t = L (sampleOf x f) t := by rw [hsample]
      have h2 : (flip f) t = !(f t) := by simp [hflip, Function.update_self]
      rw [h1, h2]
      cases L (sampleOf x f) t <;> cases f t <;> simp
    have hsum_pair : (∑ f : X → Bool, ((if L (sampleOf x f) t ≠ f t then (1 : ℕ) else 0) +
        (if L (sampleOf x (flip f)) t ≠ (flip f) t then (1 : ℕ) else 0))) = Fintype.card (X → Bool) := by
      simp only [hpair]
      simp [Finset.sum_const, Finset.card_univ]
    have hsum_split : (∑ f : X → Bool, ((if L (sampleOf x f) t ≠ f t then (1 : ℕ) else 0) +
        (if L (sampleOf x (flip f)) t ≠ (flip f) t then (1 : ℕ) else 0)))
        = (∑ f : X → Bool, (if L (sampleOf x f) t ≠ f t then (1 : ℕ) else 0)) +
          (∑ f : X → Bool, (if L (sampleOf x (flip f)) t ≠ (flip f) t then (1 : ℕ) else 0)) := by
      rw [Finset.sum_add_distrib]
    have hbij : (∑ f : X → Bool, (if L (sampleOf x (flip f)) t ≠ (flip f) t then (1 : ℕ) else 0))
        = (∑ f : X → Bool, (if L (sampleOf x f) t ≠ f t then (1 : ℕ) else 0)) := by
      let E := hinv.toPerm
      have hcomp := Equiv.sum_comp E (fun f : X → Bool => (if L (sampleOf x f) t ≠ f t then (1 : ℕ) else 0))
      have hcoe : ⇑E = flip := Function.Involutive.coe_toPerm hinv
      rw [hcoe] at hcomp
      exact hcomp
    have h2S : 2 * (∑ f : X → Bool, (if L (sampleOf x f) t ≠ f t then (1 : ℕ) else 0)) = 2 ^ Fintype.card X := by
      have h := hsum_pair
      rw [hsum_split, hbij, hcard_fun] at h
      omega
    have hpos : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨t⟩
    have hpow : (2 : ℕ) ^ Fintype.card X = 2 * 2 ^ (Fintype.card X - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hpos, pow_succ']
    have hcancel : 2 * (∑ f : X → Bool, (if L (sampleOf x f) t ≠ f t then (1 : ℕ) else 0))
        = 2 * 2 ^ (Fintype.card X - 1) := by rw [h2S, hpow]
    exact Nat.mul_left_cancel (by norm_num : 0 < 2) hcancel
  have herr : ∀ f : X → Bool, errCount x f (L (sampleOf x f))
      = ∑ t : X, (if t ∉ Set.range x ∧ L (sampleOf x f) t ≠ f t then (1 : ℕ) else 0) := by
    intro f
    unfold errCount
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hper : ∀ t : X, (∑ f : X → Bool, (if t ∉ Set.range x ∧ L (sampleOf x f) t ≠ f t then (1 : ℕ) else 0))
      = (if t ∉ Set.range x then 2 ^ (Fintype.card X - 1) else 0) := by
    intro t
    by_cases ht : t ∉ Set.range x
    · simp only [ht, not_false_eq_true, true_and, ite_true, hinner t ht]
    · simp only [ht, false_and, ite_false, Finset.sum_const_zero]
  have hcount : (Finset.univ.filter (fun t : X => t ∉ Set.range x)).card = Fintype.card X - m := by
    let s : Finset X := Finset.univ.map ⟨x, hx⟩
    have hs_card : s.card = m := by
      simp [s, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    have hmem : ∀ t : X, t ∈ s ↔ t ∈ Set.range x := by
      intro t
      simp [s, Finset.mem_map, Set.mem_range]
    have hfilter : Finset.univ.filter (fun t : X => t ∉ Set.range x) = Finset.univ \ s := by
      ext t
      simp [hmem t]
    rw [hfilter, Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ, hs_card]
  simp only [herr]
  rw [Finset.sum_comm]
  simp only [hper]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, hcount, nsmul_eq_mul]
  simp

/-- No-free-lunch, tail form: if the domain has `2m` points,
then for at least a `1/7` fraction of all targets the learner
errs on more than a `1/8` fraction of the domain (counted
against all `2m` points) outside its `m`-point sample. -/
theorem nfl_tail (L : (Fin m → X × Bool) → X → Bool)
    (x : Fin m → X) (hx : Function.Injective x)
    (hX : Fintype.card X = 2 * m) (hm : 0 < m) :
    ((Finset.univ.filter
      (fun f : X → Bool =>
        (1 / 8 : ℝ) < (errCount x f (L (sampleOf x f)) : ℝ)
          / (Fintype.card X : ℝ))).card : ℝ)
      ≥ (1 / 7) * 2 ^ (Fintype.card X) := by
  have h_avg : (∑ f : X → Bool, errCount x f (L (sampleOf x f)))
      = (Fintype.card X - m) * 2 ^ (Fintype.card X - 1) :=
    nfl_average L x hx
  have hcard_fun : Fintype.card (X → Bool) = 2 ^ Fintype.card X := by
    rw [Fintype.card_pi]
    simp [Fintype.card_bool, Finset.prod_const, Finset.card_univ]
  have hcount : (Finset.univ.filter (fun t : X => t ∉ Set.range x)).card = Fintype.card X - m := by
    let s : Finset X := Finset.univ.map ⟨x, hx⟩
    have hs_card : s.card = m := by
      simp [s, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    have hmem : ∀ t : X, t ∈ s ↔ t ∈ Set.range x := by
      intro t
      simp [s, Finset.mem_map, Set.mem_range]
    have hfilter : Finset.univ.filter (fun t : X => t ∉ Set.range x) = Finset.univ \ s := by
      ext t
      simp [hmem t]
    rw [hfilter, Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ, hs_card]
  have hle : ∀ f : X → Bool, errCount x f (L (sampleOf x f)) ≤ Fintype.card X - m := by
    intro f
    unfold errCount
    rw [← hcount]
    apply Finset.card_le_card
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact ht.1
  have hNpos : 0 < Fintype.card X := by omega
  have hNposR : (0 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast hNpos
  have hmposR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hNm : Fintype.card X - m = m := by omega
  set p : (X → Bool) → Prop := fun f => (1 / 8 : ℝ) < (errCount x f (L (sampleOf x f)) : ℝ) / (Fintype.card X : ℝ) with hp
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ p (fun f : X → Bool => ((errCount x f (L (sampleOf x f)) : ℕ) : ℝ))
  have htotalR : (∑ f : X → Bool, ((errCount x f (L (sampleOf x f)) : ℕ) : ℝ))
      = ((((Fintype.card X - m) * 2 ^ (Fintype.card X - 1) : ℕ)) : ℝ) := by
    rw [← Nat.cast_sum, h_avg]
  have hSbound : ∀ f ∈ Finset.univ.filter p, ((errCount x f (L (sampleOf x f)) : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro f hf
    have h := hle f
    have hc : ((errCount x f (L (sampleOf x f)) : ℕ) : ℝ) ≤ (((Fintype.card X - m : ℕ)) : ℝ) := by exact_mod_cast h
    rw [hNm] at hc
    exact hc
  have hSsum : (∑ f ∈ Finset.univ.filter p, ((errCount x f (L (sampleOf x f)) : ℕ) : ℝ))
      ≤ ((Finset.univ.filter p).card : ℝ) * (m : ℝ) := by
    have h := Finset.sum_le_card_nsmul (Finset.univ.filter p) (fun f : X → Bool => ((errCount x f (L (sampleOf x f)) : ℕ) : ℝ)) (m : ℝ) hSbound
    rw [nsmul_eq_mul] at h
    exact h
  have hTbound : ∀ f ∈ Finset.univ.filter (fun f => ¬ p f), ((errCount x f (L (sampleOf x f)) : ℕ) : ℝ) ≤ (Fintype.card X : ℝ) / 8 := by
    intro f hf
    have hnp : ¬ p f := (Finset.mem_filter.mp hf).2
    simp only [hp] at hnp
    have hle8 : ((errCount x f (L (sampleOf x f)) : ℕ) : ℝ) / (Fintype.card X : ℝ) ≤ 1 / 8 := not_lt.mp hnp
    have hmul : ((errCount x f (L (sampleOf x f)) : ℕ) : ℝ) ≤ (1 / 8) * (Fintype.card X : ℝ) := (div_le_iff₀ hNposR).mp hle8
    have heq : (1 / 8 : ℝ) * (Fintype.card X : ℝ) = (Fintype.card X : ℝ) / 8 := by ring
    rw [heq] at hmul
    exact hmul
  have hTsum1 : (∑ f ∈ Finset.univ.filter (fun f => ¬ p f), ((errCount x f (L (sampleOf x f)) : ℕ) : ℝ))
      ≤ ((Finset.univ.filter (fun f => ¬ p f)).card : ℝ) * ((Fintype.card X : ℝ) / 8) := by
    have h := Finset.sum_le_card_nsmul (Finset.univ.filter (fun f => ¬ p f)) (fun f : X → Bool => ((errCount x f (L (sampleOf x f)) : ℕ) : ℝ)) ((Fintype.card X : ℝ) / 8) hTbound
    rw [nsmul_eq_mul] at h
    exact h
  have hTcard_le : (Finset.univ.filter (fun f : X → Bool => ¬ p f)).card ≤ 2 ^ Fintype.card X := by
    have h1 : (Finset.univ.filter (fun f : X → Bool => ¬ p f)).card ≤ Finset.univ.card := Finset.card_filter_le Finset.univ _
    rw [Finset.card_univ, hcard_fun] at h1
    exact h1
  have hTsum : (∑ f ∈ Finset.univ.filter (fun f => ¬ p f), ((errCount x f (L (sampleOf x f)) : ℕ) : ℝ))
      ≤ (((2 ^ Fintype.card X : ℕ)) : ℝ) * ((Fintype.card X : ℝ) / 8) := by
    have hnonneg : (0 : ℝ) ≤ (Fintype.card X : ℝ) / 8 := by positivity
    have hleR : (((Finset.univ.filter (fun f => ¬ p f)).card : ℕ) : ℝ) ≤ (((2 ^ Fintype.card X : ℕ)) : ℝ) := by exact_mod_cast hTcard_le
    exact le_trans hTsum1 (mul_le_mul_of_nonneg_right hleR hnonneg)
  have hcomb : ((((Fintype.card X - m) * 2 ^ (Fintype.card X - 1) : ℕ)) : ℝ)
      ≤ ((Finset.univ.filter p).card : ℝ) * (m : ℝ) + (((2 ^ Fintype.card X : ℕ)) : ℝ) * ((Fintype.card X : ℝ) / 8) := by
    have h := hsplit
    rw [htotalR] at h
    have hle_add : (∑ f ∈ Finset.univ.filter p, ((errCount x f (L (sampleOf x f)) : ℕ) : ℝ)) + (∑ f ∈ Finset.univ.filter (fun f => ¬ p f), ((errCount x f (L (sampleOf x f)) : ℕ) : ℝ))
        ≤ ((Finset.univ.filter p).card : ℝ) * (m : ℝ) + (((2 ^ Fintype.card X : ℕ)) : ℝ) * ((Fintype.card X : ℝ) / 8) := add_le_add hSsum hTsum
    rw [h] at hle_add
    exact hle_add
  have hpowNat : (2 : ℕ) ^ Fintype.card X = 2 * 2 ^ (Fintype.card X - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hNpos, pow_succ']
  have hXr : (Fintype.card X : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hX
  have hLHS : ((((Fintype.card X - m) * 2 ^ (Fintype.card X - 1) : ℕ)) : ℝ)
      = (m : ℝ) * (((2 ^ (Fintype.card X - 1) : ℕ)) : ℝ) := by
    rw [hNm]
    push_cast
    ring
  have hBA : (((2 ^ Fintype.card X : ℕ)) : ℝ) = 2 * (((2 ^ (Fintype.card X - 1) : ℕ)) : ℝ) := by
    rw [hpowNat, Nat.cast_mul, Nat.cast_two]
  rw [hLHS, hBA] at hcomb
  have h_simp : (2 * (((2 ^ (Fintype.card X - 1) : ℕ)) : ℝ)) * ((Fintype.card X : ℝ) / 8)
      = (((2 ^ (Fintype.card X - 1) : ℕ)) : ℝ) * (m : ℝ) / 2 := by
    rw [hXr]
    ring
  rw [h_simp] at hcomb
  have hcomm : (m : ℝ) * (((2 ^ (Fintype.card X - 1) : ℕ)) : ℝ) = (((2 ^ (Fintype.card X - 1) : ℕ)) : ℝ) * (m : ℝ) := by ring
  have h_half : (((2 ^ (Fintype.card X - 1) : ℕ)) : ℝ) * (m : ℝ) / 2 ≤ ((Finset.univ.filter p).card : ℝ) * (m : ℝ) := by
    linarith [hcomb, hcomm]
  have h_half2 : (((2 ^ (Fintype.card X - 1) : ℕ)) : ℝ) / 2 * (m : ℝ) ≤ ((Finset.univ.filter p).card : ℝ) * (m : ℝ) := by
    have heq : (((2 ^ (Fintype.card X - 1) : ℕ)) : ℝ) * (m : ℝ) / 2 = (((2 ^ (Fintype.card X - 1) : ℕ)) : ℝ) / 2 * (m : ℝ) := by ring
    rw [heq] at h_half
    exact h_half
  have h_Sge : (((2 ^ (Fintype.card X - 1) : ℕ)) : ℝ) / 2 ≤ ((Finset.univ.filter p).card : ℝ) :=
    le_of_mul_le_mul_right h_half2 hmposR
  have hBnonneg : (0 : ℝ) ≤ (((2 ^ Fintype.card X : ℕ)) : ℝ) := by positivity
  have hBeq : (((2 ^ Fintype.card X : ℕ)) : ℝ) = (2 : ℝ) ^ Fintype.card X := by norm_cast
  have hgoal : ((Finset.univ.filter p).card : ℝ) ≥ (1 / 7) * (((2 ^ Fintype.card X : ℕ)) : ℝ) := by
    have h1 : ((Finset.univ.filter p).card : ℝ) ≥ (((2 ^ (Fintype.card X - 1) : ℕ)) : ℝ) / 2 := h_Sge
    have h2 : (((2 ^ Fintype.card X : ℕ)) : ℝ) = 2 * (((2 ^ (Fintype.card X - 1) : ℕ)) : ℝ) := hBA
    linarith [h1, h2, hBnonneg]
  rw [hBeq] at hgoal
  simp only [hp] at hgoal ⊢
  exact hgoal
