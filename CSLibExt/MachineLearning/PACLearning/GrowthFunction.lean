/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.MachineLearning.PACLearning.TraceCard
public import MathlibExt.Combinatorics.BinomialPartialSum
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic

/-! # Growth function and Sauer closed form

The growth function is the supremum of the trace counts a binary concept
class realizes over `m`-subsets of the domain. This is the maximum when an
`m`-subset exists (see `exists_traceFamily_card_eq_growthFunction` below),
and `0` when none does (for example `m ≥ 1` on an empty type), since `sSup`
on `ℕ` of the empty set is `0`. This file defines it that way and proves the
Sauer sum bound and the exponential closed form by composing the reused
bounds. The Sauer bounds assume classes of finite VC dimension
(`HasFiniteVCDim`), under which the natural-valued `vcDim` is meaningful.

## Main definitions

- `growthFunction`: the growth function.

## Main statements

- `traceFamily_card_le_growthFunction`, `growthFunction_le_two_pow`,
  `exists_traceFamily_card_eq_growthFunction`: adapter lemmas.
- `growthFunction_le_sum`, `growthFunction_le_exp_pow`: Sauer bounds.
- `vcDim_le_log_two_card`: finite classes bound the VC dimension.
-/

@[expose] public section

namespace Cslib.MachineLearning.PACLearning

/-- The *growth function*: the supremum of the numbers of distinct traces the
class `C` realizes over `m`-subsets of the domain. This is the maximum when
an `m`-subset exists (see `exists_traceFamily_card_eq_growthFunction`), and
`0` when none does (for example `m ≥ 1` on an empty type), since `sSup` on
`ℕ` of the empty set is `0`. This agrees with `τ_H(m)` of Shalev-Shwartz
and Ben-David. -/
noncomputable def growthFunction {α : Type*} (C : ConceptClass α Bool) (m : ℕ) : ℕ :=
  sSup { (traceFamily C s).card | (s : Finset α) (_ : s.card = m) }

/-- The trace count on any sample is bounded by the growth function. -/
theorem traceFamily_card_le_growthFunction {α : Type*} (C : ConceptClass α Bool)
    (s : Finset α) : (traceFamily C s).card ≤ growthFunction C s.card := by
  unfold growthFunction
  refine le_csSup ?_ ⟨s, rfl, rfl⟩
  refine ⟨2 ^ s.card, ?_⟩
  rintro k ⟨t, ht, rfl⟩
  rw [← ht]
  exact card_traceFamily_le_two_pow C t

/-- The growth function is bounded by `2 ^ m`. -/
theorem growthFunction_le_two_pow {α : Type*} (C : ConceptClass α Bool) (m : ℕ) :
    growthFunction C m ≤ 2 ^ m := by
  unfold growthFunction
  apply csSup_le'
  rintro k ⟨t, ht, rfl⟩
  rw [← ht]
  exact card_traceFamily_le_two_pow C t

/-- When an `m`-subset exists, the supremum is attained on one. -/
theorem exists_traceFamily_card_eq_growthFunction {α : Type*} (C : ConceptClass α Bool)
    (m : ℕ) (hex : ∃ s0 : Finset α, s0.card = m) :
    ∃ s, s.card = m ∧ (traceFamily C s).card = growthFunction C m := by
  obtain ⟨s0, hs0⟩ := hex
  have hne : { (traceFamily C t).card | (t : Finset α) (_ : t.card = m) }.Nonempty :=
    ⟨(traceFamily C s0).card, s0, hs0, rfl⟩
  have hbdd : BddAbove { (traceFamily C t).card | (t : Finset α) (_ : t.card = m) } :=
    ⟨2 ^ m, by rintro k ⟨t, ht, rfl⟩; rw [← ht]; exact card_traceFamily_le_two_pow C t⟩
  have hmem := Nat.sSup_mem hne hbdd
  obtain ⟨s, hs, hcard⟩ := hmem
  exact ⟨s, hs, hcard⟩

/-- The Sauer sum bound for the growth function, for classes of finite VC
dimension (`HasFiniteVCDim`). -/
theorem growthFunction_le_sum {α : Type*} (C : ConceptClass α Bool) (m : ℕ)
    (hC : HasFiniteVCDim C) :
    growthFunction C m ≤ ∑ k ∈ Finset.Iic (vcDim C), m.choose k := by
  unfold growthFunction
  apply csSup_le'
  rintro k ⟨t, ht, rfl⟩
  have h := card_traceFamily_le_sum_vcDim hC t
  rwa [ht] at h

/-- The exponential closed form for the growth function, for classes of
finite VC dimension (`HasFiniteVCDim`). -/
theorem growthFunction_le_exp_pow {α : Type*} (C : ConceptClass α Bool) (m : ℕ)
    (hC : HasFiniteVCDim C) (hd : 1 ≤ vcDim C) (hdm : vcDim C ≤ m) :
    (growthFunction C m : ℝ) ≤
      (Real.exp 1 * (m : ℝ) / (vcDim C : ℝ)) ^ (vcDim C) := by
  have hM1 := growthFunction_le_sum C m hC
  have hcast : (growthFunction C m : ℝ) ≤
      ((∑ k ∈ Finset.Iic (vcDim C), m.choose k : ℕ) : ℝ) := by
    exact_mod_cast hM1
  rw [Nat.cast_sum, ← Nat.range_succ_eq_Iic] at hcast
  have hclosed :=
    Real.sum_choose_le_exp_mul_div_pow (D := m) (r := vcDim C) hd hdm
  exact hcast.trans hclosed

private theorem two_pow_card_le_of_shatters {α : Type*} (H : Finset (α → Bool))
    (C : ConceptClass α Bool) (hCH : C = ↑H) (W : Finset α)
    (hWshat : SetShatters C (↑W)) : 2 ^ W.card ≤ H.card := by
  have hreal : ∀ t : Finset ↥W, ∃ c : α → Bool,
      c ∈ C ∧ ∀ w : ↥W, (c ↑w = true ↔ w ∈ t) := by
    intro t
    have hTsub : (fun w : ↥W => (w : α)) '' (↑t : Set ↥W) ⊆ (↑W : Set α) := by
      rintro x ⟨w, -, rfl⟩
      exact w.2
    obtain ⟨c, hcC, hcT⟩ := hWshat _ hTsub
    refine ⟨c, hcC, fun w => ?_⟩
    have hwW : (w : α) ∈ (↑W : Set α) := w.2
    have hiff : ((w : α) ∈ c ⁻¹' {true} ∩ ↑W) ↔
        (w : α) ∈ (fun w : ↥W => (w : α)) '' ↑t := by rw [hcT]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_image, Finset.mem_coe] at hiff
    constructor
    · intro htrue
      obtain ⟨w', hw't, hcoe⟩ := hiff.mp ⟨htrue, hwW⟩
      have heq : w' = w := Subtype.ext_iff.mpr hcoe
      subst heq
      exact hw't
    · intro hwt
      exact (hiff.mpr ⟨w, hwt, rfl⟩).1
  obtain ⟨f, hf⟩ := Classical.skolem.mp hreal
  have hfinj : Function.Injective f := by
    intro t₁ t₂ hft
    ext w
    rw [← (hf t₁).2 w, ← (hf t₂).2 w, hft]
  have hmemH : ∀ t, f t ∈ H := by
    intro t
    have hc : f t ∈ C := (hf t).1
    rw [hCH] at hc
    exact Finset.mem_coe.mp hc
  have hginj : Function.Injective (fun t : Finset ↥W => (⟨f t, hmemH t⟩ : ↥H)) := by
    intro t₁ t₂ hgt
    have hft : f t₁ = f t₂ := congrArg Subtype.val hgt
    exact hfinj hft
  have hcard := Fintype.card_le_of_injective _ hginj
  rw [Fintype.card_finset, Fintype.card_coe, Fintype.card_coe] at hcard
  exact hcard

/-- A finite concept class bounds the VC dimension. -/
theorem vcDim_le_log_two_card {α : Type*} (H : Finset (α → Bool))
    (C : ConceptClass α Bool) (hCH : C = ↑H)
    (hH : H.Nonempty) :
    2 ^ vcDim C ≤ H.card := by
  have hne : {n : ℕ | ∃ W : Finset α, W.card = n ∧ SetShatters C (↑W)}.Nonempty := by
    obtain ⟨c₀, hc₀⟩ := hH
    have hc₀C : c₀ ∈ C := by
      rw [hCH]
      exact Finset.mem_coe.mpr hc₀
    refine ⟨0, ∅, Finset.card_empty, ?_⟩
    intro W' hW'
    rw [Finset.coe_empty, Set.subset_empty_iff] at hW'
    subst hW'
    exact ⟨c₀, hc₀C, by rw [Finset.coe_empty, Set.inter_empty]⟩
  have hbdd : BddAbove {n : ℕ | ∃ W : Finset α, W.card = n ∧ SetShatters C (↑W)} := by
    refine ⟨H.card, ?_⟩
    rintro n ⟨W, hWcard, hWshat⟩
    have hle := two_pow_card_le_of_shatters H C hCH W hWshat
    rw [hWcard] at hle
    exact Nat.lt_two_pow_self.le.trans hle
  obtain ⟨W, hWcard, hWshat⟩ := Nat.sSup_mem hne hbdd
  have hdim : vcDim C = W.card := hWcard.symm
  rw [hdim]
  exact two_pow_card_le_of_shatters H C hCH W hWshat

end Cslib.MachineLearning.PACLearning
