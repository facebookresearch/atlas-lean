/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic

namespace MetaMathlibExt

@[expose] public section

/-! # Vanishing of power sums modulo a prime
-/

/--
**Power sums vanish modulo a prime.** Let $p$ be a prime and let $e \ge 0$ be an integer such
that $p - 1$ does not divide $e$ whenever $e \ge 1$. Then $p$ divides $\sum_{t=1}^{p} t^e$.

For $e = 0$ the sum is $p$. The source states the lemma for odd primes; for $p = 2$ the
hypothesis forces $e = 0$.

Source: Christian Ballot, "On a Congruence of Kimball and Webb Involving
Lucas Sequences," Journal of Integer Sequences 17 (2014), Article 14.1.3,
Lemma (label lem:char), lines 223–225,
https://cs.uwaterloo.ca/journals/JIS/VOL17/Ballot/ballot7.tex
Proves `Wanted` entry `powerSum_vanishing_mod_prime`.
-/
theorem powerSum_vanishing_mod_prime
    (p : ℕ) (hp : Nat.Prime p) (e : ℕ)
    (he : 1 ≤ e → ¬ (p - 1) ∣ e) :
    (p : ℤ) ∣ ∑ t ∈ Finset.Icc 1 p, (t : ℤ) ^ e := by
  rcases eq_or_ne e 0 with rfl | hne
  · simp only [pow_zero, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one,
      Nat.add_sub_cancel]
    exact dvd_rfl
  · have hle : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr hne
    have hdiv : ¬ (p - 1) ∣ e := he hle
    haveI := Fact.mk hp
    haveI hNe : NeZero p := ⟨hp.ne_zero⟩
    have hcast : ((∑ t ∈ Finset.Icc 1 p, (t : ℤ) ^ e : ℤ) : ZMod p)
        = ∑ t ∈ Finset.Icc 1 p, ((t : ℕ) : ZMod p) ^ e := by simp
    have hIccIco : Finset.Icc 1 p = Finset.Ico 1 (p + 1) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    have hRange : ∀ f : ZMod p → ZMod p,
        ∑ x : ZMod p, f x = ∑ i ∈ Finset.range p, f (i : ZMod p) := by
      intro f
      have he_bij : Function.Bijective
          (fun i : Fin p => ((i.val : ℕ) : ZMod p)) := by
        constructor
        · intro a b hab
          simp only at hab
          rw [ZMod.natCast_eq_natCast_iff] at hab
          exact Fin.ext (hab.eq_of_lt_of_lt (Fin.is_lt a) (Fin.is_lt b))
        · intro x
          refine ⟨⟨x.val, ZMod.val_lt x⟩, ?_⟩
          show (((x.val : ℕ)) : ZMod p) = x
          rw [ZMod.natCast_val, ZMod.cast_id]
      have h1 := Fintype.sum_bijective _ he_bij
        (fun i : Fin p => f ((i.val : ℕ) : ZMod p)) f (fun i => rfl)
      rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => f (n : ZMod p)) p] at h1
      exact h1.symm
    have hLHS : ∑ t ∈ Finset.Icc 1 p, ((t : ℕ) : ZMod p) ^ e
        = ∑ x : ZMod p, (1 + x) ^ e := by
      have h1 : ∑ t ∈ Finset.Icc 1 p, ((t : ℕ) : ZMod p) ^ e
          = ∑ k ∈ Finset.range p, (1 + ((k : ℕ) : ZMod p)) ^ e := by
        rw [hIccIco, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.cast_add, Nat.cast_one]
      rw [h1]
      exact (hRange (fun x : ZMod p => (1 + x) ^ e)).symm
    have htrans : (∑ x : ZMod p, (1 + x) ^ e) = ∑ x : ZMod p, x ^ e :=
      Fintype.sum_equiv (Equiv.addLeft (1 : ZMod p))
        (fun x => (1 + x) ^ e) (fun x => x ^ e) (fun x => rfl)
    have hzero : ∑ x : ZMod p, x ^ e = 0 := by
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
      have hord : orderOf g = p - 1 := by
        have h := orderOf_eq_card_of_forall_mem_zpowers hg
        rw [Nat.card_eq_fintype_card, ZMod.card_units] at h
        exact h
      have hex : ∃ a : (ZMod p)ˣ, a ^ e ≠ 1 := by
        by_contra hcon
        have hcon' : ∀ a : (ZMod p)ˣ, a ^ e = 1 :=
          fun a => not_ne_iff.mp (fun h => hcon ⟨a, h⟩)
        have hdvd : orderOf g ∣ e := orderOf_dvd_of_pow_eq_one (hcon' g)
        rw [hord] at hdvd
        exact hdiv hdvd
      obtain ⟨a, ha⟩ := hex
      have hc0 : ((a : ZMod p)) ≠ 0 := Units.ne_zero a
      have hce : ((a : ZMod p)) ^ e ≠ 1 := by
        intro hcon
        apply ha
        have h2 : ((a ^ e : (ZMod p)ˣ) : ZMod p)
            = ((1 : (ZMod p)ˣ) : ZMod p) := by
          rw [Units.val_pow_eq_pow_val, hcon, Units.val_one]
        exact Units.ext h2
      have hscale : ((a : ZMod p)) ^ e * (∑ x : ZMod p, x ^ e)
          = ∑ x : ZMod p, x ^ e := by
        rw [Finset.mul_sum]
        simp_rw [← mul_pow]
        exact Fintype.sum_equiv (Equiv.mulLeft₀ _ hc0)
          (fun x => ((a : ZMod p) * x) ^ e) (fun x => x ^ e) (fun x => rfl)
      have hS : (((a : ZMod p)) ^ e - 1) * (∑ x : ZMod p, x ^ e) = 0 := by
        rw [sub_mul, one_mul, hscale, sub_self]
      rcases mul_eq_zero.mp hS with h | h
      · exact absurd h (sub_ne_zero.mpr hce)
      · exact h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hcast, hLHS, htrans]
    exact hzero

end

end MetaMathlibExt
