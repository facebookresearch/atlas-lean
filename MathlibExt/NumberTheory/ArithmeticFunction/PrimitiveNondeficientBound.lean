/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MetaMathlibExt
/-! # Prime-power bound for primitive non-deficient numbers
-/

-- Counting lemma (Step 5 helper): product of p/(p-1) over distinct naturals ≥ c+1
private lemma prod_div_sub_one_le (T : Finset ℕ) (c : ℕ) (hc : 1 ≤ c)
    (hT : ∀ p ∈ T, c + 1 ≤ p) :
    (∏ p ∈ T, ((p : ℝ) / ((p : ℝ) - 1))) ≤ ((c + T.card : ℕ) : ℝ) / (c : ℝ) := by
  classical
  suffices h : ∀ U : Finset ℕ, (∀ p ∈ U, c + 1 ≤ p) →
      (∏ p ∈ U, ((p : ℝ) / ((p : ℝ) - 1))) ≤ ((c + U.card : ℕ) : ℝ) / (c : ℝ) from h T hT
  intro U
  refine Finset.induction_on_max U ?_ ?_
  · intro _
    rw [Finset.prod_empty, Finset.card_empty]
    simp only [add_zero]
    have hcR0 : (c : ℝ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
    rw [div_self hcR0]
  · intro a s hall IH hU
    have hsT : ∀ p ∈ s, c + 1 ≤ p := fun p hp => hU p (Finset.mem_insert_of_mem hp)
    have hIH := IH hsT
    have ha_le : c + 1 ≤ a := hU a (Finset.mem_insert_self a s)
    have ha_notin : a ∉ s := by
      intro hm; exact absurd (hall a hm) (lt_irrefl a)
    have hcard : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem ha_notin
    have hsub : s ⊆ Finset.Ico (c + 1) a := by
      intro x hx
      simp only [Finset.mem_Ico]
      exact ⟨hsT x hx, hall x hx⟩
    have hcle : s.card ≤ a - (c + 1) := by
      calc s.card ≤ (Finset.Ico (c + 1) a).card := Finset.card_le_card hsub
        _ = a - (c + 1) := Nat.card_Ico _ _
    have hmj : c + s.card + 1 ≤ a := by omega
    have hcardRm : c + (s.card + 1) = c + s.card + 1 := by omega
    rw [Finset.prod_insert ha_notin, hcard, hcardRm]
    have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
    have hjR : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
    have haR2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (by omega : 2 ≤ a)
    have hcc2 : ((c + s.card : ℕ) : ℝ) = (c : ℝ) + (s.card : ℝ) := by push_cast; ring
    have hBp : ((c + s.card + 1 : ℕ) : ℝ) = ((c + s.card : ℕ) : ℝ) + 1 := by push_cast; ring
    have hmjR : ((c + s.card + 1 : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hmj
    have hmono : (a : ℝ) / ((a : ℝ) - 1) ≤ ((c + s.card + 1 : ℕ) : ℝ) / ((c + s.card : ℕ) : ℝ) := by
      have h1 : (0 : ℝ) < (a : ℝ) - 1 := by linarith
      have h2 : (0 : ℝ) < ((c + s.card : ℕ) : ℝ) := by
        rw [hcc2]; linarith [hcR, hjR]
      rw [div_le_iff₀ h1, div_mul_eq_mul_div, le_div_iff₀ h2]
      nlinarith [hmjR, h1, h2, hBp]
    have hpos1 : (0 : ℝ) ≤ ∏ p ∈ s, ((p : ℝ) / ((p : ℝ) - 1)) := by
      apply Finset.prod_nonneg
      intro p hp
      apply div_nonneg (Nat.cast_nonneg _)
      have hple : c + 1 ≤ p := hsT p hp
      have h1p : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
      linarith
    have hposB : (0 : ℝ) ≤ ((c + s.card + 1 : ℕ) : ℝ) / ((c + s.card : ℕ) : ℝ) := by
      apply div_nonneg (Nat.cast_nonneg _)
      have hlt : (0 : ℝ) ≤ ((c + s.card : ℕ) : ℝ) := by rw [hcc2]; linarith [hcR, hjR]
      linarith
    have hnonneg : (0 : ℝ) ≤ ((c + s.card : ℕ) : ℝ) / (c : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt hcR)
    calc ((a : ℝ) / ((a : ℝ) - 1)) * (∏ p ∈ s, ((p : ℝ) / ((p : ℝ) - 1)))
        ≤ (((c + s.card + 1 : ℕ) : ℝ) / ((c + s.card : ℕ) : ℝ))
            * (((c + s.card : ℕ) : ℝ) / (c : ℝ)) :=
          mul_le_mul hmono hIH hpos1 hposB
      _ = ((c + s.card + 1 : ℕ) : ℝ) / (c : ℝ) := by
          have h2ne : ((c + s.card : ℕ) : ℝ) ≠ 0 := by
            have hlt : (0 : ℝ) < ((c + s.card : ℕ) : ℝ) := by rw [hcc2]; linarith [hcR, hjR]
            linarith
          field_simp

private lemma n_ge_two (n : ℕ) (hn : n ≠ 0)
    (hnondef : 2 * n ≤ ∑ d ∈ Nat.divisors n, d) : 2 ≤ n := by
  by_contra h
  have hlt : n < 2 := lt_of_not_ge h
  have h01 : n = 0 ∨ n = 1 := by omega
  rcases h01 with rfl | rfl
  · exact absurd rfl hn
  · simp at hnondef

private lemma S_nonempty (n : ℕ) (hn2 : 2 ≤ n) : n.primeFactors.Nonempty :=
  Nat.nonempty_primeFactors.mpr (by omega)

private lemma afac_pos (n p : ℕ) (hn : n ≠ 0) (hp : p ∈ n.primeFactors) :
    0 < n.factorization p := by
  have h := Nat.mem_primeFactors.mp hp
  exact Nat.Prime.factorization_pos_of_dvd h.1 hn h.2.1

private lemma R_ge_two (n : ℕ) (hne : n.primeFactors.Nonempty) :
    2 ≤ ∏ q ∈ n.primeFactors, q := by
  obtain ⟨p, hp⟩ := hne
  have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
  calc 2 ≤ p := hpp.two_le
    _ ≤ ∏ q ∈ n.primeFactors, q := by
        apply Finset.single_le_prod _ hp
        intro q hq
        have hqq : Nat.Prime q := (Nat.mem_primeFactors.mp hq).1
        have := hqq.two_le
        omega

-- Product formula for σ in ℕ
private lemma sigma_prod_nat (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ Nat.divisors n, d)
      = ∏ p ∈ n.primeFactors, (∑ k ∈ Finset.range (n.factorization p + 1), p ^ k) := by
  have h1 : (ArithmeticFunction.sigma 1) n = ∑ d ∈ Nat.divisors n, d :=
    ArithmeticFunction.sigma_one_apply n
  have h2 := ArithmeticFunction.IsMultiplicative.multiplicative_factorization
    (ArithmeticFunction.sigma (1 : ℕ) : ArithmeticFunction ℕ)
    ArithmeticFunction.isMultiplicative_sigma hn
  have h3 : (∑ d ∈ Nat.divisors n, d)
      = n.factorization.prod (fun p k => (ArithmeticFunction.sigma 1) (p ^ k)) := by
    rw [← h1]; exact h2
  rw [h3, Nat.prod_factorization_eq_prod_primeFactors]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
  exact ArithmeticFunction.sigma_one_apply_prime_pow hpp

-- Product formula cast to ℝ
private lemma sigma_prod (n : ℕ) (hn : n ≠ 0) :
    ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ)
      = ∏ p ∈ n.primeFactors, (((∑ k ∈ Finset.range (n.factorization p + 1), p ^ k : ℕ)) : ℝ) := by
  have hnat := sigma_prod_nat n hn
  calc ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ)
      = ((((∏ p ∈ n.primeFactors,
        (∑ k ∈ Finset.range (n.factorization p + 1), p ^ k) : ℕ))) : ℝ) := by
        rw [hnat]
    _ = _ := Nat.cast_prod _ _

-- Per-prime geometric sum identity in ℝ
private lemma prime_geom (p a : ℕ) (_hp : Nat.Prime p) :
    ((∑ k ∈ Finset.range (a + 1), p ^ k : ℕ) : ℝ) * ((p : ℝ) - 1)
      = (p : ℝ) ^ (a + 1) - 1 := by
  have hcast : ((∑ k ∈ Finset.range (a + 1), p ^ k : ℕ) : ℝ)
      = ∑ k ∈ Finset.range (a + 1), (p : ℝ) ^ k := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact Nat.cast_pow p k
  rw [hcast]
  exact geom_sum_mul (p : ℝ) (a + 1)

-- n as a product of prime powers, in ℝ
private lemma n_prod (n : ℕ) (hn : n ≠ 0) :
    ((n : ℕ) : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) := by
  have h : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    have h0 := Nat.prod_factorization_pow_eq_self hn
    rw [Nat.prod_factorization_eq_prod_primeFactors] at h0
    simpa using h0
  calc ((n : ℕ) : ℝ) = (((∏ p ∈ n.primeFactors, p ^ n.factorization p : ℕ)) : ℝ) := by rw [h]
    _ = _ := by
        rw [Nat.cast_prod]
        apply Finset.prod_congr rfl
        intro p _
        exact Nat.cast_pow p (n.factorization p)

-- Master identity: H = Q * P
private lemma H_eq (n : ℕ) (hn : n ≠ 0) :
    ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ)
      = (∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)))
        * (∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℝ) ^ (n.factorization p + 1)))) := by
  rw [sigma_prod n hn, n_prod n hn, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
  have hgeom := prime_geom p (n.factorization p) hpp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt hppos
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    linarith
  have hpa : ((p : ℝ) ^ n.factorization p) ≠ 0 := pow_ne_zero _ hp0
  have hxp : ((p : ℝ) ^ (n.factorization p + 1)) ≠ 0 := pow_ne_zero _ hp0
  have hSa : (((∑ k ∈ Finset.range (n.factorization p + 1), p ^ k : ℕ)) : ℝ)
      = (((p : ℝ) ^ (n.factorization p + 1)) - 1) / ((p : ℝ) - 1) :=
    (eq_div_iff hpm1).mpr hgeom
  rw [hSa]
  field_simp
  rw [pow_succ]
  ring

-- Bridge: cast of nat product of primes = real product
private lemma R_bridge (n : ℕ) :
    ((((∏ q ∈ n.primeFactors, q : ℕ))) : ℝ) = ∏ q ∈ n.primeFactors, (q : ℝ) := by
  rw [Nat.cast_prod]

-- Bridge: cast of nat product of (p-1) = real product
private lemma phi_bridge (n : ℕ) :
    ((((∏ p ∈ n.primeFactors, (p - 1) : ℕ))) : ℝ)
      = ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
  rw [Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
  change (((p - 1 : ℕ)) : ℝ) = (p : ℝ) - 1
  simpa using Nat.cast_sub (R := ℝ) hpp.one_le

-- Product of reals in (0,1) over a nonempty finset is < 1 (avoids legacy classes)
private lemma prod_lt_one_of (S : Finset ℕ) (f : ℕ → ℝ)
    (hpos : ∀ p ∈ S, 0 < f p) (hlt : ∀ p ∈ S, f p < 1) (hne : S.Nonempty) :
    ∏ p ∈ S, f p < 1 := by
  classical
  suffices h : ∀ U : Finset ℕ, (∀ p ∈ U, 0 < f p) → (∀ p ∈ U, f p < 1) →
      U.Nonempty → ∏ p ∈ U, f p < 1 from h S hpos hlt hne
  intro U
  refine Finset.induction ?_ ?_ U
  · intro _ _ hempty
    simp at hempty
  · intro a s has IH hposU hltU _
    have hpos_s : ∀ p ∈ s, 0 < f p :=
      fun p hp => hposU p (Finset.mem_insert_of_mem hp)
    have hlt_s : ∀ p ∈ s, f p < 1 :=
      fun p hp => hltU p (Finset.mem_insert_of_mem hp)
    have ha1 : f a < 1 := hltU a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert has]
    by_cases hs : s.Nonempty
    · have h1 := IH hpos_s hlt_s hs
      have h0 : 0 < ∏ p ∈ s, f p := Finset.prod_pos hpos_s
      calc f a * ∏ p ∈ s, f p < 1 * ∏ p ∈ s, f p :=
            mul_lt_mul_of_pos_right ha1 h0
        _ = ∏ p ∈ s, f p := one_mul _
        _ < 1 := h1
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.prod_empty, mul_one]
      exact ha1

-- Step 1 consequences: H ≥ 2, H < Q, Q > 2, and (A)
private lemma step1 (n : ℕ) (hn : n ≠ 0)
    (hnondef : 2 * n ≤ ∑ d ∈ Nat.divisors n, d) :
    2 ≤ ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ)
    ∧ ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ)
        < (∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)))
    ∧ 2 < (∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)))
    ∧ 2 * (∏ q ∈ n.primeFactors, (q : ℝ)) / ((∏ q ∈ n.primeFactors, (q : ℝ)) - 1)
        ≤ (∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))) := by
  have hn2 := n_ge_two n hn hnondef
  have hne := S_nonempty n hn2
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hHge : 2 ≤ ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ) := by
    have hcast : ((2 * n : ℕ) : ℝ) ≤ ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) := by
      exact_mod_cast hnondef
    rw [Nat.cast_mul, Nat.cast_ofNat] at hcast
    rw [le_div_iff₀ hnR]
    linarith [hcast]
  have hQpos : 0 < (∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))) := by
    apply Finset.prod_pos
    intro p hp
    have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    apply div_pos (by linarith) (by linarith)
  have hP1 : (∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℝ) ^ (n.factorization p + 1)))) < 1 := by
    apply prod_lt_one_of _ _ _ _ hne
    · intro p hp
      have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hxpos : (0 : ℝ) < ((p : ℝ) ^ (n.factorization p + 1)) :=
        pow_pos (by linarith) _
      have hx2 : (2 : ℝ) ≤ ((p : ℝ) ^ (n.factorization p + 1)) := by
        have hle : (p : ℝ) ≤ ((p : ℝ) ^ (n.factorization p + 1)) := by
          conv_lhs => rw [← pow_one (p : ℝ)]
          apply pow_le_pow_right₀ (by linarith) (by omega)
        linarith [hp2]
      have h1 : (1 : ℝ) / ((p : ℝ) ^ (n.factorization p + 1)) < 1 := by
        rw [div_lt_one hxpos]
        linarith
      linarith
    · intro p hp
      have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hxpos : (0 : ℝ) < ((p : ℝ) ^ (n.factorization p + 1)) :=
        pow_pos (by linarith) _
      have h1 : (0 : ℝ) < 1 / ((p : ℝ) ^ (n.factorization p + 1)) :=
        one_div_pos.mpr hxpos
      linarith
  have hHQ : ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ)
      < (∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))) := by
    have hE := H_eq n hn
    rw [hE]
    calc (∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)))
          * (∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℝ) ^ (n.factorization p + 1))))
        < (∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))) * 1 :=
          mul_lt_mul_of_pos_left hP1 hQpos
      _ = _ := mul_one _
  have hQ2 : 2 < (∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))) :=
    lt_of_le_of_lt hHge hHQ
  have hA : 2 * (∏ q ∈ n.primeFactors, (q : ℝ)) / ((∏ q ∈ n.primeFactors, (q : ℝ)) - 1)
      ≤ (∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))) := by
    have hR2 : (2 : ℝ) ≤ (∏ q ∈ n.primeFactors, (q : ℝ)) := by
      have h := R_ge_two n hne
      have h2 : ((2 : ℕ) : ℝ) ≤ ((((∏ q ∈ n.primeFactors, q : ℕ))) : ℝ) := by
        exact_mod_cast h
      rw [R_bridge] at h2
      simpa using h2
    have hphipos : (0 : ℝ) < (∏ p ∈ n.primeFactors, ((p : ℝ) - 1)) := by
      apply Finset.prod_pos
      intro p hp
      have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      linarith
    have hQR : (∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)))
        = (∏ q ∈ n.primeFactors, (q : ℝ)) / (∏ p ∈ n.primeFactors, ((p : ℝ) - 1)) :=
      Finset.prod_div_distrib _ _
    have hRgt : 2 * (∏ p ∈ n.primeFactors, ((p : ℝ) - 1))
        < (∏ q ∈ n.primeFactors, (q : ℝ)) := by
      rw [hQR] at hQ2
      exact (lt_div_iff₀ hphipos).mp hQ2
    have hnat : 2 * (∏ p ∈ n.primeFactors, (p - 1)) + 1 ≤ (∏ q ∈ n.primeFactors, q) := by
      by_contra hc
      have hc2 : (∏ q ∈ n.primeFactors, q) < 2 * (∏ p ∈ n.primeFactors, (p - 1)) + 1 :=
        lt_of_not_ge hc
      have hle : (∏ q ∈ n.primeFactors, q) ≤ 2 * (∏ p ∈ n.primeFactors, (p - 1)) := by
        omega
      have hcast : ((((∏ q ∈ n.primeFactors, q : ℕ))) : ℝ)
          ≤ 2 * ((((∏ p ∈ n.primeFactors, (p - 1) : ℕ))) : ℝ) := by
        exact_mod_cast hle
      rw [R_bridge, phi_bridge] at hcast
      linarith
    have hnatR : 2 * (∏ p ∈ n.primeFactors, ((p : ℝ) - 1)) + 1
        ≤ (∏ q ∈ n.primeFactors, (q : ℝ)) := by
      have hcast : ((((2 * (∏ p ∈ n.primeFactors, (p - 1)) + 1 : ℕ))) : ℝ)
          ≤ ((((∏ q ∈ n.primeFactors, q : ℕ))) : ℝ) := by
        exact_mod_cast hnat
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, R_bridge, phi_bridge] at hcast
      linarith [hcast]
    have hRm1 : (0 : ℝ) < (∏ q ∈ n.primeFactors, (q : ℝ)) - 1 := by linarith
    have hphine : (∏ p ∈ n.primeFactors, ((p : ℝ) - 1)) ≠ 0 := ne_of_gt hphipos
    rw [hQR, div_le_iff₀ hRm1, div_mul_eq_mul_div, le_div_iff₀ hphipos]
    nlinarith [hnatR]
  exact ⟨hHge, hHQ, hQ2, hA⟩

-- Step 2 (primitivity at n/p): H * (x_p - p) < 2 * (x_p - 1)
private lemma step2 (n p : ℕ) (hn : n ≠ 0) (hp : p ∈ n.primeFactors)
    (hprim : ∀ m ∈ Nat.divisors n, m < n → ∑ d ∈ Nat.divisors m, d < 2 * m) :
    ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ)
        * (((p : ℝ) ^ (n.factorization p + 1)) - (p : ℝ))
      < 2 * (((p : ℝ) ^ (n.factorization p + 1)) - 1) := by
  have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt hppos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have ha1 : 1 ≤ n.factorization p := afac_pos n p hn hp
  obtain ⟨b, hb0⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n.factorization p ≠ 0)
  rw [Nat.succ_eq_add_one] at hb0
  rw [hb0]
  have hpdvd : p ∣ n := (Nat.mem_primeFactors.mp hp).2.1
  have hnm0 : p ^ (b + 1) * (n / p ^ (b + 1)) = n := by
    rw [← hb0]
    exact Nat.ordProj_mul_ordCompl_eq_self n p
  have hcop0 : Nat.Coprime p (n / p ^ (b + 1)) := by
    have h := Nat.coprime_ordCompl hpp hn
    rwa [hb0] at h
  have hcop : Nat.Coprime (p ^ (b + 1)) (n / p ^ (b + 1)) := hcop0.pow_left (b + 1)
  have hcopb : Nat.Coprime (p ^ b) (n / p ^ (b + 1)) := hcop0.pow_left b
  have hnsplit : n = (p ^ b * (n / p ^ (b + 1))) * p := by
    have h1 : p ^ (b + 1) = p ^ b * p := pow_succ p b
    calc n = p ^ (b + 1) * (n / p ^ (b + 1)) := hnm0.symm
      _ = (p ^ b * (n / p ^ (b + 1))) * p := by rw [h1]; ring
  have hnp_eq : n / p = p ^ b * (n / p ^ (b + 1)) := by
    conv_lhs => rw [hnsplit]
    exact Nat.mul_div_cancel _ hpp.pos
  have hnp_dvd : n / p ∣ n := Nat.div_dvd_of_dvd hpdvd
  have hmem : n / p ∈ Nat.divisors n := Nat.mem_divisors.mpr ⟨hnp_dvd, hn⟩
  have hlt : n / p < n := Nat.div_lt_self (by omega : 0 < n) hpp.one_lt
  have hsig_lt_nat := hprim (n / p) hmem hlt
  have hsign : (ArithmeticFunction.sigma 1) n = ∑ d ∈ Nat.divisors n, d :=
    ArithmeticFunction.sigma_one_apply n
  have hsignp : (ArithmeticFunction.sigma 1) (n / p) = ∑ d ∈ Nat.divisors (n / p), d :=
    ArithmeticFunction.sigma_one_apply (n / p)
  have hmult1 : (ArithmeticFunction.sigma 1) n
      = (ArithmeticFunction.sigma 1) (p ^ (b + 1))
        * (ArithmeticFunction.sigma 1) (n / p ^ (b + 1)) := by
    have hgcd : (p ^ (b + 1)).gcd (n / p ^ (b + 1)) = 1 := hcop.gcd_eq_one
    have h := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      (f := (ArithmeticFunction.sigma (1 : ℕ) : ArithmeticFunction ℕ))
      ArithmeticFunction.isMultiplicative_sigma hgcd
    rwa [hnm0] at h
  have hmult2 : (ArithmeticFunction.sigma 1) (n / p)
      = (ArithmeticFunction.sigma 1) (p ^ b)
        * (ArithmeticFunction.sigma 1) (n / p ^ (b + 1)) := by
    have hgcd : (p ^ b).gcd (n / p ^ (b + 1)) = 1 := hcopb.gcd_eq_one
    have h := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      (f := (ArithmeticFunction.sigma (1 : ℕ) : ArithmeticFunction ℕ))
      ArithmeticFunction.isMultiplicative_sigma hgcd
    rwa [← hnp_eq] at h
  have h2 : (ArithmeticFunction.sigma 1) (p ^ (b + 1))
      = (∑ k ∈ Finset.range (b + 1 + 1), p ^ k) :=
    ArithmeticFunction.sigma_one_apply_prime_pow hpp
  have h2b : (ArithmeticFunction.sigma 1) (p ^ b)
      = (∑ k ∈ Finset.range (b + 1), p ^ k) :=
    ArithmeticFunction.sigma_one_apply_prime_pow hpp
  have e1 : ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ)
      = ((∑ k ∈ Finset.range (b + 1 + 1), p ^ k : ℕ) : ℝ)
        * (((ArithmeticFunction.sigma 1) (n / p ^ (b + 1)) : ℕ) : ℝ) := by
    have h := hmult1
    rw [hsign, h2] at h
    exact_mod_cast h
  have e2 : ((∑ d ∈ Nat.divisors (n / p), d : ℕ) : ℝ)
      = ((∑ k ∈ Finset.range (b + 1), p ^ k : ℕ) : ℝ)
        * (((ArithmeticFunction.sigma 1) (n / p ^ (b + 1)) : ℕ) : ℝ) := by
    have h := hmult2
    rw [hsignp, h2b] at h
    exact_mod_cast h
  have g1 : ((∑ k ∈ Finset.range (b + 1 + 1), p ^ k : ℕ) : ℝ) * ((p : ℝ) - 1)
      = (p : ℝ) ^ ((b + 1) + 1) - 1 :=
    prime_geom p (b + 1) hpp
  have g2 : ((∑ k ∈ Finset.range (b + 1), p ^ k : ℕ) : ℝ) * ((p : ℝ) - 1)
      = (p : ℝ) ^ (b + 1) - 1 :=
    prime_geom p b hpp
  have hsig : ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) * (((p : ℝ) ^ (b + 1)) - 1)
      = ((∑ d ∈ Nat.divisors (n / p), d : ℕ) : ℝ) * (((p : ℝ) ^ ((b + 1) + 1)) - 1) := by
    calc ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) * (((p : ℝ) ^ (b + 1)) - 1)
        = ((∑ k ∈ Finset.range (b + 1 + 1), p ^ k : ℕ) : ℝ)
          * (((ArithmeticFunction.sigma 1) (n / p ^ (b + 1)) : ℕ) : ℝ)
          * (((∑ k ∈ Finset.range (b + 1), p ^ k : ℕ) : ℝ) * ((p : ℝ) - 1)) := by
          rw [e1, ← g2]
      _ = (((∑ k ∈ Finset.range (b + 1 + 1), p ^ k : ℕ) : ℝ) * ((p : ℝ) - 1))
          * ((((∑ k ∈ Finset.range (b + 1), p ^ k : ℕ) : ℝ))
            * (((ArithmeticFunction.sigma 1) (n / p ^ (b + 1)) : ℕ) : ℝ)) := by
          ring
      _ = ((∑ d ∈ Nat.divisors (n / p), d : ℕ) : ℝ) * (((p : ℝ) ^ ((b + 1) + 1)) - 1) := by
          rw [g1, ← e2]; ring
  have hnp_cast : ((((n / p : ℕ))) : ℝ) = (n : ℝ) / (p : ℝ) :=
    Nat.cast_div hpdvd hp0
  have hltR : ((∑ d ∈ Nat.divisors (n / p), d : ℕ) : ℝ) < 2 * ((n : ℝ) / (p : ℝ)) := by
    have hc : (((∑ d ∈ Nat.divisors (n / p), d : ℕ)) : ℝ) < (((2 * (n / p) : ℕ)) : ℝ) := by
      exact_mod_cast hsig_lt_nat
    rw [Nat.cast_mul, Nat.cast_ofNat, hnp_cast] at hc
    linarith [hc]
  have hpa2 : (2 : ℝ) ≤ (p : ℝ) ^ (b + 1) := by
    have hle : (p : ℝ) ≤ (p : ℝ) ^ (b + 1) := by
      conv_lhs => rw [← pow_one (p : ℝ)]
      apply pow_le_pow_right₀ (by linarith) (by omega)
    linarith
  have hxge : (p : ℝ) ^ (b + 1) ≤ (p : ℝ) ^ ((b + 1) + 1) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hxp1 : (0 : ℝ) < ((p : ℝ) ^ ((b + 1) + 1)) - 1 := by linarith
  have hposK : (0 : ℝ) < ((((p : ℝ) ^ ((b + 1) + 1)) - 1) / (n : ℝ)) * (p : ℝ) :=
    mul_pos (div_pos hxp1 hnR) hppos
  have e_xp : ((p : ℝ) ^ ((b + 1) + 1)) - (p : ℝ)
      = (((p : ℝ) ^ (b + 1)) - 1) * (p : ℝ) := by
    have hps : (p : ℝ) ^ ((b + 1) + 1) = (p : ℝ) ^ (b + 1) * (p : ℝ) :=
      pow_succ (p : ℝ) (b + 1)
    rw [hps]; ring
  calc ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ) * (((p : ℝ) ^ ((b + 1) + 1)) - (p : ℝ))
      = (((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) * (((p : ℝ) ^ (b + 1)) - 1) / (n : ℝ)) * (p : ℝ) := by
        rw [e_xp]; field_simp
    _ = (((∑ d ∈ Nat.divisors (n / p), d : ℕ) : ℝ) * (((p : ℝ) ^ ((b + 1) + 1)) - 1) / (n : ℝ))
          * (p : ℝ) := by
        rw [hsig]
    _ < (2 * ((n : ℝ) / (p : ℝ)) * (((p : ℝ) ^ ((b + 1) + 1)) - 1) / (n : ℝ)) * (p : ℝ) := by
        have hfac1 : (((∑ d ∈ Nat.divisors (n / p), d : ℕ) : ℝ)
              * (((p : ℝ) ^ ((b + 1) + 1)) - 1) / (n : ℝ)) * (p : ℝ)
            = ((∑ d ∈ Nat.divisors (n / p), d : ℕ) : ℝ)
              * (((((p : ℝ) ^ ((b + 1) + 1)) - 1) / (n : ℝ)) * (p : ℝ)) := by
          ring
        have hfac2 : (2 * ((n : ℝ) / (p : ℝ)) * (((p : ℝ) ^ ((b + 1) + 1)) - 1) / (n : ℝ)) * (p : ℝ)
            = (2 * ((n : ℝ) / (p : ℝ)))
              * (((((p : ℝ) ^ ((b + 1) + 1)) - 1) / (n : ℝ)) * (p : ℝ)) := by
          ring
        rw [hfac1, hfac2]
        exact mul_lt_mul_of_pos_right hltR hposK
    _ = 2 * (((p : ℝ) ^ ((b + 1) + 1)) - 1) := by
        field_simp

-- Lower bound for a product by a constant power (avoids legacy classes)
private lemma prod_ge_const (S : Finset ℕ) (f : ℕ → ℝ) (c : ℝ) (h0 : 0 ≤ c)
    (hle : ∀ p ∈ S, c ≤ f p) : c ^ S.card ≤ ∏ p ∈ S, f p := by
  classical
  suffices h : ∀ U : Finset ℕ, (∀ p ∈ U, c ≤ f p) → c ^ U.card ≤ ∏ p ∈ U, f p from h S hle
  intro U
  refine Finset.induction ?_ ?_ U
  · intro _
    rw [Finset.prod_empty, Finset.card_empty, pow_zero]
  · intro a s has IH hU
    have hsU : ∀ p ∈ s, c ≤ f p :=
      fun p hp => hU p (Finset.mem_insert_of_mem hp)
    have haU : c ≤ f a := hU a (Finset.mem_insert_self a s)
    have hIH := IH hsU
    rw [Finset.prod_insert has, Finset.card_insert_of_notMem has, pow_succ']
    have h1 : (0 : ℝ) ≤ c ^ s.card := pow_nonneg h0 _
    have h2 : (0 : ℝ) ≤ f a := le_trans h0 haU
    exact mul_le_mul haU hIH h1 h2

/--
**Prime-power bound for primitive non-deficient numbers.** Let $\sigma(m)$ denote the sum of the
divisors of $m$. Let $n$ be a positive integer that is non-deficient, $\sigma(n) \ge 2n$, and
primitive, meaning that every divisor $m$ of $n$ with $m < n$ is deficient, $\sigma(m) < 2m$.
Let $k$ be the number of distinct prime factors of $n$ and $R$ their product. Then $n$ has a
prime factor $p$ with $p^{v_p(n) + 1} < 2kR$, where $v_p(n)$ is the exponent of $p$ in $n$.

Proves `Wanted` entry `primitive_nondeficient_prime_power_bound`.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number Always
Have a Small Component?," Journal of Integer Sequences 29 (2026),
Article 26.4.3, Theorem (label maintheoremboundwithkR),
equation (label Generalinequalityforprimitivenondeficientnumbers),
lines 107–109,
https://cs.uwaterloo.ca/journals/JIS/VOL29/Zelinsky/zel14.tex
-/
theorem primitive_nondeficient_prime_power_bound
    (n : ℕ) (hn : n ≠ 0)
    (hnondef : 2 * n ≤ ∑ d ∈ Nat.divisors n, d)
    (hprim : ∀ m ∈ Nat.divisors n, m < n → ∑ d ∈ Nat.divisors m, d < 2 * m) :
    ∃ p ∈ n.primeFactors,
      p ^ (n.factorization p + 1) < 2 * n.primeFactors.card * ∏ q ∈ n.primeFactors, q := by
  have hn2 := n_ge_two n hn hnondef
  have hne := S_nonempty n hn2
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨hHge, hHQ, hQ2, hA⟩ := step1 n hn hnondef
  have hk1 : 1 ≤ n.primeFactors.card := by
    have h := Finset.card_pos.mpr hne
    omega
  have hkpos : (0 : ℝ) < (n.primeFactors.card : ℝ) := by
    exact_mod_cast (by omega : 0 < n.primeFactors.card)
  have hk0 : (n.primeFactors.card : ℝ) ≠ 0 := ne_of_gt hkpos
  have hR2 : (2 : ℝ) ≤ ∏ q ∈ n.primeFactors, (q : ℝ) := by
    have h := R_ge_two n hne
    have h2 : ((2 : ℕ) : ℝ) ≤ ((((∏ q ∈ n.primeFactors, q : ℕ))) : ℝ) := by
      exact_mod_cast h
    rw [R_bridge] at h2
    simpa using h2
  have hRpos : (0 : ℝ) < ∏ q ∈ n.primeFactors, (q : ℝ) := by linarith
  have hR0 : (∏ q ∈ n.primeFactors, (q : ℝ)) ≠ 0 := ne_of_gt hRpos
  have hQnn : (0 : ℝ) ≤ (∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))) := by
    linarith [hQ2]
  by_contra hcon
  rw [not_exists] at hcon
  simp only [not_and, not_lt] at hcon
  have hcontra : ∀ p ∈ n.primeFactors,
      2 * n.primeFactors.card * (∏ q ∈ n.primeFactors, q)
        ≤ p ^ (n.factorization p + 1) :=
    fun p hp => hcon p hp
  have hBcast : ((((2 * n.primeFactors.card * (∏ q ∈ n.primeFactors, q) : ℕ))) : ℝ)
      = 2 * (n.primeFactors.card : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ)) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, R_bridge]
  have h2kR : (2 : ℝ)
      ≤ 2 * (n.primeFactors.card : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ)) := by
    have hk1R : (1 : ℝ) ≤ (n.primeFactors.card : ℝ) := by exact_mod_cast hk1
    have h := mul_le_mul hk1R hR2 (by linarith : (0 : ℝ) ≤ 2)
      (by linarith : (0 : ℝ) ≤ (n.primeFactors.card : ℝ))
    linarith
  have h2kR0 : (0 : ℝ)
      < 2 * (n.primeFactors.card : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ)) := by
    linarith [h2kR]
  have hfrac : (1 : ℝ) / (2 * (n.primeFactors.card : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ)))
      ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) h2kR
  have ha_nonneg : (0 : ℝ)
      ≤ 1 - 1 / (2 * (n.primeFactors.card : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ))) := by
    linarith [hfrac]
  have hbern : 1 - (n.primeFactors.card : ℝ)
        / (2 * (n.primeFactors.card : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ)))
      ≤ (1 - 1 / (2 * (n.primeFactors.card : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ))))
        ^ n.primeFactors.card := by
    have h := one_add_mul_le_pow
      (a := (-(1 / (2 * (n.primeFactors.card : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ))))))
      (n := n.primeFactors.card) (by linarith [hfrac] : (-2 : ℝ) ≤ _)
    have e1 : (1 : ℝ) + (n.primeFactors.card : ℝ)
          * (-(1 / (2 * (n.primeFactors.card : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ)))))
        = 1 - (n.primeFactors.card : ℝ)
          / (2 * (n.primeFactors.card : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ))) := by
      ring
    have e2 : (1 : ℝ)
          + (-(1 / (2 * (n.primeFactors.card : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ)))))
        = 1 - 1 / (2 * (n.primeFactors.card : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ))) := by
      ring
    rwa [e1, e2] at h
  have hkk : (n.primeFactors.card : ℝ)
        / (2 * (n.primeFactors.card : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ)))
      = 1 / (2 * (∏ q ∈ n.primeFactors, (q : ℝ))) := by
    have h2R0 : (2 : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ)) ≠ 0 :=
      mul_ne_zero (by norm_num) hR0
    have h2kR0' : (2 : ℝ) * (n.primeFactors.card : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ))
        ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hk0) hR0
    field_simp
  have h1 : (1 - 1 / (2 * (n.primeFactors.card : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ))))
        ^ n.primeFactors.card
      ≤ ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℝ) ^ (n.factorization p + 1))) := by
    apply prod_ge_const _ _ _ ha_nonneg
    intro p hp
    have hxc : ((((2 * n.primeFactors.card * (∏ q ∈ n.primeFactors, q) : ℕ))) : ℝ)
        ≤ ((((p ^ (n.factorization p + 1) : ℕ))) : ℝ) := by
      exact_mod_cast hcontra p hp
    rw [hBcast, Nat.cast_pow] at hxc
    have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hxp2 : (2 : ℝ) ≤ (p : ℝ) ^ (n.factorization p + 1) := by
      have hle : (p : ℝ) ≤ (p : ℝ) ^ (n.factorization p + 1) := by
        conv_lhs => rw [← pow_one (p : ℝ)]
        apply pow_le_pow_right₀ (by linarith) (by omega)
      linarith
    have hle : 1 / ((p : ℝ) ^ (n.factorization p + 1))
        ≤ 1 / (2 * (n.primeFactors.card : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ))) :=
      one_div_le_one_div_of_le h2kR0 (by linarith [hxc])
    linarith
  have hPlb : 1 - 1 / (2 * (∏ q ∈ n.primeFactors, (q : ℝ)))
      ≤ ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℝ) ^ (n.factorization p + 1))) := by
    calc 1 - 1 / (2 * (∏ q ∈ n.primeFactors, (q : ℝ)))
        = 1 - (n.primeFactors.card : ℝ)
          / (2 * (n.primeFactors.card : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ))) := by
          rw [hkk]
      _ ≤ (1 - 1 / (2 * (n.primeFactors.card : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ))))
          ^ n.primeFactors.card := hbern
      _ ≤ ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℝ) ^ (n.factorization p + 1))) := h1
  have hPnn : (0 : ℝ)
      ≤ ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℝ) ^ (n.factorization p + 1))) := by
    apply Finset.prod_nonneg
    intro p hp
    have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hx2 : (2 : ℝ) ≤ (p : ℝ) ^ (n.factorization p + 1) := by
      have hle : (p : ℝ) ≤ (p : ℝ) ^ (n.factorization p + 1) := by
        conv_lhs => rw [← pow_one (p : ℝ)]
        apply pow_le_pow_right₀ (by linarith) (by omega)
      linarith
    have hxpos : (0 : ℝ) < (p : ℝ) ^ (n.factorization p + 1) := by linarith
    have h1 : (1 : ℝ) / ((p : ℝ) ^ (n.factorization p + 1)) ≤ 1 := by
      rw [div_le_one hxpos]
      linarith [hx2]
    linarith
  have hAnn : (0 : ℝ)
      ≤ 2 * (∏ q ∈ n.primeFactors, (q : ℝ)) / ((∏ q ∈ n.primeFactors, (q : ℝ)) - 1) :=
    div_nonneg (by linarith [hR2]) (by linarith [hR2])
  have heq2 : (2 * (∏ q ∈ n.primeFactors, (q : ℝ)) - 1) / (2 * (∏ q ∈ n.primeFactors, (q : ℝ)))
      = 1 - 1 / (2 * (∏ q ∈ n.primeFactors, (q : ℝ))) := by
    have h2R0 : (2 : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ)) ≠ 0 :=
      mul_ne_zero (by norm_num) hR0
    field_simp
  have hPlb2 : (2 * (∏ q ∈ n.primeFactors, (q : ℝ)) - 1)
        / (2 * (∏ q ∈ n.primeFactors, (q : ℝ)))
      ≤ ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℝ) ^ (n.factorization p + 1))) := by
    rwa [heq2]
  have hPlb2nn : (0 : ℝ) ≤ (2 * (∏ q ∈ n.primeFactors, (q : ℝ)) - 1)
      / (2 * (∏ q ∈ n.primeFactors, (q : ℝ))) := by
    rw [heq2]
    have h2Rpos : (0 : ℝ) < 2 * (∏ q ∈ n.primeFactors, (q : ℝ)) := by linarith [hRpos]
    have h1 : (1 : ℝ) / (2 * (∏ q ∈ n.primeFactors, (q : ℝ))) ≤ 1 := by
      rw [div_le_one h2Rpos]
      linarith [hR2]
    linarith
  have hmul : (2 * (∏ q ∈ n.primeFactors, (q : ℝ)) / ((∏ q ∈ n.primeFactors, (q : ℝ)) - 1))
        * ((2 * (∏ q ∈ n.primeFactors, (q : ℝ)) - 1) / (2 * (∏ q ∈ n.primeFactors, (q : ℝ))))
      ≤ (∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)))
        * (∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℝ) ^ (n.factorization p + 1)))) :=
    mul_le_mul hA hPlb2 hPlb2nn hQnn
  have heq : (2 * (∏ q ∈ n.primeFactors, (q : ℝ)) / ((∏ q ∈ n.primeFactors, (q : ℝ)) - 1))
        * ((2 * (∏ q ∈ n.primeFactors, (q : ℝ)) - 1) / (2 * (∏ q ∈ n.primeFactors, (q : ℝ))))
      = (2 * (∏ q ∈ n.primeFactors, (q : ℝ)) - 1) / ((∏ q ∈ n.primeFactors, (q : ℝ)) - 1) := by
    have hRm10 : (∏ q ∈ n.primeFactors, (q : ℝ)) - 1 ≠ 0 := by
      have : (0 : ℝ) < (∏ q ∈ n.primeFactors, (q : ℝ)) - 1 := by linarith [hR2]
      linarith
    have h2R0 : (2 : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ)) ≠ 0 :=
      mul_ne_zero (by norm_num) hR0
    field_simp
  have hHQE : (2 * (∏ q ∈ n.primeFactors, (q : ℝ)) - 1) / ((∏ q ∈ n.primeFactors, (q : ℝ)) - 1)
      ≤ ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ) := by
    have hE := H_eq n hn
    rw [hE, ← heq]
    exact hmul
  have hRm1pos : (0 : ℝ) < (∏ q ∈ n.primeFactors, (q : ℝ)) - 1 := by linarith [hR2]
  have hH2 : (2 : ℝ) < ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ) := by
    have hE2 : (2 : ℝ) < (2 * (∏ q ∈ n.primeFactors, (q : ℝ)) - 1)
        / ((∏ q ∈ n.primeFactors, (q : ℝ)) - 1) := by
      rw [lt_div_iff₀ hRm1pos]
      linarith [hR2]
    linarith [hHQE]
  have hHdiv : ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ)
        / (((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ) - 2)
      ≤ 2 * (∏ q ∈ n.primeFactors, (q : ℝ)) - 1 := by
    have hH20 : (0 : ℝ) < ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ) - 2 := by
      linarith [hH2]
    rw [div_le_iff₀ hH20]
    have h1 : (2 : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ)) - 1
        ≤ ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ)
          * ((∏ q ∈ n.primeFactors, (q : ℝ)) - 1) := by
      have h2 := (div_le_iff₀ hRm1pos).mp hHQE
      linarith
    have huv : (1 : ℝ) ≤ (((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ) - 2)
        * ((∏ q ∈ n.primeFactors, (q : ℝ)) - 1) := by
      nlinarith [h1]
    nlinarith [huv]
  have hplt : ∀ p ∈ n.primeFactors, n.primeFactors.card < p := by
    intro p hp
    have hB := step2 n p hn hp hprim
    have hxc : ((((2 * n.primeFactors.card * (∏ q ∈ n.primeFactors, q) : ℕ))) : ℝ)
        ≤ ((((p ^ (n.factorization p + 1) : ℕ))) : ℝ) := by
      exact_mod_cast hcontra p hp
    rw [hBcast, Nat.cast_pow] at hxc
    have e3 : ((p : ℝ) ^ (n.factorization p + 1))
        < ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ) * (p : ℝ)
          / (((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ) - 2) := by
      apply (lt_div_iff₀ (by linarith [hH2] : (0 : ℝ)
        < ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ) - 2)).mpr
      linarith [hB]
    have e4 : ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ) * (p : ℝ)
          / (((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ) - 2)
        ≤ (p : ℝ) * (2 * (∏ q ∈ n.primeFactors, (q : ℝ)) - 1) := by
      have heqH : ((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ) * (p : ℝ)
            / (((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ) - 2)
          = (p : ℝ) * (((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ)
            / (((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ) - 2)) := by
        have hH20 : (((∑ d ∈ Nat.divisors n, d : ℕ) : ℝ) / (n : ℝ) - 2) ≠ 0 :=
          ne_of_gt (by linarith [hH2])
        field_simp
      rw [heqH]
      have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
      have hpposR : (0 : ℝ) < (p : ℝ) := by
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
        linarith
      exact mul_le_mul_of_nonneg_left hHdiv (le_of_lt hpposR)
    have e5 : (p : ℝ) * (2 * (∏ q ∈ n.primeFactors, (q : ℝ)) - 1)
        < 2 * (p : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ)) := by
      have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
      have hpposR : (0 : ℝ) < (p : ℝ) := by
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
        linarith
      linarith
    have e6 : 2 * (n.primeFactors.card : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ))
        < 2 * (p : ℝ) * (∏ q ∈ n.primeFactors, (q : ℝ)) :=
      lt_of_le_of_lt hxc (lt_of_lt_of_le e3 (le_trans e4 (le_of_lt e5)))
    have e7 : 2 * (n.primeFactors.card : ℝ) < 2 * (p : ℝ) :=
      lt_of_mul_lt_mul_right e6 (le_of_lt hRpos)
    have hltR : (n.primeFactors.card : ℝ) < (p : ℝ) := by linarith
    exact_mod_cast hltR
  have hcount := prod_div_sub_one_le n.primeFactors n.primeFactors.card hk1
    (fun p hp => by have h := hplt p hp; omega)
  have h2eq : (((((n.primeFactors.card + n.primeFactors.card : ℕ)))) : ℝ)
      / ((((n.primeFactors.card : ℕ))) : ℝ) = 2 := by
    have hkpos2 : (0 : ℝ) < (((n.primeFactors.card : ℕ)) : ℝ) := hkpos
    have hk00 : ((((n.primeFactors.card : ℕ))) : ℝ) ≠ 0 := ne_of_gt hkpos2
    rw [Nat.cast_add]
    field_simp
    ring
  rw [h2eq] at hcount
  linarith [hcount, hQ2]

end MetaMathlibExt
end
