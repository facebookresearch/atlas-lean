/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Prime.Int
import MathlibExt.NumberTheory.PrimeCounting.MertensThird

@[expose] public section

section
namespace MathlibExt.NumberTheory.ArithmeticFunction.GronwallSigmaLimsupWanted

/-!
# Gronwall's maximal order of σ
This file proves Gronwall's exact maximal-order theorem for the divisor-sum
function, `limsup σ(n) / (n log log n) = e^γ`. The main input is Mertens' third theorem,
`Nat.tendsto_prod_primesLE_inv_one_sub_inv_div_log`.
-/

/-- P(x) = ∏ (1 - 1/p)⁻¹ over p ∈ primesLE ⌊x⌋₊. P(x) ≥ 1 > 0. -/
private noncomputable def mertensP (x : ℝ) : ℝ :=
  ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹

-- Shared helpers.
/-- Each Mertens factor is at least 1 for prime `p`. -/
private theorem one_le_inv_one_sub_inv_prime (p : ℕ) (hp : p.Prime) :
    (1 : ℝ) ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpr : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hq1 : (p : ℝ)⁻¹ < 1 := by
    apply inv_lt_one_of_one_lt₀
    linarith
  have hq0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
  have h0 : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by linarith
  have hle : 1 - (p : ℝ)⁻¹ ≤ 1 := by linarith
  calc (1 : ℝ) = (1 : ℝ)⁻¹ := by norm_num
    _ ≤ (1 - (p : ℝ)⁻¹)⁻¹ := (inv_le_inv₀ zero_lt_one h0).mpr hle

/-- P(x) ≥ 1: each factor (1 - 1/p)⁻¹ ≥ 1 for prime p ≥ 2. -/
private theorem mertensP_ge_one (x : ℝ) : 1 ≤ mertensP x :=
  Finset.one_le_prod₀ fun p hp =>
    one_le_inv_one_sub_inv_prime p (Nat.prime_of_mem_primesLE hp)

/-- P(x) is positive. -/
private theorem mertensP_pos (x : ℝ) : 0 < mertensP x :=
  one_pos.trans_le (mertensP_ge_one x)

-- Mertens' third theorem.
private theorem tendsto_mertensP_div_log :
    Filter.Tendsto (fun x => mertensP x / Real.log x)
      Filter.atTop (nhds (Real.exp Real.eulerMascheroniConstant)) :=
  Nat.tendsto_prod_primesLE_inv_one_sub_inv_div_log

-- σ(n)/n upper bound by Mertens product.
/-- The Mertens factor as `1 + 1/(p-1)`. -/
private theorem inv_one_sub_inv_eq (p : ℕ) (hp : 2 ≤ p) :
    (1 - (p : ℝ)⁻¹)⁻¹ = 1 + 1 / ((p : ℝ) - 1) := by
  have hpr : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < (p : ℝ))
  have hp1 : ((p : ℝ) - 1) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < (p : ℝ) - 1)
  field_simp
  ring

/-- Product inequality over `ℝ` by induction. -/
private theorem prod_le_prod_of_nonneg {ι : Type*} {s : Finset ι} {f g : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  revert h0 h1
  refine Finset.induction_on s ?_ ?_
  · intro h0 h1
    simp
  · intro a t hat ih h0 h1
    rw [Finset.prod_insert hat, Finset.prod_insert hat]
    have h0t : ∀ i ∈ t, 0 ≤ f i :=
      fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have h1t : ∀ i ∈ t, f i ≤ g i :=
      fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have hag : f a ≤ g a := h1 a (Finset.mem_insert_self a t)
    have ha0 : 0 ≤ f a := h0 a (Finset.mem_insert_self a t)
    exact mul_le_mul hag (ih h0t h1t) (Finset.prod_nonneg h0t) (le_trans ha0 hag)

/-- A product of terms `≥ 1` is `≥ 1`, over `ℝ`. -/
private theorem one_le_prod_of_one_le {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro h
    simp
  · intro a t hat ih h
    rw [Finset.prod_insert hat]
    have ha : 1 ≤ f a := h a (Finset.mem_insert_self a t)
    have ht : ∀ i ∈ t, 1 ≤ f i := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have h1t : 1 ≤ ∏ i ∈ t, f i := ih ht
    calc (1 : ℝ) ≤ ∏ i ∈ t, f i := h1t
      _ ≤ f a * ∏ i ∈ t, f i :=
        le_mul_of_one_le_left (zero_le_one.trans h1t) ha

/-- Lower bound `r^#s ≤ ∏ f` over `ℝ` by induction. -/
private theorem pow_card_le_prod_of_le {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    {r : ℝ} (hr : 0 ≤ r) (h : ∀ i ∈ s, r ≤ f i) : r ^ s.card ≤ ∏ i ∈ s, f i := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro h
    simp
  · intro a t hat ih h
    rw [Finset.prod_insert hat, Finset.card_insert_of_notMem hat, pow_succ,
      mul_comm (f a)]
    have ht : ∀ i ∈ t, r ≤ f i := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha : r ≤ f a := h a (Finset.mem_insert_self a t)
    have h0t : ∀ i ∈ t, 0 ≤ f i := fun i hi => le_trans hr (ht i hi)
    exact mul_le_mul (ih ht) ha hr (Finset.prod_nonneg h0t)

/-- `σ₁(p^a)/p^a` is bounded by the Mertens factor (partial geometric sum). -/
private theorem sigma_prime_pow_div_le (p a : ℕ) (hp : p.Prime) :
    ((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ) / ((p ^ a : ℕ) : ℝ) ≤
      (1 - (p : ℝ)⁻¹)⁻¹ := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  rw [div_eq_mul_inv, Finset.sum_mul]
  have hre : ∀ k ∈ Finset.range (a + 1),
      (p : ℝ) ^ k * ((p : ℝ) ^ a)⁻¹ = ((p : ℝ)⁻¹) ^ (a - k) := by
    intro k hk
    have hka : k ≤ a := by
      have hmem := Finset.mem_range.mp hk
      omega
    have hp0 : (p : ℝ) ≠ 0 := by
      have hne : p ≠ 0 := ne_of_gt hp.pos
      exact_mod_cast hne
    have hxk : (p : ℝ) ^ k ≠ 0 := pow_ne_zero _ hp0
    have hpa : (p : ℝ) ^ a = (p : ℝ) ^ k * (p : ℝ) ^ (a - k) := by
      rw [← pow_add, Nat.add_sub_cancel' hka]
    rw [hpa, mul_inv, ← mul_assoc, mul_inv_cancel₀ hxk, one_mul, inv_pow]
  rw [Finset.sum_congr rfl hre]
  have hreflect := Finset.sum_range_reflect (fun j => ((p : ℝ)⁻¹) ^ j) (a + 1)
  simp only [Nat.add_sub_cancel] at hreflect
  rw [hreflect]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have h1p : (p : ℝ)⁻¹ < 1 := by
    apply inv_lt_one_of_one_lt₀
    linarith
  have h0p : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
  have hgeom : HasSum (fun j : ℕ => ((p : ℝ)⁻¹) ^ j) (1 - (p : ℝ)⁻¹)⁻¹ :=
    hasSum_geometric_of_lt_one h0p h1p
  exact sum_le_hasSum (Finset.range (a + 1))
    (fun j _ => pow_nonneg h0p j) hgeom

/-- Upper bound `∏ f ≤ r^#s` over `ℝ` by induction. -/
private theorem prod_le_pow_card_of_le {ι : Type*} {s : Finset ι}
    {f : ι → ℝ} {r : ℝ} (h0 : ∀ i ∈ s, 0 ≤ f i) (hr : 0 ≤ r)
    (h : ∀ i ∈ s, f i ≤ r) : ∏ i ∈ s, f i ≤ r ^ s.card := by
  classical
  revert h0 h
  refine Finset.induction_on s ?_ ?_
  · intro h0 h
    simp
  · intro a t hat ih h0 h
    rw [Finset.prod_insert hat, Finset.card_insert_of_notMem hat, pow_succ']
    have h0t : ∀ i ∈ t, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have ht : ∀ i ∈ t, f i ≤ r := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha : f a ≤ r := h a (Finset.mem_insert_self a t)
    exact mul_le_mul ha (ih h0t ht) (Finset.prod_nonneg h0t) hr

private theorem sigma_div_self_le_mertensP_mul_exp (n : ℕ) (hn : 1 ≤ n) (y : ℝ) (hy : 2 ≤ y) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ) ≤
      mertensP y * Real.exp (Real.log n / ((y - 1) * Real.log y)) := by
  have hn0 : n ≠ 0 := by omega
  have hsigma :=
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
      (k := 1) (n := n) hn0
  have hn_eq : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    have h := Nat.prod_factorization_pow_eq_self hn0
    rwa [Nat.prod_factorization_eq_prod_primeFactors] at h
  have hfac : ∀ p ∈ n.primeFactors,
      ((∑ i ∈ Finset.range (n.factorization p + 1), p ^ (i * 1) : ℕ) : ℝ) /
        ((p ^ n.factorization p : ℕ) : ℝ) ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
    intro p hpmem
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hS : (∑ i ∈ Finset.range (n.factorization p + 1), p ^ (i * 1)) =
        ArithmeticFunction.sigma 1 (p ^ n.factorization p) := by
      rw [ArithmeticFunction.sigma_one_apply_prime_pow hpp]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_one]
    rw [hS]
    exact sigma_prime_pow_div_le p _ hpp
  have hσ_cast : ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) =
      ∏ p ∈ n.primeFactors,
        ((∑ i ∈ Finset.range (n.factorization p + 1), p ^ (i * 1) : ℕ) : ℝ) := by
    conv_lhs => rw [hsigma]
    rw [Nat.cast_prod]
  have hn_cast : (n : ℝ) =
      ∏ p ∈ n.primeFactors, ((p ^ n.factorization p : ℕ) : ℝ) := by
    conv_lhs => rw [← hn_eq]
    rw [Nat.cast_prod]
  conv_lhs => rw [hσ_cast, hn_cast, ← Finset.prod_div_distrib]
  have hstep1 : ∏ p ∈ n.primeFactors,
        (((∑ i ∈ Finset.range (n.factorization p + 1), p ^ (i * 1) : ℕ) : ℝ) /
          ((p ^ n.factorization p : ℕ) : ℝ)) ≤
      ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ :=
    prod_le_prod_of_nonneg
      (fun p _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hfac
  refine le_trans hstep1 ?_
  have hsplit := Finset.prod_filter_mul_prod_filter_not n.primeFactors
    (fun p => p ≤ ⌊y⌋₊) (fun p => (1 - (p : ℝ)⁻¹)⁻¹)
  rw [← hsplit]
  have hsmall : ∏ p ∈ n.primeFactors.filter (fun p => p ≤ ⌊y⌋₊),
      (1 - (p : ℝ)⁻¹)⁻¹ ≤ mertensP y := by
    have hsub : n.primeFactors.filter (fun p => p ≤ ⌊y⌋₊) ⊆
        Nat.primesLE ⌊y⌋₊ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Nat.mem_primesLE]
      exact ⟨hp.2, Nat.prime_of_mem_primeFactors hp.1⟩
    have h1 : ∀ p ∈ Nat.primesLE ⌊y⌋₊,
        p ∉ n.primeFactors.filter (fun p => p ≤ ⌊y⌋₊) →
        1 ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
      intro p hp _
      exact one_le_inv_one_sub_inv_prime p (Nat.prime_of_mem_primesLE hp)
    have hdecomp : (∏ p ∈ Nat.primesLE ⌊y⌋₊ \
        n.primeFactors.filter (fun p => p ≤ ⌊y⌋₊), (1 - (p : ℝ)⁻¹)⁻¹) *
        (∏ p ∈ n.primeFactors.filter (fun p => p ≤ ⌊y⌋₊),
          (1 - (p : ℝ)⁻¹)⁻¹) =
        ∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹)⁻¹ :=
      Finset.prod_sdiff hsub
    have hdiff1 : 1 ≤ ∏ p ∈ Nat.primesLE ⌊y⌋₊ \
        n.primeFactors.filter (fun p => p ≤ ⌊y⌋₊), (1 - (p : ℝ)⁻¹)⁻¹ := by
      apply one_le_prod_of_one_le
      intro p hp
      rw [Finset.mem_sdiff] at hp
      exact h1 p hp.1 hp.2
    have hfilter1 : ∀ p ∈ n.primeFactors.filter (fun p => p ≤ ⌊y⌋₊),
        (1 : ℝ) ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact one_le_inv_one_sub_inv_prime p
        (Nat.prime_of_mem_primeFactors hp.1)
    have hnonneg : 0 ≤ ∏ p ∈ n.primeFactors.filter (fun p => p ≤ ⌊y⌋₊),
        (1 - (p : ℝ)⁻¹)⁻¹ :=
      Finset.prod_nonneg (fun p hp => le_trans zero_le_one (hfilter1 p hp))
    have hle : ∏ p ∈ n.primeFactors.filter (fun p => p ≤ ⌊y⌋₊),
        (1 - (p : ℝ)⁻¹)⁻¹ ≤ ∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹)⁻¹ := by
      rw [← hdecomp]
      exact le_mul_of_one_le_left hnonneg hdiff1
    have hP : mertensP y = ∏ p ∈ Nat.primesLE ⌊y⌋₊, (1 - (p : ℝ)⁻¹)⁻¹ := rfl
    rwa [hP]
  have hlarge : ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊),
      (1 - (p : ℝ)⁻¹)⁻¹ ≤
      Real.exp (Real.log n / ((y - 1) * Real.log y)) := by
    have hplt : ∀ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊),
        y < (p : ℝ) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have h1 : ⌊y⌋₊ < p := Nat.lt_of_not_ge hp.2
      have h3 : y - 1 < (⌊y⌋₊ : ℝ) := by
        have hfl := Nat.lt_floor_add_one y
        linarith
      have h4 : (⌊y⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by
        have h5 : ⌊y⌋₊ + 1 ≤ p := by omega
        exact_mod_cast h5
      linarith
    have hfac_le : ∀ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊),
        (1 - (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (1 / (y - 1)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
      have hp2 : 2 ≤ p := hpp.two_le
      have hpy : y < (p : ℝ) := hplt p (Finset.mem_filter.mpr hp)
      rw [inv_one_sub_inv_eq p hp2]
      have h1 : (1 : ℝ) + 1 / ((p : ℝ) - 1) ≤
          Real.exp (1 / ((p : ℝ) - 1)) := by
        rw [add_comm (1 : ℝ)]
        exact Real.add_one_le_exp _
      have h2 : (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 / (y - 1) := by
        apply one_div_le_one_div_of_le
        · linarith
        · linarith
      calc (1 : ℝ) + 1 / ((p : ℝ) - 1) ≤ Real.exp (1 / ((p : ℝ) - 1)) := h1
        _ ≤ Real.exp (1 / (y - 1)) := Real.exp_le_exp.mpr h2
    have h0fac : ∀ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊),
        0 ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have h1 := one_le_inv_one_sub_inv_prime p
        (Nat.prime_of_mem_primeFactors hp.1)
      linarith
    have hexp0 : (0 : ℝ) ≤ Real.exp (1 / (y - 1)) := (Real.exp_pos _).le
    have hprod_pow : ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊),
        (1 - (p : ℝ)⁻¹)⁻¹ ≤
        Real.exp (1 / (y - 1)) ^
          (n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card :=
      prod_le_pow_card_of_le h0fac hexp0 hfac_le
    have hy0 : (0 : ℝ) < y := by linarith
    have hpow_le : y ^ (n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card ≤
        ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊), (p : ℝ) :=
      pow_card_le_prod_of_le hy0.le (fun p hp => le_of_lt (hplt p hp))
    have hle1 : ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊), (p : ℝ) ≤
        ∏ p ∈ n.primeFactors, (p : ℝ) := by
      have hsubf : n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊) ⊆
          n.primeFactors :=
        Finset.filter_subset _ _
      have h1 : ∀ p ∈ n.primeFactors,
          p ∉ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊) →
          (1 : ℝ) ≤ (p : ℝ) := by
        intro p hpmem _
        have h2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hpmem).two_le
        have h2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
        linarith
      have hdecompf : (∏ p ∈ n.primeFactors \
          n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊), (p : ℝ)) *
          (∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊), (p : ℝ)) =
          ∏ p ∈ n.primeFactors, (p : ℝ) :=
        Finset.prod_sdiff hsubf
      have hdiff1 : 1 ≤ ∏ p ∈ n.primeFactors \
          n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊), (p : ℝ) := by
        apply one_le_prod_of_one_le
        intro p hp
        rw [Finset.mem_sdiff] at hp
        exact h1 p hp.1 hp.2
      have hnonneg : 0 ≤ ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊),
          (p : ℝ) :=
        Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p)
      rw [← hdecompf]
      exact le_mul_of_one_le_left hnonneg hdiff1
    have hle2 : ∏ p ∈ n.primeFactors, (p : ℝ) ≤ (n : ℝ) := by
      have hdvd := Nat.prod_primeFactors_dvd n
      have hle_nat : ∏ p ∈ n.primeFactors, p ≤ n :=
        Nat.le_of_dvd (by omega : 0 < n) hdvd
      have hcast : ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) ≤ (n : ℝ) :=
        Nat.cast_le.mpr hle_nat
      rwa [Nat.cast_prod] at hcast
    have hlog : ((n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card : ℝ) *
        Real.log y ≤ Real.log n := by
      have hpos1 : (0 : ℝ) <
          y ^ (n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card :=
        pow_pos hy0 _
      have hpos2 : (0 : ℝ) <
          ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊), (p : ℝ) := by
        apply Finset.prod_pos
        intro p hp
        rw [Finset.mem_filter] at hp
        have hpos : 0 < p := (Nat.prime_of_mem_primeFactors hp.1).pos
        exact_mod_cast hpos
      have hpos3 : (0 : ℝ) < ∏ p ∈ n.primeFactors, (p : ℝ) := by
        apply Finset.prod_pos
        intro p hpmem
        have hpos : 0 < p := (Nat.prime_of_mem_primeFactors hpmem).pos
        exact_mod_cast hpos
      calc ((n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card : ℝ) *
            Real.log y
          = Real.log (y ^ (n.primeFactors.filter
            (fun p => ¬ p ≤ ⌊y⌋₊)).card) := by rw [Real.log_pow]
        _ ≤ Real.log (∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊),
            (p : ℝ)) := Real.log_le_log hpos1 hpow_le
        _ ≤ Real.log (∏ p ∈ n.primeFactors, (p : ℝ)) :=
            Real.log_le_log hpos2 hle1
        _ ≤ Real.log n := Real.log_le_log hpos3 hle2
    have hy1 : (0 : ℝ) < y - 1 := by linarith
    have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith : (1 : ℝ) < y)
    have hexp_eq : Real.exp (1 / (y - 1)) ^
        (n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card =
        Real.exp (((n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card : ℝ) /
          (y - 1)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hfrac : ((n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card : ℝ) /
        (y - 1) ≤ Real.log n / ((y - 1) * Real.log y) := by
      have hpos : (0 : ℝ) < (y - 1) * Real.log y := mul_pos hy1 hlogy
      rw [div_le_div_iff₀ hy1 hpos]
      have hmul := mul_le_mul_of_nonneg_right hlog hy1.le
      have heq : ((n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card : ℝ) *
          ((y - 1) * Real.log y) =
          (((n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card : ℝ) *
            Real.log y) * (y - 1) := by ring
      rwa [heq]
    calc ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊),
          (1 - (p : ℝ)⁻¹)⁻¹
        ≤ Real.exp (1 / (y - 1)) ^
          (n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card := hprod_pow
      _ = Real.exp (((n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊)).card : ℝ) /
          (y - 1)) := hexp_eq
      _ ≤ Real.exp (Real.log n / ((y - 1) * Real.log y)) :=
          Real.exp_le_exp.mpr hfrac
  have hlarge0 : 0 ≤ ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ ⌊y⌋₊),
      (1 - (p : ℝ)⁻¹)⁻¹ := by
    apply Finset.prod_nonneg
    intro p hp
    rw [Finset.mem_filter] at hp
    have h1 := one_le_inv_one_sub_inv_prime p
      (Nat.prime_of_mem_primeFactors hp.1)
    linarith
  have hP0 : 0 ≤ mertensP y := le_trans zero_le_one (mertensP_ge_one y)
  exact mul_le_mul hsmall hlarge hlarge0 hP0

-- Witness family lower bound.
/-- The witness `n(m,a)` is `≥ 1` and `log n(m,a) = a * θ(m)`. -/
private theorem prod_primesLE_pow_ge_one_log (m a : ℕ) :
    1 ≤ ∏ p ∈ Nat.primesLE m, p ^ a ∧
      Real.log ((∏ p ∈ Nat.primesLE m, p ^ a : ℕ) : ℝ) =
        (a : ℝ) * Chebyshev.theta (m : ℝ) := by
  refine ⟨?_, ?_⟩
  · apply Finset.one_le_prod
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    exact one_le_pow₀ hpp.one_lt.le
  · have hne : ∀ p ∈ Nat.primesLE m, (((p ^ a : ℕ)) : ℝ) ≠ 0 := by
      intro p hp
      have hpp := Nat.prime_of_mem_primesLE hp
      have hpa : p ^ a ≠ 0 := by
        apply pow_ne_zero
        exact ne_of_gt hpp.pos
      exact Nat.cast_ne_zero.mpr hpa
    rw [Nat.cast_prod, Real.log_prod hne]
    have hterm : ∀ p ∈ Nat.primesLE m,
        Real.log (((p ^ a : ℕ)) : ℝ) = (a : ℝ) * Real.log (p : ℝ) := by
      intro p hp
      rw [Nat.cast_pow, Real.log_pow]
    rw [Finset.sum_congr rfl hterm, Chebyshev.theta_eq_sum_primesLE_log,
      ← Finset.mul_sum]

/-- Bridge between `(2⁻¹)^(a+1)` and the rpow `2^(-(a+1))`. -/
private theorem inv_pow_eq_rpow_neg (a : ℕ) :
    ((2 : ℝ)⁻¹) ^ (a + 1) = (2 : ℝ) ^ (-((a : ℝ) + 1)) := by
  have hrw : (2 : ℝ) ^ (-((a : ℝ) + 1)) = (((2 : ℝ) ^ (a + 1))⁻¹) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
      Real.rpow_natCast, pow_succ']
    ring
  rw [hrw, inv_pow]

/-- `σ₁(p^a)/p^a` equals `(1 - p^{-(a+1)})(1-1/p)⁻¹` (geometric sum). -/
private theorem sigma_prime_pow_div_eq (p a : ℕ) (hp : p.Prime) :
    ((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ) / ((p ^ a : ℕ) : ℝ) =
      (1 - ((p : ℝ)⁻¹) ^ (a + 1)) * (1 - (p : ℝ)⁻¹)⁻¹ := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  rw [div_eq_mul_inv, Finset.sum_mul]
  have hre : ∀ k ∈ Finset.range (a + 1),
      (p : ℝ) ^ k * ((p : ℝ) ^ a)⁻¹ = ((p : ℝ)⁻¹) ^ (a - k) := by
    intro k hk
    have hka : k ≤ a := by
      have hmem := Finset.mem_range.mp hk
      omega
    have hp0 : (p : ℝ) ≠ 0 := by
      have hne : p ≠ 0 := ne_of_gt hp.pos
      exact_mod_cast hne
    have hxk : (p : ℝ) ^ k ≠ 0 := pow_ne_zero _ hp0
    have hpa : (p : ℝ) ^ a = (p : ℝ) ^ k * (p : ℝ) ^ (a - k) := by
      rw [← pow_add, Nat.add_sub_cancel' hka]
    rw [hpa, mul_inv, ← mul_assoc, mul_inv_cancel₀ hxk, one_mul, inv_pow]
  rw [Finset.sum_congr rfl hre]
  have hreflect := Finset.sum_range_reflect (fun j => ((p : ℝ)⁻¹) ^ j) (a + 1)
  simp only [Nat.add_sub_cancel] at hreflect
  rw [hreflect]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hr1 : (p : ℝ)⁻¹ < 1 := by
    apply inv_lt_one_of_one_lt₀
    linarith
  have hne1 : (p : ℝ)⁻¹ - 1 ≠ 0 := ne_of_lt (by linarith : (p : ℝ)⁻¹ - 1 < 0)
  have hne2 : (1 : ℝ) - (p : ℝ)⁻¹ ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 1 - (p : ℝ)⁻¹)
  have hgeom := geom_sum_mul ((p : ℝ)⁻¹) (a + 1)
  have hdiv : ∑ j ∈ Finset.range (a + 1), ((p : ℝ)⁻¹) ^ j =
      (((p : ℝ)⁻¹) ^ (a + 1) - 1) / ((p : ℝ)⁻¹ - 1) := by
    rw [eq_div_iff hne1]
    exact hgeom
  rw [hdiv]
  have h3 : (1 - (p : ℝ)⁻¹)⁻¹ = -(((p : ℝ)⁻¹ - 1)⁻¹) := by
    rw [show (1 : ℝ) - (p : ℝ)⁻¹ = -((p : ℝ)⁻¹ - 1) by ring, inv_neg]
  rw [h3, div_eq_mul_inv]
  ring

/-- Abundancy lower bound for the witness family. -/
private theorem sigma_div_prod_primesLE_pow_ge (m a : ℕ) :
    mertensP (m : ℝ) * (1 - (m : ℝ) * (2 : ℝ) ^ (-((a : ℝ) + 1))) ≤
      ((ArithmeticFunction.sigma 1 (∏ p ∈ Nat.primesLE m, p ^ a) : ℕ) : ℝ) /
        ((∏ p ∈ Nat.primesLE m, p ^ a : ℕ) : ℝ) := by
  have hpair : ((Nat.primesLE m : Finset ℕ) : Set ℕ).Pairwise
      (Function.onFun Nat.Coprime fun p => p ^ a) := by
    intro x hx y hy hxy
    have hxp : x.Prime := Nat.prime_of_mem_primesLE (Finset.mem_coe.mp hx)
    have hyp : y.Prime := Nat.prime_of_mem_primesLE (Finset.mem_coe.mp hy)
    have hcop : Nat.Coprime x y := (Nat.coprime_primes hxp hyp).mpr hxy
    change Nat.Coprime (x ^ a) (y ^ a)
    rcases eq_or_ne a 0 with rfl | ha
    · simp only [pow_zero]
      exact Nat.coprime_one_left 1
    · have ha0 : 0 < a := Nat.pos_of_ne_zero ha
      rw [Nat.coprime_pow_left_iff ha0, Nat.coprime_pow_right_iff ha0]
      exact hcop
  have hσ_prod : ArithmeticFunction.sigma 1 (∏ p ∈ Nat.primesLE m, p ^ a) =
      ∏ p ∈ Nat.primesLE m, ArithmeticFunction.sigma 1 (p ^ a) :=
    ArithmeticFunction.isMultiplicative_sigma.map_prod _ _ hpair
  have hdiv2 : ((ArithmeticFunction.sigma 1 (∏ p ∈ Nat.primesLE m, p ^ a) : ℕ) : ℝ) /
        ((∏ p ∈ Nat.primesLE m, p ^ a : ℕ) : ℝ) =
        ∏ p ∈ Nat.primesLE m,
          (((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ) /
            ((p ^ a : ℕ) : ℝ)) := by
    rw [hσ_prod]
    simp only [Nat.cast_prod]
    rw [← Finset.prod_div_distrib]
  have hδ0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-((a : ℝ) + 1)) := by
    rw [← inv_pow_eq_rpow_neg]
    positivity
  have hδ10 : (2 : ℝ) ^ (-((a : ℝ) + 1)) ≤ 1 := by
    rw [← inv_pow_eq_rpow_neg]
    exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ ≤ 1)
  have hfac_ge : ∀ p ∈ Nat.primesLE m,
      (1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) * (1 - (p : ℝ)⁻¹)⁻¹ ≤
        ((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ) / ((p ^ a : ℕ) : ℝ) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
    rw [sigma_prime_pow_div_eq p a hpp]
    have hδ : ((p : ℝ)⁻¹) ^ (a + 1) ≤ (2 : ℝ) ^ (-((a : ℝ) + 1)) := by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hle_r : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
        (inv_le_inv₀ (by linarith : (0 : ℝ) < (p : ℝ))
          (by norm_num : (0 : ℝ) < 2)).mpr hp2
      have h0p : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
      have h1 : ((p : ℝ)⁻¹) ^ (a + 1) ≤ ((2 : ℝ)⁻¹) ^ (a + 1) :=
        pow_le_pow_left₀ h0p hle_r (a + 1)
      rwa [inv_pow_eq_rpow_neg] at h1
    have hnonneg : (0 : ℝ) ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
      have h1 := one_le_inv_one_sub_inv_prime p hpp
      linarith
    have hle : 1 - (2 : ℝ) ^ (-((a : ℝ) + 1)) ≤ 1 - ((p : ℝ)⁻¹) ^ (a + 1) := by
      linarith [hδ]
    exact mul_le_mul_of_nonneg_right hle hnonneg
  have hge1 : ∏ p ∈ Nat.primesLE m,
        ((1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) * (1 - (p : ℝ)⁻¹)⁻¹) ≤
      ∏ p ∈ Nat.primesLE m,
        (((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ) /
          ((p ^ a : ℕ) : ℝ)) :=
    prod_le_prod_of_nonneg (fun p hp => by
      have hpp := Nat.prime_of_mem_primesLE hp
      have h1 := one_le_inv_one_sub_inv_prime p hpp
      have h10 : (0 : ℝ) ≤ 1 - (2 : ℝ) ^ (-((a : ℝ) + 1)) := by
        linarith [hδ10]
      exact mul_nonneg h10 (by linarith)) hfac_ge
  have hPm : mertensP (m : ℝ) = ∏ p ∈ Nat.primesLE m, (1 - (p : ℝ)⁻¹)⁻¹ := by
    unfold mertensP
    rw [Nat.floor_natCast]
  have hprod_split : ∏ p ∈ Nat.primesLE m,
        ((1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) * (1 - (p : ℝ)⁻¹)⁻¹) =
        ((1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) ^ (Nat.primesLE m).card) *
          mertensP (m : ℝ) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, hPm]
  have hbern : ∀ n : ℕ, 1 - (n : ℝ) * (2 : ℝ) ^ (-((a : ℝ) + 1)) ≤
      (1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) ^ n := by
    intro n
    have h := one_add_mul_le_pow (a := -((2 : ℝ) ^ (-((a : ℝ) + 1))))
      (show (-2 : ℝ) ≤ -((2 : ℝ) ^ (-((a : ℝ) + 1))) from by
        linarith [hδ0, hδ10]) n
    have e1 : (1 : ℝ) - (n : ℝ) * (2 : ℝ) ^ (-((a : ℝ) + 1)) =
        1 + (n : ℝ) * -((2 : ℝ) ^ (-((a : ℝ) + 1))) := by ring
    have e2 : ((1 : ℝ) - (2 : ℝ) ^ (-((a : ℝ) + 1))) ^ n =
        (1 + -((2 : ℝ) ^ (-((a : ℝ) + 1)))) ^ n := by rw [sub_eq_add_neg]
    rwa [e1, e2]
  have hcard : (Nat.primesLE m).card ≤ m := by
    have hsub : Nat.primesLE m ⊆ Finset.Icc 1 m := by
      intro p hp
      have hpp := Nat.prime_of_mem_primesLE hp
      rw [Nat.mem_primesLE] at hp
      rw [Finset.mem_Icc]
      exact ⟨hpp.one_lt.le, hp.1⟩
    calc (Nat.primesLE m).card ≤ (Finset.Icc 1 m).card :=
          Finset.card_le_card hsub
      _ = m := by rw [Nat.card_Icc]; omega
  have hbern_m : 1 - (m : ℝ) * (2 : ℝ) ^ (-((a : ℝ) + 1)) ≤
      (1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) ^ (Nat.primesLE m).card := by
    have h1 := hbern (Nat.primesLE m).card
    have hcardR : (((Nat.primesLE m).card : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hcard
    have hmul : ((Nat.primesLE m).card : ℝ) * (2 : ℝ) ^ (-((a : ℝ) + 1)) ≤
        (m : ℝ) * (2 : ℝ) ^ (-((a : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hcardR hδ0
    linarith [h1, hmul]
  have hP0 : 0 ≤ mertensP (m : ℝ) := (mertensP_pos _).le
  have hmul_le : mertensP (m : ℝ) * (1 - (m : ℝ) * (2 : ℝ) ^ (-((a : ℝ) + 1))) ≤
      mertensP (m : ℝ) *
        ((1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) ^ (Nat.primesLE m).card) :=
    mul_le_mul_of_nonneg_left hbern_m hP0
  calc mertensP (m : ℝ) * (1 - (m : ℝ) * (2 : ℝ) ^ (-((a : ℝ) + 1)))
      ≤ mertensP (m : ℝ) *
        ((1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) ^ (Nat.primesLE m).card) := hmul_le
    _ = ((1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) ^ (Nat.primesLE m).card) *
        mertensP (m : ℝ) := mul_comm _ _
    _ = ∏ p ∈ Nat.primesLE m,
        ((1 - (2 : ℝ) ^ (-((a : ℝ) + 1))) * (1 - (p : ℝ)⁻¹)⁻¹) :=
        hprod_split.symm
    _ ≤ ∏ p ∈ Nat.primesLE m,
        (((ArithmeticFunction.sigma 1 (p ^ a) : ℕ) : ℝ) /
          ((p ^ a : ℕ) : ℝ)) := hge1
    _ = ((ArithmeticFunction.sigma 1 (∏ p ∈ Nat.primesLE m, p ^ a) : ℕ) : ℝ) /
        ((∏ p ∈ Nat.primesLE m, p ^ a : ℕ) : ℝ) := hdiv2.symm

/-- `log n → ∞` along naturals. -/
private theorem tendsto_log_natCast_atTop : Filter.Tendsto
    (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `2 ≤ log 16`, since `log 16 = 4 log 2`. -/
private theorem two_le_log_sixteen : (2 : ℝ) ≤ Real.log 16 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    have h16e : (16 : ℝ) = 2 ^ 4 := by norm_num
    rw [h16e, Real.log_pow]
    norm_num
  linarith

/-- The error exponent `log n / ((log n - 1) * log log n) -> 0`. -/
private theorem tendsto_gronwall_err : Filter.Tendsto
    (fun n : ℕ => Real.log (n : ℝ) /
      ((Real.log (n : ℝ) - 1) * Real.log (Real.log (n : ℝ))))
    Filter.atTop (nhds 0) := by
  have htop : Filter.Tendsto (fun n : ℕ => 2 / Real.log (Real.log (n : ℝ)))
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop
      (Real.tendsto_log_atTop.comp tendsto_log_natCast_atTop) 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 16] with n hn
    have hn16 : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hy2 : (2 : ℝ) ≤ Real.log (n : ℝ) :=
      le_trans two_le_log_sixteen (Real.log_le_log (by norm_num) hn16)
    have hlogy : (0 : ℝ) < Real.log (Real.log (n : ℝ)) :=
      Real.log_pos (by linarith)
    have hden : (0 : ℝ) ≤
        (Real.log (n : ℝ) - 1) * Real.log (Real.log (n : ℝ)) :=
      mul_nonneg (by linarith) hlogy.le
    exact div_nonneg (Real.log_nonneg (by linarith)) hden
  · filter_upwards [Filter.eventually_ge_atTop 16] with n hn
    have hn16 : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hy2 : (2 : ℝ) ≤ Real.log (n : ℝ) :=
      le_trans two_le_log_sixteen (Real.log_le_log (by norm_num) hn16)
    have hlogy : (0 : ℝ) < Real.log (Real.log (n : ℝ)) :=
      Real.log_pos (by linarith)
    have h1 : Real.log (n : ℝ) / (Real.log (n : ℝ) - 1) ≤ 2 := by
      rw [div_le_iff₀ (show (0 : ℝ) < Real.log (n : ℝ) - 1 by linarith)]
      linarith
    have h2 : Real.log (n : ℝ) /
        ((Real.log (n : ℝ) - 1) * Real.log (Real.log (n : ℝ))) =
        (Real.log (n : ℝ) / (Real.log (n : ℝ) - 1)) /
          Real.log (Real.log (n : ℝ)) := by
      rw [div_div]
    rw [h2, div_le_div_iff_of_pos_right hlogy]
    exact h1

-- Eventual upper bound for Gronwall's f.
private theorem gronwall_eventually_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
        ((n : ℝ) * Real.log (Real.log n)) ≤
        Real.exp Real.eulerMascheroniConstant + ε := by
  have hP : Filter.Tendsto
      (fun n : ℕ => mertensP (Real.log n) / Real.log (Real.log n))
      Filter.atTop (nhds (Real.exp Real.eulerMascheroniConstant)) :=
    tendsto_mertensP_div_log.comp tendsto_log_natCast_atTop
  have hexp : Filter.Tendsto
      (fun n : ℕ => Real.exp (Real.log (n : ℝ) /
        ((Real.log (n : ℝ) - 1) * Real.log (Real.log (n : ℝ)))))
      Filter.atTop (nhds 1) := by
    have h := (Real.continuous_exp.tendsto 0).comp tendsto_gronwall_err
    rwa [Real.exp_zero] at h
  have hprod := hP.mul hexp
  rw [mul_one] at hprod
  have hev := hprod.eventually_le_const
    (show Real.exp Real.eulerMascheroniConstant <
      Real.exp Real.eulerMascheroniConstant + ε by linarith)
  filter_upwards [hev, Filter.eventually_ge_atTop 16] with n hle hn16
  have hn16r : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn16
  have hn1 : 1 ≤ n := by omega
  have hy2 : (2 : ℝ) ≤ Real.log (n : ℝ) :=
    le_trans two_le_log_sixteen (Real.log_le_log (by norm_num) hn16r)
  have hlogy : (0 : ℝ) < Real.log (Real.log (n : ℝ)) :=
    Real.log_pos (by linarith)
  have hN11 := sigma_div_self_le_mertensP_mul_exp n hn1 (Real.log n) hy2
  have hdiv : ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
      ((n : ℝ) * Real.log (Real.log n)) =
      (((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ)) /
        Real.log (Real.log n) := by
    rw [div_div]
  rw [hdiv]
  have hle2 : ((((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ)) /
      Real.log (Real.log n)) ≤
      ((mertensP (Real.log n) *
        Real.exp (Real.log (n : ℝ) /
          ((Real.log (n : ℝ) - 1) * Real.log (Real.log (n : ℝ))))) /
        Real.log (Real.log n)) := by
    rw [div_le_div_iff_of_pos_right hlogy]
    exact hN11
  have hmul : (mertensP (Real.log n) *
      Real.exp (Real.log (n : ℝ) /
        ((Real.log (n : ℝ) - 1) * Real.log (Real.log (n : ℝ))))) /
      Real.log (Real.log n) =
      (mertensP (Real.log n) / Real.log (Real.log n)) *
        Real.exp (Real.log (n : ℝ) /
          ((Real.log (n : ℝ) - 1) * Real.log (Real.log (n : ℝ)))) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [hmul] at hle2
  exact hle2.trans hle

/-- Witness `n_k = prod_{p <= 2^k} p^{2k}`. -/
private noncomputable def gronwallWit (k : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesLE (2 ^ k), p ^ (2 * k)

/-- `2` is in `primesLE (2^k)` for `k >= 1`. -/
private theorem gronwallWit_mem_two (k : ℕ) (hk : 1 ≤ k) :
    2 ∈ Nat.primesLE (2 ^ k) := by
  rw [Nat.mem_primesLE]
  refine ⟨?_, Nat.prime_two⟩
  calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk

/-- `2^{2k} <= n_k` for `k >= 1`, by `single_le_prod`. -/
private theorem gronwallWit_pow_le (k : ℕ) (hk : 1 ≤ k) :
    2 ^ (2 * k) ≤ gronwallWit k := by
  unfold gronwallWit
  exact Finset.single_le_prod
    (fun i hi => Nat.one_le_pow _ _ (Nat.prime_of_mem_primesLE hi).pos)
    (gronwallWit_mem_two k hk)

/-- Every witness is at least `1`. -/
private theorem gronwallWit_ge_one (k : ℕ) : 1 ≤ gronwallWit k := by
  unfold gronwallWit
  exact Finset.one_le_prod
    (fun i hi => Nat.one_le_pow _ _ (Nat.prime_of_mem_primesLE hi).pos)

/-- `(2^k : R) -> infinity`. -/
private theorem tendsto_two_pow_natCast_atTop : Filter.Tendsto
    (fun k : ℕ => (((2 ^ k : ℕ)) : ℝ)) Filter.atTop Filter.atTop := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)

/-- The witness correction factor equals `2^(-(k+1))`. -/
private theorem gronwallWit_corr_eq (k : ℕ) :
    ((2 ^ k : ℕ) : ℝ) * (2 : ℝ) ^ (-(((2 * k : ℕ) : ℝ) + 1)) =
      (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1)) := by
  have h1 : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ (((k : ℕ) : ℝ)) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, Nat.cast_ofNat]
  rw [h1, ← Real.rpow_add (by norm_num)]
  congr 1
  push_cast
  ring

/-- `2^(-(k+1)) -> 0`. -/
private theorem tendsto_rpow_neg_add_one : Filter.Tendsto
    (fun k : ℕ => (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) Filter.atTop (nhds 0) := by
  have heq : ∀ k : ℕ, (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1)) =
      1 / (2 * (2 : ℝ) ^ (k : ℕ)) := by
    intro k
    rw [Real.rpow_neg (by norm_num), Real.rpow_add (by norm_num), Real.rpow_one,
      Real.rpow_natCast, one_div]
    congr 1
    ring
  have hlim : Filter.Tendsto (fun k : ℕ => 1 / (2 * (2 : ℝ) ^ (k : ℕ)))
      Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.const_div_atTop _ 1
    exact Filter.Tendsto.const_mul_atTop (by norm_num)
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have heqEv : (fun k : ℕ => 1 / (2 * (2 : ℝ) ^ (k : ℕ))) =ᶠ[Filter.atTop]
      (fun k : ℕ => (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) :=
    Filter.Eventually.of_forall (fun k => (heq k).symm)
  exact Filter.Tendsto.congr' heqEv hlim

/-- The witness tends to infinity. -/
private theorem tendsto_gronwallWit_atTop : Filter.Tendsto
    (fun k : ℕ => ((gronwallWit k : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_mono (fun k => ?_)
    tendsto_two_pow_natCast_atTop
  rcases eq_or_ne k 0 with rfl | hk0
  · simp only [pow_zero, Nat.cast_one]
    exact_mod_cast gronwallWit_ge_one 0
  · have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have h1 : (2 ^ k : ℕ) ≤ 2 ^ (2 * k) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 ^ (2 * k) : ℕ) ≤ gronwallWit k := gronwallWit_pow_le k hk
    exact_mod_cast le_trans h1 h2

/-- `log (2^k) = k * log 2` for naturals. -/
private theorem gronwall_log_two_pow (k : ℕ) :
    Real.log (((2 ^ k : ℕ)) : ℝ) = (k : ℝ) * Real.log 2 := by
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

/-- `1 < log (wit k)` for `k ≥ 1`, from `wit k ≥ 2 ^ (2k)`. -/
private theorem gronwallWit_log_gt_one (k : ℕ) (hk : 1 ≤ k) :
    1 < Real.log (gronwallWit k : ℝ) := by
  have hle : (2 : ℝ) ^ (2 * k) ≤ (gronwallWit k : ℝ) := by
    have h := gronwallWit_pow_le k hk
    calc (2 : ℝ) ^ (2 * k) = (((2 ^ (2 * k) : ℕ)) : ℝ) := by
            rw [Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ ((gronwallWit k : ℕ) : ℝ) := by exact_mod_cast h
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hle
  rw [Real.log_pow] at hlog
  have hcast : (((2 * k : ℕ)) : ℝ) = 2 * (k : ℝ) := by
    rw [Nat.cast_mul]
    norm_num
  rw [hcast] at hlog
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hbase : (1 : ℝ) < 2 * Real.log 2 := by linarith
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hmono : 2 * Real.log 2 ≤ 2 * (k : ℝ) * Real.log 2 := by
    calc 2 * Real.log 2 = (2 * Real.log 2) * 1 := by ring
      _ ≤ (2 * Real.log 2) * (k : ℝ) :=
          mul_le_mul_of_nonneg_left hk1 (by linarith)
      _ = 2 * (k : ℝ) * Real.log 2 := by ring
  linarith

/-- `log log (wit k) ≤ log (2k log 4) + k log 2` for `k ≥ 1`, via `θ`. -/
private theorem gronwallWit_loglog_le (k : ℕ) (hk : 1 ≤ k) :
    Real.log (Real.log (gronwallWit k : ℝ)) ≤
      Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2 := by
  have hgt := gronwallWit_log_gt_one k hk
  have hlog_eq := (prod_primesLE_pow_ge_one_log (2 ^ k) (2 * k)).2
  have hwit : (∏ p ∈ Nat.primesLE (2 ^ k), p ^ (2 * k)) = gronwallWit k := rfl
  rw [hwit] at hlog_eq
  have hθ := Chebyshev.theta_le_log4_mul_x
    (show (0 : ℝ) ≤ (((2 ^ k : ℕ)) : ℝ) from Nat.cast_nonneg _)
  have hcast : (((2 * k : ℕ)) : ℝ) = 2 * (k : ℝ) := by
    rw [Nat.cast_mul]
    norm_num
  rw [hcast] at hlog_eq
  have hm0 : (0 : ℝ) < (((2 ^ k : ℕ)) : ℝ) := by
    exact_mod_cast pow_pos (show (0 : ℕ) < 2 by norm_num) k
  have hle1 : Real.log (gronwallWit k : ℝ) ≤
      (2 * (k : ℝ)) * (Real.log 4 * (((2 ^ k : ℕ)) : ℝ)) := by
    rw [hlog_eq]
    exact mul_le_mul_of_nonneg_left hθ (by
      have hkk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith)
  have hpos1 : (0 : ℝ) < 2 * (k : ℝ) * Real.log 4 := by
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have h4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    exact mul_pos (mul_pos (by norm_num) hk0) h4
  have hle2 : Real.log (Real.log (gronwallWit k : ℝ)) ≤
      Real.log ((2 * (k : ℝ)) * (Real.log 4 * (((2 ^ k : ℕ)) : ℝ))) :=
    Real.log_le_log (by linarith) hle1
  have hsplit : Real.log ((2 * (k : ℝ)) * (Real.log 4 * (((2 ^ k : ℕ)) : ℝ))) =
      Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2 := by
    have heq : (2 * (k : ℝ)) * (Real.log 4 * (((2 ^ k : ℕ)) : ℝ)) =
        (2 * (k : ℝ) * Real.log 4) * (((2 ^ k : ℕ)) : ℝ) := by ring
    rw [heq, Real.log_mul (ne_of_gt hpos1) (ne_of_gt hm0),
      gronwall_log_two_pow]
  rwa [hsplit] at hle2

/-- `σ(wit k) / wit k ≥ P(2^k) * (1 - 2 ^ (-(k+1)))`. -/
private theorem gronwallWit_sigma_div_ge (k : ℕ) :
    mertensP (((2 ^ k : ℕ)) : ℝ) * (1 - (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) ≤
      ((ArithmeticFunction.sigma 1 (gronwallWit k) : ℕ) : ℝ) /
        ((gronwallWit k : ℕ) : ℝ) := by
  have hN12 := sigma_div_prod_primesLE_pow_ge (2 ^ k) (2 * k)
  have hwit : (∏ p ∈ Nat.primesLE (2 ^ k), p ^ (2 * k)) = gronwallWit k := rfl
  rw [hwit, gronwallWit_corr_eq] at hN12
  exact hN12

/-- `f(wit k)` is at least the three-factor product. -/
private theorem gronwallWit_f_ge (k : ℕ) (hk : 1 ≤ k) :
    (mertensP (((2 ^ k : ℕ)) : ℝ) / Real.log (((2 ^ k : ℕ)) : ℝ)) *
        (1 - (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) *
        (Real.log (((2 ^ k : ℕ)) : ℝ) /
          (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2)) ≤
      ((ArithmeticFunction.sigma 1 (gronwallWit k) : ℕ) : ℝ) /
        (((gronwallWit k : ℕ) : ℝ) * Real.log (Real.log (gronwallWit k : ℝ))) := by
  have hσ := gronwallWit_sigma_div_ge k
  have hgt := gronwallWit_log_gt_one k hk
  have hU := gronwallWit_loglog_le k hk
  have hlogm : Real.log (((2 ^ k : ℕ)) : ℝ) = (k : ℝ) * Real.log 2 :=
    gronwall_log_two_pow k
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hlogm_pos : (0 : ℝ) < Real.log (((2 ^ k : ℕ)) : ℝ) := by
    rw [hlogm]
    exact mul_pos hk0 hlog2
  have hll_pos : (0 : ℝ) < Real.log (Real.log (gronwallWit k : ℝ)) :=
    Real.log_pos hgt
  have hU_pos : (0 : ℝ) <
      Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2 := by
    linarith
  have hσ0 : (0 : ℝ) ≤ ((ArithmeticFunction.sigma 1 (gronwallWit k) : ℕ) : ℝ) /
      ((gronwallWit k : ℕ) : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hstep : mertensP (((2 ^ k : ℕ)) : ℝ) *
        (1 - (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) /
        (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2) ≤
      (((ArithmeticFunction.sigma 1 (gronwallWit k) : ℕ) : ℝ) /
        ((gronwallWit k : ℕ) : ℝ)) /
        Real.log (Real.log (gronwallWit k : ℝ)) := by
    have h1 : mertensP (((2 ^ k : ℕ)) : ℝ) *
          (1 - (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) /
          (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2) ≤
        (((ArithmeticFunction.sigma 1 (gronwallWit k) : ℕ) : ℝ) /
          ((gronwallWit k : ℕ) : ℝ)) /
          (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2) :=
      (div_le_div_iff_of_pos_right hU_pos).mpr hσ
    have h2 : ((((ArithmeticFunction.sigma 1 (gronwallWit k) : ℕ) : ℝ) /
          ((gronwallWit k : ℕ) : ℝ)) /
          (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2)) ≤
        (((ArithmeticFunction.sigma 1 (gronwallWit k) : ℕ) : ℝ) /
          ((gronwallWit k : ℕ) : ℝ)) /
          Real.log (Real.log (gronwallWit k : ℝ)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left
        ((inv_le_inv₀ hU_pos hll_pos).mpr hU) hσ0
    exact h1.trans h2
  have hid : (mertensP (((2 ^ k : ℕ)) : ℝ) / Real.log (((2 ^ k : ℕ)) : ℝ)) *
        (1 - (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) *
        (Real.log (((2 ^ k : ℕ)) : ℝ) /
          (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2)) =
      mertensP (((2 ^ k : ℕ)) : ℝ) *
        (1 - (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) /
        (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2) := by
    have h1 : Real.log (((2 ^ k : ℕ)) : ℝ) ≠ 0 := ne_of_gt hlogm_pos
    have h2 : Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2 ≠ 0 :=
      ne_of_gt hU_pos
    field_simp
  rw [hid, ← div_div]
  exact hstep

/-- `log k / k → 0` along naturals. -/
private theorem gronwall_log_div_nat_tendsto : Filter.Tendsto
    (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ)) Filter.atTop (nhds 0) :=
  (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop

/-- The constant part `log (2 log 4) / k → 0`. -/
private theorem gronwall_const_div_nat_tendsto :
    Filter.Tendsto (fun k : ℕ => Real.log (2 * Real.log 4) / (k : ℝ))
      Filter.atTop (nhds 0) :=
  tendsto_const_div_atTop_nhds_zero_nat _

/-- `log (2k log 4) / k → 0`. -/
private theorem gronwall_Ck_div_tendsto : Filter.Tendsto
    (fun k : ℕ => Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ))
    Filter.atTop (nhds 0) := by
  have hsplit : (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ) +
      Real.log (2 * Real.log 4) / (k : ℝ)) =ᶠ[Filter.atTop]
      (fun k : ℕ => Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have h4 : (2 : ℝ) * Real.log 4 ≠ 0 :=
      mul_ne_zero (by norm_num) (Real.log_ne_zero_of_pos_of_ne_one
        (by norm_num) (by norm_num))
    have heq : Real.log (2 * (k : ℝ) * Real.log 4) =
        Real.log (k : ℝ) + Real.log (2 * Real.log 4) := by
      rw [show 2 * (k : ℝ) * Real.log 4 = (k : ℝ) * (2 * Real.log 4) by ring,
        Real.log_mul hk0 h4]
    rw [heq, add_div]
  have h := gronwall_log_div_nat_tendsto.add gronwall_const_div_nat_tendsto
  rw [add_zero] at h
  exact Filter.Tendsto.congr' hsplit h

/-- `k log 2 / (log (2k log 4) + k log 2) → 1`. -/
private theorem gronwall_logwit_ratio_tendsto : Filter.Tendsto
    (fun k : ℕ => (k : ℝ) * Real.log 2 /
      (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2))
    Filter.atTop (nhds 1) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hconst : Filter.Tendsto (fun _ : ℕ => Real.log 2)
      Filter.atTop (nhds (Real.log 2)) := tendsto_const_nhds
  have hden : Filter.Tendsto
      (fun k : ℕ => Real.log 2 + Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ))
      Filter.atTop (nhds (Real.log 2)) := by
    have h := hconst.add gronwall_Ck_div_tendsto
    rwa [add_zero] at h
  have hdiv := hconst.div hden hlog2.ne'
  rw [div_self hlog2.ne'] at hdiv
  have hdiv' : Filter.Tendsto
      (fun k : ℕ => Real.log 2 /
        (Real.log 2 + Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ)))
      Filter.atTop (nhds 1) := hdiv
  refine Filter.Tendsto.congr' ?_ hdiv'
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hCk0 : (0 : ℝ) ≤ Real.log (2 * (k : ℝ) * Real.log 4) := by
    apply Real.log_nonneg
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hlog4 : (1 : ℝ) ≤ 2 * Real.log 4 := by
      have h16 : Real.log (16 : ℝ) = 2 * Real.log 4 := by
        have h16e : (16 : ℝ) = 4 ^ 2 := by norm_num
        rw [h16e, Real.log_pow]
        norm_num
      have h2 := two_le_log_sixteen
      linarith
    have h1k : (1 : ℝ) ≤ (k : ℝ) * (2 * Real.log 4) := by
      calc (1 : ℝ) ≤ 2 * Real.log 4 := hlog4
        _ = (2 * Real.log 4) * 1 := by ring
        _ ≤ (2 * Real.log 4) * (k : ℝ) :=
            mul_le_mul_of_nonneg_left hk1 (by linarith)
        _ = (k : ℝ) * (2 * Real.log 4) := by ring
    have heq : 2 * (k : ℝ) * Real.log 4 = (k : ℝ) * (2 * Real.log 4) := by ring
    rwa [heq]
  have hUpos : (0 : ℝ) <
      Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2 := by
    have hpos : (0 : ℝ) < (k : ℝ) * Real.log 2 :=
      mul_pos (by exact_mod_cast (by omega : 0 < k)) hlog2
    linarith
  have hU0 : Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2 ≠ 0 :=
    ne_of_gt hUpos
  have hden0 : Real.log 2 + Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ) ≠ 0 := by
    have hdiv0 : (0 : ℝ) ≤ Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ) :=
      div_nonneg hCk0 (Nat.cast_nonneg _)
    have hpos : (0 : ℝ) < Real.log 2 + Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ) := by
      linarith
    exact ne_of_gt hpos
  rw [div_eq_div_iff hden0 hU0]
  have hcancel : (k : ℝ) * (Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ)) =
      Real.log (2 * (k : ℝ) * Real.log 4) :=
    mul_div_cancel₀ _ hk0
  rw [mul_add, mul_add,
    show (k : ℝ) * Real.log 2 * (Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ)) =
      Real.log 2 * ((k : ℝ) * (Real.log (2 * (k : ℝ) * Real.log 4) / (k : ℝ))) by
      ring,
    hcancel]
  ring

/-- Mertens' third theorem along `2 ^ k`. -/
private theorem gronwall_mertens_two_pow_tendsto : Filter.Tendsto
    (fun k : ℕ => mertensP (((2 ^ k : ℕ)) : ℝ) / Real.log (((2 ^ k : ℕ)) : ℝ))
    Filter.atTop (nhds (Real.exp Real.eulerMascheroniConstant)) :=
  tendsto_mertensP_div_log.comp tendsto_two_pow_natCast_atTop

/-- The correction `1 - 2 ^ (-(k+1)) → 1`. -/
private theorem gronwall_corr_tendsto : Filter.Tendsto
    (fun k : ℕ => 1 - (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1)))
    Filter.atTop (nhds 1) := by
  have h1 : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have h := h1.sub tendsto_rpow_neg_add_one
  rwa [sub_zero] at h

/-- The lower-bound product tends to `exp γ`. -/
private theorem gronwall_g_tendsto : Filter.Tendsto
    (fun k : ℕ => (mertensP (((2 ^ k : ℕ)) : ℝ) /
        Real.log (((2 ^ k : ℕ)) : ℝ)) *
      (1 - (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) *
      (Real.log (((2 ^ k : ℕ)) : ℝ) /
        (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2)))
    Filter.atTop (nhds (Real.exp Real.eulerMascheroniConstant)) := by
  have h3 : Filter.Tendsto
      (fun k : ℕ => Real.log (((2 ^ k : ℕ)) : ℝ) /
        (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2))
      Filter.atTop (nhds 1) := by
    refine Filter.Tendsto.congr' ?_ gronwall_logwit_ratio_tendsto
    filter_upwards with k
    rw [gronwall_log_two_pow]
  have h := (gronwall_mertens_two_pow_tendsto.mul gronwall_corr_tendsto).mul h3
  rw [mul_one, mul_one] at h
  exact h

private theorem gronwall_frequently_ge (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ n : ℕ in Filter.atTop,
      Real.exp Real.eulerMascheroniConstant - ε ≤
        ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
          ((n : ℝ) * Real.log (Real.log n)) := by
  rw [Filter.frequently_atTop]
  intro N
  have hwit_top : Filter.Tendsto gronwallWit Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_iff.mp tendsto_gronwallWit_atTop
  have hevW : ∀ᶠ k : ℕ in Filter.atTop, N ≤ gronwallWit k :=
    hwit_top.eventually_ge_atTop N
  have hev1 : ∀ᶠ k : ℕ in Filter.atTop, 1 ≤ k := Filter.eventually_ge_atTop 1
  have hev2 : ∀ᶠ k : ℕ in Filter.atTop,
      Real.exp Real.eulerMascheroniConstant - ε ≤
        (mertensP (((2 ^ k : ℕ)) : ℝ) / Real.log (((2 ^ k : ℕ)) : ℝ)) *
          (1 - (2 : ℝ) ^ (-(((k : ℕ) : ℝ) + 1))) *
          (Real.log (((2 ^ k : ℕ)) : ℝ) /
            (Real.log (2 * (k : ℝ) * Real.log 4) + (k : ℝ) * Real.log 2)) := by
    have hlt : Real.exp Real.eulerMascheroniConstant - ε <
        Real.exp Real.eulerMascheroniConstant := by linarith
    have h := gronwall_g_tendsto.eventually (Ioi_mem_nhds hlt)
    filter_upwards [h] with k hk
    exact (Set.mem_Ioi.mp hk).le
  obtain ⟨k, hk1, hkN, hkg⟩ := (hev1.and (hevW.and hev2)).exists
  refine ⟨gronwallWit k, hkN, ?_⟩
  exact le_trans hkg (gronwallWit_f_ge k hk1)

/--
**Gronwall's theorem** (maximal order of the sum-of-divisors function): the `limsup`
at `Filter.atTop` of `σ(n) / (n * log (log n))` equals `Real.exp
Real.eulerMascheroniConstant`, i.e. `e ^ γ`. Source: S. Nazardonyavi and S. Yakubovich,
"Extremely Abundant Numbers and the Riemann Hypothesis," Journal of Integer Sequences 17
(2014), Article 14.2.8, lines 98–111,
https://cs.uwaterloo.ca/journals/JIS/VOL17/Nazar/nazar4.tex (live source SHA-256
`6854eacdc72e1e5a005b005552942d6d7cfa7a41d7892c0f61bb2b1886e1d7c5`); original
attribution: T. H. Gronwall, "Some asymptotic expressions in the theory of numbers,"
Transactions of the AMS 14 (1913), 113–122. Totalization note: `σ`, division, and the
logarithms are total Lean functions, so the finitely many small natural inputs where
`n * log (log n)` is nonpositive or zero merely contribute finitely many values and do
not affect the `limsup` at `Filter.atTop`.

Proves `Wanted` entry `gronwall_sigma_limsup`.
-/
theorem gronwall_sigma_limsup :
    Filter.limsup
      (fun n : ℕ => ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
        ((n : ℝ) * Real.log (Real.log n))) Filter.atTop =
      Real.exp Real.eulerMascheroniConstant := by
  apply le_antisymm
  · -- Upper: limsup ≤ exp γ + ε for every ε > 0 (eventual upper bound + frequent lower bound).
    apply le_of_forall_pos_le_add
    intro ε hε
    have hcob : Filter.IsCoboundedUnder (fun x1 x2 : ℝ => x1 ≤ x2) Filter.atTop
        (fun n : ℕ => ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
          ((n : ℝ) * Real.log (Real.log n))) :=
      Filter.IsCoboundedUnder.of_frequently_ge
        (gronwall_frequently_ge 1 one_pos)
    have hev := gronwall_eventually_le ε hε
    have hle : Filter.limsup
        (fun n : ℕ => ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
          ((n : ℝ) * Real.log (Real.log n))) Filter.atTop ≤
        Real.exp Real.eulerMascheroniConstant + ε :=
      Filter.limsup_le_of_le hcob hev
    exact hle
  · -- Lower: exp γ - ε ≤ limsup for every ε > 0 (frequent lower bound + eventual boundedness).
    apply le_of_forall_pos_le_add
    intro ε hε
    have hbdd : Filter.IsBoundedUnder (fun x1 x2 : ℝ => x1 ≤ x2) Filter.atTop
        (fun n : ℕ => ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
          ((n : ℝ) * Real.log (Real.log n))) :=
      Filter.isBoundedUnder_of_eventually_le
        (gronwall_eventually_le 1 one_pos)
    have hfreq := gronwall_frequently_ge ε hε
    have hle : Real.exp Real.eulerMascheroniConstant - ε ≤ Filter.limsup
        (fun n : ℕ => ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
          ((n : ℝ) * Real.log (Real.log n))) Filter.atTop :=
      Filter.le_limsup_of_frequently_le hfreq hbdd
    linarith

end MathlibExt.NumberTheory.ArithmeticFunction.GronwallSigmaLimsupWanted
end
