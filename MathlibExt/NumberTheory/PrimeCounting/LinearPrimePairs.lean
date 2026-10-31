/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SmoothNumbers
import MathlibExt.NumberTheory.SelbergSieve
import MathlibExt.NumberTheory.Sieve.Basic

/-!
# Primes `p` with `kp + 1` prime

Selberg's upper bound sieve applied to the sequence `n (kn + 1)` shows that, uniformly in the
even integer `k ≥ 2`, the number of primes `p ≤ x` such that `kp + 1` is also prime is
`O(x / (log x)² · ∏_{p ∣ k} (1 + 1/p))`. For `k = 2` this is the upper bound of the correct
order for Sophie Germain primes.

## Main statements

* `Nat.card_filter_prime_mul_add_one_prime_le`: there is an absolute constant `C` with
  `#{p ≤ x : p, kp + 1 prime} ≤ C x / (log x)² ∏_{p ∣ k} (1 + 1/p)` for every even `k ≥ 2`
  and `x ≥ 2`.
-/

@[expose] public section

open Finset

namespace Nat

/-! ### Counting a residue class -/

/-- `M / d ≤ #{n ∈ [1, M] | n ≡ c [MOD d]} ≤ M / d + 1`. -/
private theorem card_Icc_filter_modEq_bounds (M : ℕ) {d : ℕ} (hd : 0 < d) (c : ℕ) :
    M / d ≤ ((Icc 1 M).filter (fun n => n ≡ c [MOD d])).card ∧
      ((Icc 1 M).filter (fun n => n ≡ c [MOD d])).card ≤ M / d + 1 := by
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨c', hc'⟩ : ∃ c' : ℕ, c' = ((c : ZMod d) - 1).val := ⟨_, rfl⟩
  have hshift : ((Icc 1 M).filter (fun n => n ≡ c [MOD d])).card =
      ((range M).filter (fun m => m ≡ c' [MOD d])).card := by
    apply Finset.card_nbij' (· - 1) (· + 1)
    · intro n hn
      simp only [Finset.coe_filter, Finset.mem_Icc, Finset.mem_range, Set.mem_ofPred_eq] at hn ⊢
      refine ⟨by omega, ?_⟩
      rw [← ZMod.natCast_eq_natCast_iff, hc', ZMod.natCast_zmod_val,
        ← (ZMod.natCast_eq_natCast_iff _ _ _).2 hn.2]
      have : n = (n - 1) + 1 := by omega
      conv_rhs => rw [this]
      push_cast; ring
    · intro m hm
      simp only [Finset.coe_filter, Finset.mem_Icc, Finset.mem_range, Set.mem_ofPred_eq] at hm ⊢
      refine ⟨by omega, ?_⟩
      rw [← ZMod.natCast_eq_natCast_iff]
      have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 hm.2
      rw [hc', ZMod.natCast_zmod_val] at h2
      push_cast; rw [h2]; ring
    · intro n hn
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hn
      simp only; omega
    · intro m _; simp
  have hcm : ((range M).filter (fun m => m ≡ c' [MOD d])).card =
      M / d + if c' % d < M % d then 1 else 0 := by
    rw [← Nat.count_eq_card_filter_range]
    exact Nat.count_modEq_card (b := M) (r := d) hd c'
  rw [hshift, hcm]
  constructor
  · omega
  · split_ifs <;> omega

/-- `|#{n ∈ [1, ⌊x⌋₊] | n ≡ c [MOD d]} - x / d| ≤ 1` for `0 ≤ x`. -/
private theorem abs_card_Icc_floor_filter_modEq_sub_div_le_one {x : ℝ} (hx : 0 ≤ x) {d : ℕ}
    (hd : 0 < d) (c : ℕ) :
    |(((Icc 1 ⌊x⌋₊).filter (fun n => n ≡ c [MOD d])).card : ℝ) - x / d| ≤ 1 := by
  obtain ⟨hlow, hup⟩ := card_Icc_filter_modEq_bounds ⌊x⌋₊ hd c
  set cnt := ((Icc 1 ⌊x⌋₊).filter (fun n => n ≡ c [MOD d])).card
  set M := ⌊x⌋₊ with hM
  obtain ⟨q, hq⟩ : ∃ q, q = M / d := ⟨_, rfl⟩
  rw [← hq] at hlow hup
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hqd : q * d ≤ M := hq ▸ Nat.div_mul_le_self M d
  have hMq : M + 1 ≤ (q + 1) * d := by
    rw [hq]; have := Nat.lt_div_mul_add (a := M) hd; nlinarith
  have hqdR : (q : ℝ) * d ≤ M := by exact_mod_cast hqd
  have hMqR : (M : ℝ) + 1 ≤ ((q : ℝ) + 1) * d := by exact_mod_cast hMq
  have hMx : (M : ℝ) ≤ x := Nat.floor_le hx
  have hxM : x < M + 1 := Nat.lt_floor_add_one x
  have h1 : (q : ℝ) ≤ x / d := by rw [le_div_iff₀ hdR]; linarith
  have h2 : x / d ≤ (q : ℝ) + 1 := by rw [div_le_iff₀ hdR]; linarith
  have r1 : (q : ℝ) ≤ cnt := by exact_mod_cast hlow
  have r2 : (cnt : ℝ) ≤ q + 1 := by exact_mod_cast hup
  rw [abs_le]; constructor <;> linarith

/-! ### The local densities of `n (kn + 1)` -/

private lemma exists_dvd_mul_add_one_iff_modEq (k m : ℕ) (hm0 : 0 < m) (hm : Nat.Coprime m k) :
    ∃ c : ℕ, ∀ n : ℕ, m ∣ k * n + 1 ↔ n ≡ c [MOD m] := by
  have : NeZero m := ⟨hm0.ne'⟩
  obtain ⟨v, hv⟩ : ∃ v : (ZMod m)ˣ, (v : ZMod m) = (k : ZMod m) :=
    ⟨ZMod.unitOfCoprime k hm.symm, rfl⟩
  refine ⟨(-(↑v⁻¹ : ZMod m)).val, fun n => ?_⟩
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  push_cast
  rw [← hv]
  have hvv : (v : ZMod m) * ↑v⁻¹ = 1 := v.mul_inv
  constructor
  · intro h
    linear_combination (↑v⁻¹ : ZMod m) * h - (n : ZMod m) * hvv
  · intro h
    linear_combination (v : ZMod m) * h - hvv

private lemma exists_dvd_and_dvd_mul_add_one_iff_modEq {e e' k : ℕ} (he' : 0 < e')
    (hee : Nat.Coprime e e') (hk : Nat.Coprime e' k) :
    ∃ c : ℕ, ∀ n : ℕ, (e ∣ n ∧ e' ∣ k * n + 1) ↔ n ≡ c [MOD e * e'] := by
  obtain ⟨c', hc'⟩ := exists_dvd_mul_add_one_iff_modEq k e' he' hk
  have h1 : (Nat.chineseRemainder hee 0 c' : ℕ) ≡ 0 [MOD e] :=
    (Nat.chineseRemainder hee 0 c').2.1
  have h2 : (Nat.chineseRemainder hee 0 c' : ℕ) ≡ c' [MOD e'] :=
    (Nat.chineseRemainder hee 0 c').2.2
  refine ⟨Nat.chineseRemainder hee 0 c', fun n => ?_⟩
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hee, hc', ← Nat.modEq_zero_iff_dvd]
  constructor
  · rintro ⟨a, b⟩; exact ⟨a.trans h1.symm, b.trans h2.symm⟩
  · rintro ⟨a, b⟩; exact ⟨a.trans h1, b.trans h2⟩

private lemma exists_fiber_iff_modEq {d k : ℕ} (hd : Squarefree d) {e : ℕ} (he : e ∈ d.divisors) :
    ∃ c : ℕ, ∀ n : ℕ, (d ∣ n * (k * n + 1) ∧ Nat.gcd d n = e) ↔
      (Nat.Coprime (d / e) k ∧ n ≡ c [MOD d]) := by
  obtain ⟨⟨e', rfl⟩, hd0⟩ := Nat.mem_divisors.1 he
  have he0 : 0 < e := Nat.pos_of_ne_zero (left_ne_zero_of_mul hd0)
  have he'0 : 0 < e' := Nat.pos_of_ne_zero (right_ne_zero_of_mul hd0)
  rw [Nat.mul_div_cancel_left e' he0]
  have hee : Nat.Coprime e e' := (Nat.squarefree_mul_iff.1 hd).1
  have hcopkn : ∀ n, Nat.Coprime (k * n + 1) n := fun n =>
    (Nat.coprime_mul_right_add_left 1 n k).2 (Nat.coprime_one_left n)
  have hcopk : ∀ n, Nat.Coprime (k * n + 1) k := fun n =>
    (Nat.coprime_mul_left_add_left 1 k n).2 (Nat.coprime_one_left k)
  have hfwd : ∀ n, (e * e' ∣ n * (k * n + 1) ∧ Nat.gcd (e * e') n = e) →
      e ∣ n ∧ e' ∣ k * n + 1 := by
    rintro n ⟨h1, h2⟩
    have hen : e ∣ n := h2 ▸ Nat.gcd_dvd_right _ _
    have he'n : Nat.Coprime e' n := by
      have hg1 : Nat.gcd e' n ∣ e := by
        rw [← h2]
        exact Nat.dvd_gcd ((Nat.gcd_dvd_left e' n).trans (dvd_mul_left e' e))
          (Nat.gcd_dvd_right e' n)
      exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hg1 hee)
        (Nat.gcd_dvd_left e' n)
    exact ⟨hen, he'n.dvd_of_dvd_mul_left ((dvd_mul_left e' e).trans h1)⟩
  by_cases hk : Nat.Coprime e' k
  · obtain ⟨c, hc⟩ := exists_dvd_and_dvd_mul_add_one_iff_modEq he'0 hee hk
    refine ⟨c, fun n => ?_⟩
    rw [← hc]
    refine ⟨fun h => ⟨hk, hfwd n h⟩, ?_⟩
    rintro ⟨-, hen, he'⟩
    have he'n : Nat.Coprime e' n := Nat.Coprime.coprime_dvd_left he' (hcopkn n)
    refine ⟨Nat.mul_dvd_mul hen he', ?_⟩
    rw [Nat.Coprime.gcd_mul_right_cancel e he'n]
    exact Nat.gcd_eq_left hen
  · refine ⟨0, fun n => ?_⟩
    simp only [hk, false_and, iff_false]
    intro h
    exact hk (Nat.Coprime.coprime_dvd_left (hfwd n h).2 (hcopk n))

/-- `|#{n ≤ x : d ∣ n (kn + 1)} - x ρ(d) / d| ≤ 2 ρ(d)` for squarefree `d`, where
`ρ(d) = #{e ∣ d : (d / e, k) = 1}` is the number of roots of `n (kn + 1)` modulo `d`. -/
private lemma abs_card_filter_dvd_sub_le (x : ℝ) (hx : 0 ≤ x) {d k : ℕ} (hd : Squarefree d) :
    |(((Icc 1 ⌊x⌋₊).filter (fun n => d ∣ n * (k * n + 1))).card : ℝ) -
      x * ((d.divisors.filter (fun e => Nat.Coprime (d / e) k)).card : ℝ) / d| ≤
      2 * ((d.divisors.filter (fun e => Nat.Coprime (d / e) k)).card : ℝ) := by
  have hd0 : d ≠ 0 := hd.ne_zero
  have hc := fun e (he : e ∈ d.divisors) => exists_fiber_iff_modEq (k := k) hd he
  choose! c hc using hc
  rw [Finset.card_eq_sum_card_fiberwise (f := fun n => Nat.gcd d n) (t := d.divisors)
    (fun n _ => Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left _ _, hd0⟩)]
  have hfib : ∀ e ∈ d.divisors,
      (((Icc 1 ⌊x⌋₊).filter (fun n => d ∣ n * (k * n + 1))).filter
        (fun n => Nat.gcd d n = e)).card =
      if Nat.Coprime (d / e) k then
        ((Icc 1 ⌊x⌋₊).filter (fun n => n ≡ c e [MOD d])).card else 0 := by
    intro e he
    rw [Finset.filter_filter]
    split_ifs with hcop
    · congr 1
      exact Finset.filter_congr fun n _ => by rw [hc e he n]; exact and_iff_right hcop
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro n _ hn
      exact hcop ((hc e he n).1 hn).1
  rw [Finset.sum_congr rfl hfib]
  push_cast
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, mul_comm x, mul_div_assoc,
    Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
  have := (abs_card_Icc_floor_filter_modEq_sub_div_le_one hx (Nat.pos_of_ne_zero hd0)
    (c e)).trans one_le_two
  simpa [mul_div_assoc] using this

/-! ### Euler-product bounds for the harmonic sum -/

private theorem sum_le_prod_tsum_of_mem_factoredNumbers {g : ℕ → ℝ} (hg0 : ∀ n, 0 ≤ g n)
    (hg1 : g 1 = 1) (hmul : ∀ {m n : ℕ}, m.Coprime n → g (m * n) = g m * g n)
    (hsum : ∀ {p : ℕ}, p.Prime → Summable fun e => ‖g (p ^ e)‖)
    {s T : Finset ℕ} (hT : ∀ n ∈ T, n ∈ Nat.factoredNumbers s) :
    ∑ n ∈ T, g n ≤ ∏ p ∈ s with p.Prime, ∑' e, g (p ^ e) := by
  obtain ⟨-, hHas⟩ :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hg1 hmul hsum s
  calc ∑ n ∈ T, g n = ∑ x ∈ T.subtype (· ∈ Nat.factoredNumbers s), g x :=
        (Finset.sum_subtype_of_mem g hT).symm
    _ ≤ _ := sum_le_hasSum _ (fun i _ => hg0 i) hHas

/-- `∑_{t ∈ T} 1/t ≤ k/φ(k)` whenever every `t ∈ T` has all its prime factors dividing `k`. -/
private theorem sum_inv_le_div_totient_of_mem_factoredNumbers {k : ℕ} (hkne : k ≠ 0)
    {T : Finset ℕ} (hT : ∀ t ∈ T, t ∈ Nat.factoredNumbers k.primeFactors) :
    ∑ t ∈ T, (1 : ℝ) / t ≤ (k : ℝ) / Nat.totient k := by
  obtain ⟨s, hs⟩ : ∃ s : Finset ℕ, s = k.primeFactors := ⟨_, rfl⟩
  have hspr : ∀ i ∈ s, 2 ≤ (i : ℝ) := by
    intro i hi
    rw [hs] at hi
    exact_mod_cast (Nat.prime_of_mem_primeFactors hi).two_le
  have h := sum_le_prod_tsum_of_mem_factoredNumbers (g := fun n : ℕ => (1 : ℝ) / n)
    (fun n => by positivity) (by simp)
    (fun {m n} _ => by push_cast; exact (one_div_mul_one_div _ _).symm)
    (fun {p} hp => by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      simpa [Nat.cast_pow, one_div, inv_pow] using
        summable_geometric_of_lt_one (r := (p : ℝ)⁻¹) (by positivity)
          (inv_lt_one_of_one_lt₀ hp1))
    hT
  refine h.trans (le_of_eq ?_)
  rw [Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primeFactors hp, ← hs]
  have hgeo : ∀ p ∈ s, ∑' e : ℕ, (1 : ℝ) / ((p ^ e : ℕ) : ℝ) = (p : ℝ) / (p - 1) := by
    intro p hp
    have h2 := hspr p hp
    simp only [Nat.cast_pow, one_div, ← inv_pow]
    rw [tsum_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))]
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  rw [Finset.prod_congr rfl hgeo]
  have h := Nat.totient_mul_prod_primeFactors k
  rw [← hs] at h
  have hR : (Nat.totient k : ℝ) * ∏ p ∈ s, (p : ℝ) = k * ∏ p ∈ s, ((p : ℝ) - 1) := by
    have h' : ((Nat.totient k * ∏ p ∈ s, p : ℕ) : ℝ) = ((k * ∏ p ∈ s, (p - 1) : ℕ) : ℝ) := by
      rw [h]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod] at h'
    rw [h']
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [hs] at hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]
  have hφ0 : (Nat.totient k : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 (by omega)).ne'
  have hpr : ∏ p ∈ s, ((p : ℝ) - 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp => by linarith [hspr p hp]
  rw [Finset.prod_div_distrib, eq_div_iff hφ0, div_mul_eq_mul_div, div_eq_iff hpr]
  linarith [hR]

/-- `∑_{t ≤ N, t ∣ k^N} 1/t ≤ k/φ(k)`. -/
private theorem sum_filter_dvd_pow_inv_le_div_totient {k : ℕ} (hk : k ≠ 0) (N : ℕ) :
    ∑ t ∈ (Icc 1 N).filter (· ∣ k ^ N), (1 : ℝ) / t ≤ (k : ℝ) / Nat.totient k := by
  refine sum_inv_le_div_totient_of_mem_factoredNumbers hk fun t ht => ?_
  rw [Finset.mem_filter, Finset.mem_Icc] at ht
  refine Nat.mem_factoredNumbers_of_primeFactors_subset (by omega) fun p hp => ?_
  have hp' := Nat.mem_primeFactors.1 hp
  exact Nat.mem_primeFactors.2 ⟨hp'.1, hp'.1.dvd_of_dvd_pow (hp'.2.1.trans ht.2), hk⟩

/-- `∑_{m ≤ N} 1/m ≤ (∑_{t ≤ N, t ∣ k^N} 1/t) (∑_{δ ≤ N, (δ, k) = 1} 1/δ)`, via
`m ↦ (gcd(m, k^N), m / gcd(m, k^N))`. -/
private theorem sum_inv_le_sum_smooth_mul_sum_coprime (k : ℕ) (hkne : k ≠ 0) (N : ℕ) :
    ∑ m ∈ Icc 1 N, (1 : ℝ) / m ≤
      (∑ t ∈ (Icc 1 N).filter (· ∣ k ^ N), (1 : ℝ) / t) *
      ∑ δ ∈ (Icc 1 N).filter (fun δ => ∀ p ∈ δ.primeFactors, p.Prime ∧ ¬ p ∣ k),
        (1 : ℝ) / δ := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  let g : ℕ → ℕ × ℕ := fun m => (Nat.gcd m (k ^ N), m / Nat.gcd m (k ^ N))
  have hinj : Set.InjOn g (Icc 1 N) := by
    intro m₁ _ m₂ _ h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [g] at h1 h2
    rw [← Nat.div_mul_cancel (Nat.gcd_dvd_left m₁ (k ^ N)),
      ← Nat.div_mul_cancel (Nat.gcd_dvd_left m₂ (k ^ N)), h2, h1]
  have hkN : k ^ N ≠ 0 := pow_ne_zero _ hkne
  have hsub : (Icc 1 N).image g ⊆
      ((Icc 1 N).filter (· ∣ k ^ N)) ×ˢ
        ((Icc 1 N).filter (fun δ => ∀ p ∈ δ.primeFactors, p.Prime ∧ ¬ p ∣ k)) := by
    intro e he
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 he
    rw [Finset.mem_Icc] at hm
    have hm0 : m ≠ 0 := by omega
    have hgpos : 0 < Nat.gcd m (k ^ N) := Nat.gcd_pos_of_pos_left _ (by omega)
    have hgle : Nat.gcd m (k ^ N) ≤ m := Nat.gcd_le_left _ (by omega)
    simp only [g, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨⟨hgpos, by omega⟩, Nat.gcd_dvd_right _ _⟩,
      ⟨⟨Nat.div_pos hgle hgpos, (Nat.div_le_self _ _).trans hm.2⟩, ?_⟩⟩
    intro p hp
    have hpδ := Nat.mem_primeFactors.1 hp
    refine ⟨hpδ.1, fun hpk => ?_⟩
    have h1 : 0 < (m / Nat.gcd m (k ^ N)).factorization p :=
      hpδ.1.factorization_pos_of_dvd hpδ.2.2 hpδ.2.1
    have h2 : (m / Nat.gcd m (k ^ N)).factorization p =
        m.factorization p - min (m.factorization p) (N * k.factorization p) := by
      rw [Nat.factorization_div (Nat.gcd_dvd_left m (k ^ N)), Finsupp.tsub_apply,
        Nat.factorization_gcd hm0 hkN, Finsupp.inf_apply, Nat.factorization_pow,
        Finsupp.smul_apply, smul_eq_mul]
    have h4 : m.factorization p < m := Nat.factorization_lt _ hm0
    have h5 : 0 < k.factorization p := hpδ.1.factorization_pos_of_dvd hkne hpk
    have h6 : N ≤ N * k.factorization p := Nat.le_mul_of_pos_right N h5
    omega
  calc ∑ m ∈ Icc 1 N, (1 : ℝ) / m
      = ∑ m ∈ Icc 1 N, (fun e : ℕ × ℕ => (1 : ℝ) / e.1 * (1 / e.2)) (g m) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [g]
        rw [one_div_mul_one_div]
        congr 1
        exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left m (k ^ N))).symm
    _ = ∑ e ∈ (Icc 1 N).image g, (1 : ℝ) / e.1 * (1 / e.2) :=
        (Finset.sum_image (f := fun e : ℕ × ℕ => (1 : ℝ) / e.1 * (1 / e.2)) hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

/-- The lower bound for the Selberg level sum of `n (kn + 1)`:
`(φ(k)/k) (log z / 2)² ≤ ∑_{δ ≤ z} ρ(δ) / δ`, where `ρ(δ) = #{t ∣ δ : (t, k) = 1}`. -/
private lemma levelSum_lower (k : ℕ) (hk : k ≠ 0) (z : ℝ) (hz : 1 ≤ z) :
    (Nat.totient k / k : ℝ) * (Real.log z / 2) ^ 2 ≤
      ∑ δ ∈ Icc 1 ⌊z⌋₊, ((δ.divisors.filter (fun t => Nat.Coprime t k)).card : ℝ) / δ := by
  classical
  obtain ⟨N, hN⟩ : ∃ N, N = ⌊Real.sqrt z⌋₊ := ⟨_, rfl⟩
  obtain ⟨Tset, hTset⟩ : ∃ T : Finset ℕ,
      T = (Icc 1 N).filter (fun δ => ∀ p ∈ δ.primeFactors, p.Prime ∧ ¬ p ∣ k) :=
    ⟨_, rfl⟩
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ, H = ∑ m ∈ Icc 1 N, (1:ℝ)/m := ⟨_, rfl⟩
  have hH : Real.log z / 2 ≤ H := by
    have h := log_le_harmonic_floor (Real.sqrt z) (Real.sqrt_nonneg z)
    rw [harmonic_eq_sum_Icc, Real.log_sqrt (by linarith), ← hN] at h
    push_cast at h
    rw [hHdef]; simpa [one_div] using h
  have hlog0 : 0 ≤ Real.log z / 2 := by have := Real.log_nonneg hz; linarith
  have hk0 : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hφ0 : (0:ℝ) < Nat.totient k := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero hk)
  have hHT : (Nat.totient k / k : ℝ) * H ≤ ∑ t ∈ Tset, (1:ℝ)/t := by
    have h1 := (sum_inv_le_sum_smooth_mul_sum_coprime k hk N).trans
      (mul_le_mul_of_nonneg_right (sum_filter_dvd_pow_inv_le_div_totient hk N)
        (Finset.sum_nonneg fun _ _ => by positivity))
    rw [← hTset, ← hHdef] at h1
    calc (Nat.totient k / k : ℝ) * H ≤
          Nat.totient k / k * (k / Nat.totient k * ∑ t ∈ Tset, (1:ℝ)/t) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ∑ t ∈ Tset, (1:ℝ)/t := by field_simp
  have hNz : N * N ≤ ⌊z⌋₊ := by
    apply Nat.le_floor
    push_cast
    have := Nat.floor_le (Real.sqrt_nonneg z)
    rw [← hN] at this
    calc (N:ℝ) * N ≤ Real.sqrt z * Real.sqrt z :=
          _root_.mul_self_le_mul_self (Nat.cast_nonneg _) this
      _ = z := Real.mul_self_sqrt (by linarith)
  have hpair : H * ∑ t ∈ Tset, (1:ℝ)/t ≤
      ∑ δ ∈ Icc 1 ⌊z⌋₊, ((δ.divisors.filter (fun t => Nat.Coprime t k)).card : ℝ) / δ := by
    have hR : ∀ δ ∈ Icc 1 ⌊z⌋₊,
        ((δ.divisors.filter (fun t => Nat.Coprime t k)).card : ℝ) / δ =
          ∑ t ∈ δ.divisors.filter (fun t => Nat.Coprime t k), (1:ℝ) / δ := by
      intros; rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    rw [Finset.sum_congr rfl hR, Finset.sum_sigma', hHdef, Finset.sum_mul_sum,
      ← Finset.sum_product']
    let g : ℕ × ℕ → (Σ _ : ℕ, ℕ) := fun p => ⟨p.1 * p.2, p.2⟩
    have hinj : Set.InjOn g ((Icc 1 N ×ˢ Tset : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      rintro ⟨a, t⟩ hat ⟨a', t'⟩ hat' h
      simp only [g, Sigma.mk.inj_iff, heq_eq_eq] at h
      obtain ⟨h1, rfl⟩ := h
      have ht : 0 < t := by
        simp only [Finset.mem_coe, Finset.mem_product, hTset, Finset.mem_filter,
          Finset.mem_Icc] at hat
        omega
      have : a = a' := Nat.eq_of_mul_eq_mul_right ht h1
      rw [this]
    have hsub : (Icc 1 N ×ˢ Tset).image g ⊆
        (Icc 1 ⌊z⌋₊).sigma (fun δ => δ.divisors.filter (fun t => Nat.Coprime t k)) := by
      intro x hx
      obtain ⟨⟨a, t⟩, hat, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_product, hTset, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc] at hat
      obtain ⟨⟨ha1, ha2⟩, ⟨ht1, ht2⟩, htp⟩ := hat
      simp only [g, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
      refine ⟨⟨Nat.one_le_iff_ne_zero.2 (by positivity),
        le_trans (Nat.mul_le_mul ha2 ht2) hNz⟩, ⟨dvd_mul_left t a, by positivity⟩, ?_⟩
      refine Nat.coprime_of_dvd fun p hp hpt hpk => ?_
      exact (htp p (Nat.mem_primeFactors.2 ⟨hp, hpt, by omega⟩)).2 hpk
    calc ∑ x ∈ Icc 1 N ×ˢ Tset, (1:ℝ) / x.1 * (1 / x.2)
        = ∑ x ∈ Icc 1 N ×ˢ Tset, (fun y : (Σ _ : ℕ, ℕ) => (1:ℝ) / y.1) (g x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [g]; push_cast; rw [one_div_mul_one_div]
      _ = ∑ y ∈ (Icc 1 N ×ˢ Tset).image g, (1:ℝ) / y.1 :=
          (Finset.sum_image (f := fun y : (Σ _ : ℕ, ℕ) => (1:ℝ) / y.1) hinj).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hHnn : 0 ≤ H := hlog0.trans hH
  calc (Nat.totient k / k : ℝ) * (Real.log z / 2) ^ 2
      ≤ (Nat.totient k / k : ℝ) * (H * H) := by
        gcongr
        rw [sq]; exact mul_le_mul hH hH hlog0 hHnn
    _ = ((Nat.totient k / k : ℝ) * H) * H := by ring
    _ ≤ (∑ t ∈ Tset, (1:ℝ)/t) * H := mul_le_mul_of_nonneg_right hHT hHnn
    _ = H * ∑ t ∈ Tset, (1:ℝ)/t := by ring
    _ ≤ _ := hpair

/-! ### The sieve -/

/-- The coprimality indicator `n ↦ [n ≠ 0 ∧ (n, k) = 1]` as a multiplicative arithmetic
function. -/
private noncomputable def coprimeIndicator (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≠ 0 ∧ Nat.Coprime n k then 1 else 0, by simp⟩

private theorem coprimeIndicator_apply {k n : ℕ} (hn : n ≠ 0) :
    coprimeIndicator k n = if Nat.Coprime n k then 1 else 0 := by
  simp [coprimeIndicator, hn]

private theorem isMultiplicative_coprimeIndicator (k : ℕ) :
    (coprimeIndicator k).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [coprimeIndicator], fun {m n} hm hn _ => ?_⟩
  rw [coprimeIndicator_apply (mul_ne_zero hm hn), coprimeIndicator_apply hm,
    coprimeIndicator_apply hn]
  simp only [Nat.coprime_mul_iff_left]
  split_ifs <;> simp_all

/-- `ρ(n) = #{t ∣ n : (t, k) = 1}`, a multiplicative function. -/
private noncomputable def rootCount (k : ℕ) : ArithmeticFunction ℝ :=
  coprimeIndicator k * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)

private theorem rootCount_apply (k n : ℕ) :
    rootCount k n = ((n.divisors.filter (fun t => Nat.Coprime t k)).card : ℝ) := by
  rw [rootCount, ArithmeticFunction.coe_mul_zeta_apply, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [coprimeIndicator_apply (Nat.pos_of_mem_divisors hi).ne']
  split_ifs <;> simp

private theorem rootCount_apply' (k n : ℕ) :
    rootCount k n = ((n.divisors.filter (fun e => Nat.Coprime (n / e) k)).card : ℝ) := by
  rw [rootCount_apply, Finset.card_filter, Finset.card_filter, ← Nat.sum_div_divisors]

private theorem rootCount_prime_pow (k : ℕ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    rootCount k (p ^ e) = if Nat.Coprime p k then (e : ℝ) + 1 else 1 := by
  rw [rootCount, ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp,
    Finset.sum_range_succ', pow_zero, (isMultiplicative_coprimeIndicator k).map_one]
  have : ∀ i ∈ Finset.range e,
      coprimeIndicator k (p ^ (i + 1)) = if Nat.Coprime p k then 1 else 0 := by
    intro i _
    rw [coprimeIndicator_apply (pow_ne_zero _ hp.ne_zero)]
    simp only [Nat.coprime_pow_left_iff (Nat.succ_pos i)]
  rw [Finset.sum_congr rfl this]
  split_ifs <;> simp

private theorem isMultiplicative_rootCount (k : ℕ) : (rootCount k).IsMultiplicative :=
  (isMultiplicative_coprimeIndicator k).mul ArithmeticFunction.isMultiplicative_zeta.natCast

/-- The local density `ν(d) = ρ(d) / d` of `n (kn + 1)`. -/
private noncomputable def density (k : ℕ) : ArithmeticFunction ℝ :=
  (rootCount k).pdiv ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)

private theorem density_apply (k n : ℕ) : density k n = rootCount k n / n := by
  rw [density, ArithmeticFunction.pdiv_apply]
  simp

private theorem rootCount_nonneg (k n : ℕ) : 0 ≤ rootCount k n := by
  rw [rootCount_apply]; positivity

/-- `ρ(δ) / δ ≤ ∏_{p^e ∥ δ} ν(p)^e`. -/
private theorem rootCount_div_le_prod (k : ℕ) {δ : ℕ} (hδ : δ ≠ 0) :
    rootCount k δ / δ ≤ ∏ p ∈ δ.primeFactors, density k p ^ δ.factorization p := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast Nat.pos_of_ne_zero hδ
  have hprod : ∏ p ∈ δ.primeFactors, density k p ^ δ.factorization p =
      (∏ p ∈ δ.primeFactors, rootCount k p ^ δ.factorization p) / δ := by
    have hδeq : (δ : ℝ) = ∏ p ∈ δ.primeFactors, (p : ℝ) ^ δ.factorization p := by
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hδ]
      rw [Finsupp.prod, Nat.support_factorization]
      push_cast
      rfl
    rw [hδeq, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [density_apply, div_pow]
  rw [hprod]
  refine div_le_div_of_nonneg_right ?_ hδR.le
  rw [(isMultiplicative_rootCount k).multiplicative_factorization (rootCount k) hδ, Finsupp.prod,
    Nat.support_factorization]
  refine Finset.prod_le_prod₀ (fun p _ => rootCount_nonneg k _) fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  have h1 := rootCount_prime_pow k hpp 1
  rw [pow_one] at h1
  rw [rootCount_prime_pow k hpp, h1]
  split_ifs
  · have := Nat.lt_two_pow_self (n := δ.factorization p)
    have : ((δ.factorization p : ℕ) : ℝ) + 1 ≤ 2 ^ (δ.factorization p) := by exact_mod_cast this
    norm_num
    linarith
  · simp

/-- **Primes `p` with `kp + 1` prime.** There is an absolute constant `C` such that for every
even `k ≥ 2` and every real `x ≥ 2`, the number of primes `p ≤ x` with `kp + 1` also prime is at
most `C x / (log x)² ∏_{p ∣ k} (1 + 1/p)`. -/
theorem card_filter_prime_mul_add_one_prime_le :
    ∃ C : ℝ, ∀ k : ℕ, Even k → 2 ≤ k → ∀ x : ℝ, 2 ≤ x →
      (((primesLE ⌊x⌋₊).filter (fun p : ℕ => (k * p + 1).Prime)).card : ℝ) ≤
        C * x / Real.log x ^ 2 * ∏ p ∈ k.primeFactors, (1 + (p : ℝ)⁻¹) := by
  classical
  refine ⟨600, fun k hk hk2 x hx => ?_⟩
  have hk0 : k ≠ 0 := by omega
  have hx0 : 0 < x := by linarith
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = x ^ ((1:ℝ)/10) := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; positivity
  have hw10 : w ^ 10 = x := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hw1 : 1 ≤ w := by rw [hw]; exact Real.one_le_rpow (by linarith) (by norm_num)
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = w ^ 2 := ⟨_, rfl⟩
  have hz1 : 1 ≤ z := by rw [hz]; nlinarith
  have hL : Real.log x = 10 * Real.log w := by rw [← hw10, Real.log_pow]; norm_num
  have hLz : Real.log z = 2 * Real.log w := by rw [hz, Real.log_pow]; norm_num
  have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hLw : Real.log x ≤ 10 * w := by
    have := Real.log_le_rpow_div hx0.le (by norm_num : (0:ℝ) < 1/10)
    rw [← hw] at this; linarith
  set R := ⌊z⌋₊ with hRdef
  have hR1 : 1 ≤ R := Nat.le_floor (by exact_mod_cast hz1)
  have hRz : (R : ℝ) ≤ z := Nat.floor_le (by linarith)
  set N := ⌊x⌋₊ with hNdef
  set g : ℕ → ℕ := fun n => n * (k * n + 1) with hg
  have hginj : Set.InjOn g (Icc 1 N : Set ℕ) := by
    intro a _ b _ hab
    simp only [hg] at hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have : a * (k * a + 1) < b * (k * b + 1) :=
        Nat.mul_lt_mul_of_lt_of_le h (by nlinarith) (by omega)
      omega
    · have : b * (k * b + 1) < a * (k * a + 1) :=
        Nat.mul_lt_mul_of_lt_of_le h (by nlinarith) (by omega)
      omega
  set A : Finset ℕ := (Icc 1 N).image g with hA
  -- the sieve
  have hρpos : ∀ p : ℕ, p.Prime → 0 < density k p := by
    intro p hp
    have h1 := rootCount_prime_pow k hp 1
    rw [pow_one] at h1
    rw [density_apply, h1]
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    split_ifs <;> positivity
  have hρlt : ∀ p : ℕ, p.Prime → density k p < 1 := by
    intro p hp
    have h1 := rootCount_prime_pow k hp 1
    rw [pow_one] at h1
    rw [density_apply, h1]
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    split_ifs with hcop
    · have hp3 : 3 ≤ p := by
        rcases hp.eq_two_or_odd' with h | h
        · exfalso; rw [h] at hcop
          exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hcop (even_iff_two_dvd.1 hk)
        · have := hp.two_le
          rcases h with ⟨m, hm⟩; omega
      have : (3:ℝ) ≤ p := by exact_mod_cast hp3
      rw [div_lt_one (by linarith)]; norm_num; linarith
    · rw [div_lt_one (by linarith)]; linarith
  let s : BoundingSieve :=
    { support := A
      prodPrimes := primorial R
      prodPrimes_squarefree := squarefree_primorial R
      weights := fun m => if m ∈ A then 1 else 0
      weights_nonneg := fun m => by split_ifs <;> norm_num
      totalMass := x
      nu := density k
      nu_mult := (isMultiplicative_rootCount k).pdiv
        ArithmeticFunction.isMultiplicative_id.natCast
      nu_pos_of_prime := fun p hp _ => hρpos p hp
      nu_lt_one_of_prime := fun p hp _ => hρlt p hp }
  have hsum_A : ∀ c : ℕ → Prop, ∀ _ : DecidablePred c,
      (∑ m ∈ A, if c m then (if m ∈ A then (1 : ℝ) else 0) else 0) =
        (((Icc 1 N).filter (fun n => c (g n))).card : ℝ) := by
    intro c _
    rw [Finset.card_filter, Nat.cast_sum, hA, Finset.sum_image hginj]
    refine Finset.sum_congr rfl fun n hn => ?_
    have : g n ∈ (Icc 1 N).image g := Finset.mem_image_of_mem g hn
    simp only [this, ↓reduceIte]
    split_ifs <;> simp
  have hsifted : s.siftedSum =
      (((Icc 1 N).filter (fun n => Nat.Coprime (primorial R) (g n))).card : ℝ) :=
    hsum_A _ _
  have hmult : ∀ d, s.multSum d = (((Icc 1 N).filter (fun n => d ∣ g n)).card : ℝ) := by
    intro d
    exact hsum_A _ _
  have hlcm : ∀ l : ℕ, l ∣ primorial R → |s.rem l| ≤ 2 * l := by
    intro l hl
    have hlsq : Squarefree l := (squarefree_primorial R).squarefree_of_dvd hl
    change |s.multSum l - density k l * x| ≤ 2 * l
    rw [hmult, density_apply, rootCount_apply', div_mul_eq_mul_div, mul_comm _ x]
    refine (abs_card_filter_dvd_sub_le x hx0.le hlsq).trans ?_
    have h1 : (l.divisors.filter (fun e => Nat.Coprime (l / e) k)).card ≤ l :=
      (Finset.card_filter_le _ _).trans (Nat.card_divisors_le_self l)
    have h2 : ((l.divisors.filter (fun e => Nat.Coprime (l / e) k)).card : ℝ) ≤ l := by
      exact_mod_cast h1
    linarith
  -- the primes above `R` survive the sieve
  have hcount : ((primesLE N).filter (fun p : ℕ => (k * p + 1).Prime)).card ≤
      (R + 1) + ((Icc 1 N).filter (fun n => Nat.Coprime (primorial R) (g n))).card := by
    rw [← Finset.card_filter_add_card_filter_not
      (s := (primesLE N).filter (fun p : ℕ => (k * p + 1).Prime)) (fun p => p ≤ R)]
    refine add_le_add ?_ (Finset.card_le_card fun p hp => ?_)
    · calc _ ≤ (Finset.Iic R).card :=
            Finset.card_le_card fun p hp => Finset.mem_Iic.2 (Finset.mem_filter.1 hp).2
        _ = R + 1 := Nat.card_Iic R
    · simp only [Finset.mem_filter, mem_primesLE, not_le] at hp
      obtain ⟨⟨⟨hpN, hpp⟩, hkp⟩, hpR⟩ := hp
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hpp.one_lt.le, hpN⟩, ?_⟩
      simp only [hg]
      refine Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hpp).2 fun h => ?_).symm
        ((Nat.Prime.coprime_iff_not_dvd hkp).2 fun h => ?_).symm
      · have := hpp.dvd_primorial_iff.1 h; omega
      · have := hkp.dvd_primorial_iff.1 h
        have : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
        omega
  -- Selberg's bound
  have hsieve := MathlibExt.SelbergSieve.siftedSum_le_totalMass_div_levelSum_add s R hR1
  have hLSP : ∀ d ∈ MathlibExt.SelbergSieve.levelSet s R, d ∣ primorial R ∧ d ≤ R :=
    fun d hd => by
      simp only [MathlibExt.SelbergSieve.levelSet, Finset.mem_filter, Nat.mem_divisors] at hd
      exact ⟨hd.1.1, hd.2⟩
  have hLScard : ((MathlibExt.SelbergSieve.levelSet s R).card : ℝ) ≤ R := by
    have hsub : MathlibExt.SelbergSieve.levelSet s R ⊆ Icc 1 R := by
      intro d hd
      obtain ⟨hdP, hdR⟩ := hLSP d hd
      exact Finset.mem_Icc.2 ⟨Nat.pos_of_dvd_of_pos hdP (primorial_pos R), hdR⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact_mod_cast this
  have herr : ∑ d₁ ∈ MathlibExt.SelbergSieve.levelSet s R,
      ∑ d₂ ∈ MathlibExt.SelbergSieve.levelSet s R, |s.rem (d₁.lcm d₂)| ≤ 2 * (R : ℝ) ^ 4 := by
    calc _ ≤ ∑ d₁ ∈ MathlibExt.SelbergSieve.levelSet s R,
          ∑ d₂ ∈ MathlibExt.SelbergSieve.levelSet s R, 2 * (R : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun d₁ h₁ => Finset.sum_le_sum fun d₂ h₂ => ?_
          obtain ⟨hd₁P, hd₁R⟩ := hLSP d₁ h₁
          obtain ⟨hd₂P, hd₂R⟩ := hLSP d₂ h₂
          refine (hlcm _ (Nat.lcm_dvd hd₁P hd₂P)).trans ?_
          have hl : d₁.lcm d₂ ≤ d₁ * d₂ := Nat.div_le_self _ _
          have hl' : d₁.lcm d₂ ≤ R * R := hl.trans (Nat.mul_le_mul hd₁R hd₂R)
          have : ((d₁.lcm d₂ : ℕ) : ℝ) ≤ (R : ℝ) ^ 2 := by rw [sq]; exact_mod_cast hl'
          linarith
      _ = ((MathlibExt.SelbergSieve.levelSet s R).card : ℝ) *
            (MathlibExt.SelbergSieve.levelSet s R).card * (2 * (R : ℝ) ^ 2) := by
          simp only [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ (R : ℝ) * R * (2 * (R : ℝ) ^ 2) := by
          gcongr
      _ = 2 * (R : ℝ) ^ 4 := by ring
  -- the main term
  have hlow : (Nat.totient k / k : ℝ) * (Real.log x / 10) ^ 2 ≤
      MathlibExt.SelbergSieve.levelSum s R := by
    have h1 := levelSum_lower k hk0 z hz1
    rw [hLz, show 2 * Real.log w / 2 = Real.log x / 10 by rw [hL]; ring] at h1
    refine h1.trans (le_trans ?_ (MathlibExt.SelbergSieve.sum_prod_nu_pow_le_levelSum s R))
    have hfil : (Icc 1 R).filter (fun δ => δ.primeFactors ⊆ s.prodPrimes.primeFactors) =
        Icc 1 R := by
      refine Finset.filter_true_of_mem fun δ hδ p hp => ?_
      change p ∈ (primorial R).primeFactors
      rw [primeFactors_primorial, mem_primesLE]
      have hδ1 := Finset.mem_Icc.1 hδ
      exact ⟨(Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)).trans hδ1.2,
        Nat.prime_of_mem_primeFactors hp⟩
    rw [hfil]
    refine Finset.sum_le_sum fun δ hδ => ?_
    have hδ0 : δ ≠ 0 := by have := (Finset.mem_Icc.1 hδ).1; omega
    rw [← rootCount_apply]
    exact rootCount_div_le_prod k hδ0
  have hk0R : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
  have hφ0 : (0:ℝ) < Nat.totient k := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero hk0)
  have hprod1 : 1 ≤ ∏ p ∈ k.primeFactors, (1 + (p : ℝ)⁻¹) :=
    Finset.one_le_prod₀ fun p _ => by
      have : (0:ℝ) ≤ (p:ℝ)⁻¹ := by positivity
      linarith
  have hmain : x / MathlibExt.SelbergSieve.levelSum s R ≤
      200 * (x / Real.log x ^ 2 * ∏ p ∈ k.primeFactors, (1 + (p : ℝ)⁻¹)) := by
    have hlb : 0 < (Nat.totient k / k : ℝ) * (Real.log x / 10) ^ 2 := by positivity
    calc x / MathlibExt.SelbergSieve.levelSum s R ≤
          x / ((Nat.totient k / k : ℝ) * (Real.log x / 10) ^ 2) :=
          div_le_div_of_nonneg_left hx0.le hlb hlow
      _ = (k / Nat.totient k : ℝ) * (100 * (x / Real.log x ^ 2)) := by field_simp; ring
      _ ≤ (2 * ∏ p ∈ k.primeFactors, (1 + (p : ℝ)⁻¹)) * (100 * (x / Real.log x ^ 2)) :=
          mul_le_mul_of_nonneg_right (div_totient_le_two_mul_prod_one_add_inv hk0)
            (by positivity)
      _ = _ := by ring
  have hsmall : z + 1 + 2 * z ^ 4 ≤
      400 * (x / Real.log x ^ 2 * ∏ p ∈ k.primeFactors, (1 + (p : ℝ)⁻¹)) := by
    have h4 : z + 1 + 2 * z ^ 4 ≤ 4 * z ^ 4 := by
      have : z ≤ z ^ 4 := le_self_pow₀ hz1 (by norm_num)
      have : 1 ≤ z ^ 4 := one_le_pow₀ hz1
      linarith
    have hL2 : Real.log x ^ 2 ≤ 100 * w ^ 2 := by nlinarith
    have h5 : 4 * z ^ 4 ≤ 400 * (x / Real.log x ^ 2) := by
      have hz4 : z ^ 4 = w ^ 8 := by rw [hz]; ring
      rw [mul_div_assoc', le_div_iff₀ (by positivity), hz4]
      calc 4 * w ^ 8 * Real.log x ^ 2 ≤ 4 * w ^ 8 * (100 * w ^ 2) := by gcongr
        _ = 400 * w ^ 10 := by ring
        _ = 400 * x := by rw [hw10]
    have h6 : x / Real.log x ^ 2 ≤
        x / Real.log x ^ 2 * ∏ p ∈ k.primeFactors, (1 + (p : ℝ)⁻¹) :=
      le_mul_of_one_le_right (by positivity) hprod1
    linarith
  have hR4 : 2 * (R : ℝ) ^ 4 ≤ 2 * z ^ 4 := by
    have : (R : ℝ) ^ 4 ≤ z ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hRz 4
    linarith
  have hcountR : (((primesLE N).filter (fun p : ℕ => (k * p + 1).Prime)).card : ℝ)
      ≤ ((R : ℝ) + 1) +
        (((Icc 1 N).filter (fun n => Nat.Coprime (primorial R) (g n))).card : ℝ) := by
    exact_mod_cast hcount
  rw [hsifted] at hsieve
  rw [show (600:ℝ) * x / Real.log x ^ 2 * ∏ p ∈ k.primeFactors, (1 + (p : ℝ)⁻¹) =
    600 * (x / Real.log x ^ 2 * ∏ p ∈ k.primeFactors, (1 + (p : ℝ)⁻¹)) by ring]
  change x / MathlibExt.SelbergSieve.levelSum s R ≤ _ at hmain
  linarith only [hcountR, hsieve, herr, hRz, hmain, hsmall, hR4]

end Nat
