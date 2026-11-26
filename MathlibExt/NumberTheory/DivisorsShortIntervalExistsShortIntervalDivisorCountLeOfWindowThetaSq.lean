/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.NumberTheory.DivisorsShortInterval
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Divisors in windows of length `n ^ (θ ^ 2 - ε)`

The bound follows Patrick Letendre, *Divisors of an Integer in a Short Interval*
(INTEGERS 26 (2026), Article A115), Proposition 1: Cohen's lcm-gcd inequality bounds
a power product of the divisors in the window, the gcd of two distinct divisors in the
window divides their difference, and comparing exponents bounds their number.
-/

namespace MetaMathlibExt

/-- Twice the number of strict pairs in `s ×ˢ s` is `s.card ^ 2 - s.card`. -/
private theorem card_filter_lt_mul_two (s : Finset ℕ) :
    2 * (((s ×ˢ s).filter fun p : ℕ × ℕ => p.1 < p.2).card) = s.card ^ 2 - s.card := by
  set P := (s ×ˢ s).filter (fun p : ℕ × ℕ => p.1 < p.2) with hP
  set Q := (s ×ˢ s).filter (fun p : ℕ × ℕ => p.2 < p.1) with hQ
  set D := (s ×ˢ s).filter (fun p : ℕ × ℕ => p.1 = p.2) with hD
  have hQP : Q.card = P.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [hQ, hP, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p₁ _ p₂ _ h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro q hq
      simp only [hP, Finset.mem_filter, Finset.mem_product] at hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      simp only [hQ, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩
  have hDs : D.card = s.card := by
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp
      simp only [hD, Finset.mem_filter, Finset.mem_product] at hp
      exact hp.1.1
    · intro p₁ h₁ p₂ h₂ h
      simp only [hD, Finset.mem_filter] at h₁ h₂
      exact Prod.ext h (by rw [← h₁.2, h, h₂.2])
    · intro x hx
      refine ⟨(x, x), ?_, rfl⟩
      simp only [hD, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hx, hx⟩, trivial⟩
  have hunion : P ∪ Q ∪ D = s ×ˢ s := by
    ext p
    simp only [hP, hQ, hD, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ((⟨hm, _⟩ | ⟨hm, _⟩) | ⟨hm, _⟩) <;> exact hm
    · intro hm
      rcases lt_trichotomy p.1 p.2 with h | h | h
      · exact Or.inl (Or.inl ⟨hm, h⟩)
      · exact Or.inr ⟨hm, h⟩
      · exact Or.inl (Or.inr ⟨hm, h⟩)
  have hdisj1 : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [hP, hQ, Finset.mem_filter] at hp1 hp2
    omega
  have hdisj2 : Disjoint (P ∪ Q) D := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [hP, hQ, hD, Finset.mem_union, Finset.mem_filter] at hp1 hp2
    rcases hp1 with (⟨_, h⟩ | ⟨_, h⟩) <;> omega
  have hcard : (s ×ˢ s).card = P.card + Q.card + D.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1]
  rw [Finset.card_product] at hcard
  rw [hQP, hDs] at hcard
  rw [pow_two]
  omega

/-- Applying a finset sum of finitely supported functions. -/
private theorem finsupp_finset_sum_apply {α : Type} [DecidableEq α] (s : Finset α)
    (f : α → ℕ →₀ ℕ) (p : ℕ) : (∑ x ∈ s, f x) p = ∑ x ∈ s, (f x) p := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hxt ih =>
      rw [Finset.sum_insert hxt, Finset.sum_insert hxt, Finsupp.add_apply, ih]

/-- Level inequality: `2 * t * c ≤ t * (t + 1) + c * (c - 1)`. -/
private theorem two_mul_le_of_consec (t c : ℕ) :
    2 * t * c ≤ t * (t + 1) + c * (c - 1) := by
  cases c with
  | zero => simp
  | succ c =>
      have hsub : (((c + 1 - 1 : ℕ)) : ℤ) = ((c : ℕ) : ℤ) := by rw [Nat.add_sub_cancel]
      have key : (0 : ℤ) ≤ ((t : ℤ) - ((c : ℕ) : ℤ) - 1) ^ 2 + ((t : ℤ) - ((c : ℕ) : ℤ) - 1) := by
        by_cases h0 : (0 : ℤ) ≤ (t : ℤ) - ((c : ℕ) : ℤ) - 1
        · exact add_nonneg (sq_nonneg _) h0
        · have h0' : (t : ℤ) - ((c : ℕ) : ℤ) - 1 < 0 := not_le.mp h0
          have h1 : (t : ℤ) - ((c : ℕ) : ℤ) - 1 + 1 ≤ 0 := by omega
          have h2 := mul_nonneg_of_nonpos_of_nonpos (le_of_lt h0') h1
          have heq : ((t : ℤ) - ((c : ℕ) : ℤ) - 1) ^ 2 + ((t : ℤ) - ((c : ℕ) : ℤ) - 1)
              = ((t : ℤ) - ((c : ℕ) : ℤ) - 1) * (((t : ℤ) - ((c : ℕ) : ℤ) - 1) + 1) := by ring
          linarith
      have hcast : ((2 * t * (c + 1) : ℕ) : ℤ)
          ≤ ((t * (t + 1) + (c + 1) * ((c + 1) - 1) : ℕ) : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, hsub]
        linear_combination key
      exact_mod_cast hcast

/-- Per-prime estimate for Cohen's inequality, by counting levels. -/
private theorem per_prime_le (S : Finset ℕ) (e : ℕ → ℕ) (t E : ℕ)
    (hE : 2 * E = t * (t + 1)) :
    ∑ x ∈ S, 2 * t * e x
      ≤ 2 * E * (S.sup e)
        + ∑ p ∈ (S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 < p.2), 2 * min (e p.1) (e p.2) := by
  have hle : ∀ x ∈ S, e x ≤ S.sup e := fun x hx => Finset.le_sup hx
  have hid1 : ∀ x ∈ S, ((Finset.range (S.sup e)).filter fun m => m < e x).card = e x := by
    intro x hx
    have hsub : (Finset.range (S.sup e)).filter (fun m => m < e x) = Finset.range (e x) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · intro h
        exact h.2
      · intro h
        exact ⟨lt_of_lt_of_le h (hle x hx), h⟩
    rw [hsub, Finset.card_range]
  have hid2 : ∀ x ∈ S, ∀ y ∈ S,
      ((Finset.range (S.sup e)).filter fun m => m < e x ∧ m < e y).card
        = min (e x) (e y) := by
    intro x hx y hy
    have hsub : (Finset.range (S.sup e)).filter (fun m => m < e x ∧ m < e y)
        = Finset.range (min (e x) (e y)) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · intro h
        exact lt_min h.2.1 h.2.2
      · intro h
        refine ⟨lt_of_lt_of_le (lt_of_lt_of_le h (min_le_left _ _)) (hle x hx), ?_, ?_⟩
        · exact lt_of_lt_of_le h (min_le_left _ _)
        · exact lt_of_lt_of_le h (min_le_right _ _)
    rw [hsub, Finset.card_range]
  have hmin : ∀ p ∈ (S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 < p.2),
      ((Finset.range (S.sup e)).filter fun m => m < e p.1 ∧ m < e p.2).card
        = min (e p.1) (e p.2) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    exact hid2 _ hp.1.1 _ hp.1.2
  have hswap1 : ∑ x ∈ S, ((Finset.range (S.sup e)).filter fun m => m < e x).card
      = ∑ m ∈ Finset.range (S.sup e), (S.filter fun x => m < e x).card := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  have hswap2 : ∑ p ∈ (S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 < p.2),
          ((Finset.range (S.sup e)).filter fun m => m < e p.1 ∧ m < e p.2).card
      = ∑ m ∈ Finset.range (S.sup e),
          (((S ×ˢ S).filter fun p : ℕ × ℕ => p.1 < p.2).filter
            fun p => m < e p.1 ∧ m < e p.2).card := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm (s := Finset.range (S.sup e))]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : a.1 < a.2 <;> simp [h]
  have hLHS : (∑ x ∈ S, 2 * t * e x)
      = ∑ m ∈ Finset.range (S.sup e), 2 * t * (S.filter fun x => m < e x).card := by
    have h1 : ∀ x ∈ S, 2 * t * e x
        = 2 * t * (((Finset.range (S.sup e)).filter fun m => m < e x).card) := by
      intro x hx
      rw [hid1 x hx]
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, hswap1, Finset.mul_sum]
  have hRHS : (∑ p ∈ (S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 < p.2), 2 * min (e p.1) (e p.2))
      = ∑ m ∈ Finset.range (S.sup e),
          2 * ((((S ×ˢ S).filter fun p : ℕ × ℕ => p.1 < p.2).filter
            fun p => m < e p.1 ∧ m < e p.2).card) := by
    have h1 : ∀ p ∈ (S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 < p.2),
        2 * min (e p.1) (e p.2)
          = 2 * (((Finset.range (S.sup e)).filter fun m => m < e p.1 ∧ m < e p.2).card) := by
      intro p hp
      rw [hmin p hp]
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, hswap2, Finset.mul_sum]
  have hMID : 2 * E * (S.sup e) = ∑ _m ∈ Finset.range (S.sup e), 2 * E := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]
    ring
  rw [hLHS, hMID, hRHS, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun m _ => ?_
  have hcongr : (((S ×ˢ S).filter fun p : ℕ × ℕ => p.1 < p.2).filter
          fun p => m < e p.1 ∧ m < e p.2)
      = (((S.filter fun x => m < e x) ×ˢ (S.filter fun x => m < e x)).filter
          fun p : ℕ × ℕ => p.1 < p.2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hcongr]
  have hN := card_filter_lt_mul_two (S.filter fun x => m < e x)
  have hcc : (S.filter fun x => m < e x).card ^ 2 - (S.filter fun x => m < e x).card
      = (S.filter fun x => m < e x).card * ((S.filter fun x => m < e x).card - 1) := by
    rw [mul_tsub, mul_one, pow_two]
  rw [hcc] at hN
  have hsc := two_mul_le_of_consec t ((S.filter fun x => m < e x).card)
  omega

/-- Cohen's lcm-gcd inequality for divisors of `n`, with the lcm replaced by `n`. -/
private theorem cohen_dvd (S : Finset ℕ) (n t : ℕ)
    (hS : ∀ x ∈ S, x ∣ n) (hS0 : ∀ x ∈ S, x ≠ 0) (hn : n ≠ 0) :
    (∏ x ∈ S, x ^ (2 * t))
      ∣ n ^ (2 * (t * (t + 1) / 2))
        * ∏ p ∈ (S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 < p.2), (Nat.gcd p.1 p.2) ^ 2 := by
  have h2E : 2 * (t * (t + 1) / 2) = t * (t + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self t)
  have hLHS0 : (∏ x ∈ S, x ^ (2 * t)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro x hx
    exact pow_ne_zero _ (hS0 x hx)
  have hmem : ∀ q ∈ (S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 < p.2), q.1 ≠ 0 ∧ q.2 ≠ 0 := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq
    exact ⟨hS0 _ hq.1.1, hS0 _ hq.1.2⟩
  have hPmem : ∀ q ∈ (S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 < p.2),
      (Nat.gcd q.1 q.2) ^ 2 ≠ 0 := by
    intro q hq
    obtain ⟨h1, -⟩ := hmem q hq
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left q.1 q.2
    exact pow_ne_zero 2 fun hcon => h1 (by rw [hcon, zero_mul] at hk; exact hk)
  have hP0 : (∏ p ∈ (S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 < p.2),
      (Nat.gcd p.1 p.2) ^ 2) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    exact hPmem
  have hRHS0 : (n ^ (2 * (t * (t + 1) / 2))
      * ∏ p ∈ (S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 < p.2), (Nat.gcd p.1 p.2) ^ 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hn) hP0
  rw [← Nat.factorization_le_iff_dvd hLHS0 hRHS0, Finsupp.le_def]
  intro p
  have hLHS : ((∏ x ∈ S, x ^ (2 * t)).factorization) p
      = ∑ x ∈ S, 2 * t * (x.factorization p) := by
    rw [Nat.factorization_prod (fun x hx => pow_ne_zero _ (hS0 x hx)),
      finsupp_finset_sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hRHS : ((n ^ (2 * (t * (t + 1) / 2))
        * ∏ q ∈ (S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 < p.2), (Nat.gcd q.1 q.2) ^ 2).factorization) p
      = 2 * (t * (t + 1) / 2) * (n.factorization p)
        + ∑ q ∈ (S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 < p.2),
            2 * min ((q.1).factorization p) ((q.2).factorization p) := by
    rw [Nat.factorization_mul (pow_ne_zero _ hn) hP0, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_prod hPmem, finsupp_finset_sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨h1, h2⟩ := hmem q hq
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_gcd h1 h2, Finsupp.inf_apply]
  rw [hLHS, hRHS]
  have hbase := per_prime_le S (fun x => x.factorization p) t (t * (t + 1) / 2) h2E
  have hMv : S.sup (fun x => x.factorization p) ≤ n.factorization p := by
    refine Finset.sup_le fun x hx => ?_
    exact Finsupp.le_def.mp
      ((Nat.factorization_le_iff_dvd (hS0 x hx) hn).mpr (hS x hx)) p
  have hMv' : 2 * (t * (t + 1) / 2) * (S.sup fun x => x.factorization p)
      ≤ 2 * (t * (t + 1) / 2) * (n.factorization p) :=
    mul_le_mul_of_nonneg_left hMv (by positivity)
  omega

@[expose] public section

/-- **Divisors in windows of length $n^{\theta^2 - \varepsilon}$.** For a natural number $n$ and
real numbers $X$, $Y$, let $D_n(X, Y)$ be the number of divisors $d$ of $n$ with
$X \le d \le X + Y$. There is an absolute constant $C$ such that for every integer $n \ge 1$ and
all real numbers $\theta$, $\varepsilon$ with $0 < \theta < 1$ and $0 < \varepsilon < \theta^2$,
$D_n(n^\theta, n^{\theta^2 - \varepsilon}) \le
C \left(\theta(1 - \theta)/\varepsilon + 1/(\theta(1 - \theta))\right)$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Proposition 1 (`integers-2026-A115-prop-1`). -/
public theorem exists_shortIntervalDivisorCount_le_of_window_theta_sq :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ θ ε : ℝ, 0 < θ → θ < 1 → 0 < ε → ε < θ ^ 2 →
      (shortIntervalDivisorCount n ((n : ℝ) ^ θ) ((n : ℝ) ^ (θ ^ 2 - ε)) : ℝ) ≤
        C * (θ * (1 - θ) / ε + 1 / (θ * (1 - θ))) := by
  refine ⟨4, fun n hn θ ε hθ0 hθ1 hε0 _ => ?_⟩
  have hApos : (0 : ℝ) < θ * (1 - θ) := mul_pos hθ0 (sub_pos.mpr hθ1)
  have hA14 : θ * (1 - θ) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (θ - 1 / 2)]
  have h16 : (16 : ℝ) ≤ 4 / (θ * (1 - θ)) := by
    rw [le_div_iff₀ hApos]
    linarith [hA14]
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  set S := n.divisors.filter
    (fun d : ℕ => (n : ℝ) ^ θ ≤ (d : ℝ) ∧ (d : ℝ) ≤ (n : ℝ) ^ θ + (n : ℝ) ^ (θ ^ 2 - ε)) with hS
  have hScard : (shortIntervalDivisorCount n ((n : ℝ) ^ θ) ((n : ℝ) ^ (θ ^ 2 - ε)) : ℝ)
      = (S.card : ℝ) := rfl
  rw [hScard]
  have hmemS : ∀ d ∈ S,
      d ∈ n.divisors ∧ (n : ℝ) ^ θ ≤ (d : ℝ)
        ∧ (d : ℝ) ≤ (n : ℝ) ^ θ + (n : ℝ) ^ (θ ^ 2 - ε) := by
    intro d hd
    simp only [hS, Finset.mem_filter] at hd
    exact hd
  have hS0 : ∀ d ∈ S, d ≠ 0 := by
    intro d hd hcon
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp (hmemS d hd).1
    subst hcon
    rw [zero_dvd_iff] at hdvd
    exact hn0 hdvd
  have hSdiv : ∀ d ∈ S, d ∣ n := fun d hd => (Nat.mem_divisors.mp (hmemS d hd).1).1
  set P := (S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 < p.2) with hP
  by_cases hk : (S.card : ℝ) ≤ 4 / (θ * (1 - θ))
  · have hnn1 : (0 : ℝ) ≤ θ * (1 - θ) / ε := div_nonneg hApos.le hε0.le
    have heq : (4 : ℝ) / (θ * (1 - θ)) = 4 * (1 / (θ * (1 - θ))) := by ring
    rw [heq] at hk
    linarith [hk, hnn1]
  · have hklt4 : 4 / (θ * (1 - θ)) < (S.card : ℝ) := not_le.mp hk
    have hk2 : 2 ≤ S.card := by
      have h1lt : (1 : ℝ) < S.card := by linarith [hklt4, h16]
      have h1lt' : 1 < S.card := by exact_mod_cast h1lt
      omega
    have hn2 : 2 ≤ n := by
      by_contra hcon
      have hn1 : n = 1 := by omega
      subst hn1
      have hle1 : S.card ≤ 1 := by
        have hsub : S ⊆ Nat.divisors 1 := by
          rw [hS]
          exact Finset.filter_subset _ _
        rw [Nat.divisors_one] at hsub
        calc S.card ≤ ({1} : Finset ℕ).card := Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton 1
      have hle1' : (S.card : ℝ) ≤ 1 := by exact_mod_cast hle1
      linarith [hklt4, h16, hle1']
    have hlogn : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
    set t := ⌈θ * (S.card : ℝ)⌉₊ with ht
    have hθk0 : (0 : ℝ) ≤ θ * (S.card : ℝ) := by positivity
    have htle : θ * (S.card : ℝ) ≤ (t : ℝ) := Nat.le_ceil _
    have htlt : (t : ℝ) < θ * (S.card : ℝ) + 1 := Nat.ceil_lt_add_one hθk0
    set ζ := (t : ℝ) - θ * (S.card : ℝ) with hζ
    have hζ0 : (0 : ℝ) ≤ ζ := by rw [hζ]; linarith [htle]
    have hζ1 : ζ < 1 := by rw [hζ]; linarith [htlt]
    have hcohen := cohen_dvd S n t hSdiv hS0 hn0
    rw [← hP] at hcohen
    have hposA : 0 < ∏ x ∈ S, x ^ (2 * t) :=
      Finset.prod_pos (fun x hx => pow_pos (Nat.pos_of_ne_zero (hS0 x hx)) _)
    have hgcd_ne : ∀ p ∈ P, Nat.gcd p.1 p.2 ≠ 0 := by
      intro p hp
      rw [hP] at hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      have h1 := hS0 _ hp.1.1
      obtain ⟨k, hk⟩ := Nat.gcd_dvd_left p.1 p.2
      intro hcon
      apply h1
      rw [hcon, zero_mul] at hk
      exact hk
    have hposB : 0 < n ^ (2 * (t * (t + 1) / 2))
        * ∏ p ∈ P, (Nat.gcd p.1 p.2) ^ 2 :=
      mul_pos (pow_pos (Nat.pos_of_ne_zero hn0) _)
        (Finset.prod_pos fun p hp => pow_pos (Nat.pos_of_ne_zero (hgcd_ne p hp)) _)
    have hle_nat := Nat.le_of_dvd hposB hcohen
    have hlogx : ∀ x ∈ S, θ * Real.log (n : ℝ) ≤ Real.log (x : ℝ) := by
      intro x hx
      obtain ⟨-, hX, -⟩ := hmemS x hx
      have hpos : (0 : ℝ) < (n : ℝ) ^ θ := Real.rpow_pos_of_pos hnpos θ
      have h := Real.log_le_log hpos hX
      rw [Real.log_rpow hnpos θ] at h
      exact h
    have hloggcd : ∀ p ∈ P, Real.log ((Nat.gcd p.1 p.2 : ℕ) : ℝ)
        ≤ (θ ^ 2 - ε) * Real.log (n : ℝ) := by
      intro p hp
      have hp' : p ∈ (S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 < p.2) := by
        rw [← hP]
        exact hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp'
      obtain ⟨⟨hxS, hyS⟩, hlt⟩ := hp'
      obtain ⟨-, hXx, -⟩ := hmemS _ hxS
      obtain ⟨-, -, hYy⟩ := hmemS _ hyS
      have hgcd_pos : (0 : ℝ) < ((Nat.gcd p.1 p.2 : ℕ) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (hgcd_ne p hp)
      have hdvd : Nat.gcd p.1 p.2 ∣ p.2 - p.1 :=
        Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
      have hle : ((Nat.gcd p.1 p.2 : ℕ) : ℝ) ≤ (n : ℝ) ^ (θ ^ 2 - ε) := by
        have hpos1 : 0 < p.2 - p.1 := by omega
        have hle1 : Nat.gcd p.1 p.2 ≤ p.2 - p.1 := Nat.le_of_dvd hpos1 hdvd
        have hcast : (((p.2 - p.1 : ℕ)) : ℝ) = (p.2 : ℝ) - (p.1 : ℝ) :=
          Nat.cast_sub (le_of_lt hlt)
        have hle2 : (p.2 : ℝ) - (p.1 : ℝ) ≤ (n : ℝ) ^ (θ ^ 2 - ε) := by
          linarith [hYy, hXx]
        calc ((Nat.gcd p.1 p.2 : ℕ) : ℝ) ≤ (((p.2 - p.1 : ℕ)) : ℝ) := by exact_mod_cast hle1
          _ = (p.2 : ℝ) - (p.1 : ℝ) := hcast
          _ ≤ (n : ℝ) ^ (θ ^ 2 - ε) := hle2
      have h := Real.log_le_log hgcd_pos hle
      rw [Real.log_rpow hnpos (θ ^ 2 - ε)] at h
      exact h
    have hneA : ∀ x ∈ S, ((x : ℝ)) ^ (2 * t) ≠ 0 := by
      intro x hx
      exact ne_of_gt (pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (hS0 x hx)) _)
    have hneQ : ∀ p ∈ P, ((((Nat.gcd p.1 p.2) ^ 2 : ℕ)) : ℝ) ≠ 0 := by
      intro p hp
      rw [Nat.cast_pow]
      exact ne_of_gt (pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (hgcd_ne p hp)) 2)
    have hnR0 : (((n ^ (2 * (t * (t + 1) / 2)) : ℕ)) : ℝ) ≠ 0 := by
      have h : (0 : ℝ) < (((n ^ (2 * (t * (t + 1) / 2)) : ℕ)) : ℝ) := by
        rw [Nat.cast_pow]
        exact pow_pos hnpos _
      exact ne_of_gt h
    have hQ0 : ((∏ p ∈ P, (Nat.gcd p.1 p.2) ^ 2 : ℕ) : ℝ) ≠ 0 := by
      have hQpos : (0 : ℝ) < ∏ p ∈ P, (((Nat.gcd p.1 p.2 : ℕ)) : ℝ) ^ 2 :=
        Finset.prod_pos (fun p hp =>
          pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (hgcd_ne p hp)) 2)
      have hQcast : ((∏ p ∈ P, (Nat.gcd p.1 p.2) ^ 2 : ℕ) : ℝ)
          = ∏ p ∈ P, (((Nat.gcd p.1 p.2 : ℕ)) : ℝ) ^ 2 := by
        rw [Nat.cast_prod]
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [Nat.cast_pow]
      rw [hQcast]
      exact ne_of_gt hQpos
    have hcastA : (((∏ x ∈ S, x ^ (2 * t) : ℕ)) : ℝ) = ∏ x ∈ S, ((x : ℝ)) ^ (2 * t) := by
      rw [Nat.cast_prod]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [Nat.cast_pow]
    have hexpA : Real.log (((∏ x ∈ S, x ^ (2 * t) : ℕ)) : ℝ)
        = ∑ x ∈ S, (2 * (t : ℝ)) * Real.log (x : ℝ) := by
      rw [hcastA, Real.log_prod hneA]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
    have hexpB : Real.log (((n ^ (2 * (t * (t + 1) / 2))
          * ∏ p ∈ P, (Nat.gcd p.1 p.2) ^ 2 : ℕ)) : ℝ)
        = (2 * (((t * (t + 1) / 2 : ℕ)) : ℝ)) * Real.log (n : ℝ)
          + ∑ p ∈ P, (2 : ℝ) * Real.log ((Nat.gcd p.1 p.2 : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul hnR0 hQ0, Nat.cast_pow, Nat.cast_prod]
      congr 1
      · rw [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
      · rw [Real.log_prod hneQ]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    have hlog : Real.log (((∏ x ∈ S, x ^ (2 * t) : ℕ)) : ℝ)
        ≤ Real.log (((n ^ (2 * (t * (t + 1) / 2))
          * ∏ p ∈ P, (Nat.gcd p.1 p.2) ^ 2 : ℕ)) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hposA) (by exact_mod_cast hle_nat)
    have hsumA : ∑ x ∈ S, (2 * (t : ℝ)) * (θ * Real.log (n : ℝ))
        ≤ ∑ x ∈ S, (2 * (t : ℝ)) * Real.log (x : ℝ) :=
      Finset.sum_le_sum (fun x hx =>
        mul_le_mul_of_nonneg_left (hlogx x hx) (by positivity))
    have hsumB : ∑ p ∈ P, (2 : ℝ) * Real.log ((Nat.gcd p.1 p.2 : ℕ) : ℝ)
        ≤ ∑ p ∈ P, (2 : ℝ) * ((θ ^ 2 - ε) * Real.log (n : ℝ)) :=
      Finset.sum_le_sum (fun p hp =>
        mul_le_mul_of_nonneg_left (hloggcd p hp) (by norm_num))
    have hAL : (∑ x ∈ S, (2 * (t : ℝ)) * (θ * Real.log (n : ℝ)))
        = (2 * (t : ℝ) * (S.card : ℝ) * θ) * Real.log (n : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    have hBL : (∑ p ∈ P, (2 : ℝ) * ((θ ^ 2 - ε) * Real.log (n : ℝ)))
        = (2 * (P.card : ℝ) * (θ ^ 2 - ε)) * Real.log (n : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    have key : (2 * (t : ℝ) * (S.card : ℝ) * θ) * Real.log (n : ℝ)
        ≤ (2 * (((t * (t + 1) / 2 : ℕ)) : ℝ)) * Real.log (n : ℝ)
          + (2 * (P.card : ℝ) * (θ ^ 2 - ε)) * Real.log (n : ℝ) := by
      rw [← hAL, ← hBL]
      linarith [hlog, hexpA, hexpB, hsumA, hsumB]
    have key2 : (2 * (t : ℝ) * (S.card : ℝ) * θ) * Real.log (n : ℝ)
        ≤ (2 * (((t * (t + 1) / 2 : ℕ)) : ℝ)
          + 2 * (P.card : ℝ) * (θ ^ 2 - ε)) * Real.log (n : ℝ) := by
      rw [add_mul]
      exact key
    have hdiv : (2 : ℝ) * (t : ℝ) * (S.card : ℝ) * θ
        ≤ 2 * (((t * (t + 1) / 2 : ℕ)) : ℝ) + 2 * (P.card : ℝ) * (θ ^ 2 - ε) :=
      (mul_le_mul_iff_of_pos_right hlogn).mp key2
    have h2E : 2 * (t * (t + 1) / 2) = t * (t + 1) :=
      Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self t)
    have hE : (2 : ℝ) * (((t * (t + 1) / 2 : ℕ)) : ℝ) = (t : ℝ) * ((t : ℝ) + 1) := by
      exact_mod_cast h2E
    have hNS : 2 * P.card = S.card ^ 2 - S.card := by
      rw [hP]
      exact card_filter_lt_mul_two S
    have hkk : S.card * (S.card - 1) = S.card ^ 2 - S.card := by
      rw [mul_tsub, mul_one, pow_two]
    have hNpc : 2 * P.card = S.card * (S.card - 1) := by
      rw [hkk]
      exact hNS
    have hPc : (2 : ℝ) * (P.card : ℝ) = (S.card : ℝ) * ((S.card : ℝ) - 1) := by
      have hsub : (((S.card - 1 : ℕ)) : ℝ) = (S.card : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ S.card), Nat.cast_one]
      have h1 := congrArg (fun x : ℕ => (x : ℝ)) hNpc
      simp only [Nat.cast_mul, Nat.cast_ofNat, hsub] at h1
      exact h1
    have ht : (t : ℝ) = θ * (S.card : ℝ) + ζ := by
      rw [hζ]
      ring
    have hexp : ε * (S.card : ℝ) * ((S.card : ℝ) - 1)
        ≤ θ * (S.card : ℝ) - θ ^ 2 * (S.card : ℝ) + ζ * (ζ + 1) := by
      rw [ht] at hdiv hE
      linear_combination hdiv + hE + (θ ^ 2 - ε) * hPc
    have hζ2 : ζ * (ζ + 1) ≤ 2 := by
      have h1 : (0 : ℝ) ≤ ζ + 2 := by linarith [hζ0]
      have h2 : ζ - 1 ≤ 0 := by linarith [hζ1]
      have h := mul_nonpos_of_nonneg_of_nonpos h1 h2
      linear_combination h
    have hle2 : ε * (S.card : ℝ) * ((S.card : ℝ) - 1)
        ≤ (θ * (1 - θ)) * (S.card : ℝ) + 2 := by
      linear_combination hexp + hζ2
    have hAk : (4 : ℝ) < (S.card : ℝ) * (θ * (1 - θ)) := by
      have h := mul_lt_mul_of_pos_right hklt4 hApos
      rwa [div_mul_cancel₀ _ hApos.ne'] at h
    have h2 : (2 : ℝ) < (S.card : ℝ) * (θ * (1 - θ)) / 2 := by linarith [hAk]
    have hk2' : (S.card : ℝ) / 2 ≤ (S.card : ℝ) - 1 := by
      have h2k : (2 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hk2
      linarith
    have hnn0 : (0 : ℝ) ≤ ε * (S.card : ℝ) :=
      mul_nonneg hε0.le (Nat.cast_nonneg _)
    have hmul : ε * (S.card : ℝ) * ((S.card : ℝ) / 2)
        ≤ ε * (S.card : ℝ) * ((S.card : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hk2' hnn0
    have hfin : ε * (S.card : ℝ) * ((S.card : ℝ) / 2)
        < (θ * (1 - θ)) * (S.card : ℝ) + (S.card : ℝ) * (θ * (1 - θ)) / 2 := by
      linarith [hmul, hle2, h2]
    have hkpos : (0 : ℝ) < (S.card : ℝ) / 2 := by
      have h2k : (2 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hk2
      linarith
    have hdiv2 : ε * (S.card : ℝ) < 3 * (θ * (1 - θ)) := by
      have hfin2 : (ε * (S.card : ℝ)) * ((S.card : ℝ) / 2)
          < (3 * (θ * (1 - θ))) * ((S.card : ℝ) / 2) := by
        linear_combination hfin
      exact (mul_lt_mul_iff_of_pos_right hkpos).mp hfin2
    have hklt : (S.card : ℝ) < 3 * ((θ * (1 - θ)) / ε) := by
      rw [← mul_div_assoc, lt_div_iff₀ hε0]
      linarith [hdiv2]
    have hnn1 : (0 : ℝ) ≤ (θ * (1 - θ)) / ε := div_nonneg hApos.le hε0.le
    have hnn2 : (0 : ℝ) ≤ 1 / (θ * (1 - θ)) := div_nonneg zero_le_one hApos.le
    linarith [hklt, hnn1, hnn2]

end

end MetaMathlibExt
