/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Sieve.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Squarefree

/-!
# Brun's pure sieve

Brun's truncated Möbius function `μ_r(d)` agrees with `μ(d)` when `d` has at most `r` distinct
prime factors and vanishes otherwise. Its divisor sum `ψ_r = μ_r * ζ` is an alternating
binomial coefficient, `ψ_r(n) = (-1)^r C(ω(n) - 1, r)` for `n ≥ 2`, so it oscillates in sign
with `r` (the Bonferroni inequalities). Summed over the divisors of a sifting product against
a multiplicative density, it is small when `r` is large compared to `log log z`.

## Main definitions

* `ArithmeticFunction.brunMoebius r`: Brun's truncated Möbius function `μ_r`.
* `ArithmeticFunction.brunPsi r`: its divisor sum `ψ_r = μ_r * ζ`.

## Main statements

* `ArithmeticFunction.brunPsi_eq_neg_one_pow_mul_choose`: `ψ_r(n) = (-1)^r C(ω(n) - 1, r)` for
  `n ≥ 2`.
* `ArithmeticFunction.abs_sum_brunPsi_mul_div_le`: for a sieve density `ω` with
  `∑_{p ≤ z, P p} ω(p)/p ≤ c₁ log log z + c₂`,
  `|∑_{δ ∣ P(z), δ > 1} ψ_r(δ) ω(δ) / Ω(δ)| ≤ K (c₁ log log z + c₄)^r (log z)^{c₁} / r!`, where
  `Ω(δ) = ∏_{p ∣ δ} (p - ω(p))`.
-/

@[expose] public section

open Finset

namespace ArithmeticFunction

open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega ArithmeticFunction.zeta

/-- `ω n = #n.primeFactors`. -/
theorem cardDistinctFactors_eq_card_primeFactors (n : ℕ) : ω n = n.primeFactors.card := by
  rw [cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

/-- `ω (∏ p ∈ s, p) = #s` for a finset `s` of primes. -/
theorem cardDistinctFactors_prod_of_prime {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    ω (∏ p ∈ s, p) = s.card := by
  rw [cardDistinctFactors_eq_card_primeFactors, Nat.primeFactors_prod hs]

/-- `μ (∏ p ∈ s, p) = (-1) ^ #s` for a finset `s` of primes. -/
theorem moebius_prod_of_prime {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    μ (∏ p ∈ s, p) = (-1) ^ s.card := by
  have hsq := Nat.squarefree_prod_of_prime hs
  rw [moebius_apply_of_squarefree hsq,
    ← (cardDistinctFactors_eq_cardFactors_iff_squarefree hsq.ne_zero).mpr hsq,
    cardDistinctFactors_prod_of_prime hs]

/-- Squarefree divisors of `n ≠ 0` correspond to subsets of `n.primeFactors`. This is Mathlib's
`Nat.sum_divisors_filter_squarefree`, indexed by `primeFactors` instead of `normalizedFactors`. -/
theorem sum_divisors_filter_squarefree_eq_sum_powerset {M : Type*} [AddCommMonoid M] {n : ℕ}
    (hn : n ≠ 0) (f : ℕ → M) :
    ∑ d ∈ n.divisors with Squarefree d, f d = ∑ s ∈ n.primeFactors.powerset, f (∏ p ∈ s, p) := by
  rw [Nat.sum_divisors_filter_squarefree hn, Nat.factors_eq]
  simp only [Finset.prod_val]
  rfl

/-- Brun's truncated Möbius function: `μ_r(d) = μ(d)` if `d` has at most `r` distinct prime
factors, and `0` otherwise. -/
def brunMoebius (r : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun d => if ω d ≤ r then μ d else 0, by simp⟩

/-- Unfolding `μ_r`. -/
theorem brunMoebius_apply (r d : ℕ) : brunMoebius r d = if ω d ≤ r then μ d else 0 := rfl

/-- The divisor sum `ψ_r = μ_r * ζ` of Brun's truncated Möbius function. -/
def brunPsi (r : ℕ) : ArithmeticFunction ℤ := brunMoebius r * ζ

/-- `ψ_r(n) = ∑_{d ∣ n} μ_r(d)`. -/
theorem brunPsi_apply (r n : ℕ) : brunPsi r n = ∑ d ∈ n.divisors, brunMoebius r d := by
  rw [brunPsi, coe_mul_zeta_apply]

/-- `ψ_r(1) = 1`. -/
theorem brunPsi_one (r : ℕ) : brunPsi r 1 = 1 := by
  simp [brunPsi_apply, brunMoebius_apply]

/-- **Brun's truncation identity**: for `n ≥ 2`, `ψ_r(n) = (-1)^r C(ω(n) - 1, r)`. -/
theorem brunPsi_eq_neg_one_pow_mul_choose {n : ℕ} (hn : 2 ≤ n) (r : ℕ) :
    brunPsi r n = (-1) ^ r * ((ω n - 1).choose r : ℤ) := by
  set g : ℕ → ℤ := fun k => if k ≤ r then (-1) ^ k else 0 with hg
  have hn0 : n ≠ 0 := by omega
  have h1 : brunPsi r n = ∑ d ∈ n.divisors with Squarefree d, brunMoebius r d := by
    rw [brunPsi_apply, Finset.sum_filter_of_ne]
    intro d _ hd
    by_contra hsq
    apply hd
    simp [brunMoebius_apply, moebius_eq_zero_of_not_squarefree hsq]
  have h2 : ∑ d ∈ n.divisors with Squarefree d, brunMoebius r d =
      ∑ s ∈ n.primeFactors.powerset, g s.card := by
    rw [sum_divisors_filter_squarefree_eq_sum_powerset hn0]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hp : ∀ p ∈ s, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hs hp)
    simp only [brunMoebius_apply, hg, cardDistinctFactors_prod_of_prime hp,
      moebius_prod_of_prime hp]
  rw [h1, h2, Finset.sum_powerset_apply_card, ← cardDistinctFactors_eq_card_primeFactors]
  obtain ⟨m, hm⟩ : ∃ m, ω n = m + 1 := by
    refine Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero ?_)
    rw [Ne, cardDistinctFactors_eq_zero]; omega
  rw [hm, Nat.add_sub_cancel, ← Int.alternating_sum_range_choose_eq_choose]
  set F : ℕ → ℤ := fun k => if k ≤ r then (-1 : ℤ) ^ k * ((m + 1).choose k : ℤ) else 0 with hF
  calc ∑ k ∈ Finset.range (m + 1 + 1), (m + 1).choose k • g k
      = ∑ k ∈ Finset.range (m + 1 + 1), F k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hg, hF, nsmul_eq_mul]
        split_ifs <;> ring
    _ = ∑ k ∈ Finset.range (m + r + 2), F k := by
        refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun k _ hk => ?_
        simp only [Finset.mem_range, not_lt] at hk
        simp [hF, Nat.choose_eq_zero_of_lt (by omega : m + 1 < k)]
    _ = ∑ k ∈ Finset.range (r + 1), F k := by
        refine (Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
          fun k _ hk => ?_).symm
        simp only [Finset.mem_range, not_lt] at hk
        simp only [hF]
        rw [ite_eq_right (by omega)]
    _ = ∑ k ∈ Finset.range (r + 1), (-1) ^ k * ((m + 1).choose k : ℤ) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_range] at hk
        simp only [hF]
        rw [ite_eq_left (by omega)]

/-- `r! ∑_{T ⊆ S} C(|T|, r) ∏_{p ∈ T} a_p ≤ A^r e^A` with `A = ∑_{p ∈ S} a_p`, for `a ≥ 0`
on `S`. -/
private theorem factorial_mul_sum_powerset_choose_le (a : ℕ → ℝ) (S : Finset ℕ)
    (ha : ∀ p ∈ S, 0 ≤ a p) :
    ∀ r : ℕ, (r.factorial : ℝ) * ∑ T ∈ S.powerset, ((T.card.choose r : ℕ) : ℝ) * ∏ p ∈ T, a p ≤
      (∑ p ∈ S, a p) ^ r * Real.exp (∑ p ∈ S, a p) := by
  induction S using Finset.induction_on with
  | empty => intro r; cases r <;> simp
  | @insert x S hx ih =>
    have ha' : ∀ p ∈ S, 0 ≤ a p := fun p hp => ha p (Finset.mem_insert_of_mem hp)
    have hax : 0 ≤ a x := ha x (Finset.mem_insert_self x S)
    have ih := ih ha'
    set A := ∑ p ∈ S, a p with hAdef
    have hA : 0 ≤ A := Finset.sum_nonneg ha'
    set F : ℕ → ℝ := fun r => ∑ T ∈ S.powerset, ((T.card.choose r : ℕ) : ℝ) * ∏ p ∈ T, a p
      with hFdef
    have hsplit : ∀ r, ∑ T ∈ (insert x S).powerset, ((T.card.choose r : ℕ) : ℝ) * ∏ p ∈ T, a p =
        F r + a x * ∑ T ∈ S.powerset, (((T.card + 1).choose r : ℕ) : ℝ) * ∏ p ∈ T, a p := by
      intro r
      rw [Finset.sum_powerset_insert hx, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun T hT => ?_
      have : x ∉ T := fun h => hx (Finset.mem_powerset.mp hT h)
      rw [Finset.card_insert_of_notMem this, Finset.prod_insert this]; ring
    have hsum : ∑ p ∈ insert x S, a p = A + a x := by rw [Finset.sum_insert hx]; ring
    have hexp : Real.exp A * (1 + a x) ≤ Real.exp (A + a x) := by
      rw [Real.exp_add]; gcongr; linarith [Real.add_one_le_exp (a x)]
    intro r
    rw [hsplit r, hsum]
    cases r with
    | zero =>
      have h0 : ∑ T ∈ S.powerset, (((T.card + 1).choose 0 : ℕ) : ℝ) * ∏ p ∈ T, a p = F 0 := by
        simp [hFdef]
      rw [h0]
      have := ih 0
      simp only [Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero] at this ⊢
      nlinarith
    | succ r =>
      have h0 : ∑ T ∈ S.powerset, (((T.card + 1).choose (r + 1) : ℕ) : ℝ) * ∏ p ∈ T, a p =
          F r + F (r + 1) := by
        simp only [hFdef, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [Nat.choose_succ_succ]; push_cast; ring
      rw [h0]
      have h1 := ih (r + 1)
      have h2 := ih r
      have hfac : ((r + 1).factorial : ℝ) = (r + 1) * r.factorial := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hB : A ^ (r + 1) + (r + 1) * a x * A ^ r ≤ (A + a x) ^ (r + 1) := by
        have := pow_add_mul_le_add_pow hA (by linarith : 0 ≤ 2 * A + a x) (r + 1)
        simp only [Nat.add_sub_cancel] at this
        push_cast at this
        linarith
      calc ((r + 1).factorial : ℝ) * (F (r + 1) + a x * (F r + F (r + 1)))
          = (1 + a x) * (((r + 1).factorial : ℝ) * F (r + 1)) +
              a x * (r + 1) * ((r.factorial : ℝ) * F r) := by rw [hfac]; ring
        _ ≤ (1 + a x) * (A ^ (r + 1) * Real.exp A) + a x * (r + 1) * (A ^ r * Real.exp A) := by
          gcongr
        _ = Real.exp A * (1 + a x) * (A ^ (r + 1) + (r + 1) * a x * A ^ r) -
              a x ^ 2 * (r + 1) * A ^ r * Real.exp A := by ring
        _ ≤ Real.exp A * (1 + a x) * (A + a x) ^ (r + 1) := by
          have : 0 ≤ a x ^ 2 * (r + 1) * A ^ r * Real.exp A := by positivity
          have : Real.exp A * (1 + a x) * (A ^ (r + 1) + (r + 1) * a x * A ^ r) ≤
              Real.exp A * (1 + a x) * (A + a x) ^ (r + 1) := by gcongr
          linarith
        _ ≤ (A + a x) ^ (r + 1) * Real.exp (A + a x) := by
          rw [mul_comm ((A + a x) ^ (r + 1))]; gcongr

/-- **Brun's sieve remainder bound.** Let `0 ≤ ω(p) ≤ c` and `ω(p) < p` for the sifting primes,
and suppose `∑_{p ≤ z, P p} ω(p)/p ≤ c₁ log log z + c₂` for `z ≥ 3`. Then there are constants
`c₄, K` with
`|∑_{δ ∣ P(z), δ > 1} ψ_r(δ) ω(δ) / Ω(δ)| ≤ K (c₁ log log z + c₄)^r / r! · (log z)^{c₁}`
for every `z ≥ 3` and `r`, where `ω(δ) = ∏_{p ∣ δ} ω(p)` and `Ω(δ) = ∏_{p ∣ δ} (p - ω(p))`. -/
theorem abs_sum_brunPsi_mul_div_le (P : ℕ → Prop) [DecidablePred P] (ω' : ℕ → ℝ) (c c₁ c₂ : ℝ)
    (hω0 : ∀ p, 0 ≤ ω' p) (hωp : ∀ p, P p → p.Prime → ω' p < p) (hωc : ∀ p, ω' p ≤ c)
    (hsum : ∀ z : ℝ, 3 ≤ z →
      ∑ p ∈ (Nat.primesLE ⌊z⌋₊).filter P, ω' p / p ≤ c₁ * Real.log (Real.log z) + c₂) :
    ∃ c₄ K : ℝ, ∀ z : ℝ, 3 ≤ z → ∀ r : ℕ,
      |∑ δ ∈ (Nat.siftingPrimorial P ⌊z⌋₊).divisors with 1 < δ,
          (brunPsi r δ : ℝ) * (∏ p ∈ δ.primeFactors, ω' p) /
            ∏ p ∈ δ.primeFactors, ((p : ℝ) - ω' p)| ≤
        K * (c₁ * Real.log (Real.log z) + c₄) ^ r / r.factorial * Real.log z ^ c₁ := by
  set a : ℕ → ℝ := fun p => ω' p / ((p : ℝ) - ω' p) with ha_def
  have ha0 : ∀ p, P p → p.Prime → 0 ≤ a p := fun p hP hp =>
    div_nonneg (hω0 p) (by linarith [hωp p hP hp])
  set Q : Finset ℕ := (Finset.range (⌊2 * c⌋₊ + 1)).filter (fun p => P p ∧ p.Prime) with hQ
  set B : ℝ := ∑ p ∈ Q, a p with hB
  refine ⟨c₂ + 4 * c ^ 2 + B, Real.exp (c₂ + 4 * c ^ 2 + B), ?_⟩
  intro z hz r
  set S : Finset ℕ := (Nat.primesLE ⌊z⌋₊).filter P with hSdef
  have hSp : ∀ p ∈ S, p.Prime ∧ P p ∧ p ≤ ⌊z⌋₊ := fun p hp => by
    have h := Finset.mem_filter.mp hp
    exact ⟨(Nat.mem_primesLE.mp h.1).2, h.2, (Nat.mem_primesLE.mp h.1).1⟩
  have haS : ∀ p ∈ S, 0 ≤ a p := fun p hp => ha0 p (hSp p hp).2.1 (hSp p hp).1
  set A := ∑ p ∈ S, a p with hAdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg haS
  -- Step 1: reduce to the powerset sum
  have hstep1 : |∑ δ ∈ (Nat.siftingPrimorial P ⌊z⌋₊).divisors with 1 < δ,
        (brunPsi r δ : ℝ) * (∏ p ∈ δ.primeFactors, ω' p) /
          ∏ p ∈ δ.primeFactors, ((p : ℝ) - ω' p)| ≤
      ∑ T ∈ S.powerset, ((T.card.choose r : ℕ) : ℝ) * ∏ p ∈ T, a p := by
    have hN : Nat.siftingPrimorial P ⌊z⌋₊ = ∏ p ∈ S, p := rfl
    have hsq : Squarefree (∏ p ∈ S, p) := Nat.squarefree_prod_of_prime fun p hp => (hSp p hp).1
    have hpf : (∏ p ∈ S, p).primeFactors = S := Nat.primeFactors_prod fun p hp => (hSp p hp).1
    rw [hN]
    have hsub : ∀ δ ∈ (∏ p ∈ S, p).divisors, δ.primeFactors ⊆ S := fun δ hδ => by
      rw [← hpf]; exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hδ) hsq.ne_zero
    set g : ℕ → ℝ := fun δ => ((δ.primeFactors.card.choose r : ℕ) : ℝ) * ∏ p ∈ δ.primeFactors, a p
      with hg
    have hg0 : ∀ δ ∈ (∏ p ∈ S, p).divisors, 0 ≤ g δ := fun δ hδ =>
      mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun p hp => haS p (hsub δ hδ hp))
    have hfg : ∀ δ ∈ (∏ p ∈ S, p).divisors.filter (fun δ => 1 < δ),
        |(brunPsi r δ : ℝ) * (∏ p ∈ δ.primeFactors, ω' p) /
          ∏ p ∈ δ.primeFactors, ((p : ℝ) - ω' p)| ≤ g δ := by
      intro δ hδ
      obtain ⟨hδd, hδ1⟩ := Finset.mem_filter.mp hδ
      have hprod : 0 ≤ ∏ p ∈ δ.primeFactors, a p :=
        Finset.prod_nonneg fun p hp => haS p (hsub δ hδd hp)
      have hψ : |(brunPsi r δ : ℝ)| ≤ ((δ.primeFactors.card.choose r : ℕ) : ℝ) := by
        rw [brunPsi_eq_neg_one_pow_mul_choose (by omega) r,
          cardDistinctFactors_eq_card_primeFactors]
        simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
        exact_mod_cast Nat.choose_le_choose r (Nat.sub_le _ _)
      rw [mul_div_assoc, ← Finset.prod_div_distrib, abs_mul, abs_of_nonneg hprod]
      exact mul_le_mul_of_nonneg_right hψ hprod
    calc _ ≤ ∑ δ ∈ (∏ p ∈ S, p).divisors with 1 < δ,
            |(brunPsi r δ : ℝ) * (∏ p ∈ δ.primeFactors, ω' p) /
              ∏ p ∈ δ.primeFactors, ((p : ℝ) - ω' p)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ δ ∈ (∏ p ∈ S, p).divisors with 1 < δ, g δ := Finset.sum_le_sum hfg
      _ ≤ ∑ δ ∈ (∏ p ∈ S, p).divisors, g δ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun δ hδ _ => hg0 δ hδ
      _ = ∑ T ∈ S.powerset, ((T.card.choose r : ℕ) : ℝ) * ∏ p ∈ T, a p := by
          have hfil : (∏ p ∈ S, p).divisors.filter (fun d => Squarefree d) =
              (∏ p ∈ S, p).divisors := Finset.filter_true_of_mem fun δ hδ =>
                hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hδ)
          rw [← hfil, sum_divisors_filter_squarefree_eq_sum_powerset hsq.ne_zero, hpf]
          refine Finset.sum_congr rfl fun T hT => ?_
          simp only [hg]
          rw [Nat.primeFactors_prod fun p hp => (hSp p (Finset.mem_powerset.mp hT hp)).1]
  -- Step 2: bound `A`
  have hstep2 : A ≤ c₁ * Real.log (Real.log z) + (c₂ + 4 * c ^ 2 + B) := by
    have hpt : ∀ p ∈ S, a p ≤ ω' p / p + 2 * c ^ 2 * ((p : ℝ) ^ 2)⁻¹ +
        (if (p : ℝ) ≤ 2 * c then a p else 0) := by
      intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hSp p hp).1.pos
      have h1 : 0 ≤ ω' p / p := div_nonneg (hω0 p) hp0.le
      have h2 : 0 ≤ 2 * c ^ 2 * ((p : ℝ) ^ 2)⁻¹ := by positivity
      split_ifs with hpc
      · linarith
      · push Not at hpc
        have hw := hωc p
        have hw0 := hω0 p
        have hqw : (p : ℝ) / 2 < p - ω' p := by linarith
        have hqw0 : 0 < (p : ℝ) - ω' p := by linarith
        simp only [ha_def]
        rw [div_le_iff₀ hqw0]
        have e : (ω' p / p + 2 * c ^ 2 * ((p : ℝ) ^ 2)⁻¹ + 0) * (p - ω' p) =
            ω' p - ω' p ^ 2 / p + 2 * c ^ 2 * (p - ω' p) / p ^ 2 := by
          field_simp; ring
        rw [e]
        have h3 : ω' p ^ 2 / p ≤ 2 * c ^ 2 * (p - ω' p) / p ^ 2 := by
          rw [div_le_div_iff₀ hp0 (by positivity)]
          have h5 : ω' p ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hw0 hw 2
          have h6 := mul_nonneg (mul_nonneg (sq_nonneg c) hp0.le)
            (by linarith : (0 : ℝ) ≤ 2 * (p - ω' p) - p)
          have h7 := mul_le_mul_of_nonneg_right h5 (sq_nonneg (p : ℝ))
          nlinarith
        linarith
    have hS1 : ∑ p ∈ S, ω' p / p ≤ c₁ * Real.log (Real.log z) + c₂ := hsum z hz
    have hS2 : ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ ≤ 2 := by
      calc ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ ≤ ∑ i ∈ Finset.Ioo 0 (⌊z⌋₊ + 1), ((i : ℝ) ^ 2)⁻¹ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
            intro p hp
            have := hSp p hp
            simp only [Finset.mem_Ioo]
            exact ⟨this.1.pos, by omega⟩
        _ ≤ 2 / ((0 : ℕ) + 1 : ℝ) := sum_Ioo_inv_sq_le 0 _
        _ = 2 := by norm_num
    have hS3 : ∑ p ∈ S, (if (p : ℝ) ≤ 2 * c then a p else 0) ≤ B := by
      rw [← Finset.sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p hp _ => ?_
      · intro p hp
        obtain ⟨hpS, hpc⟩ := Finset.mem_filter.mp hp
        have := hSp p hpS
        simp only [hQ, Finset.mem_filter, Finset.mem_range]
        exact ⟨Nat.lt_succ_of_le (Nat.le_floor hpc), this.2.1, this.1⟩
      · obtain ⟨-, hpP, hpp⟩ := Finset.mem_filter.mp hp
        exact ha0 p hpP hpp
    calc A ≤ ∑ p ∈ S, (ω' p / p + 2 * c ^ 2 * ((p : ℝ) ^ 2)⁻¹ +
          (if (p : ℝ) ≤ 2 * c then a p else 0)) := Finset.sum_le_sum hpt
      _ = ∑ p ∈ S, ω' p / p + 2 * c ^ 2 * ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ +
          ∑ p ∈ S, (if (p : ℝ) ≤ 2 * c then a p else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (c₁ * Real.log (Real.log z) + c₂) + 2 * c ^ 2 * 2 + B := by
          have : 0 ≤ 2 * c ^ 2 := by positivity
          gcongr
      _ = c₁ * Real.log (Real.log z) + (c₂ + 4 * c ^ 2 + B) := by ring
  -- Step 3: assemble
  set X := c₁ * Real.log (Real.log z) + (c₂ + 4 * c ^ 2 + B) with hX
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have haux := factorial_mul_sum_powerset_choose_le a S haS r
  have hexp : Real.exp A ≤ Real.exp (c₂ + 4 * c ^ 2 + B) * Real.log z ^ c₁ := by
    rw [Real.rpow_def_of_pos hlogz, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by rw [hX] at hstep2; linarith)
  have hpow : A ^ r ≤ X ^ r := pow_le_pow_left₀ hA0 hstep2 r
  calc _ ≤ ∑ T ∈ S.powerset, ((T.card.choose r : ℕ) : ℝ) * ∏ p ∈ T, a p := hstep1
    _ ≤ A ^ r * Real.exp A / r.factorial := by
        rw [le_div_iff₀ hfac]; linarith
    _ ≤ X ^ r * (Real.exp (c₂ + 4 * c ^ 2 + B) * Real.log z ^ c₁) / r.factorial := by
        gcongr
        exact pow_nonneg (hA0.trans hstep2) r
    _ = Real.exp (c₂ + 4 * c ^ 2 + B) * X ^ r / r.factorial * Real.log z ^ c₁ := by ring

end ArithmeticFunction
