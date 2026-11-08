/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ConsecutivePrime
public import MathlibExt.NumberTheory.PrimeGap
public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.LiminfLimsup

/-!
# The least recurring consecutive-prime gap

The increasing enumeration is `Nat.nth Nat.Prime`; `primeGap` is the existing
canonical difference of two successive entries. Its liminf stays in `WithTop ℕ`,
so finiteness is not assumed. Index zero has gap one and is irrelevant to the liminf.
-/

@[expose] public section

namespace MathlibExt.NumberTheory

/-- The liminf of actual consecutive-prime gaps, with infinity retained. -/
noncomputable def primeGapLiminf : WithTop ℕ :=
  Filter.liminf (fun n : ℕ ↦ (primeGap n : WithTop ℕ)) Filter.atTop

/-- Successive entries of the prime enumeration are genuinely consecutive primes. -/
theorem consecutive_nth_prime (n : ℕ) :
    MetaMathlibExt.AreConsecutivePrimes (Nat.nth Nat.Prime n) (Nat.nth Nat.Prime (n + 1)) := by
  refine ⟨Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n,
    Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (n + 1),
    Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self n), ?_⟩
  intro r hr
  by_cases h : r ≤ Nat.nth Nat.Prime n
  · exact Or.inl h
  · exact Or.inr ((Nat.nth_add_one_le_iff Nat.infinite_setOfPred_prime hr).2
      (Nat.lt_of_not_ge h))

/-- Every actual consecutive-prime gap is positive, including the first gap. -/
theorem primeGap_pos (n : ℕ) : 0 < primeGap n := by
  exact Nat.sub_pos_iff_lt.mpr
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self n))

/-- After the prime two, both endpoints are odd and every gap is at least two. -/
theorem two_le_primeGap (n : ℕ) (hn : 1 ≤ n) : 2 ≤ primeGap n := by
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hpPrime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n
  have hqPrime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (n + 1)
  have htwo_lt_p : 2 < Nat.nth Nat.Prime n := by
    rw [← Nat.nth_prime_zero_eq_two]
    exact hmono hn
  have hp_lt_q := hmono (Nat.lt_succ_self n)
  have hpOdd := hpPrime.odd_of_ne_two (ne_of_gt htwo_lt_p)
  have hqOdd := hqPrime.odd_of_ne_two (ne_of_gt (htwo_lt_p.trans hp_lt_q))
  refine (Nat.two_le_iff _).2 ⟨ne_of_gt (primeGap_pos n), ?_⟩
  intro hgap
  have hgapEven := Nat.Odd.sub_odd hqOdd hpOdd
  change Even (primeGap n) at hgapEven
  simp [hgap] at hgapEven

/-- The elementary lower bound for the least recurring prime gap. -/
theorem two_le_primeGapLiminf : 2 ≤ primeGapLiminf := by
  unfold primeGapLiminf
  refine Filter.le_liminf_of_le (by isBoundedDefault) (Filter.eventually_atTop.2 ⟨1, ?_⟩)
  intro n hn
  exact WithTop.coe_le_coe.mpr (two_le_primeGap n hn)

/-- A finite upper bound on the liminf means infinitely many actual gaps obey that bound. -/
theorem primeGapLiminf_le_iff_infinite (B : ℕ) :
    primeGapLiminf ≤ (B : WithTop ℕ) ↔ Set.Infinite {n : ℕ | primeGap n ≤ B} := by
  constructor
  · intro h
    have hlt : primeGapLiminf < ((B + 1 : ℕ) : WithTop ℕ) :=
      h.trans_lt (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self B))
    have hfreq := Filter.frequently_lt_of_liminf_lt
      (u := fun n : ℕ ↦ (primeGap n : WithTop ℕ)) (by isBoundedDefault) hlt
    exact Nat.frequently_atTop_iff_infinite.mp (hfreq.mono fun n hn ↦
      Nat.lt_succ_iff.mp (WithTop.coe_lt_coe.mp hn))
  · intro h
    exact Filter.liminf_le_of_frequently_le
      ((Nat.frequently_atTop_iff_infinite.mpr h).mono fun n hn ↦ WithTop.coe_le_coe.mpr hn)

/-- Finiteness is equivalent to the exact bounded-prime-pairs proposition already
requested by `WantedExt.NumberTheory.BoundedPrimeGapsWanted`. No finiteness is proved here. -/
theorem primeGapLiminf_ne_top_iff_bounded_pairs :
    primeGapLiminf ≠ ⊤ ↔ ∃ B : ℕ, 0 < B ∧
      Set.Infinite {p : ℕ | Nat.Prime p ∧
        ∃ q : ℕ, Nat.Prime q ∧ p < q ∧ q - p ≤ B} := by
  constructor
  · intro hfinite
    obtain ⟨B, hB⟩ := WithTop.ne_top_iff_exists.mp hfinite
    have hle : primeGapLiminf ≤ ((B + 1 : ℕ) : WithTop ℕ) := by
      rw [← hB]
      exact WithTop.coe_le_coe.mpr (Nat.le_succ B)
    have hinf := (primeGapLiminf_le_iff_infinite (B + 1)).mp hle
    have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
    refine ⟨B + 1, Nat.succ_pos B, (hinf.image hmono.injective.injOn).mono ?_⟩
    rintro p ⟨n, hn, rfl⟩
    exact ⟨Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n,
      Nat.nth Nat.Prime (n + 1),
      Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (n + 1),
      hmono (Nat.lt_succ_self n), hn⟩
  · rintro ⟨B, _, hinfPrimes⟩
    have hinfImage : Set.Infinite ((Nat.nth Nat.Prime) '' {n : ℕ | primeGap n ≤ B}) := by
      apply hinfPrimes.mono
      rintro p ⟨hp, q, hq, hpq, hgap⟩
      obtain ⟨n, rfl⟩ := Nat.subset_range_nth hp
      refine ⟨n, ?_, rfl⟩
      have hnext := (Nat.nth_add_one_le_iff Nat.infinite_setOfPred_prime hq).2 hpq
      exact (Nat.sub_le_sub_right hnext _).trans hgap
    have hle := (primeGapLiminf_le_iff_infinite B).mpr hinfImage.of_image
    exact ne_of_lt (hle.trans_lt (WithTop.coe_lt_top B))

/-- An actual gap two is equivalent to a twin prime at the same prime index. -/
theorem primeGap_eq_two_iff (n : ℕ) :
    primeGap n = 2 ↔ Nat.Prime (Nat.nth Nat.Prime n + 2) := by
  constructor
  · intro hgap
    have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
    have hspan := Nat.sub_add_cancel (hmono (Nat.lt_succ_self n)).le
    have heq : Nat.nth Nat.Prime (n + 1) = Nat.nth Nat.Prime n + 2 := by
      change primeGap n + Nat.nth Nat.Prime n = Nat.nth Nat.Prime (n + 1) at hspan
      omega
    rw [← heq]
    exact Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (n + 1)
  · intro hq
    have hn : 1 ≤ n := by
      by_contra h
      have hn0 : n = 0 := by omega
      have hfour : Nat.Prime 4 := by simpa [hn0, Nat.nth_prime_zero_eq_two] using hq
      exact (by decide : ¬ Nat.Prime 4) hfour
    have hnext : Nat.nth Nat.Prime (n + 1) ≤ Nat.nth Nat.Prime n + 2 :=
      (Nat.nth_add_one_le_iff Nat.infinite_setOfPred_prime hq).2 (by
        change Nat.nth Nat.Prime n < Nat.nth Nat.Prime n + 2
        omega)
    have hlow := two_le_primeGap n hn
    change Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n = 2
    change 2 ≤ Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n at hlow
    omega

/-- Equality to two means precisely infinitely many actual twin-prime pairs. -/
theorem primeGapLiminf_eq_two_iff :
    primeGapLiminf = 2 ↔ Set.Infinite {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)} := by
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hset : (Nat.nth Nat.Prime) '' {n : ℕ | primeGap n = 2} =
      {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)} := by
    ext p
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n,
        (primeGap_eq_two_iff n).mp hn⟩
    · rintro ⟨hp, hq⟩
      obtain ⟨n, rfl⟩ := Nat.subset_range_nth hp
      exact ⟨n, (primeGap_eq_two_iff n).mpr hq, rfl⟩
  constructor
  · intro h
    have hinf := (primeGapLiminf_le_iff_infinite 2).mp h.le
    have hfreq := Nat.frequently_atTop_iff_infinite.mpr hinf
    have htwo : ∃ᶠ n : ℕ in Filter.atTop, primeGap n = 2 := by
      refine (hfreq.and_eventually (Filter.eventually_atTop.2 ⟨1, fun _ hn ↦ hn⟩)).mono ?_
      intro n hn
      exact le_antisymm hn.1 (two_le_primeGap n hn.2)
    rw [← hset]
    exact (Nat.frequently_atTop_iff_infinite.mp htwo).image hmono.injective.injOn
  · intro h
    rw [← hset] at h
    have hup := (primeGapLiminf_le_iff_infinite 2).mpr
      (h.of_image.mono fun n hn ↦ hn.le)
    exact le_antisymm hup two_le_primeGapLiminf

end MathlibExt.NumberTheory
