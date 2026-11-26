/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HardyLittlewoodPrimeTuple
public import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.Primorial
import MathlibExt.NumberTheory.AdmissibleFinsetSmallPrimes

/-!
# Difference smoothness of admissible sets

A singleton is difference smooth at every bound. An admissible set of at least
`z` integers cannot be difference smooth below the prime `z`. For every `k`, the first
`k` multiples of the primorial of `k` form an admissible difference `k`-smooth set.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Difference-smooth sets of integers.** Let $y$ be a natural number. A finite set $H$ of
integers is difference $y$-smooth if for all distinct $h, h' \in H$ every prime factor of
$h - h'$ is at most $y$.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Definition 3. -/
def IsDifferenceSmooth (y : ℕ) (H : Finset ℤ) : Prop :=
  ∀ a ∈ H, ∀ b ∈ H, a ≠ b → (a - b).natAbs ∈ Nat.smoothNumbers (y + 1)

/-- **One-element sets are difference smooth.** For every natural number $y$ and every integer
$a$, the set $\{a\}$ is difference $y$-smooth.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Definition 3. -/
theorem isDifferenceSmooth_singleton (y : ℕ) (a : ℤ) : IsDifferenceSmooth y {a} := by
  intro b hb c hc hbc
  rw [Finset.mem_singleton] at hb hc
  exact absurd (hb.trans hc.symm) hbc

/-- **Admissible sets are not difference smooth at small bounds.** Let $H$ be an admissible
finite set of $k \ge 2$ integers, let $z \le k$ be a prime and let $\ell < z$ be a natural
number. Then $H$ is not difference $\ell$-smooth. Equivalently, $H$ is not difference
$\ell$-smooth for any $\ell$ less than the largest prime at most $k$.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Proposition 1 (`integers-2025-A44-prop-1`). -/
theorem not_isDifferenceSmooth_of_isAdmissibleFinset (H : Finset ℤ)
    (hk : 2 ≤ H.card) (hH : IsAdmissibleFinset H) (z : ℕ) (hz : z.Prime) (hzk : z ≤ H.card)
    (ℓ : ℕ) (hℓ : ℓ < z) : ¬ IsDifferenceSmooth ℓ H := by
  intro hsmooth
  have : NeZero z := ⟨hz.ne_zero⟩
  obtain ⟨r, hr⟩ := hH z hz
  have hcard : (Finset.univ.erase r).card < H.card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, ZMod.card]
    exact (Nat.sub_le_sub_right hzk 1).trans_lt
      (Nat.sub_lt (Nat.zero_lt_of_lt hk) Nat.zero_lt_one)
  obtain ⟨a, ha, b, hb, hab, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (f := fun a : ℤ => (a : ZMod z)) hcard fun a ha =>
      Finset.mem_erase.mpr ⟨hr a ha, Finset.mem_univ _⟩
  have hdvd : z ∣ (b - a).natAbs :=
    Int.natCast_dvd.mp ((ZMod.intCast_eq_intCast_iff_dvd_sub a b z).mp heq)
  exact (Nat.not_lt_of_ge hℓ) (Nat.mem_smoothNumbers'.mp (hsmooth b hb a ha hab.symm) z hz hdvd)

/-- **Admissible difference-smooth sets of every size.** For every natural number $k$ there is
an admissible set $H$ of exactly $k$ integers that is difference $k$-smooth: for all distinct
$h, h' \in H$, every prime factor of $h - h'$ is at most $k$.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Theorem 5 (`integers-2025-A44-thm-5`). -/
theorem exists_admissible_differenceSmooth (k : ℕ) :
    ∃ H : Finset ℤ, H.card = k ∧ IsAdmissibleFinset H ∧ IsDifferenceSmooth k H := by
  let H := (Finset.range k).image fun i : ℕ => (i : ℤ) * (primorial k : ℤ)
  have hstep : (primorial k : ℤ) ≠ 0 := by exact_mod_cast primorial_ne_zero k
  have hcard : H.card = k := by
    rw [Finset.card_image_of_injective _ (fun i j hij => ?_), Finset.card_range]
    exact_mod_cast mul_right_cancel₀ hstep hij
  refine ⟨H, hcard, ?_, ?_⟩
  · apply (isAdmissibleFinset_iff_forall_prime_le_card H).2
    intro p hp hpk
    have := Fact.mk hp
    have hz : (primorial k : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff ..).2 (hp.dvd_primorial_iff.2 (hcard ▸ hpk))
    refine ⟨1, fun _ h => ?_⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    simp [hz]
  · intro a ha b hb hab
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    have hij : i ≠ j := fun heq => hab (heq ▸ rfl)
    rw [← sub_mul, Int.natAbs_mul, Int.natAbs_natCast]
    apply Nat.mul_mem_smoothNumbers
    · rw [Finset.mem_range] at hi hj
      exact Nat.mem_smoothNumbers_of_lt (by omega) (by omega)
    · exact Nat.mem_smoothNumbers'.2 fun p hp hdvd =>
        Nat.lt_succ_of_le (hp.dvd_primorial_iff.1 hdvd)

end

end MetaMathlibExt
