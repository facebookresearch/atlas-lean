/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HardyLittlewoodPrimeTuple
public import Mathlib.NumberTheory.SmoothNumbers

/-!
# Difference smoothness of admissible sets

A singleton is difference smooth at every bound. An admissible set of at least
`z` integers cannot be difference smooth below the prime `z`.
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

end

end MetaMathlibExt
