/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.PrimesCongruentOne

/-!
# Odd multiples of half the predecessor of a prime

Let `P` be the product of `(q - 1) / 2` over the selected primes `q`.
Choosing a prime `p ≡ 1 [MOD 4 * P]` makes `(p - 1) / 2` an even multiple of
every `(q - 1) / 2` in the family.
-/

namespace MetaMathlibExt

/-- **The odd multiples of $(p-1)/2$ admit no finite subcover.** For a prime $p$ write
$A_p = \{\tfrac{p-1}{2}(2m+1) : m \in \mathbb{N}\}$ for the set of odd multiples of $(p-1)/2$. For
every finite set $S$ of primes $q$ with $q \ge 13$ and $q \equiv 1 \pmod 4$, there is a natural
number $k$ that lies in $A_p$ for some prime $p \ge 13$ with $p \equiv 1 \pmod 4$ but lies in no
$A_q$ with $q \in S$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-
Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Lemma 3. -/
public theorem odd_multiple_prime_half_sets_not_finitely_coverable :
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ 13 ≤ p ∧ p % 4 = 1) → ∃ k,
      (∃ p m, p.Prime ∧ 13 ≤ p ∧ p % 4 = 1 ∧
        k = ((p - 1) / 2) * (2 * m + 1)) ∧
      ∀ p ∈ S, ¬∃ m, k = ((p - 1) / 2) * (2 * m + 1) := by
  intro S hS
  have half_pos (q : ℕ) (hq : q ∈ S) : 0 < (q - 1) / 2 := by
    have := (hS q hq).2.1
    omega
  let P := ∏ q ∈ S, ((q - 1) / 2)
  have hP : 0 < P := Finset.prod_pos half_pos
  obtain ⟨p, hp, hp₁₃, hmod⟩ := Nat.exists_prime_gt_modEq_one 12 (k := 4 * P) (by positivity)
  obtain ⟨r, hr⟩ := hmod.symm.dvd'
  have hhalf : (p - 1) / 2 = 2 * (P * r) := by
    rw [hr, Nat.mul_assoc]
    omega
  refine ⟨(p - 1) / 2, ⟨p, 0, hp, hp₁₃, hmod.of_dvd (dvd_mul_right 4 P), by simp⟩, ?_⟩
  rintro q hq ⟨m, hm⟩
  have hd : (q - 1) / 2 ∣ P * r := dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ hq) _
  obtain ⟨d, hd⟩ := hd
  rw [hhalf, hd, mul_left_comm] at hm
  have := Nat.eq_of_mul_eq_mul_left (half_pos q hq) hm
  omega

end MetaMathlibExt
