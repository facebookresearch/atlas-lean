/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.ModularSchurNumbers
import Mathlib.Data.Nat.Prime.Basic

/-!
# Singleton sum-free sets modulo a prime power

A congruence between a sum of copies of `a` and `a` would give divisibility of
`(l - 1) * a` by the modulus. The assumption on `l` lets us cancel `l - 1`
from this divisibility.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Singletons are sum-free modulo a prime power.** Let $p$ be a prime, let $i$ and $l$ be
positive integers with $l \not\equiv 1 \pmod{p}$, and let $a$ be a natural number not divisible
by $p^i$. Then the singleton $\{a\}$ is $l$-sum-free modulo $p^i$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Lemma 1
(`integers-2025-A62-lem-1`). -/
public theorem isSumFreeMod_singleton_prime_pow (p a i l : ℕ) (hp : p.Prime) (hi : 0 < i)
    (hl : 0 < l) (ha : ¬ p ^ i ∣ a) (hlp : ¬ l ≡ 1 [MOD p]) :
    IsSumFreeMod (p ^ i) l {(a : ℤ)} := by
  intro x hx y hy hsum
  simp only [Set.mem_singleton_iff] at hx hy
  subst y
  rw [show x = fun _ => (a : ℤ) from funext hx, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Nat.cast_mul, Int.natCast_modEq_iff] at hsum
  have hle : a ≤ l * a := by simpa using Nat.mul_le_mul_right a hl
  have hd : p ^ i ∣ (l - 1) * a := by
    rw [Nat.sub_mul, Nat.one_mul]
    exact (Nat.modEq_iff_dvd' hle).mp hsum.symm
  have hnot : ¬ p ∣ l - 1 := fun h => hlp ((Nat.modEq_iff_dvd' hl).mpr h).symm
  have hcop : (p ^ i).Coprime (l - 1) :=
    (Nat.coprime_pow_left_iff hi p (l - 1)).mpr (hp.coprime_iff_not_dvd.mpr hnot)
  exact ha (hcop.dvd_of_dvd_mul_left hd)

end -- public section

end MetaMathlibExt
