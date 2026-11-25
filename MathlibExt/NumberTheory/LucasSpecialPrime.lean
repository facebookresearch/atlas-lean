/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Int.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Special primes of a Lucas pair.** For integers $P$ and $Q$, a natural number $p$ is a special
prime for the Lucas parameters $(P, Q)$ if $p$ is prime and $p$ divides $\gcd(P, Q)$.

Source: concept `jis_term_9fa09acd972f484f5b457a48`; sources `jis_source_eb765815f14b18e047ccd51b`,
`jis_source_e9bb56af5eef26576559cf4c`, `jis_source_de2518f50026ac96429ae911`. -/
def IsLucasSpecialPrime (P Q : Int) (p : Nat) : Prop :=
  Nat.Prime p ∧ p ∣ Int.gcd P Q

/-- **Special primes are the common prime divisors of the parameters.** For integers $P$ and $Q$
and a natural number $p$, $p$ is a special prime for the Lucas parameters $(P, Q)$ if and only if
$p$ is prime and $p$ divides both $P$ and $Q$ in $\mathbb{Z}$.

Source: concept `jis_term_9fa09acd972f484f5b457a48`; sources `jis_source_eb765815f14b18e047ccd51b`,
`jis_source_e9bb56af5eef26576559cf4c`, `jis_source_de2518f50026ac96429ae911`. -/
theorem isLucasSpecialPrime_iff (P Q : Int) (p : Nat) :
    IsLucasSpecialPrime P Q p ↔ Nat.Prime p ∧ (p : Int) ∣ P ∧ (p : Int) ∣ Q := by
  unfold IsLucasSpecialPrime
  constructor
  · rintro ⟨hp, hdvd⟩
    have hgcd : Int.gcd P Q = Nat.gcd P.natAbs Q.natAbs :=
      Int.gcd_eq_natAbs_gcd_natAbs P Q
    rw [hgcd] at hdvd
    refine ⟨hp, ?_, ?_⟩
    · rw [Int.natCast_dvd]
      exact dvd_trans hdvd (Nat.gcd_dvd_left _ _)
    · rw [Int.natCast_dvd]
      exact dvd_trans hdvd (Nat.gcd_dvd_right _ _)
  · rintro ⟨hp, hP, hQ⟩
    exact ⟨hp, Int.dvd_gcd hP hQ⟩

end

end MetaMathlibExt
