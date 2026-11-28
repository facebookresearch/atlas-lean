/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SpoofLehmerFactorization
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Tactic.Ring

/-!
# Exponents of nontrivial spoof Lehmer factorizations

Statements from Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26
(2026), Article A33. A spoof factorization `x_1^{a_1} ⋯ x_r^{a_r}` is a multiset of pairs
`(x_i, a_i)` of positive integers. This module proves that every exponent of a nontrivial spoof
Lehmer factorization is `1`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Nontrivial spoof Lehmer factorizations have all exponents $1$.** If $F$ is a nontrivial spoof
$k$-Lehmer factorization for some integer $k$, then every exponent of $F$ is $1$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 3 (`integers-2026-A33-thm-3`). -/
public theorem spoofLehmer_exponents_eq_one (F : Multiset (ℕ × ℕ))
    (k : ℤ) (hL : IsSpoofLehmer k F) (hnt : ¬ IsTrivialSpoof F) : ∀ p ∈ F, p.2 = 1 := by
  intro p hp
  by_contra hne
  obtain ⟨hpos, heq, hcard⟩ := hL
  have h1 : 0 < p.2 := (hpos p hp).2
  have ha : 1 < p.2 := by omega
  have hexp : p.2 = (p.2 - 1) + 1 := (Nat.sub_add_cancel ha.le).symm
  have hpow2 : (p.1 : ℤ) ^ p.2 = (p.1 : ℤ) ^ (p.2 - 1) * (p.1 : ℤ) := by
    conv_lhs => rw [hexp, pow_succ]
  have hdiv : (p.1 : ℤ) ^ (p.2 - 1) ∣ (p.1 : ℤ) ^ p.2 - (p.1 : ℤ) ^ (p.2 - 1) :=
    ⟨(p.1 : ℤ) - 1, by rw [hpow2]; ring⟩
  have hfactor : (p.1 : ℤ) ∣ (p.1 : ℤ) ^ p.2 - (p.1 : ℤ) ^ (p.2 - 1) :=
    (dvd_pow_self _ (by omega : p.2 - 1 ≠ 0)).trans hdiv
  have htot : (p.1 : ℤ) ∣ spoofTotient F :=
    hfactor.trans (Multiset.dvd_prod (Multiset.mem_map_of_mem _ hp))
  have hdiff : (p.1 : ℤ) ∣ spoofEval F - 1 := by
    rw [← heq]
    exact dvd_mul_of_dvd_right htot k
  have heval : (p.1 : ℤ) ∣ spoofEval F :=
    (dvd_pow_self _ h1.ne').trans (Multiset.dvd_prod (Multiset.mem_map_of_mem _ hp))
  have hbase : p.1 = 1 :=
    Nat.dvd_one.mp (Int.ofNat_dvd.mp (by simpa using dvd_sub heval hdiff))
  exact hnt (isTrivialSpoof_of_isSpoofLehmer_of_one_mem F ⟨k, hpos, heq, hcard⟩ ⟨p, hp, hbase⟩)

end

end MetaMathlibExt
