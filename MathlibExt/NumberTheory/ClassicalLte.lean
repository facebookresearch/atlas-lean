/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Multiplicity

/-!
# Classical integer lifting the exponent

The source is the remark after Lemma 5 in Bayarmagnai, Batbold, and Hu,
[On the divisibility of sums of powers of integers](https://cs.uwaterloo.ca/journals/JIS/VOL25/Bayarmagnai/bayar10.tex),
lines 260–262.  It states the classical odd-prime LTE formula for signed integers.

Mathlib already proves the underlying result as `Int.emultiplicity_pow_sub_pow`.  The theorem
below is therefore a proved convenience wrapper, not a missing result: the nonzero hypotheses
convert the extended-natural multiplicities in Mathlib's theorem into the finite natural-valued
functions `padicValInt` and `padicValNat`.  The source assumption `p ∤ a*b` supplies the
nondivisibility of `a` required by the Mathlib theorem.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Lifting the exponent for odd primes.** Let $p$ be an odd prime, let $a \ne b$ be integers
such that $p$ divides $a - b$ but does not divide $ab$, and let $n \ge 1$ be a natural number.
Then
$$v_p(a^n - b^n) = v_p(n) + v_p(a - b),$$
where $v_p$ denotes the $p$-adic valuation. -/
theorem padicValInt_pow_sub_pow (p : ℕ) [Fact (Nat.Prime p)] {a b : ℤ} {n : ℕ}
    (hodd : Odd p) (hne : a ≠ b) (hcop : ¬ (p : ℤ) ∣ a * b)
    (hdiv : (p : ℤ) ∣ a - b) (hn : n ≠ 0) :
    padicValInt p (a ^ n - b ^ n) = padicValNat p n + padicValInt p (a - b) := by
  have hp : Nat.Prime p := Fact.out
  have ha : ¬ (p : ℤ) ∣ a := fun hpa => hcop (dvd_mul_of_dvd_left hpa b)
  have hbase : FiniteMultiplicity (p : ℤ) (a - b) := by
    rw [Int.finiteMultiplicity_iff]
    exact ⟨by simpa using hp.ne_one, sub_ne_zero.mpr hne⟩
  have hnfin : FiniteMultiplicity p n := by
    rw [Nat.finiteMultiplicity_iff]
    exact ⟨hp.ne_one, Nat.pos_of_ne_zero hn⟩
  have hem := Int.emultiplicity_pow_sub_pow hp hodd hdiv ha n
  have hval (z : ℤ) : padicValInt p z = (emultiplicity (p : ℤ) z).toNat := by
    rw [padicValInt, ← Nat.toNat_emultiplicity, Int.emultiplicity_natAbs]
  rw [hval, hval, ← Nat.toNat_emultiplicity]
  rw [hem, ENat.toNat_add
    (finiteMultiplicity_iff_emultiplicity_ne_top.mp hbase)
    (finiteMultiplicity_iff_emultiplicity_ne_top.mp hnfin), add_comm]

end

end MetaMathlibExt
