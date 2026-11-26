/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.FermatPsp
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Counting Fermat pseudoprime bases

As in Baillie–Wagstaff's proof, the Chinese remainder theorem reduces the Fermat congruence to
congruences modulo the prime powers dividing `n`. Instead of lifting roots from the prime
moduli, this proof counts roots directly in the prime-power unit groups.

## References

* Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
  Article A23, Theorem 2. This statement cites the proofs by Baillie–Wagstaff and Monier.
* Robert Baillie and Samuel S. Wagstaff, Jr., *Lucas pseudoprimes*, Mathematics of
  Computation 35 (1980), 1391–1417, Theorem 1.
* Louis Monier, *Evaluation and comparison of two efficient probabilistic primality testing
  algorithms*, Theoretical Computer Science 12 (1980), 97–108.
-/

namespace MetaMathlibExt

private theorem card_fermat_base_representatives {n : ℕ} (hn : 1 < n) (hc : ¬n.Prime) :
    {b : ℕ | 1 ≤ b ∧ b < n ∧ Nat.FermatPsp n b}.ncard =
      Nat.card {u : (ZMod n)ˣ // u ^ (n - 1) = 1} := by
  have : NeZero n := ⟨by omega⟩
  have : Fact (1 < n) := ⟨hn⟩
  let B : Set ℕ := {b | 1 ≤ b ∧ b < n ∧ Nat.FermatPsp n b}
  have hpow (b : B) : (b.val : ZMod n) ^ (n - 1) = 1 :=
    (Nat.probablePrime_iff_zmod_one n (by have := b.prop.1; omega)).mp b.prop.2.2.1
  have hu (b : B) : IsUnit (b.val : ZMod n) := IsUnit.of_pow_eq_one (hpow b) (by omega)
  refine Nat.card_congr
    { toFun := fun b => ⟨(hu b).unit, Units.ext (by
        change ((hu b).unit : ZMod n) ^ (n - 1) = 1
        simpa only [IsUnit.unit_spec] using hpow b)⟩
      invFun := fun u => ⟨(u.val : ZMod n).val, ?_⟩
      left_inv := fun b => Subtype.ext (by
        change ((hu b).unit : ZMod n).val = b.val
        rw [IsUnit.unit_spec, ZMod.val_natCast_of_lt b.prop.2.1])
      right_inv := fun u => Subtype.ext (Units.ext (by
        rw [IsUnit.unit_spec, ZMod.natCast_zmod_val])) }
  have hpos : 1 ≤ (u.val : ZMod n).val := by
    have := (ZMod.val_eq_zero (u.val : ZMod n)).not.mpr u.val.ne_zero
    omega
  refine ⟨hpos, ZMod.val_lt _, ?_, hc, hn⟩
  rw [Nat.probablePrime_iff_zmod_one n (by omega), ZMod.natCast_zmod_val]
  exact congrArg Units.val u.prop

private theorem card_fermat_fiber_crt {n : ℕ} (hn : n ≠ 0) (m : ℕ) :
    Nat.card {u : (ZMod n)ˣ // u ^ m = 1} =
      ∏ p : n.primeFactors, Nat.card {u : (ZMod (p.val ^ n.factorization p))ˣ // u ^ m = 1} := by
  let e := (Units.mapEquiv (ZMod.equivPi n hn).toMulEquiv).trans (MulEquiv.piUnits :
    (∀ p : n.primeFactors, ZMod (p.val ^ n.factorization p))ˣ ≃*
      ∀ p : n.primeFactors, (ZMod (p.val ^ n.factorization p))ˣ)
  rw [← Nat.card_pi]
  refine Nat.card_congr ((e.toEquiv.subtypeEquiv ?_).trans Equiv.subtypePiEquivPi)
  intro u
  change u ^ m = 1 ↔ ∀ p, (e u p) ^ m = 1
  rw [← e.injective.eq_iff, map_pow, map_one]
  exact funext_iff

private theorem card_fermat_fiber_prime_pow {n p : ℕ} (hn : 1 < n) (hp : p ∈ n.primeFactors) :
    Nat.card {u : (ZMod (p ^ n.factorization p))ˣ // u ^ (n - 1) = 1} =
      Nat.gcd (n - 1) (p - 1) := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hdvd := Nat.dvd_of_mem_primeFactors hp
  have hfac := hprime.factorization_pos_of_dvd (show n ≠ 0 by omega) hdvd
  have : NeZero (p ^ n.factorization p) := ⟨pow_ne_zero _ hprime.ne_zero⟩
  have hcop : p.Coprime (n - 1) :=
    ((Nat.coprime_self_sub_right hn.le).mpr (Nat.coprime_one_right n)).coprime_dvd_left hdvd
  have hcard : Nat.card (ZMod (p ^ n.factorization p))ˣ =
      p ^ (n.factorization p - 1) * (p - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hprime hfac]
  by_cases hp2 : p = 2
  · -- The group need not be cyclic at 2, but its order is coprime to the exponent.
    subst p
    have hcop' : (Nat.card (ZMod (2 ^ n.factorization 2))ˣ).Coprime (n - 1) := by
      simpa only [hcard, Nat.reduceSub, mul_one] using hcop.pow_left (n.factorization 2 - 1)
    have hone (u : {u : (ZMod (2 ^ n.factorization 2))ˣ // u ^ (n - 1) = 1}) : u.val = 1 := by
      apply orderOf_eq_one_iff.mp
      have hd := Nat.dvd_gcd (orderOf_dvd_natCard u.val) (orderOf_dvd_iff_pow_eq_one.mpr u.prop)
      rw [hcop'.gcd_eq_one] at hd
      exact Nat.dvd_one.mp hd
    let : Unique {u : (ZMod (2 ^ n.factorization 2))ˣ // u ^ (n - 1) = 1} :=
      { default := ⟨1, one_pow _⟩
        uniq := fun u => Subtype.ext (hone u) }
    simp only [Nat.card_unique, Nat.reduceSub, Nat.gcd_one_right]
  · have : IsCyclic (ZMod (p ^ n.factorization p))ˣ :=
      ZMod.isCyclic_units_of_prime_pow p hprime hp2 (n.factorization p)
    change Nat.card (powMonoidHom (α := (ZMod (p ^ n.factorization p))ˣ) (n - 1)).ker = _
    rw [IsCyclic.card_powMonoidHom_ker, hcard, (hcop.pow_left _).gcd_mul_left_cancel, Nat.gcd_comm]

/-- **Number of Fermat pseudoprime bases (Monier; Baillie–Wagstaff).** Let $n > 1$ be a
composite natural number. Then the number of integers $b$ with $1 \le b < n$ such that $n$ is a
Fermat pseudoprime to the base $b$, that is, $b^{n-1} \equiv 1 \pmod{n}$, equals
$\prod_p \gcd(n - 1, p - 1)$, where $p$ runs over the distinct prime divisors of $n$.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Theorem 2 (`integers-2024-A23-thm-2`). -/
public theorem card_fermatPsp_bases_eq_prod_gcd {n : ℕ} (hn : 1 < n) (hcomp : ¬n.Prime) :
    {b : ℕ | 1 ≤ b ∧ b < n ∧ Nat.FermatPsp n b}.ncard =
      ∏ p ∈ n.primeFactors, Nat.gcd (n - 1) (p - 1) := by
  rw [card_fermat_base_representatives hn hcomp, card_fermat_fiber_crt (by omega : n ≠ 0)]
  simpa only [card_fermat_fiber_prime_pow hn (Subtype.prop _)] using
    Finset.prod_coe_sort n.primeFactors (fun p => Nat.gcd (n - 1) (p - 1))

end MetaMathlibExt
