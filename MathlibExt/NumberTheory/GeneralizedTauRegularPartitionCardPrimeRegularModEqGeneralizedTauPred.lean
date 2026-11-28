/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.NumberTheory.ChooseAddModEqPrime
public import MathlibExt.NumberTheory.GeneralizedTau
public import MathlibExt.NumberTheory.GeneralizedTauPrimeSquare
public import MathlibExt.NumberTheory.NineRegularPartitionIteration
public import MathlibExt.NumberTheory.PartitionConvolutionModThree
public import MathlibExt.NumberTheory.RamanujanTauModNineteen
public import MathlibExt.NumberTheory.RamanujanTauModSeventeen
public import MathlibExt.NumberTheory.RamanujanTauModThree
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# Prime and power-of-two regular partitions and the generalized tau function

For a prime $p$ and a natural number $n$, the number $R_p(n)$ of partitions of $n$ with no part
divisible by $p$ is congruent modulo $p$ to $\tau_{p-1}(n+1)$. For a positive integer $s$ and a
natural number $n$, the number $R_{2^s}(n)$ of partitions of $n$ with no part divisible by $2^s$
is congruent modulo $2$ to $\tau_{2^s-1}(n+1)$.

The second congruence includes $n=0$, consistent with the constant term in the paper's
proof: the empty partition counts once and $\tau_{2^s-1}(1)=1$. Both proofs use Frobenius
in place of the paper's binomial coefficient calculations.

## References

* S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a
  Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024),
  Article A39, pp. 1–30, Theorems 5 (pp. 10–11, equation (13)) and 20 (p. 24, equation (35)).
* James Glaisher, *On the residue of a binomial-theorem coefficient with respect to a prime
  modulus*, Quarterly Journal of Pure and Applied Mathematics 30 (1899), pp. 150–156.
  The source paper uses the parity recurrence from this work in equation (14).
* J. W. L. Glaisher, *A theorem in partitions*, Messenger of Mathematics 12 (1883), pp. 158–170.
  The proofs use this partition theorem via `Nat.Partition.card_restricted_eq_card_countRestricted`.
* Leonhard Euler, *Evolutio producti infiniti $(1-x)(1-x^2)(1-x^3)$ etc. in seriem simplicem*,
  Acta Academiae Scientiarum Imperialis Petropolitanae, vol. 1780, part I (1783), pp. 47–55,
  the pentagonal number theorem used in equation (1) of the source paper.
* The power-of-two proof generalizes the Euler-factor argument for
  `card_prime_regular_modEq_generalizedTau_pred` in this module.
-/

namespace MetaMathlibExt

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace card_prime_regular_modEq_generalizedTau_pred

/-- Each Glaisher factor is an Euler-factor power in characteristic `p`. -/
private theorem geom (p : ℕ) (hp : p.Prime) (s i : ℕ) :
    ∑ j ∈ Finset.range (p ^ s), (X ^ (i + 1) : (ZMod p)⟦X⟧) ^ j
      = (1 - X ^ (i + 1)) ^ (p ^ s - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hcancel : (1 : (ZMod p)⟦X⟧) - X ^ (i + 1) ≠ 0 := by
    intro h
    simpa using congrArg constantCoeff h
  have : CharP (ZMod p)⟦X⟧ p := CharP.of_ringHom_of_ne_zero C p hp.pos.ne'
  apply mul_right_cancel₀ hcancel
  rw [geom_sum_mul_neg, ← pow_succ, Nat.sub_add_cancel (pow_pos hp.pos s),
    sub_pow_char_pow (p := p), one_pow]

/-- The `p ^ s`-regular partition counts are the Euler-power coefficients mod `p`. -/
private theorem count_eq_coeff (p : ℕ) (hp : p.Prime) (s n : ℕ) :
    ((Nat.Partition.restricted n (¬ p ^ s ∣ ·)).card : ZMod p)
      = ((coeff n ((pentagonalSeries ℤ) ^ (p ^ s - 1)) : ℤ) : ZMod p) := by
  let : TopologicalSpace (ZMod p) := ⊥
  have : DiscreteTopology (ZMod p) := ⟨rfl⟩
  let φ := PowerSeries.map (Int.castRingHom (ZMod p))
  have cont : Continuous (φ : ℤ⟦X⟧ → (ZMod p)⟦X⟧) := by
    rw [continuous_iff_continuousAt]
    intro F
    rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
    intro k
    exact (continuous_of_discreteTopology (f := Int.castRingHom (ZMod p))).continuousAt.comp
      ((WithPiTopology.continuous_coeff ℤ k).continuousAt)
  have h := ((WithPiTopology.hasProd_one_sub_X_pow ℤ).pow (p ^ s - 1)).map φ cont
  simp only [φ, Function.comp_def, map_pow, map_sub, map_one, map_X] at h
  have hm : 0 < p ^ s := pow_pos hp.pos s
  have hc := Nat.Partition.hasProd_powerSeriesMk_card_countRestricted (ZMod p) hm
  simp_rw [pow_mul, geom p hp s] at hc
  have eqn := congrArg (coeff n) (hc.unique h)
  rw [Nat.Partition.card_restricted_eq_card_countRestricted n hm]
  simpa [φ, ← map_pow] using eqn

end card_prime_regular_modEq_generalizedTau_pred

@[expose] public section

open card_prime_regular_modEq_generalizedTau_pred in
/-- **Prime-regular partitions and the generalized tau function.** Let $p$ be a prime and $n$ a
natural number. Let $R_p(n)$ be the number of partitions of $n$ in which no part is divisible by
$p$, and let $\tau_k(m)$ be the generalized tau function, the coefficient of $q^m$ in
$q \prod_{j \ge 1} (1 - q^j)^k$. Then $R_p(n) \equiv \tau_{p-1}(n + 1) \pmod p$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a
Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024),
Article A39, Theorem 20 (`integers-2024-A39-thm-20`). -/
public theorem card_prime_regular_modEq_generalizedTau_pred (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ((Nat.Partition.restricted (n) (¬ p ∣ ·)).card : ℤ)
        ≡ generalizedTau ((p : ℤ) - 1) (n + 1) [ZMOD p]
    := by
  have hcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  have htau : generalizedTau ((p : ℤ) - 1) (n + 1)
      = coeff n (pentagonalSeries ℤ ^ (p - 1)) := by
    rw [← hcast, generalizedTau_natCast, coeff_succ_X_mul]
  rw [htau, ← ZMod.intCast_eq_intCast_iff]
  push_cast
  simpa only [pow_one] using count_eq_coeff p hp 1 n

open card_prime_regular_modEq_generalizedTau_pred in
/-- **$2^s$-regular partitions and the generalized tau function modulo 2.** Let $s$ be a positive
integer and $n$ a natural number. Let $R_{2^s}(n)$ be the number of partitions of $n$ in which no
part is divisible by $2^s$, and let $\tau_k(m)$ be the generalized tau function, the coefficient
of $q^m$ in $q \prod_{j \ge 1} (1 - q^j)^k$. Then $R_{2^s}(n) \equiv \tau_{2^s - 1}(n + 1) \pmod 2$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a
Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024),
Article A39, Theorem 5 (`integers-2024-A39-thm-5`). -/
public theorem card_two_pow_regular_modEq_generalizedTau (s : ℕ) (hs : 0 < s) (n : ℕ) :
    ((Nat.Partition.restricted (n) (¬ 2 ^ s ∣ ·)).card : ℤ)
        ≡ generalizedTau ((2 : ℤ) ^ s - 1) (n + 1) [ZMOD 2] := by
  cases n with
  | zero => simp [Nat.Partition.restricted, generalizedTau_one]
  | succ n =>
    have hm : 1 ≤ (2 : ℕ) ^ s := (one_lt_pow₀ Nat.one_lt_two hs.ne').le
    have hcast : ((2 ^ s - 1 : ℕ) : ℤ) = (2 : ℤ) ^ s - 1 := by
      rw [Nat.cast_sub hm, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    rw [← hcast, generalizedTau_natCast, coeff_succ_X_mul]
    apply (ZMod.intCast_eq_intCast_iff _ _ 2).mp
    push_cast
    exact count_eq_coeff 2 Nat.prime_two s (n + 1)

end

end MetaMathlibExt
