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
# Prime-regular partitions and the generalized tau function

This module proves `card_prime_regular_modEq_generalizedTau_pred`: for a prime `p` and
a natural number `n`, the number of partitions of `n` with no part divisible by `p`
is congruent modulo `p` to `τ_{p-1}(n + 1)`.

Statements from S. Sriram and A. David Christopher, *Congruences Relating Regular Partition
Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*,
INTEGERS 24 (2024), Article A39 (arXiv:2509.26559).
-/

namespace MetaMathlibExt

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace card_prime_regular_modEq_generalizedTau_pred

/-- Each Glaisher factor is an Euler-factor power in characteristic `p`. -/
private theorem geom (p : ℕ) (hp : p.Prime) (i : ℕ) :
    ∑ j ∈ Finset.range p, (X ^ (i + 1) : (ZMod p)⟦X⟧) ^ j
      = (1 - X ^ (i + 1)) ^ (p - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hne : (1 : (ZMod p)⟦X⟧) ≠ X ^ (i + 1) := fun e ↦ by
    simpa using congrArg constantCoeff e
  have hcancel : (1 : (ZMod p)⟦X⟧) - X ^ (i + 1) ≠ 0 := sub_ne_zero.mpr hne
  have hchar : CharP (ZMod p)⟦X⟧ p := CharP.of_ringHom_of_ne_zero C p hp.pos.ne'
  have hgeom := geom_sum_mul_neg (X ^ (i + 1) : (ZMod p)⟦X⟧) p
  have hfrob : (1 - X ^ (i + 1) : (ZMod p)⟦X⟧) ^ p = 1 - (X ^ (i + 1)) ^ p := by
    rw [sub_pow_char (p := p) (1 : (ZMod p)⟦X⟧) (X ^ (i + 1)), one_pow]
  have hpow : ((1 - X ^ (i + 1) : (ZMod p)⟦X⟧) ^ (p - 1)) * (1 - X ^ (i + 1))
      = (1 - X ^ (i + 1)) ^ p := by
    rw [mul_comm, ← pow_succ', Nat.sub_add_cancel hp.one_lt.le]
  exact mul_right_cancel₀ hcancel (by rw [hgeom, hpow, hfrob])

/-- The `p`-regular partition counts are the Euler-power coefficients mod `p`. -/
private theorem count_eq_coeff (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ((Nat.Partition.restricted n (¬ p ∣ ·)).card : ZMod p)
      = ((coeff n ((pentagonalSeries ℤ) ^ (p - 1)) : ℤ) : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
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
  have h := ((WithPiTopology.hasProd_one_sub_X_pow ℤ).pow (p - 1)).map φ cont
  simp only [φ, Function.comp_def, map_pow, map_sub, map_one, map_X] at h
  have hc :=
    Nat.Partition.hasProd_powerSeriesMk_card_countRestricted (ZMod p) (m := p) hp.pos
  simp_rw [pow_mul, geom p hp] at hc
  have eqn := congrArg (coeff n) (hc.unique h)
  rw [Nat.Partition.card_restricted_eq_card_countRestricted n hp.pos]
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
  exact count_eq_coeff p hp n

end

end MetaMathlibExt
