/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.NumberField.ExistsRamified
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import MathlibExt.NumberTheory.NumberField.Unramified

@[expose] public section

/-!
# Cyclotomic fields are unramified away from the conductor

Packaging of the pointwise ramification-index computation for cyclotomic
extensions as a native `Algebra.IsUnramifiedIn` statement. This is the
"in particular, if `p` does not divide `m` then `Q(zeta_m)` is unramified
at `p`" clause of MIT 18.785 Proposition 19.14 (ATLAS NumberTheoryI N390).

## Source map for the `p`-power bottom theorem

`eq_bot_of_isUnramifiedIn_prime_pow` below formalizes the prime-power
vanishing step of the N390 maximality argument, following the ATLAS source
`v1/Atlas/NumberTheoryI/code/AnalyticClassNumber.lean` at revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, lines 1462--1547:

* `cyclotomic_ppow_unramified_at_other_primes` (lines 1462--1479) becomes
  `isUnramifiedIn_of_not_dvd` above, descended with
  `NumberField.isUnramifiedIn_mono` (the generic form of the source's
  `isUnramifiedAtPrime_of_le`, lines 1433--1460);
* `minkowski_no_unramified_extension` (lines 1482--1530) becomes
  `NumberField.exists_not_isUnramifiedIn`, which packages the Minkowski
  discriminant argument in Mathlib;
* `cyclotomic_ppow_unramified_le_bot` (lines 1532--1547) becomes
  `eq_bot_of_isUnramifiedIn_prime_pow`, generalized to an arbitrary
  exponent `e` and an arbitrary number-field ambient `L` (the source fixes
  `e = padicValNat p m` and `L = CyclotomicField m ℚ`).

This closes the `p`-power-vanishing prerequisite of Proposition 19.14, but
not the full proposition or the N390 maximality theorem: no compositum
unramifiedness and no localization equivalence is claimed here.
-/

open scoped NumberField

namespace IsCyclotomicExtension.Rat

/-- **Cyclotomic fields are unramified at primes not dividing $m$.** Let $m \ge 1$ and let $p$ be
a prime number with $p \nmid m$. If $K$ is a number field that is an $m$-th cyclotomic extension
of $\mathbb{Q}$ (that is, $K = \mathbb{Q}(\zeta_m)$ for a primitive $m$-th root of unity
$\zeta_m$), then $p$ is unramified in $K$: every prime ideal of the ring of integers
$\mathcal{O}_K$ lying over $p\mathbb{Z}$ is unramified over $\mathbb{Z}$. -/
theorem isUnramifiedIn_of_not_dvd
    {m p : ℕ} [NeZero m] (hp : p.Prime)
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {m} ℚ K] (hm : ¬ p ∣ m) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}) := by
  let _ : Fact p.Prime := ⟨hp⟩
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  intro P hP hLie
  have _ := hP
  have _ := hLie
  exact ramificationIdx_eq_of_not_dvd p K P hm

/-- **The $p$-free part of $m$ gives a cyclotomic field unramified at $p$.** Let $m \ge 1$, let
$p$ be a prime number, and let $m'$ be $m$ divided by the largest power of $p$ dividing it, so
that $m = p^a m'$ for some $a \ge 0$ with $p \nmid m'$. Then $p$ is unramified in the $m'$-th
cyclotomic field $\mathbb{Q}(\zeta_{m'})$, where $\zeta_{m'}$ is a primitive $m'$-th root of
unity: every prime ideal of its ring of integers lying over $p\mathbb{Z}$ is unramified over
$\mathbb{Z}$. -/
theorem isUnramifiedIn_divMaxPow
    (m p : ℕ) [NeZero m] (hp : p.Prime) :
    Algebra.IsUnramifiedIn
      (𝓞 (CyclotomicField (Nat.divMaxPow m p) ℚ))
      (Ideal.span {(p : ℤ)}) := by
  have h_eq := Nat.divMaxPow_mul_pow_padicValNat p m
  have hne : Nat.divMaxPow m p ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h_eq
    exact NeZero.ne m h_eq.symm
  let _ : NeZero (Nat.divMaxPow m p) := ⟨hne⟩
  let _ : NeZero ((Nat.divMaxPow m p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hne⟩
  let _ : IsCyclotomicExtension {Nat.divMaxPow m p} ℚ
      (CyclotomicField (Nat.divMaxPow m p) ℚ) :=
    CyclotomicField.isCyclotomicExtension (Nat.divMaxPow m p) ℚ
  exact isUnramifiedIn_of_not_dvd (m := Nat.divMaxPow m p) (p := p) hp
    (CyclotomicField (Nat.divMaxPow m p) ℚ)
    (Nat.not_dvd_divMaxPow hp.one_lt (NeZero.ne m))

/-- **Subfields of a $p$-power cyclotomic field unramified at $p$ are trivial.** Let $p$ be a
prime number, $e \ge 0$ an integer and $L$ a number field. Let $E_1$ and $F$ be subfields of $L$
such that $E_1$ is a $p^e$-th cyclotomic extension of $\mathbb{Q}$ and $F \subseteq E_1$. If $p$
is unramified in $F$, that is, every prime ideal of the ring of integers $\mathcal{O}_F$ lying
over $p\mathbb{Z}$ is unramified over $\mathbb{Z}$, then $F = \mathbb{Q}$.

Source: the prime-power vanishing step of the N390 maximality argument
(`cyclotomic_ppow_unramified_le_bot` in the primary source), which takes $e$ to be the
exponent of $p$ in a positive integer $m$ and $L = \mathbb{Q}(\zeta_m)$ for a primitive $m$-th
root of unity $\zeta_m$; here $e$ and $L$ are arbitrary. -/
theorem eq_bot_of_isUnramifiedIn_prime_pow
    {p e : ℕ} (hp : p.Prime)
    (L : Type*) [Field L] [NumberField L]
    (E₁ : IntermediateField ℚ L) [IsCyclotomicExtension {p ^ e} ℚ E₁]
    (F : IntermediateField ℚ L) (hFE₁ : F ≤ E₁)
    (hF : Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(p : ℤ)})) :
    F = ⊥ := by
  by_contra hFne
  have hfin : Module.finrank ℚ F ≠ 1 :=
    fun h => hFne (IntermediateField.finrank_eq_one_iff.mp h)
  obtain ⟨q, hq, hram⟩ : ∃ q : ℕ, q.Prime ∧
      ¬ Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(q : ℤ)}) :=
    NumberField.exists_not_isUnramifiedIn hfin
  apply hram
  by_cases hqp : q = p
  · subst hqp
    exact hF
  · have hqdvd : ¬ q ∣ p ^ e := by
      intro hd
      exact hqp (Nat.prime_eq_prime_of_dvd_pow hq hp hd)
    have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
    exact NumberField.isUnramifiedIn_mono F E₁ hFE₁ (Ideal.span {(q : ℤ)})
      (isUnramifiedIn_of_not_dvd (m := p ^ e) (p := q) hq E₁ hqdvd)

end IsCyclotomicExtension.Rat

end
