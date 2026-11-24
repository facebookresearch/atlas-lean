/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Ideal.BigOperators
import MathlibExt.Algebra.DeepPowerSumCongruences

/-!
# Powers of congruent elements in a divided-power ideal

In the binomial expansion of `((x - y) + y) ^ n`, the divided-power condition supplies
a factor of `k!` in each term of positive degree `k` in `x - y`. The product of this
factorial and the binomial coefficient is a multiple of `n`.
-/

namespace MetaMathlibExt

/-- **Divided-power ideal.** An ideal $I$ of a commutative ring $A$ is a *divided-power ideal* when
for every $a \in I$ and every integer $k \ge 1$ there is $c \in I$ with $a^k = k! \, c$, that is,
$a^k \in k! \, I$. For a prime $p$, in a torsion-free $\mathbb{Z}_{(p)}$-algebra this says
$a^k / k! \in I$.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 2.2. -/
@[expose] public def IsDividedPowerIdeal {A : Type*} [CommRing A] (I : Ideal A) : Prop :=
  ∀ a ∈ I, ∀ k : ℕ, 1 ≤ k → ∃ c ∈ I, a ^ k = (k.factorial : A) * c

/-- **The $p$-th power criterion for divided-power ideals.** Let $p$ be a prime and let $A$ be a
commutative ring in which every natural number not divisible by $p$ is a unit (a
$\mathbb{Z}_{(p)}$-algebra). An ideal $\mathfrak{a}$ of $A$ is a divided-power ideal if and only if
for every $a \in \mathfrak{a}$ there is $c \in \mathfrak{a}$ with $a^p = p\,c$, that is,
$a^p \in p\mathfrak{a}$.

The paper also assumes $A$ torsion-free; the statement does not need it.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 4 (`integers-2024-A46-cor-4`). -/
public theorem isDividedPowerIdeal_iff_pow_prime_mem {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommRing A] (hA : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A)) (I : Ideal A) :
    IsDividedPowerIdeal I ↔ ∀ a ∈ I, ∃ c ∈ I, a ^ p = (p : A) * c := by
  have hp : p.Prime := Fact.out
  -- The factor of `k!` left after removing the full power of `p` is a unit in `A`.
  have hfactorial (k : ℕ) : ∃ u : Aˣ,
      (k.factorial : A) = (p : A) ^ padicValNat p k.factorial * u := by
    have hfin : FiniteMultiplicity p k.factorial :=
      Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, Nat.factorial_pos k⟩
    obtain ⟨m, hm, hpm⟩ := hfin.exists_eq_pow_mul_and_not_dvd
    obtain ⟨u, hu⟩ := hA m hpm
    refine ⟨u, ?_⟩
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.padicValNat_def, hu] using
      congrArg (fun n : ℕ => (n : A)) hm
  refine Iff.trans ?_ (pow_mem_prime_pow_padicValNat_factorial_iff I)
  constructor
  · intro h k hk a ha
    obtain ⟨c, hc, heq⟩ := h a ha k hk
    obtain ⟨u, hu⟩ := hfactorial k
    exact ⟨(u : A) * c, I.mul_mem_left _ hc, by simpa only [hu, mul_assoc] using heq⟩
  · intro h a ha k hk
    obtain ⟨c, hc, heq⟩ := h k hk a ha
    obtain ⟨u, hu⟩ := hfactorial k
    refine ⟨↑u⁻¹ * c, I.mul_mem_left _ hc, ?_⟩
    rw [heq, hu, mul_assoc, u.mul_inv_cancel_left]

/-- If two elements agree modulo a divided-power ideal, their `n`th powers differ by
`n` times an element of the ideal. -/
public theorem IsDividedPowerIdeal.exists_pow_sub_pow_eq_mul {A : Type*} [CommRing A]
    {I : Ideal A} (hI : IsDividedPowerIdeal I) {x y : A} (hxy : x - y ∈ I) (n : ℕ) :
    ∃ c ∈ I, x ^ n - y ^ n = (n : A) * c := by
  choose d hd hpow using fun k : ℕ => hI (x - y) hxy (k + 1) (Nat.succ_pos k)
  cases n with
  | zero => exact ⟨0, I.zero_mem, by simp⟩
  | succ n =>
    refine ⟨∑ k ∈ Finset.range (n + 1), (n.descFactorial k : A) * y ^ (n - k) * d k,
      I.sum_mem fun k _ => I.mul_mem_left _ (hd k), ?_⟩
    rw [← sub_add_cancel x y, add_pow, Finset.sum_range_succ']
    simp only [pow_zero, one_mul, tsub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
      add_sub_cancel_right, Nat.succ_sub_succ_eq_sub, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hpow]
    calc
      _ = ((k + 1).factorial * (n + 1).choose (k + 1) : ℕ) * y ^ (n - k) * d k := by
        rw [Nat.cast_mul]
        ring
      _ = _ := by
        rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.succ_descFactorial_succ,
          Nat.cast_mul]
        ring

-- Factorial divisibility gives the result without using the unit hypothesis.
set_option linter.unusedVariables false in
/-- **Powers of elements congruent modulo a divided-power ideal.** Let $p$ be a prime, let $A$ be
a commutative ring in which every natural number not divisible by $p$ is a unit (a
$\mathbb{Z}_{(p)}$-algebra), and let $\mathfrak{a}$ be a divided-power ideal of $A$. If
$x, y \in A$ satisfy $x - y \in \mathfrak{a}$, then for every $m \ge 0$ there is
$c \in \mathfrak{a}$ with $x^{p^m} - y^{p^m} = p^m c$, and for every $n \ge 0$ there is
$c \in \mathfrak{a}$ with $x^n - y^n = n c$.

The ring $A$ is not assumed to be torsion-free.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Lemma 25 (`integers-2024-A46-lem-25`). -/
public theorem pow_sub_pow_mem_of_sub_mem {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A]
    (hA : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A)) {I : Ideal A} (hI : IsDividedPowerIdeal I)
    {x y : A} (hxy : x - y ∈ I) :
    (∀ m : ℕ, ∃ c ∈ I, x ^ p ^ m - y ^ p ^ m = (p : A) ^ m * c) ∧
      ∀ n : ℕ, ∃ c ∈ I, x ^ n - y ^ n = (n : A) * c := by
  have h := hI.exists_pow_sub_pow_eq_mul hxy
  exact ⟨fun m => by simpa only [Nat.cast_pow] using h (p ^ m), h⟩

end MetaMathlibExt
