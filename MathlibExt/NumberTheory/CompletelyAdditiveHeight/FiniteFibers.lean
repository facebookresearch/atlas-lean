/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CompletelyAdditiveHeight
import Mathlib.NumberTheory.PrimeCounting

/-!
# Height functions with prescribed values at the primes

A function $f$ on the positive integers with positive values and finite fibers defines a height
function: the completely additive function sending the $i$-th prime to $f(i)$. The map sending
a prime $p$ to its one-based index $\#\{q < p : q \text{ prime}\} + 1$ is a bijection from the
primes onto the positive integers, so the primes at height $n$ correspond to the indices $i$
with $f(i) = n$.
-/

namespace MetaMathlibExt

@[expose] public section

namespace isHeightFunction_of_finite_fibers

/-- The one-based index of a prime, `Nat.count Nat.Prime p + 1`, maps the primes with
`f (index) = n` onto the positive indices with `f i = n`. -/
private theorem index_image (f : ℕ → ℕ) (n : ℕ) :
    (fun p => Nat.count Nat.Prime p + 1) ''
        {p : ℕ | p.Prime ∧ f (Nat.count Nat.Prime p + 1) = n} =
      {i : ℕ | 1 ≤ i ∧ f i = n} := by
  ext i
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, ⟨-, hp⟩, rfl⟩
    exact ⟨by omega, hp⟩
  · rintro ⟨hi, hfi⟩
    refine ⟨Nat.nth Nat.Prime (i - 1), ⟨Nat.prime_nth_prime _, ?_⟩, ?_⟩ <;>
      rw [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime, Nat.sub_add_cancel hi]
    exact hfi

/-- The one-based prime index is injective on the primes. -/
private theorem index_injOn (S : Set ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Set.InjOn (fun p => Nat.count Nat.Prime p + 1) S := by
  intro a ha b hb hab
  exact Nat.count_injective (p := Nat.Prime) (hS a ha) (hS b hb) (by simpa using hab)

end isHeightFunction_of_finite_fibers

open isHeightFunction_of_finite_fibers in
/-- **Height functions with prescribed values at the primes.** Let $f : \mathbb{N} \to \mathbb{N}$
satisfy $f(i) \ge 1$ for every $i \ge 1$, and suppose that for every $t \ge 1$ only finitely many
$i \ge 1$ have $f(i) = t$. Let $H$ be the completely additive function on the positive integers
with $H(p) = f(i)$ when $p$ is the $i$-th prime (so $H(2) = f(1)$). Then $H$ is a height function,
and for every $n \ge 1$ the number of primes $p$ with $H(p) = n$ equals the number of integers
$i \ge 1$ with $f(i) = n$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 3
(`integers-2026-A116-prop-3`). -/
public theorem isHeightFunction_of_finite_fibers (f : ℕ → ℕ)
    (hpos : ∀ i, 1 ≤ i → 1 ≤ f i) (hfin : ∀ t, 1 ≤ t → {i : ℕ | 1 ≤ i ∧ f i = t}.Finite) :
    let H := additiveOfPrimeValues fun p => f (Nat.count Nat.Prime p + 1)
    IsHeightFunction H ∧
      ∀ n, 1 ≤ n → {p : ℕ | p.Prime ∧ H p = n}.ncard = {i : ℕ | 1 ≤ i ∧ f i = n}.ncard := by
  intro H
  have hset : ∀ n, {p : ℕ | p.Prime ∧ H p = n} =
      {p : ℕ | p.Prime ∧ f (Nat.count Nat.Prime p + 1) = n} := by
    intro n
    ext p
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hp, h⟩
      exact ⟨hp, by rwa [show H p = _ from additiveOfPrimeValues_prime _ hp] at h⟩
    · rintro ⟨hp, h⟩
      exact ⟨hp, by rwa [show H p = _ from additiveOfPrimeValues_prime _ hp]⟩
  have hsub : ∀ n, ∀ p ∈ {p : ℕ | p.Prime ∧ f (Nat.count Nat.Prime p + 1) = n}, p.Prime :=
    fun _ _ hp => hp.1
  refine ⟨⟨isCompletelyAdditiveNat_additiveOfPrimeValues _, fun p hp => ?_, fun n hn => ?_⟩,
    fun n _ => ?_⟩
  · rw [show H p = _ from additiveOfPrimeValues_prime _ hp]
    exact hpos _ (by omega)
  · rw [hset n]
    refine Set.Finite.of_finite_image ?_ (index_injOn _ (hsub n))
    rw [index_image]
    exact hfin n hn
  · rw [hset n, ← index_image f n, (index_injOn _ (hsub n)).ncard_image]

end

end MetaMathlibExt
