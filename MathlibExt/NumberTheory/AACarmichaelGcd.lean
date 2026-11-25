/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.PrimeFin

/-!
# Shifted gcds in the generalized Carmichael number construction
-/

namespace MetaMathlibExt

@[expose] public section

/-- **$(a, a)$-Carmichael numbers.** Let $a$ be an integer. A natural number $n$ is an
$(a, a)$-Carmichael number if $n$ is squarefree and $p - a$ divides $n - a$ in $\mathbb{Z}$ for
every prime $p$ dividing $n$.

Source: Thomas Wright, *(a,a)-Carmichael Numbers and Greatest Common Divisors of p-a*,
INTEGERS 26 (2026), Article A123, abstract and Section 1 (definition read from the arXiv version,
arXiv:2607.02738; the journal display could not be checked). -/
def IsAACarmichael (a : ℤ) (n : ℕ) : Prop :=
  Squarefree n ∧ ∀ p ∈ n.primeFactors, ((p : ℤ) - a) ∣ ((n : ℤ) - a)

/-- **Primes are $(a, a)$-Carmichael numbers.** For every integer $a$, every prime $p$ is an
$(a, a)$-Carmichael number.

Source: Thomas Wright, *(a,a)-Carmichael Numbers and Greatest Common Divisors of p-a*,
INTEGERS 26 (2026), Article A123, characteristic lemma of the definition in Section 1. -/
theorem isAACarmichael_of_prime (a : ℤ) {p : ℕ} (hp : p.Prime) : IsAACarmichael a p := by
  refine ⟨hp.prime.squarefree, fun q hq => ?_⟩
  rw [hp.primeFactors, Finset.mem_singleton] at hq
  subst hq
  exact dvd_rfl

/-- **Exact gcd of two shifted values in the construction.** Let $a$ be an integer and let $\nu$,
$L_1$, $L_2$, $k_1$, $k_2$, $d_1$, $d_2$ be natural numbers with $\gcd(L_1, L_2) = 1$,
$\gcd(k_1, \nu L_1 L_2) = \gcd(k_2, \nu L_1 L_2) = 1$, $\gcd(k_1, k_2) = 1$, $d_1 \mid L_1$ and
$d_2 \mid L_2$. If $p_1 = d_1 k_1 \nu + a$ and $p_2 = d_2 k_2 \nu + a$, then
$\gcd(p_1 - a, p_2 - a) = \nu$.

In the paper $p_1, p_2$ are primes, $d_1, d_2$ have a prescribed number of prime factors,
$L_1, L_2$ are the products of two disjoint sets of primes, and $k_1, k_2$ come from Lemmas 4 and
5; the statement keeps only the hypotheses the conclusion uses.

Source: Thomas Wright, *(a,a)-Carmichael Numbers and Greatest Common Divisors of p-a*,
INTEGERS 26 (2026), Article A123, Section 5 (definition of `𝒫^i_k`) and Lemma 6
(`integers-2026-A123-lem-6`). -/
theorem int_gcd_sub_eq_of_eq_mul_mul_add
    (a : ℤ) (ν L₁ L₂ k₁ k₂ d₁ d₂ : ℕ) (hL : Nat.Coprime L₁ L₂)
    (hk₁ : Nat.Coprime k₁ (ν * L₁ * L₂)) (hk₂ : Nat.Coprime k₂ (ν * L₁ * L₂))
    (hk : Nat.Coprime k₁ k₂) (hd₁ : d₁ ∣ L₁) (hd₂ : d₂ ∣ L₂) (p₁ p₂ : ℤ)
    (hp₁ : p₁ = d₁ * k₁ * ν + a) (hp₂ : p₂ = d₂ * k₂ * ν + a) :
    Int.gcd (p₁ - a) (p₂ - a) = ν := by
  simp only [Nat.coprime_mul_iff_right] at hk₁ hk₂
  have hLk : Nat.Coprime (L₁ * k₁) (L₂ * k₂) :=
    (hL.mul_right hk₂.1.2.symm).mul_left (hk₁.2.mul_right hk)
  have hdk := hLk.of_dvd (Nat.mul_dvd_mul_right hd₁ k₁) (Nat.mul_dvd_mul_right hd₂ k₂)
  simp only [hp₁, hp₂, Int.add_sub_cancel, ← Int.natCast_mul, Int.gcd_natCast_natCast,
    Nat.gcd_mul_right, hdk.gcd_eq_one, one_mul]

end

end MetaMathlibExt
