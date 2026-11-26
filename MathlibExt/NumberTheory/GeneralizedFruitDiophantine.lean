/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification

/-! # The generalized fruit equation at a prime above two

For each unramified degree-one prime above two, we identify the quotients by its positive powers
with the corresponding rings of integers modulo powers of two. The generalized fruit equation
has no solution with even first coordinate when such a prime exists.
-/

namespace MetaMathlibExt

@[expose] public section

open NumberField

/-- **Unramified primes of degree one above $2$.** For a number field $K$ with ring of integers
$\mathcal{O}_K$, $T_K$ is the set of prime ideals $P$ of $\mathcal{O}_K$ that contain $2$ and have
ramification index $e(P \mid 2) = 1$ and inertia degree $f(P \mid 2) = 1$ over $\mathbb{Z}$.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Section 2 (definition of `T_K`). -/
def twoUnramifiedDegreeOnePrimes (K : Type*) [Field K] [NumberField K] : Set (Ideal (𝓞 K)) :=
  {P | P.IsPrime ∧ (2 : 𝓞 K) ∈ P ∧ P.ramificationIdx ℤ = 1 ∧ P.inertiaDeg ℤ = 1}

/-- **Membership in $T_K$.** Let $K$ be a number field with ring of integers $\mathcal{O}_K$, and
let $T_K$ be the set of prime ideals of $\mathcal{O}_K$ that contain $2$ and have ramification
index $1$ and inertia degree $1$ over $\mathbb{Z}$. Then an ideal $P$ of $\mathcal{O}_K$ lies in
$T_K$ if and only if $P$ is a prime ideal, $2 \in P$, and $P$ has ramification index $1$ and
inertia degree $1$ over $\mathbb{Z}$.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Section 2. -/
theorem mem_twoUnramifiedDegreeOnePrimes {K : Type*} [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) :
    P ∈ twoUnramifiedDegreeOnePrimes K ↔
      P.IsPrime ∧ (2 : 𝓞 K) ∈ P ∧ P.ramificationIdx ℤ = 1 ∧ P.inertiaDeg ℤ = 1 :=
  Iff.rfl

open Ideal in
/-- **Quotients by powers of a prime in $T_K$.** Let $K$ be a number field with ring of integers
$\mathcal{O}_K$, and let $P \in T_K$, that is, $P$ is a prime ideal of $\mathcal{O}_K$ lying over
$2$ with ramification index $1$ and inertia degree $1$ over $\mathbb{Z}$. Then for every $n \ge 1$
the ring $\mathcal{O}_K / P^n$ is isomorphic to $\mathbb{Z} / 2^n \mathbb{Z}$.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Lemma 1 (`integers-2026-A21-lem-1`). -/
theorem ringOfIntegers_quotient_pow_ringEquiv_zmod_two_pow (K : Type*) [Field K]
    [NumberField K] (P : Ideal (𝓞 K)) (hP : P ∈ twoUnramifiedDegreeOnePrimes K) (n : ℕ)
    (hn : 1 ≤ n) :
    Nonempty ((𝓞 K ⧸ P ^ n) ≃+* ZMod (2 ^ n)) := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨hprime, htwo, he, hf⟩ := (mem_twoUnramifiedDegreeOnePrimes P).mp hP
  let : P.IsPrime := hprime
  let p : Ideal ℤ := span {(2 : ℤ)}
  let : P.LiesOver p := (liesOver_span_iff hprime.ne_top
    (Nat.prime_iff_prime_int.mp Nat.prime_two)).mpr (by simpa using htwo)
  have hP0 : P ≠ ⊥ := by
    intro h
    simp [h] at htwo
  let R := 𝓞 K ⧸ P ^ (m + 1)
  let : Infinite (𝓞 K) := Infinite.of_injective _ (Int.cast_injective (α := 𝓞 K))
  let : Finite R := Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ hP0)
  let : Fintype R := Fintype.ofFinite R
  -- The inertia degree determines the cardinality of the quotient.
  have hnorm : P.absNorm = 2 := by simpa [hf] using (pow_inertiaDeg 2 P).symm
  have hcard : Fintype.card R = 2 ^ (m + 1) := by
    rw [← Nat.card_eq_fintype_card, ← absNorm_eq_natCard (P ^ (m + 1)), map_pow, hnorm]
  -- Since the ramification index is one, the multiplicity of P in (2^m) is m.
  have hmap : p.map (algebraMap ℤ (𝓞 K)) = span {(2 : 𝓞 K)} := by simp [p, map_span]
  have hspan : span {(2 : 𝓞 K)} ≠ ⊥ := by simp
  have hmult : multiplicity P (span {(2 : 𝓞 K)}) = 1 := by
    rwa [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p P (hmap ▸ hspan), hmap] at he
  have hnot : (2 : 𝓞 K) ^ m ∉ P ^ (m + 1) := by
    rw [← dvd_span_singleton, ← span_singleton_pow]
    have hp := prime_of_isPrime hP0 hprime
    rw [(FiniteMultiplicity.of_prime_left hp (pow_ne_zero m hspan)).pow_dvd_iff_le_multiplicity,
      multiplicity_pow hp, hmult, mul_one]
    exact Nat.not_succ_le_self m
  let : CharP R (2 ^ (m + 1)) := by
    apply ringChar.of_eq (Nat.eq_prime_pow_of_dvd_least_prime_pow Nat.prime_two ?_ ?_)
    · rw [← ringChar.spec R, Nat.cast_pow, Nat.cast_ofNat]
      rw [← map_ofNat (Ideal.Quotient.mk (P ^ (m + 1))) 2, ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hnot
    · rw [← hcard]
      exact ringChar.dvd (Nat.cast_card_eq_zero R)
  exact ⟨(ZMod.ringEquiv R hcard).symm⟩

namespace generalizedFruit_no_solution_two_dvd

private theorem residue_obstruction (t y z : ZMod 4) :
    -y ^ 2 - z ^ 2 + (2 * t) * y * z + 3 ≠ 0 := by
  -- Equality would force opposite parity for y and z. Their squares then sum to 1
  -- and the mixed term vanishes.
  revert t y z
  decide +kernel

end generalizedFruit_no_solution_two_dvd

set_option linter.unusedVariables false in
/-- **No solutions of the generalized fruit equation with even $x$.** Let $K$ be a number field
with ring of integers $\mathcal{O}_K$ such that some prime ideal of $\mathcal{O}_K$ lying over $2$
has ramification index $1$ and inertia degree $1$ over $\mathbb{Z}$. Let $a, b \in \mathcal{O}_K$
be nonzero, let $r \ge 2$ and $d \ge 3$ be odd natural numbers, and let $c = 2^d b - 3^r$. Then
the equation $a x^d - y^2 - z^2 + x y z - c = 0$ has no solution $(x, y, z) \in \mathcal{O}_K^3$
with $2 \mid x$ in $\mathcal{O}_K$.

The hypothesis that $r$ is odd cannot be dropped: over $K = \mathbb{Q}$ with $a = b = 1$, $d = 3$
and $r = 2$ (so $c = -1$), $(x, y, z) = (2, 3, 0)$ is a solution. The source states "integers
$r \ge 2$ and $d \ge 3$ odd"; its proof (arXiv:2408.12278, proof of Theorem 1) uses that $r$ is
odd, so oddness is read as applying to both $r$ and $d$.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Theorem 1 (`integers-2026-A21-thm-1`). -/
theorem generalizedFruit_no_solution_two_dvd (K : Type*) [Field K]
    [NumberField K] (hT : (twoUnramifiedDegreeOnePrimes K).Nonempty) (a b : 𝓞 K)
    (ha : a ≠ 0) (hb : b ≠ 0) (r d : ℕ) (hr : 2 ≤ r) (hr' : Odd r) (hd : 3 ≤ d)
    (hd' : Odd d) (x y z : 𝓞 K) (hx : 2 ∣ x) :
    a * x ^ d - y ^ 2 - z ^ 2 + x * y * z - (2 ^ d * b - 3 ^ r) ≠ 0 := by
  obtain ⟨P, hP⟩ := hT
  obtain ⟨e⟩ := ringOfIntegers_quotient_pow_ringEquiv_zmod_two_pow K P hP 2 (by decide)
  let f : 𝓞 K →+* ZMod 4 := e.toRingHom.comp (Ideal.Quotient.mk (P ^ 2))
  obtain ⟨t, rfl⟩ := hx
  intro h
  have hred := congrArg f h
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero] at hred
  have h2 : (2 : ZMod 4) ^ 2 = 0 := by decide
  have h2d := pow_eq_zero_of_le (show 2 ≤ d by omega) h2
  have h3 : (3 : ZMod 4) ^ r = 3 := by
    calc
      (3 : ZMod 4) ^ r = (-1) ^ r := by rw [show (3 : ZMod 4) = -1 by decide]
      _ = -1 := hr'.neg_one_pow
      _ = 3 := by decide
  apply generalizedFruit_no_solution_two_dvd.residue_obstruction (f t) (f y) (f z)
  simpa only [mul_pow, h2d, zero_mul, mul_zero, h3, zero_sub, sub_neg_eq_add] using hred

end

end MetaMathlibExt
