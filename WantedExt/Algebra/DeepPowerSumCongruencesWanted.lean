/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Elementary symmetric functions and deep power-sum congruences

Statements from Samuele Anni, Alexandru Ghitza and Anna Medvedovsky, *Elementary Symmetric
Functions and Deep Power-Sum Congruences*, INTEGERS 24 (2024), Article A46 (arXiv `2207.07108`,
TeX source read).

Conventions. A torsion-free `ℤ_(p)`-algebra `A` is a commutative ring with `IsAddTorsionFree A` in
which every natural number prime to `p` is a unit. An ideal `𝔞` is a *divided-power ideal* when
`a ^ k / k! ∈ 𝔞` for every `a ∈ 𝔞` and `k ≥ 1`; stated division-free as `IsDividedPowerIdeal`.
"`x ≡ y mod n𝔞`" is `∃ c ∈ 𝔞, x - y = n * c`. For a monic `P ∈ A[X]`, `polyElemSymm P n` is the
paper's `e_n(P)` and `polyPowerSum P n` its `p_n(P)`, defined through Newton's identities with
`p_0(P) = deg P`, as in the paper's Notation of Section 3.2. Symmetric functions are taken in
finitely many variables (`MvPolynomial σ ℚ`, `σ` finite), which loses nothing for identities
between them.
-/

open Polynomial

namespace MetaMathlibExt

@[expose] public section

/-- An ideal `I` of a commutative ring is a *divided-power ideal* when `a ^ k ∈ k! • I` for every
`a ∈ I` and every `k ≥ 1`; in a torsion-free `ℤ_(p)`-algebra this says `a ^ k / k! ∈ I`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 2.2. -/
def IsDividedPowerIdeal {A : Type*} [CommRing A] (I : Ideal A) : Prop :=
  ∀ a ∈ I, ∀ k : ℕ, 1 ≤ k → ∃ c ∈ I, a ^ k = (k.factorial : A) * c

/-- The zero ideal is a divided-power ideal.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 2.2 (the definition). -/
theorem isDividedPowerIdeal_bot {A : Type*} [CommRing A] : IsDividedPowerIdeal (⊥ : Ideal A) := by
  intro a ha k hk
  rw [Ideal.mem_bot] at ha
  refine ⟨0, Ideal.zero_mem _, ?_⟩
  rw [ha, zero_pow (by omega), mul_zero]

/-- An ideal carrying a divided-power structure in Mathlib's sense is a divided-power ideal.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 2.2 (the maps `γ_k(a) = a ^ k / k!`). -/
theorem DividedPowers.isDividedPowerIdeal {A : Type*} [CommRing A] {I : Ideal A}
    (hI : DividedPowers I) : IsDividedPowerIdeal I := by
  intro a ha k hk
  exact ⟨hI.dpow k a, hI.dpow_mem (by omega) ha, (hI.factorial_mul_dpow_eq_pow ha).symm⟩

/-- The paper's `e_n(P)` for a monic polynomial `P` of degree `d`: `1` for `n = 0`, the
`X ^ (d - n)`-coefficient times `(-1) ^ n` for `1 ≤ n ≤ d`, and `0` for `n > d`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 3.2, Notation. -/
noncomputable def polyElemSymm {A : Type*} [CommRing A] (P : A[X]) (n : ℕ) : A :=
  if n ≤ P.natDegree then (-1) ^ n * P.coeff (P.natDegree - n) else 0

/-- `e_0(P) = 1` for monic `P`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 3.2, Notation. -/
theorem polyElemSymm_zero {A : Type*} [CommRing A] {P : A[X]} (hP : P.Monic) :
    polyElemSymm P 0 = 1 := by
  simp [polyElemSymm, hP.coeff_natDegree]

/-- `e_n(P) = 0` for `n > deg P`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 3.2, Notation. -/
theorem polyElemSymm_of_natDegree_lt {A : Type*} [CommRing A] {P : A[X]} {n : ℕ}
    (h : P.natDegree < n) : polyElemSymm P n = 0 := by
  simp [polyElemSymm, Nat.not_le.mpr h]

/-- The paper's `p_n(P)`: `p_0(P) = deg P` and, for `n ≥ 1`, Newton's identity
`p_n = Σ_{i=1}^{n-1} (-1)^(i-1) e_i p_(n-i) + (-1)^(n-1) n e_n` with `e_i = e_i(P)`. For `P` with
roots `α_1, …, α_d` in a domain this is `α_1 ^ n + ⋯ + α_d ^ n`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Sections 2.1 and 3.2 (Newton's identities,
Macdonald I.2.11'). -/
noncomputable def polyPowerSum {A : Type*} [CommRing A] (P : A[X]) : ℕ → A
  | 0 => P.natDegree
  | n + 1 => (-1) ^ n * ((n + 1 : ℕ) : A) * polyElemSymm P (n + 1) +
      ∑ i : Fin n, (-1) ^ (i : ℕ) * polyElemSymm P (i + 1) * polyPowerSum P (n - i)
  decreasing_by omega

/-- `p_0(P) = deg P`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 3.2, Notation. -/
theorem polyPowerSum_zero {A : Type*} [CommRing A] (P : A[X]) :
    polyPowerSum P 0 = P.natDegree := by
  rw [polyPowerSum]

/-- `p_1(P) = e_1(P)`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 3.2 (Newton's identities). -/
theorem polyPowerSum_one {A : Type*} [CommRing A] (P : A[X]) :
    polyPowerSum P 1 = polyElemSymm P 1 := by
  rw [polyPowerSum]
  simp

/-- Newton's recurrence for `p_(n+1)(P)`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 3.2 (Newton's identities). -/
theorem polyPowerSum_succ {A : Type*} [CommRing A] (P : A[X]) (n : ℕ) :
    polyPowerSum P (n + 1) = (-1) ^ n * ((n + 1 : ℕ) : A) * polyElemSymm P (n + 1) +
      ∑ i : Fin n, (-1) ^ (i : ℕ) * polyElemSymm P (i + 1) * polyPowerSum P (n - i) := by
  rw [polyPowerSum]

/-- For an ideal `b` of any commutative ring, `a ^ n ∈ p ^ v_p(n!) b` for all `n ≥ 1` and `a ∈ b`
if and only if `a ^ p ∈ p b` for all `a ∈ b`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 3 (`integers-2024-A46-prop-3`). -/
public theorem_wanted pow_mem_prime_pow_padicValNat_factorial_iff {p : ℕ} [Fact p.Prime]
    {B : Type*} [CommRing B] (I : Ideal B) :
    (∀ n : ℕ, 1 ≤ n → ∀ a ∈ I, ∃ c ∈ I, a ^ n = (p : B) ^ padicValNat p n.factorial * c) ↔
      ∀ a ∈ I, ∃ c ∈ I, a ^ p = (p : B) * c

/-- In a `ℤ_(p)`-algebra, an ideal is a divided-power ideal if and only if `a ^ p ∈ p 𝔞` for every
`a ∈ 𝔞`. The paper also assumes `A` torsion-free; the statement does not need it.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 4 (`integers-2024-A46-cor-4`). -/
public theorem_wanted isDividedPowerIdeal_iff_pow_prime_mem {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommRing A] (hA : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A)) (I : Ideal A) :
    IsDividedPowerIdeal I ↔ ∀ a ∈ I, ∃ c ∈ I, a ^ p = (p : A) * c

/-- In a `ℤ_(p)`-algebra, the ideal generated by `S` is a divided-power ideal if and only if
`a ^ p ∈ p 𝔞` for every generator `a ∈ S`. Torsion-freeness is not needed.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 5 (`integers-2024-A46-prop-5`). -/
public theorem_wanted isDividedPowerIdeal_span_iff {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommRing A] (hA : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A)) (S : Set A) :
    IsDividedPowerIdeal (Ideal.span S) ↔ ∀ a ∈ S, ∃ c ∈ Ideal.span S, a ^ p = (p : A) * c

/-- If `𝔞` is a divided-power ideal, then so is `𝔞𝔟` for every ideal `𝔟`. Stated for any
commutative ring.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 6 (`integers-2024-A46-cor-6`). -/
public theorem_wanted IsDividedPowerIdeal.mul {A : Type*} [CommRing A] {I : Ideal A}
    (hI : IsDividedPowerIdeal I) (J : Ideal A) : IsDividedPowerIdeal (I * J)

/-- In a discrete valuation ring `O` with `p O = 𝔪 ^ e`, `e ≥ 1` (so `v_p(𝔪) = 1 / e`), the ideal
`𝔪 ^ k` is a divided-power ideal if and only if `e ≤ (p - 1) k`, that is
`v_p(𝔪 ^ k) ≥ 1 / (p - 1)`. The paper states this for `p`-adic DVRs and remarks that it also holds
for localizations of rings of integers; here `O` is any such DVR, and the zero ideal is omitted.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Lemma 7 (`integers-2024-A46-lem-7`). -/
public theorem_wanted isDividedPowerIdeal_maximalIdeal_pow_iff {p : ℕ} [Fact p.Prime]
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {e : ℕ} (he0 : e ≠ 0)
    (he : Ideal.span {(p : O)} = IsLocalRing.maximalIdeal O ^ e) (k : ℕ) :
    IsDividedPowerIdeal (IsLocalRing.maximalIdeal O ^ k) ↔ e ≤ (p - 1) * k

/-- The maximal ideal of a discrete valuation ring `O` with `p O = 𝔪 ^ e`, `e ≥ 1`, is a
divided-power ideal if and only if the ramification degree `e` is at most `p - 1`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 8 (`integers-2024-A46-cor-8`). -/
public theorem_wanted isDividedPowerIdeal_maximalIdeal_iff {p : ℕ} [Fact p.Prime]
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {e : ℕ} (he0 : e ≠ 0)
    (he : Ideal.span {(p : O)} = IsLocalRing.maximalIdeal O ^ e) :
    IsDividedPowerIdeal (IsLocalRing.maximalIdeal O) ↔ e ≤ p - 1

/-- `(p)` is a divided-power ideal of `ℤ_p`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 8, last sentence
(`integers-2024-A46-cor-8`). -/
public theorem_wanted isDividedPowerIdeal_span_prime_padicInt (p : ℕ) [Fact p.Prime] :
    IsDividedPowerIdeal (Ideal.span {(p : ℤ_[p])})

/-- Let `A` be a torsion-free `ℤ_(p)`-algebra, `𝔞` a divided-power ideal, `P, Q` monic and
`N ≥ 1`. If `e_n(P) ≡ e_n(Q) mod 𝔞` for `1 ≤ n ≤ N`, then `p_N(P) ≡ p_N(Q) mod N𝔞`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 12 (`integers-2024-A46-prop-12`). -/
public theorem_wanted polyPowerSum_sub_mem_of_polyElemSymm_sub_mem {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommRing A] [IsAddTorsionFree A] (hA : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A))
    {I : Ideal A} (hI : IsDividedPowerIdeal I) {P Q : A[X]} (hP : P.Monic) (hQ : Q.Monic)
    {N : ℕ} (hN : 1 ≤ N)
    (h : ∀ n, 1 ≤ n → n ≤ N → polyElemSymm P n - polyElemSymm Q n ∈ I) :
    ∃ c ∈ I, polyPowerSum P N - polyPowerSum Q N = (N : A) * c

/-- Let `A` be a torsion-free `ℤ_(p)`-algebra, `𝔞` a divided-power ideal and `P, Q` monic. If
`p_n(P) ≡ p_n(Q) mod n𝔞` for `1 ≤ n ≤ N`, then `e_n(P) ≡ e_n(Q) mod 𝔞` for `1 ≤ n ≤ N`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 13 (`integers-2024-A46-prop-13`). -/
public theorem_wanted polyElemSymm_sub_mem_of_polyPowerSum_sub_mem {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommRing A] [IsAddTorsionFree A] (hA : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A))
    {I : Ideal A} (hI : IsDividedPowerIdeal I) {P Q : A[X]} (hP : P.Monic) (hQ : Q.Monic)
    {N : ℕ}
    (h : ∀ n, 1 ≤ n → n ≤ N → ∃ c ∈ I, polyPowerSum P n - polyPowerSum Q n = (n : A) * c) :
    ∀ n, 1 ≤ n → n ≤ N → polyElemSymm P n - polyElemSymm Q n ∈ I

/-- For `S ⊆ ℕ`, `exp P_S(t) = Σ_n Σ_{λ ⊢ n, parts in S} (-1)^λ p_λ / z_λ tⁿ`, where
`P_S(t) = Σ_{s ∈ S} (-1)^(s-1) p_s tˢ / s`, `(-1)^λ = (-1)^(n - #parts)` and
`z_λ = Π_a a^(r_a) r_a!`. A `0 ∈ S` is ignored, as the paper's `S` consists of positive integers.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 19 (`integers-2024-A46-prop-19`). -/
public theorem_wanted exp_signedPowerSumSeries_eq_sum_partitions (σ : Type*) [Fintype σ]
    (S : Set ℕ) [DecidablePred (· ∈ S)] :
    (PowerSeries.subst (PowerSeries.mk fun s => if s ∈ S ∧ s ≠ 0 then
        ((-1 : ℚ) ^ (s - 1) / s) • MvPolynomial.psum σ ℚ s else 0) (PowerSeries.exp ℚ) :
        PowerSeries (MvPolynomial σ ℚ)) =
      PowerSeries.mk fun n => ∑ l : n.Partition with ∀ a ∈ l.parts, a ∈ S,
        ((-1 : ℚ) ^ (n - Multiset.card l.parts) /
          ((l.parts.toFinset.prod fun a => a ^ l.parts.count a * (l.parts.count a).factorial :
            ℕ) : ℚ)) • (l.parts.map (MvPolynomial.psum σ ℚ)).prod

/-- `E(t) = exp P(t)`: `Σ_k e_k tᵏ = exp (Σ_{n ≥ 1} (-1)^(n-1) p_n tⁿ / n)`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 20 (`integers-2024-A46-prop-20`). -/
public theorem_wanted exp_signedPowerSumSeries_eq_esymmSeries (σ : Type*) [Fintype σ] :
    (PowerSeries.subst (PowerSeries.mk fun n => if n = 0 then 0 else
        ((-1 : ℚ) ^ (n - 1) / n) • MvPolynomial.psum σ ℚ n) (PowerSeries.exp ℚ) :
        PowerSeries (MvPolynomial σ ℚ)) =
      PowerSeries.mk fun k => MvPolynomial.esymm σ ℚ k

/-- `e_n = Σ_{λ ⊢ n} (-1)^λ p_λ / z_λ`, with `(-1)^λ = (-1)^(n - #parts)` and
`z_λ = Π_a a^(r_a) r_a!`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 21 (`integers-2024-A46-cor-21`). -/
public theorem_wanted esymm_eq_sum_partitions (σ : Type*) [Fintype σ] (n : ℕ) :
    MvPolynomial.esymm σ ℚ n = ∑ l : n.Partition,
      ((-1 : ℚ) ^ (n - Multiset.card l.parts) /
        ((l.parts.toFinset.prod fun a => a ^ l.parts.count a * (l.parts.count a).factorial :
          ℕ) : ℚ)) • (l.parts.map (MvPolynomial.psum σ ℚ)).prod

/-- Kummer: `v_p` of the multinomial coefficient `(r_1 + ⋯ + r_k; r_1, …, r_k)` is the sum of the
carries when `r_1 + ⋯ + r_k` is added in base `p`; the carry into digit position `i ≥ 1` is
`⌊Σ_j (r_j mod pⁱ) / pⁱ⌋`, and positions beyond `m = Σ_j r_j` carry nothing.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Theorem 23 (`integers-2024-A46-thm-23`). -/
public theorem_wanted padicValNat_multinomial_eq_sum_carries {p : ℕ} [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (r : ι → ℕ) :
    padicValNat p (Nat.multinomial s r) =
      ∑ i ∈ Finset.Icc 1 (∑ j ∈ s, r j), (∑ j ∈ s, r j % p ^ i) / p ^ i

/-- `v_p(r_i) ≥ v_p(m) - v_p((m; r_1, …, r_k))` for `m = r_1 + ⋯ + r_k` and `r_i ≠ 0` (the paper
has `v_p(0) = ∞`; with `r = (0, p)` and Mathlib's `v_p(0) = 0` the inequality fails).

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 24 (`integers-2024-A46-cor-24`). -/
public theorem_wanted padicValNat_sum_le_add_padicValNat_multinomial {p : ℕ} [Fact p.Prime]
    {ι : Type*} (s : Finset ι) (r : ι → ℕ) {j : ι} (hj : j ∈ s) (hr : r j ≠ 0) :
    padicValNat p (∑ i ∈ s, r i) ≤ padicValNat p (r j) + padicValNat p (Nat.multinomial s r)

/-- In a `ℤ_(p)`-algebra with divided-power ideal `𝔞`, `x ≡ y mod 𝔞` implies
`x ^ (p ^ m) ≡ y ^ (p ^ m) mod p ^ m 𝔞` for all `m` and `xⁿ ≡ yⁿ mod n𝔞` for all `n`.
Torsion-freeness is not needed.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Lemma 25 (`integers-2024-A46-lem-25`). -/
public theorem_wanted pow_sub_pow_mem_of_sub_mem {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A]
    (hA : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A)) {I : Ideal A} (hI : IsDividedPowerIdeal I)
    {x y : A} (hxy : x - y ∈ I) :
    (∀ m : ℕ, ∃ c ∈ I, x ^ p ^ m - y ^ p ^ m = (p : A) ^ m * c) ∧
      ∀ n : ℕ, ∃ c ∈ I, x ^ n - y ^ n = (n : A) * c

/-- If `f_n ≡ g_n mod 𝔞` for all `n ≥ 1` (`𝔞` a divided-power ideal) and every part of the
partition `λ` occurs a multiple of `p ^ v` times, then `f_λ ≡ g_λ mod p ^ v 𝔞`. Corrected reading:
the paper writes `v = v_p(λ) = min_i v_p(λ_i)`, which is false (`f = e`, `p = 2`, `λ = (2)`,
`P = X² + 2`, `Q = X²`: `e_n(P) ≡ e_n(Q) mod 2` for all `n`, but `e_2(P) - e_2(Q) = 2 ∉ 4ℤ`); the
proof, writing `λ = μ ^ (p ^ v)` in the partition monoid and using `v_p(r_i(λ))` in Proposition 12,
uses the multiplicity valuation stated here. The symmetric functions are abstracted to arbitrary
sequences `f, g`, as the statement only uses their values.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 26 (`integers-2024-A46-cor-26`). -/
public theorem_wanted multiset_prod_sub_prod_mem_of_count_dvd {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommRing A] {I : Ideal A} (hI : IsDividedPowerIdeal I) (f g : ℕ → A)
    (hfg : ∀ n, 1 ≤ n → f n - g n ∈ I) {n : ℕ} (l : n.Partition) {v : ℕ}
    (hv : ∀ a ∈ l.parts, p ^ v ∣ l.parts.count a) :
    ∃ c ∈ I, (l.parts.map f).prod - (l.parts.map g).prod = (p : A) ^ v * c

/-- `Σ_{d ∣ n, p ∤ d} μ(d)` is `1` if `n` is a power of `p` and `0` otherwise (`n ≥ 1`).

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Lemma 28 (`integers-2024-A46-lem-28`). -/
public theorem_wanted sum_moebius_divisors_not_dvd_prime {p : ℕ} (hp : p.Prime) {n : ℕ}
    (hn : n ≠ 0) :
    ∑ d ∈ n.divisors with ¬ p ∣ d, ArithmeticFunction.moebius d =
      if p ^ Nat.log p n = n then 1 else 0

/-- The Artin-Hasse exponential `F(z) = exp (Σ_{j ≥ 0} z^(p^j) / p^j)` has `p`-integral
coefficients: no coefficient has denominator divisible by `p`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 29 (`integers-2024-A46-cor-29`). -/
public theorem_wanted artinHasse_coeff_den_not_dvd (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ¬ p ∣ (PowerSeries.coeff n (PowerSeries.subst
      (PowerSeries.mk fun m : ℕ => if p ^ Nat.log p m = m then (m : ℚ)⁻¹ else 0)
      (PowerSeries.exp ℚ) : PowerSeries ℚ)).den

/-- The Artin-Hasse exponential as an infinite product:
`F(z) = Π_{p ∤ d} (1 - z^d)^(-μ(d)/d)`. The rational power of a series with constant term `1` is
`(1 - z^d)^a = exp (a · log (1 - z^d))` with `log (1 - z^d) = -Σ_{k ≥ 1} z^(dk)/k`, whose
coefficient at `z^m` (`d ∣ m`, `m ≠ 0`) is `-d/m`; the infinite product is read coefficientwise:
the factors with `d > N` are `1 + O(z^(N+1))`, so the identity says that `F` agrees with the
finite product over `d ≤ N` up to `z^N`, for every `N`. `F` is written as in Corollary 29.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 27 (`integers-2024-A46-prop-27`). -/
public theorem_wanted artinHasse_eq_prod_one_sub_pow (p : ℕ) [Fact p.Prime] (N : ℕ) :
    PowerSeries.trunc (N + 1) (PowerSeries.subst
      (PowerSeries.mk fun m : ℕ => if p ^ Nat.log p m = m then (m : ℚ)⁻¹ else 0)
      (PowerSeries.exp ℚ) : PowerSeries ℚ) =
    PowerSeries.trunc (N + 1) (∏ d ∈ Finset.Icc 1 N with ¬ p ∣ d,
      (PowerSeries.subst (PowerSeries.mk fun m : ℕ => if m ≠ 0 ∧ d ∣ m then
          (-(ArithmeticFunction.moebius d : ℚ) / d) * (-(d : ℚ) / m) else 0)
        (PowerSeries.exp ℚ) : PowerSeries ℚ))

/-- `s` is a *`p`-splitting* of `t` (multisets of parts): `t` contains a part `p u` with `u ≥ 1`,
and `s` is obtained from `t` by replacing one instance of `p u` with `p` copies of `u`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Definition 30. -/
public def IsPSplitting (p : ℕ) (s t : Multiset ℕ) : Prop :=
  ∃ u, 1 ≤ u ∧ p * u ∈ t ∧ s = t.erase (p * u) + Multiset.replicate p u

/-- `(u)^p` is a `p`-splitting of `(pu)`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Definition 30. -/
public theorem isPSplitting_replicate_singleton (p : ℕ) {u : ℕ} (hu : 1 ≤ u) :
    IsPSplitting p (Multiset.replicate p u) {p * u} :=
  ⟨u, hu, Multiset.mem_singleton_self _, by simp⟩

/-- The `p`-equivalence class `C_λ` of the multiset of parts `s`: the partitions `μ` of `|s|`
with `μ ∼_p s`, where `∼_p` (`p`-equivalence) is the equivalence relation generated by
`p`-splitting.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Definition 31. -/
public noncomputable def pEquivClass (p : ℕ) (s : Multiset ℕ) : Finset s.sum.Partition := by
  classical
  exact Finset.univ.filter fun μ => Relation.EqvGen (IsPSplitting p) μ.parts s

/-- The contribution `g_λ = Σ_{μ ∼_p λ} (-1)^μ p_μ / z_μ` of one `p`-equivalence class to
`e_n` (Corollary 21), with `(-1)^μ = (-1)^(n - #parts)` and `z_μ = Π_a a^(r_a) r_a!`, as a
symmetric polynomial in finitely many variables over `ℚ`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 5.2, display (8). -/
public noncomputable def pEquivClassSum (σ : Type*) [Fintype σ] (p : ℕ) (s : Multiset ℕ) :
    MvPolynomial σ ℚ :=
  ∑ μ ∈ pEquivClass p s, ((-1 : ℚ) ^ (s.sum - Multiset.card μ.parts) /
    ((μ.parts.toFinset.prod fun a => a ^ μ.parts.count a * (μ.parts.count a).factorial : ℕ) : ℚ)) • (μ.parts.map (MvPolynomial.psum σ ℚ)).prod

/-- `g_∅ = 1`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Section 5.2. -/
public theorem pEquivClassSum_zero (σ : Type*) [Fintype σ] (p : ℕ) :
    pEquivClassSum σ p 0 = 1 := by
  classical
  have h0 : ∀ μ : Nat.Partition 0, μ.parts = 0 := fun μ =>
    Multiset.eq_zero_of_forall_notMem fun a ha =>
      (Nat.pos_iff_ne_zero.mp (μ.parts_pos ha)) (Multiset.sum_eq_zero_iff.mp μ.parts_sum a ha)
  have hc : pEquivClass p 0 = Finset.univ := by
    ext μ
    simp only [pEquivClass, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rw [h0 μ]; exact Relation.EqvGen.refl _
  rw [pEquivClassSum, hc]
  change ∑ μ : Nat.Partition 0, _ = 1
  rw [Finset.univ_unique, Finset.sum_singleton, h0]
  simp

/-- For `p`-deprived multisets of parts `λ`, `μ` (no part divisible by `p`, so no part is `0`)
with no common parts, `g_{λμ} = g_λ g_μ`; consequently `g_λ = Π_u g_{(u)^(r_u(λ))}`, the
product over the distinct parts `u` of `λ` (the factors with `r_u(λ) = 0` are `g_∅ = 1`).

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Lemma 34 (`integers-2024-A46-lem-34`). -/
public theorem_wanted pEquivClassSum_add_of_disjoint (σ : Type*) [Fintype σ] {p : ℕ}
    [Fact p.Prime] {s t : Multiset ℕ} (hs : ∀ a ∈ s, ¬ p ∣ a) (ht : ∀ a ∈ t, ¬ p ∣ a)
    (hst : ∀ a ∈ s, a ∉ t) :
    pEquivClassSum σ p (s + t) = pEquivClassSum σ p s * pEquivClassSum σ p t ∧
      pEquivClassSum σ p s =
        ∏ u ∈ s.toFinset, pEquivClassSum σ p (Multiset.replicate (s.count u) u)

/-- For odd `p` the signs in `g_λ` are constant on the class:
`g_λ = (-1)^λ Σ_{μ ∼_p λ} p_μ / z_μ`.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Lemma 35 (`integers-2024-A46-lem-35`). -/
public theorem_wanted pEquivClassSum_eq_neg_one_pow_smul (σ : Type*) [Fintype σ] {p : ℕ}
    [Fact p.Prime] (hp : Odd p) {n : ℕ} (l : n.Partition) :
    pEquivClassSum σ p l.parts = ((-1 : ℚ) ^ (n - Multiset.card l.parts)) •
      ∑ μ ∈ pEquivClass p l.parts, (1 / ((μ.parts.toFinset.prod fun a => a ^ μ.parts.count a * (μ.parts.count a).factorial : ℕ) : ℚ)) • (μ.parts.map (MvPolynomial.psum σ ℚ)).prod

/-- `g_λ` is `p`-integral: in any finite number of variables, no coefficient of `g_λ` has
denominator divisible by `p` (the paper's `g_λ ∈ Λ_{ℤ_(p)}`).

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Proposition 36 (`integers-2024-A46-prop-36`). -/
public theorem_wanted pEquivClassSum_coeff_den_not_dvd (σ : Type*) [Fintype σ] {p : ℕ}
    [Fact p.Prime] {n : ℕ} (l : n.Partition) (m : σ →₀ ℕ) :
    ¬ p ∣ ((pEquivClassSum σ p l.parts).coeff m).den

end

end MetaMathlibExt
