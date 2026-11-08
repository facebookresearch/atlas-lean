/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.Trace.Basic

/-!
# Necklaces over a group with identity product

Statements from Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6 (arXiv:2405.08937).

An `n`-tuple `x : Fin n → G` is identity-product if `x₁ x₂ ⋯ xₙ = 1`; the cyclic group `C_n`
acts by rotation, here through powers of `finRotate n`, and the orbits are necklaces. The
paper's `[G ÷ m]` is the number `#{a ∈ G | a^m = 1}`, and `[G ÷ K ÷ m] = #{a ∈ G | a^m ∈ K}`
(Definitions 2.2 and 8.2 of the arXiv text). The main count (Theorem 5) is the existing
`MetaMathlibExt.identity_product_necklace_count`.
-/

namespace MetaMathlibExt

@[expose] public section

open scoped ArithmeticFunction.Moebius

/-- The rotation orbit `{x ∘ σ^m | m ∈ ℕ}` of a tuple `x : Fin n → α`, `σ = finRotate n`.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Definition 2.3 (the action of `C_n` by
rotation; necklaces are its orbits), used by Theorem 16 (`jis-2026-26.4.6-thm-16`). -/
def tupleRotationOrbit {α : Type*} {n : ℕ} (x : Fin n → α) : Set (Fin n → α) :=
  {y | ∃ m : ℕ, y = x ∘ ⇑((finRotate n) ^ m)}

/-- A tuple lies in its own rotation orbit.

Source: Grinberg and Mao, Journal of Integer Sequences 29 (2026), Article 26.4.6,
Definition 2.3. -/
theorem self_mem_tupleRotationOrbit {α : Type*} {n : ℕ} (x : Fin n → α) :
    x ∈ tupleRotationOrbit x :=
  ⟨0, by simp⟩

/-- Rotating by one step stays in the orbit.

Source: Grinberg and Mao, Journal of Integer Sequences 29 (2026), Article 26.4.6,
Definition 2.3. -/
theorem comp_finRotate_mem_tupleRotationOrbit {α : Type*} {n : ℕ} (x : Fin n → α) :
    x ∘ ⇑(finRotate n) ∈ tupleRotationOrbit x :=
  ⟨1, by simp⟩

/-- Corollary 6: for `G = ∏_{i=1}^m C_{k_i}` (written additively as `∏ ZMod k_i`, as
`Multiplicative`), the number of identity-product `n`-necklaces is
`(1/n) ∑_{d ∣ n} φ(n/d) ∏_i gcd(k_i, n/d) k_i^{d-1}`.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Corollary 6
(`jis-2026-26.4.6-cor-6`). -/
public theorem_wanted identityProductNecklace_count_pi_cyclic (m : ℕ) (k : Fin m → ℕ)
    [∀ i, NeZero (k i)] (n : ℕ) (hn : 0 < n) :
    (Set.ncard {O : Set (Fin n → ∀ i, Multiplicative (ZMod (k i))) |
        ∃ x, (List.ofFn x).prod = 1 ∧ O = tupleRotationOrbit x} : ℚ) =
      (1 / n : ℚ) * ∑ d ∈ n.divisors, (Nat.totient (n / d) : ℚ) *
        ∏ i, ((Nat.gcd (k i) (n / d) : ℚ) * (k i : ℚ) ^ (d - 1))

/-- Lemma 9: if `g(k) = ∑_{d ∣ k} f(d)` for all `k ≥ 1`, then
`∑_{d ∣ k} (k/d) f(d) = ∑_{d ∣ k} φ(k/d) g(d)` for all `k ≥ 1`.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 9
(`jis-2026-26.4.6-lem-9`). -/
public theorem_wanted sum_div_mul_eq_sum_totient_mul (f g : ℕ → ℚ)
    (hfg : ∀ k, 0 < k → g k = ∑ d ∈ k.divisors, f d) (k : ℕ) (hk : 0 < k) :
    ∑ d ∈ k.divisors, ((k / d : ℕ) : ℚ) * f d =
      ∑ d ∈ k.divisors, (Nat.totient (k / d) : ℚ) * g d

/-- Lemma 11: for integers `a, b, c` with `a, b` not both zero, `a ∣ bc` if and only if
`a / gcd(a, b) ∣ c`.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 11
(`jis-2026-26.4.6-lem-11`). -/
public theorem_wanted int_dvd_mul_iff_div_gcd_dvd (a b c : ℤ) (h : a ≠ 0 ∨ b ≠ 0) :
    a ∣ b * c ↔ a / (Int.gcd a b : ℤ) ∣ c

/-- Lemma 12: `[C_a ÷ b] = gcd(a, b)`: the cyclic group of order `a` has exactly `gcd(a, b)`
elements `x` with `x^b = 1`. Stated for every `b ≥ 0` (the paper takes `b` positive; for
`b = 0` both sides are `a`).

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 12
(`jis-2026-26.4.6-lem-12`). -/
public theorem_wanted card_pow_eq_one_zmod (a b : ℕ) [NeZero a] :
    Fintype.card {x : Multiplicative (ZMod a) // x ^ b = 1} = Nat.gcd a b

/-- Lemma 13: for `k ∣ n` (`n ≥ 1`), the set `A_k` of identity-product `n`-tuples fixed by the
rotation by `k` has `[G ÷ n/k] |G|^{k-1}` elements.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 13, with `A_k` as defined in
Section 5 of the arXiv text (`jis-2026-26.4.6-lem-13`). -/
public theorem_wanted card_identityProduct_period (G : Type*) [Group G] [Fintype G]
    [DecidableEq G] (n k : ℕ) (hn : 0 < n) (hk : k ∣ n) :
    Set.ncard {x : Fin n → G | (List.ofFn x).prod = 1 ∧ x ∘ ⇑((finRotate n) ^ k) = x} =
      Fintype.card {g : G // g ^ (n / k) = 1} * Fintype.card G ^ (k - 1)

/-- Lemma 14: for every `k ≥ 1`, `|A_k| = ∑_{d ∣ k} |P_d|`, where `A_k` is the set of
identity-product `n`-tuples with period `k` and `P_d` those with smallest period `d`.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 14, with `A_k`, `P_k` as in
equation (9) of the arXiv text (`jis-2026-26.4.6-lem-14`). -/
public theorem_wanted card_identityProduct_period_eq_sum_smallestPeriod (G : Type*) [Group G]
    [Fintype G] (n k : ℕ) (hk : 0 < k) :
    Set.ncard {x : Fin n → G | (List.ofFn x).prod = 1 ∧ x ∘ ⇑((finRotate n) ^ k) = x} =
      ∑ d ∈ k.divisors, Set.ncard {x : Fin n → G | (List.ofFn x).prod = 1 ∧
        x ∘ ⇑((finRotate n) ^ d) = x ∧ ∀ l, 0 < l → l < d → x ∘ ⇑((finRotate n) ^ l) ≠ x}

/-- Theorem 16: the number of aperiodic identity-product `n`-necklaces (rotation orbits of
size `n`) is `(1/n) ∑_{d ∣ n} μ(n/d) [G ÷ n/d] |G|^{d-1}`.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 16
(`jis-2026-26.4.6-thm-16`). -/
public theorem_wanted aperiodic_identityProductNecklace_count (G : Type*) [Group G] [Fintype G]
    [DecidableEq G] (n : ℕ) (hn : 0 < n) :
    (Set.ncard {O : Set (Fin n → G) | ∃ x, (List.ofFn x).prod = 1 ∧
        O = tupleRotationOrbit x ∧ O.ncard = n} : ℚ) =
      (1 / n : ℚ) * ∑ d ∈ n.divisors, (μ (n / d) : ℚ) *
        (Fintype.card {g : G // g ^ (n / d) = 1} : ℚ) * (Fintype.card G : ℚ) ^ (d - 1)

/-- Corollary 18: for `k ∣ n`, the number of identity-product `n`-necklaces with smallest
period `k` (rotation orbits of size `k`) is `(1/k) ∑_{d ∣ k} μ(k/d) [G ÷ n/d] |G|^{d-1}`.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Corollary 18
(`jis-2026-26.4.6-cor-18`). -/
public theorem_wanted identityProductNecklace_count_smallestPeriod (G : Type*) [Group G]
    [Fintype G] [DecidableEq G] (n k : ℕ) (hn : 0 < n) (hk : k ∣ n) :
    (Set.ncard {O : Set (Fin n → G) | ∃ x, (List.ofFn x).prod = 1 ∧
        O = tupleRotationOrbit x ∧ O.ncard = k} : ℚ) =
      (1 / k : ℚ) * ∑ d ∈ k.divisors, (μ (k / d) : ℚ) *
        (Fintype.card {g : G // g ^ (n / d) = 1} : ℚ) * (Fintype.card G : ℚ) ^ (d - 1)

/-- Theorem 19: the orbits of `C_n × G` on `G^n` (rotate, and multiply every entry by `h` on
the left) are as many as the identity-product `n`-necklaces, namely
`(1/n) ∑_{d ∣ n} φ(n/d) [G ÷ n/d] |G|^{d-1}`.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 19, with the action of
Section 7 of the arXiv text (`jis-2026-26.4.6-thm-19`). -/
public theorem_wanted homogeneousNecklace_count (G : Type*) [Group G] [Fintype G]
    [DecidableEq G] (n : ℕ) (hn : 0 < n) :
    (Set.ncard {O : Set (Fin n → G) | ∃ x : Fin n → G,
        O = {y | ∃ (m : ℕ) (h : G), y = fun i => h * x (((finRotate n) ^ m) i)}} : ℚ) =
      (1 / n : ℚ) * ∑ d ∈ n.divisors, (Nat.totient (n / d) : ℚ) *
        (Fintype.card {g : G // g ^ (n / d) = 1} : ℚ) * (Fintype.card G : ℚ) ^ (d - 1)

/-- Theorem 22: for a conjugation-closed `K ⊆ G`, the number of `K`-product `n`-necklaces
(`x₁ ⋯ xₙ ∈ K`) is `(1/n) ∑_{d ∣ n} φ(n/d) [G ÷ K ÷ n/d] |G|^{d-1}`. The extraction prints
`[G ÷ K ÷ n]`; the arXiv text (Theorem 8.3) has `n/d`, and the printed version fails for
`G = S₃`, `K = {1}`, `n = 2` (`5` necklaces against `14`).

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 22
(`jis-2026-26.4.6-thm-22`). -/
public theorem_wanted productInNecklace_count (G : Type*) [Group G] [Fintype G] (K : Set G)
    (hK : ∀ g k, k ∈ K → g * k * g⁻¹ ∈ K) (n : ℕ) (hn : 0 < n) :
    (Set.ncard {O : Set (Fin n → G) | ∃ x, (List.ofFn x).prod ∈ K ∧
        O = tupleRotationOrbit x} : ℚ) =
      (1 / n : ℚ) * ∑ d ∈ n.divisors, (Nat.totient (n / d) : ℚ) *
        (Set.ncard {a : G | a ^ (n / d) ∈ K} : ℚ) * (Fintype.card G : ℚ) ^ (d - 1)

/-- Lemma 23: for conjugation-closed `K` and `k ∣ n` (`n ≥ 1`), the `K`-product `n`-tuples
fixed by the rotation by `k` number `[G ÷ K ÷ n/k] |G|^{k-1}`.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 23
(`jis-2026-26.4.6-lem-23`). -/
public theorem_wanted card_productIn_period (G : Type*) [Group G] [Fintype G] (K : Set G)
    (hK : ∀ g k, k ∈ K → g * k * g⁻¹ ∈ K) (n k : ℕ) (hn : 0 < n) (hk : k ∣ n) :
    Set.ncard {x : Fin n → G | (List.ofFn x).prod ∈ K ∧ x ∘ ⇑((finRotate n) ^ k) = x} =
      Set.ncard {a : G | a ^ (n / k) ∈ K} * Fintype.card G ^ (k - 1)

/-- Theorem 24: for conjugation-closed `K`, the number of aperiodic `K`-product
`n`-necklaces is `(1/n) ∑_{d ∣ n} μ(n/d) [G ÷ K ÷ n/d] |G|^{d-1}`.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 24
(`jis-2026-26.4.6-thm-24`). -/
public theorem_wanted aperiodic_productInNecklace_count (G : Type*) [Group G] [Fintype G]
    (K : Set G) (hK : ∀ g k, k ∈ K → g * k * g⁻¹ ∈ K) (n : ℕ) (hn : 0 < n) :
    (Set.ncard {O : Set (Fin n → G) | ∃ x, (List.ofFn x).prod ∈ K ∧
        O = tupleRotationOrbit x ∧ O.ncard = n} : ℚ) =
      (1 / n : ℚ) * ∑ d ∈ n.divisors, (μ (n / d) : ℚ) *
        (Set.ncard {a : G | a ^ (n / d) ∈ K} : ℚ) * (Fintype.card G : ℚ) ^ (d - 1)

section FiniteField

variable (F K : Type*) [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]

/-- Theorem 27 (normal basis theorem for finite fields): `K` has a normal basis over `F`, an
element whose Galois conjugates are linearly independent over `F` (hence a basis, as
`|Gal(K/F)| = [K : F]`).

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 27
(`jis-2026-26.4.6-thm-27`). -/
public theorem_wanted exists_normalBasis_finiteField :
    ∃ β : K, LinearIndependent F (fun σ : K ≃ₐ[F] K => σ β)

/-- Lemma 28: for `n = [K : F]`, `q = |F|` and a normal basis `β, β^q, …, β^{q^{n-1}}`, the
map `Φ(a) = ∑ aᵢ β^{qⁱ}` from `Fⁿ` to `K` is a bijection that turns Frobenius into rotation:
`Φ(a)^q = Φ(a ∘ σ⁻¹)`.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 28, with `Φ` as defined in
Section 9 of the arXiv text (`jis-2026-26.4.6-lem-28`). -/
public theorem_wanted normalBasisMap_bijective_frobenius (n : ℕ)
    (hn : Module.finrank F K = n) (β : K)
    (hβ : LinearIndependent F (fun i : Fin n => β ^ (Fintype.card F ^ (i : ℕ)))) :
    Function.Bijective (fun a : Fin n → F => ∑ i, a i • β ^ (Fintype.card F ^ (i : ℕ))) ∧
      ∀ a : Fin n → F, (∑ i, a i • β ^ (Fintype.card F ^ (i : ℕ))) ^ Fintype.card F =
        ∑ i, (a ∘ ⇑(finRotate n).symm) i • β ^ (Fintype.card F ^ (i : ℕ))

/-- Corollary 29: with `Φ` as in Lemma 28, two tuples lie in the same rotation orbit if and
only if their images are conjugate (have the same minimal polynomial over `F`).

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Corollary 29
(`jis-2026-26.4.6-cor-29`). -/
public theorem_wanted normalBasisMap_rotation_iff_conj (n : ℕ)
    (hn : Module.finrank F K = n) (β : K)
    (hβ : LinearIndependent F (fun i : Fin n => β ^ (Fintype.card F ^ (i : ℕ))))
    (a b : Fin n → F) :
    b ∈ tupleRotationOrbit a ↔
      minpoly F (∑ i, a i • β ^ (Fintype.card F ^ (i : ℕ))) =
        minpoly F (∑ i, b i • β ^ (Fintype.card F ^ (i : ℕ)))

/-- Theorem 30: with `Φ` as in Lemma 28, a tuple is zero-sum if and only if its image has
trace `0` (the trace of a conjugacy class is that of any member).

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 30
(`jis-2026-26.4.6-thm-30`). -/
public theorem_wanted normalBasisMap_sum_eq_zero_iff_trace (n : ℕ)
    (hn : Module.finrank F K = n) (β : K)
    (hβ : LinearIndependent F (fun i : Fin n => β ^ (Fintype.card F ^ (i : ℕ))))
    (a : Fin n → F) :
    ∑ i, a i = 0 ↔ Algebra.trace F K (∑ i, a i • β ^ (Fintype.card F ^ (i : ℕ))) = 0

/-- Corollary 31: the number of conjugacy classes (Galois orbits) of elements of `K` with
trace `0` equals the number `|F^n_0 / C_n|` of zero-sum `n`-necklaces over `F`,
`n = [K : F]`.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Corollary 31
(`jis-2026-26.4.6-cor-31`). -/
public theorem_wanted card_traceZero_conjClasses (n : ℕ) (hn : Module.finrank F K = n) :
    Set.ncard {O : Set K | ∃ z, Algebra.trace F K z = 0 ∧
        O = Set.range (fun σ : K ≃ₐ[F] K => σ z)} =
      Set.ncard {O : Set (Fin n → F) | ∃ a, ∑ i, a i = 0 ∧ O = tupleRotationOrbit a}

/-- Proposition 32: the number of size-`n` conjugacy classes of elements of `K` with trace `0`
equals the number of aperiodic zero-sum `n`-necklaces over `F`, `n = [K : F]`.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Proposition 32
(`jis-2026-26.4.6-prop-32`). -/
public theorem_wanted card_traceZero_conjClasses_size_eq (n : ℕ)
    (hn : Module.finrank F K = n) :
    Set.ncard {O : Set K | ∃ z, Algebra.trace F K z = 0 ∧
        O = Set.range (fun σ : K ≃ₐ[F] K => σ z) ∧ O.ncard = n} =
      Set.ncard {O : Set (Fin n → F) | ∃ a, ∑ i, a i = 0 ∧ O = tupleRotationOrbit a ∧
        O.ncard = n}

/-- Corollary 33: there are `|P_n|` elements of `K` with trace `0` in size-`n` conjugacy
classes, where `P_n` is the set of zero-sum `n`-tuples over `F` with smallest period `n`. The
extraction drops "with trace `0`" (arXiv Corollary 9.9 has it); without it the count fails
for `F = 𝔽₂`, `n = 3` (`6` elements against `|P_3| = 3`).

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Corollary 33
(`jis-2026-26.4.6-cor-33`). -/
public theorem_wanted card_traceZero_size_eq (n : ℕ) (hn : Module.finrank F K = n) :
    Set.ncard {z : K | Algebra.trace F K z = 0 ∧
        (Set.range (fun σ : K ≃ₐ[F] K => σ z)).ncard = n} =
      Set.ncard {a : Fin n → F | ∑ i, a i = 0 ∧
        ∀ l, 0 < l → l < n → a ∘ ⇑((finRotate n) ^ l) ≠ a}

/-- Corollary 35: for `n ≥ 1`, the number of monic irreducible polynomials of degree `n` over
`F` whose coefficient of `X^{n-1}` vanishes equals the number of aperiodic zero-sum
`n`-necklaces over `F`.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Corollary 35
(`jis-2026-26.4.6-cor-35`). -/
public theorem_wanted card_monic_irreducible_nextCoeff_zero (n : ℕ) (hn : 0 < n) :
    Set.ncard {p : Polynomial F | p.Monic ∧ Irreducible p ∧ p.natDegree = n ∧
        p.coeff (n - 1) = 0} =
      Set.ncard {O : Set (Fin n → F) | ∃ a, ∑ i, a i = 0 ∧ O = tupleRotationOrbit a ∧
        O.ncard = n}

end FiniteField

end

end MetaMathlibExt
