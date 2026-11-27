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
public import MathlibExt.Combinatorics.Enumerative.IdentityProductNecklacePiCyclic
public import MathlibExt.Combinatorics.Enumerative.PeriodicTupleProductCount
public import MathlibExt.Combinatorics.Enumerative.TotientWeightedDivisorSum
public import MathlibExt.Data.Int.GCD
public import MathlibExt.FieldTheory.FiniteFieldNormalBasis
public import MathlibExt.FieldTheory.NormalBasisFrobeniusRotation

/-!
# Necklaces over a group with identity product

Statements from Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6 (arXiv:2405.08937).

An `n`-tuple `x : Fin n → G` is identity-product if `x₁ x₂ ⋯ xₙ = 1`; the cyclic group `C_n`
acts by rotation, here through powers of `finRotate n`, and the orbits are necklaces. The
paper's `[G ÷ m]` is the number `#{a ∈ G | a^m = 1}`, and `[G ÷ K ÷ m] = #{a ∈ G | a^m ∈ K}`
(Definitions 2.2 and 8.2 of the arXiv text). The main count (Theorem 5) is the existing
`MetaMathlibExt.identity_product_necklace_count`. The rotation orbits `tupleRotationOrbit` are
defined in `MathlibExt.Combinatorics.Enumerative.TupleRotationOrbit`, and the count over a product
of cyclic groups (Corollary 6) is proved in
`MathlibExt.Combinatorics.Enumerative.IdentityProductNecklacePiCyclic`. The count of periodic
tuples with product in a conjugation-closed set, `MetaMathlibExt.card_productIn_period`, is proved
in `MathlibExt.Combinatorics.Enumerative.PeriodicTupleProductCount`.
-/

namespace MetaMathlibExt

@[expose] public section

open scoped ArithmeticFunction.Moebius

/-- **Splitting periodic identity-product tuples by smallest period.** Let $G$ be a finite
group, $n$ a natural number and $k \ge 1$. Say that $x = (x_0, \dots, x_{n-1}) \in G^n$ has
period $l$ if $x_{i+l} = x_i$ for all $i$, with indices taken mod $n$. Let $A_k$ be the set of
tuples $x$ with $x_0 x_1 \cdots x_{n-1} = 1$ and period $k$, and for $d \ge 1$ let $P_d$ be the
set of tuples $x$ with $x_0 x_1 \cdots x_{n-1} = 1$ that have period $d$ but no period $l$ with
$0 < l < d$. Then $|A_k| = \sum_{d \mid k} |P_d|$.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 14, with `A_k`, `P_k` as in
equation (9) of the arXiv text (`jis-2026-26.4.6-lem-14`). -/
public theorem_wanted card_identityProduct_period_eq_sum_smallestPeriod (G : Type*) [Group G]
    [Fintype G] (n k : ℕ) (hk : 0 < k) :
    Set.ncard {x : Fin n → G | (List.ofFn x).prod = 1 ∧ x ∘ ⇑((finRotate n) ^ k) = x} =
      ∑ d ∈ k.divisors, Set.ncard {x : Fin n → G | (List.ofFn x).prod = 1 ∧
        x ∘ ⇑((finRotate n) ^ d) = x ∧ ∀ l, 0 < l → l < d → x ∘ ⇑((finRotate n) ^ l) ≠ x}

/-- **Counting aperiodic necklaces with identity product.** Let $G$ be a finite group and
$n \ge 1$. For an $n$-tuple $x = (x_0, \dots, x_{n-1}) \in G^n$ let its rotation orbit be the set
of its cyclic rotations $(x_m, x_{m+1}, \dots, x_{m+n-1})$, $m \ge 0$, with indices taken mod
$n$. Then the number of rotation orbits with exactly $n$ elements of tuples $x$ with
$x_0 x_1 \cdots x_{n-1} = 1$ is

$$\frac{1}{n} \sum_{d \mid n} \mu(n/d) \, r_{n/d}(G) \, |G|^{d-1},$$

where $\mu$ is the Möbius function and $r_k(G)$ is the number of $g \in G$ with $g^k = 1$.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 16
(`jis-2026-26.4.6-thm-16`). -/
public theorem_wanted aperiodic_identityProductNecklace_count (G : Type*) [Group G] [Fintype G]
    [DecidableEq G] (n : ℕ) (hn : 0 < n) :
    (Set.ncard {O : Set (Fin n → G) | ∃ x, (List.ofFn x).prod = 1 ∧
        O = tupleRotationOrbit x ∧ O.ncard = n} : ℚ) =
      (1 / n : ℚ) * ∑ d ∈ n.divisors, (μ (n / d) : ℚ) *
        (Fintype.card {g : G // g ^ (n / d) = 1} : ℚ) * (Fintype.card G : ℚ) ^ (d - 1)

/-- **Identity-product necklaces with a given smallest period.** Let $G$ be a finite group, let
$n \ge 1$ and let $k$ be a divisor of $n$. The number of rotation orbits of size $k$ of $n$-tuples
$(x_1, \dots, x_n) \in G^n$ with $x_1 x_2 \cdots x_n = 1$ (identity-product $n$-necklaces of
smallest period $k$) is
$$\frac{1}{k} \sum_{d \mid k} \mu(k/d)\, N(n/d)\, |G|^{d-1},$$
where $\mu$ is the Möbius function and $N(e)$ is the number of $g \in G$ with $g^e = 1$.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Corollary 18
(`jis-2026-26.4.6-cor-18`). -/
public theorem_wanted identityProductNecklace_count_smallestPeriod (G : Type*) [Group G]
    [Fintype G] [DecidableEq G] (n k : ℕ) (hn : 0 < n) (hk : k ∣ n) :
    (Set.ncard {O : Set (Fin n → G) | ∃ x, (List.ofFn x).prod = 1 ∧
        O = tupleRotationOrbit x ∧ O.ncard = k} : ℚ) =
      (1 / k : ℚ) * ∑ d ∈ k.divisors, (μ (k / d) : ℚ) *
        (Fintype.card {g : G // g ^ (n / d) = 1} : ℚ) * (Fintype.card G : ℚ) ^ (d - 1)

/-- **Counting tuples up to rotation and left multiplication.** Let $G$ be a finite group and let
$n \ge 1$. Let $C_n \times G$ act on $G^n$, the cyclic group $C_n$ rotating tuples and $h \in G$
multiplying every entry on the left, so that the orbit of $x = (x_0, \dots, x_{n-1})$ is the set
of tuples $(h x_m, h x_{m+1}, \dots, h x_{m+n-1})$, indices taken modulo $n$, for $m \in \mathbb{N}$
and $h \in G$. The number of these orbits is
$$\frac{1}{n} \sum_{d \mid n} \varphi(n/d)\, N(n/d)\, |G|^{d-1},$$
where $\varphi$ is Euler's totient function and $N(e)$ is the number of $g \in G$ with $g^e = 1$.

The same formula counts the identity-product $n$-necklaces over $G$ (Theorem 5 of the paper), so
the two counts agree.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 19, with the action of
Section 7 of the arXiv text (`jis-2026-26.4.6-thm-19`). -/
public theorem_wanted homogeneousNecklace_count (G : Type*) [Group G] [Fintype G]
    [DecidableEq G] (n : ℕ) (hn : 0 < n) :
    (Set.ncard {O : Set (Fin n → G) | ∃ x : Fin n → G,
        O = {y | ∃ (m : ℕ) (h : G), y = fun i => h * x (((finRotate n) ^ m) i)}} : ℚ) =
      (1 / n : ℚ) * ∑ d ∈ n.divisors, (Nat.totient (n / d) : ℚ) *
        (Fintype.card {g : G // g ^ (n / d) = 1} : ℚ) * (Fintype.card G : ℚ) ^ (d - 1)

/-- **Counting necklaces with product in a conjugation-closed set.** Let $G$ be a finite group,
let $K \subseteq G$ be closed under conjugation ($g k g^{-1} \in K$ for all $g \in G$ and
$k \in K$), and let $n \ge 1$. The number of rotation orbits of $n$-tuples
$(x_1, \dots, x_n) \in G^n$ with $x_1 x_2 \cdots x_n \in K$ ($K$-product $n$-necklaces) is
$$\frac{1}{n} \sum_{d \mid n} \varphi(n/d)\, N_K(n/d)\, |G|^{d-1},$$
where $\varphi$ is Euler's totient function and $N_K(e)$ is the number of $a \in G$ with
$a^e \in K$.

The printed Theorem 22 has $N_K(n)$ in place of $N_K(n/d)$; the arXiv text (Theorem 8.3) has
$n/d$, and the printed formula fails for $G = S_3$, $K = \{1\}$, $n = 2$ ($5$ necklaces against
$14$).

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 22
(`jis-2026-26.4.6-thm-22`). -/
public theorem_wanted productInNecklace_count (G : Type*) [Group G] [Fintype G] (K : Set G)
    (hK : ∀ g k, k ∈ K → g * k * g⁻¹ ∈ K) (n : ℕ) (hn : 0 < n) :
    (Set.ncard {O : Set (Fin n → G) | ∃ x, (List.ofFn x).prod ∈ K ∧
        O = tupleRotationOrbit x} : ℚ) =
      (1 / n : ℚ) * ∑ d ∈ n.divisors, (Nat.totient (n / d) : ℚ) *
        (Set.ncard {a : G | a ^ (n / d) ∈ K} : ℚ) * (Fintype.card G : ℚ) ^ (d - 1)

/-- **Counting aperiodic necklaces with product in a conjugation-closed set.** Let $G$ be a
finite group, let $K \subseteq G$ satisfy $g c g^{-1} \in K$ for all $g \in G$ and $c \in K$, and
let $n \ge 1$. For an $n$-tuple $x = (x_0, \dots, x_{n-1}) \in G^n$ let its rotation orbit be the
set of its cyclic rotations $(x_m, x_{m+1}, \dots, x_{m+n-1})$, $m \ge 0$, with indices taken mod
$n$. Then the number of rotation orbits with exactly $n$ elements of tuples $x$ with
$x_0 x_1 \cdots x_{n-1} \in K$ is

$$\frac{1}{n} \sum_{d \mid n} \mu(n/d) \, \#\{a \in G : a^{n/d} \in K\} \, |G|^{d-1},$$

where $\mu$ is the Möbius function.

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

/-- **Rotation orbits correspond to conjugate elements.** Let $K$ be a finite field that is an
algebra over a finite field $F$, let $q = |F|$ and $n = [K : F]$, and let $\beta \in K$ be such
that $\beta, \beta^q, \dots, \beta^{q^{n-1}}$ are linearly independent over $F$. Define
$\Phi : F^n \to K$ by $\Phi(a_0, \dots, a_{n-1}) = \sum_{i=0}^{n-1} a_i \beta^{q^i}$. Then for all
$a, b \in F^n$, the tuple $b$ lies in the rotation orbit of $a$ if and only if $\Phi(a)$ and
$\Phi(b)$ have the same minimal polynomial over $F$.

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

/-- **Zero-sum tuples correspond to trace-zero elements.** Let $K$ be a finite field that is an
algebra over a finite field $F$, let $q = |F|$ and $n = [K : F]$, and let $\beta \in K$ be such
that $\beta, \beta^q, \dots, \beta^{q^{n-1}}$ are linearly independent over $F$. Define
$\Phi : F^n \to K$ by $\Phi(a_0, \dots, a_{n-1}) = \sum_{i=0}^{n-1} a_i \beta^{q^i}$. Then for
every $a = (a_0, \dots, a_{n-1}) \in F^n$, we have $a_0 + a_1 + \dots + a_{n-1} = 0$ if and only if
the trace of $\Phi(a)$ from $K$ to $F$ is $0$.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 30
(`jis-2026-26.4.6-thm-30`). -/
public theorem_wanted normalBasisMap_sum_eq_zero_iff_trace (n : ℕ)
    (hn : Module.finrank F K = n) (β : K)
    (hβ : LinearIndependent F (fun i : Fin n => β ^ (Fintype.card F ^ (i : ℕ))))
    (a : Fin n → F) :
    ∑ i, a i = 0 ↔ Algebra.trace F K (∑ i, a i • β ^ (Fintype.card F ^ (i : ℕ))) = 0

/-- **Trace-zero Galois orbits and zero-sum necklaces.** Let $K$ be a finite field extension
of a finite field $F$ and $n = [K : F]$. For $z \in K$ let its Galois orbit be the set of all
$\sigma(z)$ with $\sigma$ an automorphism of $K$ fixing $F$, and for
$a = (a_0, \dots, a_{n-1}) \in F^n$ let its rotation orbit be the set of its cyclic rotations
$(a_m, a_{m+1}, \dots, a_{m+n-1})$, $m \ge 0$, with indices taken mod $n$. The number of Galois
orbits of elements $z \in K$ with $\operatorname{Tr}_{K/F}(z) = 0$ equals the number of rotation
orbits of tuples $a \in F^n$ with $a_0 + a_1 + \dots + a_{n-1} = 0$.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Corollary 31
(`jis-2026-26.4.6-cor-31`). -/
public theorem_wanted card_traceZero_conjClasses (n : ℕ) (hn : Module.finrank F K = n) :
    Set.ncard {O : Set K | ∃ z, Algebra.trace F K z = 0 ∧
        O = Set.range (fun σ : K ≃ₐ[F] K => σ z)} =
      Set.ncard {O : Set (Fin n → F) | ∃ a, ∑ i, a i = 0 ∧ O = tupleRotationOrbit a}

/-- **Trace-zero Galois orbits of full size and aperiodic zero-sum necklaces.** Let $K$ be a
finite field extension of a finite field $F$ and $n = [K : F]$. For $z \in K$ let its Galois
orbit be the set of all $\sigma(z)$ with $\sigma$ an automorphism of $K$ fixing $F$, and for
$a = (a_0, \dots, a_{n-1}) \in F^n$ let its rotation orbit be the set of its cyclic rotations
$(a_m, a_{m+1}, \dots, a_{m+n-1})$, $m \ge 0$, with indices taken mod $n$. The number of Galois
orbits with exactly $n$ elements of elements $z \in K$ with $\operatorname{Tr}_{K/F}(z) = 0$
equals the number of rotation orbits with exactly $n$ elements of tuples $a \in F^n$ with
$a_0 + a_1 + \dots + a_{n-1} = 0$.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Proposition 32
(`jis-2026-26.4.6-prop-32`). -/
public theorem_wanted card_traceZero_conjClasses_size_eq (n : ℕ)
    (hn : Module.finrank F K = n) :
    Set.ncard {O : Set K | ∃ z, Algebra.trace F K z = 0 ∧
        O = Set.range (fun σ : K ≃ₐ[F] K => σ z) ∧ O.ncard = n} =
      Set.ncard {O : Set (Fin n → F) | ∃ a, ∑ i, a i = 0 ∧ O = tupleRotationOrbit a ∧
        O.ncard = n}

/-- **Trace-zero elements with Galois orbits of full size.** Let $K$ be a finite field
extension of a finite field $F$ and $n = [K : F]$. The number of $z \in K$ with
$\operatorname{Tr}_{K/F}(z) = 0$ whose Galois orbit, the set of all $\sigma(z)$ with $\sigma$ an
automorphism of $K$ fixing $F$, has exactly $n$ elements equals the number of tuples
$a = (a_0, \dots, a_{n-1}) \in F^n$ with $a_0 + a_1 + \dots + a_{n-1} = 0$ for which there is no
$l$ with $0 < l < n$ such that $a_{i+l} = a_i$ for all $i$ (indices taken mod $n$).

The trace condition, present in Corollary 9.9 of the arXiv text, cannot be dropped: for
$F = \mathbb{F}_2$ and $n = 3$ there are $6$ elements with Galois orbits of size $3$ but only $3$
such tuples.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Corollary 33
(`jis-2026-26.4.6-cor-33`). -/
public theorem_wanted card_traceZero_size_eq (n : ℕ) (hn : Module.finrank F K = n) :
    Set.ncard {z : K | Algebra.trace F K z = 0 ∧
        (Set.range (fun σ : K ≃ₐ[F] K => σ z)).ncard = n} =
      Set.ncard {a : Fin n → F | ∑ i, a i = 0 ∧
        ∀ l, 0 < l → l < n → a ∘ ⇑((finRotate n) ^ l) ≠ a}

/-- **Monic irreducible polynomials with vanishing second coefficient.** Let $F$ be a finite
field and $n \ge 1$. For $a = (a_0, \dots, a_{n-1}) \in F^n$ let its rotation orbit be the set
of its cyclic rotations $(a_m, a_{m+1}, \dots, a_{m+n-1})$, $m \ge 0$, with indices taken mod
$n$. The number of monic irreducible polynomials of degree $n$ over $F$ whose coefficient of
$X^{n-1}$ is $0$ equals the number of rotation orbits with exactly $n$ elements of tuples
$a \in F^n$ with $a_0 + a_1 + \dots + a_{n-1} = 0$.

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
