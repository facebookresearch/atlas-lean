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

/-- **Rotation orbit of a tuple.** Let $x = (x_0, \dots, x_{n-1})$ be a tuple of length $n$ with
entries in a type $\alpha$, and let $\sigma$ be the cyclic rotation of $\{0, \dots, n-1\}$ that
sends $i$ to $i + 1$ for $i < n - 1$ and sends $n - 1$ to $0$. The rotation orbit of $x$ is the
set of tuples $x \circ \sigma^m$ for $m \in \mathbb{N}$, that is, of the cyclic shifts
$(x_m, x_{m+1}, \dots, x_{m+n-1})$ of $x$, with indices taken modulo $n$.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Definition 2.3 (the action of `C_n` by
rotation; necklaces are its orbits), used by Theorem 16 (`jis-2026-26.4.6-thm-16`). -/
def tupleRotationOrbit {α : Type*} {n : ℕ} (x : Fin n → α) : Set (Fin n → α) :=
  {y | ∃ m : ℕ, y = x ∘ ⇑((finRotate n) ^ m)}

/-- **A tuple lies in its own rotation orbit.** Every tuple $x$ of length $n$ with entries in a
type $\alpha$ belongs to the rotation orbit of $x$.

Source: Grinberg and Mao, Journal of Integer Sequences 29 (2026), Article 26.4.6,
Definition 2.3. -/
theorem self_mem_tupleRotationOrbit {α : Type*} {n : ℕ} (x : Fin n → α) :
    x ∈ tupleRotationOrbit x :=
  ⟨0, by simp⟩

/-- **One-step rotation stays in the rotation orbit.** For every tuple
$x = (x_0, \dots, x_{n-1})$ with entries in a type $\alpha$, the tuple whose $i$-th entry is
$x_{i+1}$, indices taken modulo $n$ (that is, $(x_1, \dots, x_{n-1}, x_0)$ when $n \ge 1$), lies in
the rotation orbit of $x$.

Source: Grinberg and Mao, Journal of Integer Sequences 29 (2026), Article 26.4.6,
Definition 2.3. -/
theorem comp_finRotate_mem_tupleRotationOrbit {α : Type*} {n : ℕ} (x : Fin n → α) :
    x ∘ ⇑(finRotate n) ∈ tupleRotationOrbit x :=
  ⟨1, by simp⟩

/-- **Identity-product necklaces over a product of cyclic groups.** Let $k_1, \dots, k_m$ be
positive integers and let $G = C_{k_1} \times \dots \times C_{k_m}$, where $C_k$ is the cyclic
group $\mathbb{Z} / k\mathbb{Z}$ written multiplicatively. For $n \ge 1$, the number of rotation
orbits of $n$-tuples $(x_1, \dots, x_n) \in G^n$ with $x_1 x_2 \cdots x_n = 1$ (identity-product
$n$-necklaces) is
$$\frac{1}{n} \sum_{d \mid n} \varphi(n/d) \prod_{i=1}^{m} \gcd(k_i, n/d)\, k_i^{d-1},$$
where $\varphi$ is Euler's totient function.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Corollary 6
(`jis-2026-26.4.6-cor-6`). -/
public theorem_wanted identityProductNecklace_count_pi_cyclic (m : ℕ) (k : Fin m → ℕ)
    [∀ i, NeZero (k i)] (n : ℕ) (hn : 0 < n) :
    (Set.ncard {O : Set (Fin n → ∀ i, Multiplicative (ZMod (k i))) |
        ∃ x, (List.ofFn x).prod = 1 ∧ O = tupleRotationOrbit x} : ℚ) =
      (1 / n : ℚ) * ∑ d ∈ n.divisors, (Nat.totient (n / d) : ℚ) *
        ∏ i, ((Nat.gcd (k i) (n / d) : ℚ) * (k i : ℚ) ^ (d - 1))

/-- **Totient-weighted divisor sum identity.** Let $f$ and $g$ be functions from the natural
numbers to the rational numbers such that $g(k) = \sum_{d \mid k} f(d)$ for every positive
integer $k$, where sums over $d \mid k$ run over the positive divisors $d$ of $k$. Then for
every positive integer $k$,
$$\sum_{d \mid k} \frac{k}{d} \, f(d) = \sum_{d \mid k} \varphi\left(\frac{k}{d}\right) g(d),$$
where $\varphi$ is Euler's totient function.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 9
(`jis-2026-26.4.6-lem-9`). -/
public theorem_wanted sum_div_mul_eq_sum_totient_mul (f g : ℕ → ℚ)
    (hfg : ∀ k, 0 < k → g k = ∑ d ∈ k.divisors, f d) (k : ℕ) (hk : 0 < k) :
    ∑ d ∈ k.divisors, ((k / d : ℕ) : ℚ) * f d =
      ∑ d ∈ k.divisors, (Nat.totient (k / d) : ℚ) * g d

/-- **Divisibility of a product through the gcd.** Let $a, b, c$ be integers with $a$ and $b$ not
both zero. Then $a$ divides $bc$ if and only if $a / \gcd(a, b)$ divides $c$.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 11
(`jis-2026-26.4.6-lem-11`). -/
public theorem_wanted int_dvd_mul_iff_div_gcd_dvd (a b c : ℤ) (h : a ≠ 0 ∨ b ≠ 0) :
    a ∣ b * c ↔ a / (Int.gcd a b : ℤ) ∣ c

/-- **Counting solutions of $x^b = 1$ in a cyclic group.** For natural numbers $a \ge 1$ and
$b$, the cyclic group of order $a$ has exactly $\gcd(a, b)$ elements $x$ with $x^b = 1$.

The paper takes $b$ positive; for $b = 0$ both sides equal $a$.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 12
(`jis-2026-26.4.6-lem-12`). -/
public theorem_wanted card_pow_eq_one_zmod (a b : ℕ) [NeZero a] :
    Fintype.card {x : Multiplicative (ZMod a) // x ^ b = 1} = Nat.gcd a b

/-- **Counting identity-product tuples with a given period.** Let $G$ be a finite group,
$n \ge 1$ and $k$ a divisor of $n$. The number of tuples $x = (x_0, \dots, x_{n-1}) \in G^n$
with $x_0 x_1 \cdots x_{n-1} = 1$ and $x_{i+k} = x_i$ for all $i$ (indices taken mod $n$) is
$r_{n/k}(G) \, |G|^{k-1}$, where $r_m(G)$ is the number of $g \in G$ with $g^m = 1$.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 13, with `A_k` as defined in
Section 5 of the arXiv text (`jis-2026-26.4.6-lem-13`). -/
public theorem_wanted card_identityProduct_period (G : Type*) [Group G] [Fintype G]
    [DecidableEq G] (n k : ℕ) (hn : 0 < n) (hk : k ∣ n) :
    Set.ncard {x : Fin n → G | (List.ofFn x).prod = 1 ∧ x ∘ ⇑((finRotate n) ^ k) = x} =
      Fintype.card {g : G // g ^ (n / k) = 1} * Fintype.card G ^ (k - 1)

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

/-- **Counting periodic tuples with product in a conjugation-closed set.** Let $G$ be a finite
group, let $K \subseteq G$ satisfy $g c g^{-1} \in K$ for all $g \in G$ and $c \in K$, let
$n \ge 1$ and let $k$ be a divisor of $n$. The number of tuples
$x = (x_0, \dots, x_{n-1}) \in G^n$ with $x_0 x_1 \cdots x_{n-1} \in K$ and $x_{i+k} = x_i$ for
all $i$ (indices taken mod $n$) is $\#\{a \in G : a^{n/k} \in K\} \cdot |G|^{k-1}$.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 23
(`jis-2026-26.4.6-lem-23`). -/
public theorem_wanted card_productIn_period (G : Type*) [Group G] [Fintype G] (K : Set G)
    (hK : ∀ g k, k ∈ K → g * k * g⁻¹ ∈ K) (n k : ℕ) (hn : 0 < n) (hk : k ∣ n) :
    Set.ncard {x : Fin n → G | (List.ofFn x).prod ∈ K ∧ x ∘ ⇑((finRotate n) ^ k) = x} =
      Set.ncard {a : G | a ^ (n / k) ∈ K} * Fintype.card G ^ (k - 1)

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

/-- **Normal basis theorem for finite fields.** Let $K$ be a finite field that is an algebra over
a finite field $F$. Then there is an element $\beta \in K$ whose images $\sigma(\beta)$, as $\sigma$
ranges over the $F$-algebra automorphisms of $K$, are linearly independent over $F$ (as a family
indexed by $\sigma$).

Since $K / F$ is Galois, there are $[K : F]$ such automorphisms, so these images form a basis of
$K$ over $F$, a normal basis.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 27
(`jis-2026-26.4.6-thm-27`). -/
public theorem_wanted exists_normalBasis_finiteField :
    ∃ β : K, LinearIndependent F (fun σ : K ≃ₐ[F] K => σ β)

/-- **Normal basis coordinates turn Frobenius into rotation.** Let $K$ be a finite field that is an
algebra over a finite field $F$, let $q = |F|$ and $n = [K : F]$, and let $\beta \in K$ be such
that $\beta, \beta^q, \dots, \beta^{q^{n-1}}$ are linearly independent over $F$. Define
$\Phi : F^n \to K$ by $\Phi(a_0, \dots, a_{n-1}) = \sum_{i=0}^{n-1} a_i \beta^{q^i}$. Then $\Phi$ is
a bijection, and for every $a \in F^n$,
$$\Phi(a_0, \dots, a_{n-1})^q = \Phi(a_{n-1}, a_0, a_1, \dots, a_{n-2}),$$
that is, raising to the $q$-th power rotates the coordinates one step.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Lemma 28, with `Φ` as defined in
Section 9 of the arXiv text (`jis-2026-26.4.6-lem-28`). -/
public theorem_wanted normalBasisMap_bijective_frobenius (n : ℕ)
    (hn : Module.finrank F K = n) (β : K)
    (hβ : LinearIndependent F (fun i : Fin n => β ^ (Fintype.card F ^ (i : ℕ)))) :
    Function.Bijective (fun a : Fin n → F => ∑ i, a i • β ^ (Fintype.card F ^ (i : ℕ))) ∧
      ∀ a : Fin n → F, (∑ i, a i • β ^ (Fintype.card F ^ (i : ℕ))) ^ Fintype.card F =
        ∑ i, (a ∘ ⇑(finRotate n).symm) i • β ^ (Fintype.card F ^ (i : ℕ))

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
