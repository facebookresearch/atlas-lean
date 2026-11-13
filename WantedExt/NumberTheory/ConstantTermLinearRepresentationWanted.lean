/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.ZMod.Basic
public import MathlibExt.Data.Set.Density

namespace MetaMathlibExt

@[expose] public section

/-! A Laurent polynomial in `r` variables with coefficients in `R` is an element of
`AddMonoidAlgebra R (Fin r → ℤ)`; its coefficient of `x^j` is `f.coeff j` and its
constant term `ct[f]` is `f.coeff 0`. Kohen's array `a^n_k = coef_{-k}[P^n]` is
`(P ^ n).coeff (-k)`. The paper's index box `T = [-m, m]^r` is
`Fintype.piFinset fun _ => Finset.Icc (-m) m`. Definitions follow Kohen's arXiv
version (arXiv:2503.21988v1, Sections 1, 2 and 5), which matches the journal records. -/

/-- **Cartier operator $\Lambda_k$ on Laurent polynomials.** Let $R$ be a semiring and $f$ a
Laurent polynomial in $r$ variables with coefficients in $R$. For a natural number $k > 0$,
$\Lambda_k f$ keeps the terms of $f$ whose exponents are all multiples of $k$ and substitutes
$x_s^k \mapsto x_s$ for each variable, so that the coefficient of $x^j$ in $\Lambda_k f$ is the
coefficient of $x^{kj}$ in $f$ for every $j \in \mathbb{Z}^r$. For $k = 0$ it is set to
$\Lambda_0 f = 0$ (the paper uses only positive $k$).

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Section 2 (definition of `Λ_k`). -/
public noncomputable def laurentCartier {R : Type*} [Semiring R] {r : ℕ} (k : ℕ)
    (f : AddMonoidAlgebra R (Fin r → ℤ)) : AddMonoidAlgebra R (Fin r → ℤ) :=
  if hk : k = 0 then 0 else
    .ofCoeff (Finsupp.comapDomain (fun j => k • j) f.coeff
      (fun _ _ _ _ h => smul_right_injective (Fin r → ℤ) hk h))

/-- **Coefficients of Kohen's operator $\Lambda_k$.** Let $R$ be a semiring and let $r$ and
$k \ne 0$ be natural numbers. For every Laurent polynomial $f$ in $r$ variables with coefficients
in $R$ and every $j \in \mathbb{Z}^r$, the coefficient of $x^j$ in $\Lambda_k f$ is the
coefficient of $x^{kj}$ in $f$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Section 2 (definition of `Λ_k`). -/
public theorem coeff_laurentCartier {R : Type*} [Semiring R] {r k : ℕ} (hk : k ≠ 0)
    (f : AddMonoidAlgebra R (Fin r → ℤ)) (j : Fin r → ℤ) :
    (laurentCartier k f).coeff j = f.coeff (k • j) := by
  simp [laurentCartier, hk]

/-- **Degree of a Laurent polynomial.** Let $R$ be a semiring and let $f$ be a Laurent polynomial
in $r$ variables $x_1, \dots, x_r$ with coefficients in $R$. Kohen's degree $\deg f$ of $f$ is the
largest absolute value $|j_i|$ of a single exponent, taken over all $i$ and all exponent vectors
$j \in \mathbb{Z}^r$ whose monomial $x^j$ has nonzero coefficient in $f$, and is $0$ if there is
no such exponent (in particular for the zero polynomial). For example, over $\mathbb{Z}$ in two
variables $x, y$ one has $\deg(5x^{-3}y^{-2} + 2xy^{-1}) = 3$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Section 1.1. -/
public def laurentDeg {R : Type*} [Semiring R] {r : ℕ}
    (f : AddMonoidAlgebra R (Fin r → ℤ)) : ℕ :=
  f.coeff.support.sup fun j => Finset.univ.sup fun i => (j i).natAbs

/-- **Exponent criterion for the degree of a Laurent polynomial.** Let $R$ be a semiring, let
$r$ and $m$ be natural numbers, and let $f$ be a Laurent polynomial in $r$ variables
$x_1, \dots, x_r$ with coefficients in $R$. Then Kohen's degree of $f$ (the largest absolute
value of a single exponent occurring in $f$, or $0$ if there is none) is at most $m$ if and only
if every exponent vector $j \in \mathbb{Z}^r$ whose monomial $x^j$ has nonzero coefficient in
$f$ satisfies $|j_i| \le m$ for every $i$, that is, lies in $[-m, m]^r$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Section 1.1. -/
public theorem laurentDeg_le_iff {R : Type*} [Semiring R] {r : ℕ}
    (f : AddMonoidAlgebra R (Fin r → ℤ)) (m : ℕ) :
    laurentDeg f ≤ m ↔ ∀ j ∈ f.coeff.support, ∀ i, (j i).natAbs ≤ m := by
  simp [laurentDeg, Finset.sup_le_iff]

/-- **Occurrence of a sequence factor at a position.** Let $s = (s_n)_{n \ge 0}$ be a sequence and
let $i$, $\ell$ and $i'$ be natural numbers. The factor of $s$ of length $\ell$ starting at
position $i$ occurs at position $i'$ when $s_{i'+t} = s_{i+t}$ for every natural number $t < \ell$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Definition 1. -/
public def SeqFactorOccursAt {α : Type*} (s : ℕ → α) (i ℓ i' : ℕ) : Prop :=
  ∀ t < ℓ, s (i' + t) = s (i + t)

/-- **Recurrent sequence.** A sequence $s : \mathbb{N} \to \alpha$ is recurrent if every
occurrence of a factor is followed by a later occurrence: for all $i, \ell \in \mathbb{N}$ there
is $j > 0$ such that $s(i + j + t) = s(i + t)$ for every $t < \ell$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
definition before Proposition 19. -/
public def IsRecurrentSeq {α : Type*} (s : ℕ → α) : Prop :=
  ∀ i ℓ : ℕ, ∃ j, 0 < j ∧ SeqFactorOccursAt s i ℓ (i + j)

/-- **Uniformly recurrent sequence.** A sequence $s : \mathbb{N} \to \alpha$ is uniformly
recurrent if for every factor $w$ there is a constant $C_w$ such that every occurrence of $w$ is
followed by another occurrence at distance at most $C_w$: for all $i, \ell \in \mathbb{N}$ there
is $C \in \mathbb{N}$ such that for every $i'$ with $s(i' + t) = s(i + t)$ for all $t < \ell$,
there is $j$ with $0 < j \le C$ and $s(i' + j + t) = s(i + t)$ for all $t < \ell$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Definition 1. -/
public def IsUniformlyRecurrentSeq {α : Type*} (s : ℕ → α) : Prop :=
  ∀ i ℓ : ℕ, ∃ C, ∀ i', SeqFactorOccursAt s i ℓ i' →
    ∃ j, 0 < j ∧ j ≤ C ∧ SeqFactorOccursAt s i ℓ (i' + j)

/-- **Linearly recurrent sequence.** A sequence $s = (s_n)_{n \in \mathbb{N}}$ with values in a
set $\alpha$ is linearly recurrent if there is $K \in \mathbb{N}$ such that for all
$i, i' \in \mathbb{N}$ and $\ell \ge 1$ with $s_{i'+t} = s_{i+t}$ for all $t < \ell$, there is $j$
with $0 < j \le K \ell$ and $s_{i'+j+t} = s_{i+t}$ for all $t < \ell$. That is, each occurrence
of a nonempty factor of length $\ell$ is followed by another occurrence starting at most
$K \ell$ positions later.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Definition 1. -/
public def IsLinearlyRecurrentSeq {α : Type*} (s : ℕ → α) : Prop :=
  ∃ K : ℕ, ∀ i ℓ : ℕ, 0 < ℓ → ∀ i', SeqFactorOccursAt s i ℓ i' →
    ∃ j, 0 < j ∧ j ≤ K * ℓ ∧ SeqFactorOccursAt s i ℓ (i' + j)

/-- **Linearly recurrent sequences are uniformly recurrent.** Every linearly recurrent sequence
$s : \mathbb{N} \to \alpha$, with values in any type $\alpha$, is uniformly recurrent.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Definition 1. -/
public theorem IsLinearlyRecurrentSeq.isUniformlyRecurrentSeq {α : Type*} {s : ℕ → α}
    (h : IsLinearlyRecurrentSeq s) : IsUniformlyRecurrentSeq s := by
  obtain ⟨K, hK⟩ := h
  intro i ℓ
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · exact ⟨1, fun _ _ => ⟨1, one_pos, le_rfl, fun t ht => absurd ht (Nat.not_lt_zero t)⟩⟩
  · exact ⟨K * ℓ, fun i' hi' => hK i ℓ hℓ i' hi'⟩

/-- **Uniformly recurrent sequences are recurrent.** Every uniformly recurrent sequence
$s : \mathbb{N} \to \alpha$, with values in any type $\alpha$, is recurrent.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Definition 1. -/
public theorem IsUniformlyRecurrentSeq.isRecurrentSeq {α : Type*} {s : ℕ → α}
    (h : IsUniformlyRecurrentSeq s) : IsRecurrentSeq s := by
  intro i ℓ
  obtain ⟨C, hC⟩ := h i ℓ
  obtain ⟨j, hj, -, hocc⟩ := hC i fun _ _ => rfl
  exact ⟨j, hj, hocc⟩

/-- **Constant sequences are linearly recurrent.** For every set $\alpha$ and every $c \in \alpha$,
the constant sequence $n \mapsto c$ on $\mathbb{N}$ is linearly recurrent.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Definition 1. -/
public theorem isLinearlyRecurrentSeq_const {α : Type*} (c : α) :
    IsLinearlyRecurrentSeq fun _ : ℕ => c :=
  ⟨1, fun _ ℓ hℓ _ _ => ⟨1, one_pos, by omega, fun _ _ => rfl⟩⟩

/-! ### Section 2: the Rowland–Zeilberger congruence and the degree bound -/

/-- **Rowland–Zeilberger congruence.** Let $p$ be a prime and let $P$ and $Q$ be Laurent
polynomials in $r$ variables with integer coefficients. Write $\operatorname{ct}[F]$ for the
constant term of a Laurent polynomial $F$ and $\Lambda_p$ for Kohen's operator, which keeps the
terms whose exponents are all divisible by $p$ and replaces $x^{pj}$ by $x^j$. Then for all
natural numbers $n$ and $k$,
$\operatorname{ct}[P^{pn+k} Q] \equiv \operatorname{ct}[P^n \Lambda_p(P^k Q)] \pmod{p}$.

The exponents $n$ and $k$ are natural numbers; the paper writes "integers", but negative powers
of a general Laurent polynomial are undefined.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 3 (`jis-2026-26.4.2-lem-3`). -/
public theorem_wanted constantTerm_pow_mul_modEq_laurentCartier {r p : ℕ} (hp : p.Prime)
    (P Q : AddMonoidAlgebra ℤ (Fin r → ℤ)) (n k : ℕ) :
    (P ^ (p * n + k) * Q).coeff 0 ≡ (P ^ n * laurentCartier p (P ^ k * Q)).coeff 0 [ZMOD p]

/-- **Degree bound for the Rowland–Zeilberger states.** Let $p$ be a prime and let $P$ and $Q$
be Laurent polynomials in $r$ variables with integer coefficients. Write $\deg F$ for the largest
absolute value of an exponent of a variable occurring in $F$, and $\Lambda_p$ for the operator
that keeps the terms whose exponents are all multiples of $p$ and substitutes $x_s^p \mapsto x_s$.
For every finite list $k_1, \dots, k_n$ of natural numbers with each $k_t < p$, starting from $Q$
and applying $R \mapsto \Lambda_p(P^{k_t} R)$ for $t = 1, \dots, n$ in turn gives a Laurent
polynomial of degree at most $\max(\deg P - 1, \deg Q)$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 4 (`jis-2026-26.4.2-lem-4`). -/
public theorem_wanted laurentDeg_foldl_laurentCartier_le {r p : ℕ} (hp : p.Prime)
    (P Q : AddMonoidAlgebra ℤ (Fin r → ℤ)) (ks : List ℕ) (hks : ∀ k ∈ ks, k < p) :
    laurentDeg (ks.foldl (fun R k => laurentCartier p (P ^ k * R)) Q) ≤
      max (laurentDeg P - 1) (laurentDeg Q)

/-! ### Section 3: the linear representation mod `p` -/

/-- **Cartier operator applied to a power times a monomial.** Let $p$ be a prime and $P$ a
Laurent polynomial in $r$ variables with integer coefficients. Write $\mathrm{coef}_e[F]$ for the
coefficient of $x^e$ in a Laurent polynomial $F$, $\deg F$ for the largest absolute value of an
exponent of a variable occurring in $F$, and $\Lambda_p$ for the Cartier operator with
$\mathrm{coef}_j[\Lambda_p F] = \mathrm{coef}_{pj}[F]$. Let $m \in \mathbb{N}$ with
$\deg P \le m + 1$, put $T = [-m, m]^r \subset \mathbb{Z}^r$, and let $k < p$ be a natural
number and $i \in T$. Then
$\Lambda_p(P^k x^i) = \sum_{j \in T} \mathrm{coef}_{pj - i}[P^k] \, x^j$.

In Kohen's notation $\mathrm{coef}_{pj - i}[P^k]$ is $a^k_{i - pj}$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Proposition 6 (`jis-2026-26.4.2-prop-6`). -/
public theorem_wanted laurentCartier_pow_mul_single_eq_sum {r p : ℕ} (hp : p.Prime)
    (P : AddMonoidAlgebra ℤ (Fin r → ℤ)) (m : ℕ) (hm : laurentDeg P ≤ m + 1) (k : ℕ)
    (hk : k < p) (i : Fin r → ℤ)
    (hi : i ∈ Fintype.piFinset fun _ : Fin r => Finset.Icc (-(m : ℤ)) m) :
    laurentCartier p (P ^ k * AddMonoidAlgebra.single i 1) =
      ∑ j ∈ Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(m : ℤ)) m),
        AddMonoidAlgebra.single j ((P ^ k).coeff (p • j - i))

/-- **Kohen's linear representation step modulo $p$.** Let $p$ be a prime, let $P$ be a Laurent
polynomial in $r$ variables with integer coefficients, and write $\deg P$ for the largest absolute
value of an exponent of a single variable in a monomial occurring in $P$ ($0$ if $P = 0$). Let $m$
be a natural number with $\deg P \le m + 1$. Write $T = [-m, m]^r \subseteq \mathbb{Z}^r$ and
$[x^e]F$ for the coefficient of $x^e$ in a Laurent polynomial $F$. Then for every natural number
$k < p$, every natural number $n$ and every $i \in T$,
$$[x^{-i}]P^{pn+k} \equiv \sum_{j \in T} [x^{pj - i}]P^k \cdot [x^{-j}]P^n \pmod{p}.$$

With Kohen's $a^n_i = [x^{-i}]P^n$, $\gamma(k) = (a^k_{i-pj})_{i,j \in T}$ and
$V(n) = (a^n_i)_{i \in T}$, this is the entrywise form of $\gamma(k) V(n) = V(pn + k)$ over
$\mathbb{F}_p$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 9 (`jis-2026-26.4.2-lem-9`). -/
public theorem_wanted coeff_pow_modEq_sum_gamma_mul_V {r p : ℕ} (hp : p.Prime)
    (P : AddMonoidAlgebra ℤ (Fin r → ℤ)) (m : ℕ) (hm : laurentDeg P ≤ m + 1) (k : ℕ)
    (hk : k < p) (n : ℕ) (i : Fin r → ℤ)
    (hi : i ∈ Fintype.piFinset fun _ : Fin r => Finset.Icc (-(m : ℤ)) m) :
    (P ^ (p * n + k)).coeff (-i) ≡
      ∑ j ∈ Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(m : ℤ)) m),
        (P ^ k).coeff (p • j - i) * (P ^ n).coeff (-j) [ZMOD p]

/-- **Powers of $\gamma(0)$ modulo $p$ stabilize at a matrix unit.** Let $p$ be a prime, let
$r, m \ge 0$ be natural numbers, let $T = \{-m, \dots, m\}^r \subseteq \mathbb{Z}^r$, and let
$\gamma(0)$ be the $T \times T$ matrix over $\mathbb{Z}/p\mathbb{Z}$ whose $(i, j)$ entry is $1$
if $i = p j$ and $0$ otherwise. Then there is $s \in \mathbb{N}$ such that for every $s' \ge s$,
$\gamma(0)^{s'}$ is the matrix whose $(0, 0)$ entry is $1$ and whose other entries are $0$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 11 (`jis-2026-26.4.2-lem-11`). -/
public theorem_wanted exists_gammaZero_pow_eq_single {p : ℕ} (hp : p.Prime) (r m : ℕ) :
    ∃ s : ℕ, ∀ s' ≥ s,
      (Matrix.of fun i j : ↥(Fintype.piFinset fun _ : Fin r => Finset.Icc (-(m : ℤ)) m) =>
        if (i : Fin r → ℤ) = p • (j : Fin r → ℤ) then (1 : ZMod p) else 0) ^ s' =
        Matrix.single ⟨0, by simp⟩ ⟨0, by simp⟩ 1

/-! ### Section 4: classification mod `p` -/

/-- **Divisibility of constant terms of powers is decided on a bounded prefix.** Let $p$ be a
prime, let $r$ and $d$ be natural numbers, and write $\operatorname{ct}[F]$ for the constant term
of a Laurent polynomial $F$ and $\deg F$ for the largest absolute value of an exponent of a single
variable in a monomial occurring in $F$ ($0$ if $F = 0$). There is a natural number $B$ such that
for every Laurent polynomial $P$ in $r$ variables with integer coefficients and $\deg P \le d$, if
$p$ divides $\operatorname{ct}[P^n]$ for some natural number $n$, then $p$ divides
$\operatorname{ct}[P^{n_0}]$ for some natural number $n_0 < B$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Proposition 12 (`jis-2026-26.4.2-prop-12`). -/
public theorem_wanted exists_bound_constantTerm_pow_dvd {p : ℕ} (hp : p.Prime) (r d : ℕ) :
    ∃ B : ℕ, ∀ P : AddMonoidAlgebra ℤ (Fin r → ℤ), laurentDeg P ≤ d →
      (∃ n, (p : ℤ) ∣ (P ^ n).coeff 0) → ∃ n₀ < B, (p : ℤ) ∣ (P ^ n₀).coeff 0

/-- **Density-one zeros of constant terms modulo $p$.** Let $p$ be a prime, let $P$ be a Laurent
polynomial in $r$ variables with integer coefficients, write $\operatorname{ct}[F]$ for the
constant term of a Laurent polynomial $F$, and suppose that $p$ divides $\operatorname{ct}[P^n]$
for some natural number $n$. Then for every Laurent polynomial $Q$ in $r$ variables with integer
coefficients, the set of natural numbers $n$ with $p \mid \operatorname{ct}[P^n Q]$ has natural
density $1$; for every natural number $L$ there is a natural number $i$ such that
$p \mid \operatorname{ct}[P^{i+t} Q]$ for all $t < L$; and either
$p \mid \operatorname{ct}[P^n Q]$ for every $n$, or the sequence of residues
$\operatorname{ct}[P^n Q] \bmod p$ in $\mathbb{Z}/p\mathbb{Z}$ is not uniformly recurrent.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Theorem 14 (`jis-2026-26.4.2-thm-14`). -/
public theorem_wanted constantTerm_zero_density_mod_prime {r p : ℕ} (hp : p.Prime)
    (P : AddMonoidAlgebra ℤ (Fin r → ℤ)) (hP : ∃ n, (p : ℤ) ∣ (P ^ n).coeff 0)
    (Q : AddMonoidAlgebra ℤ (Fin r → ℤ)) :
    ({n : ℕ | (p : ℤ) ∣ (P ^ n * Q).coeff 0} : Set ℕ).HasDensity 1 ∧
      (∀ L : ℕ, ∃ i, ∀ t < L, (p : ℤ) ∣ (P ^ (i + t) * Q).coeff 0) ∧
      ((∀ n, (p : ℤ) ∣ (P ^ n * Q).coeff 0) ∨
        ¬ IsUniformlyRecurrentSeq fun n => ((P ^ n * Q).coeff 0 : ZMod p))

/-- **Return to the initial coefficient vector modulo $p$.** Let $p$ be a prime, let
$m \in \mathbb{N}$, and let $P$ be a Laurent polynomial with integer coefficients in variables
$x_1, \dots, x_r$ with $\deg P \le m + 1$, where $\deg P$ is the largest absolute value of an
exponent of a single variable in a monomial occurring in $P$ (and $0$ if $P = 0$). Let
$T = \{-m, \dots, m\}^r$. Then there is $t_0 \in \mathbb{N}$ such that for every $n \in \mathbb{N}$
for which $p$ does not divide the constant term of $P^n$, there is $j < p^{t_0}$ such that for
every $i \in T$ the coefficient of $x^{-i}$ in $P^{p^{t_0} n + j}$ is congruent modulo $p$ to $1$
if $i = 0$ and to $0$ otherwise.

Equivalently, writing $V(n)$ for the vector of coefficients of $x^{-i}$ in $P^n$, $i \in T$,
reduced modulo $p$, the block $V(p^{t_0} n), \dots, V(p^{t_0} n + p^{t_0} - 1)$ contains $V(0)$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Proposition 15 (`jis-2026-26.4.2-prop-15`). -/
public theorem_wanted exists_sigma_pow_V_contains_V_zero {r p : ℕ} (hp : p.Prime)
    (P : AddMonoidAlgebra ℤ (Fin r → ℤ)) (m : ℕ) (hm : laurentDeg P ≤ m + 1) :
    ∃ t₀ : ℕ, ∀ n : ℕ, ¬ (p : ℤ) ∣ (P ^ n).coeff 0 → ∃ j < p ^ t₀,
      ∀ i ∈ Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(m : ℤ)) m),
        (P ^ (p ^ t₀ * n + j)).coeff (-i) ≡ if i = 0 then 1 else 0 [ZMOD p]

/-- **Linear recurrence of constant terms modulo $p$.** Let $p$ be a prime and let $P, Q$ be
Laurent polynomials with integer coefficients in $r$ variables; write $\operatorname{ct}[f]$ for
the constant term of $f$. Suppose $p \nmid \operatorname{ct}[P^n Q]$ for some $n \in \mathbb{N}$.
Then the sequence $u_n = \operatorname{ct}[P^n Q] \bmod p$ is linearly recurrent if and only if
$p \nmid \operatorname{ct}[P^n]$ for all $n \in \mathbb{N}$, and if $u$ is not linearly recurrent,
then the set of $n$ with $p \mid \operatorname{ct}[P^n Q]$ has natural density $1$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Theorem 16 (`jis-2026-26.4.2-thm-16`). -/
public theorem_wanted isLinearlyRecurrentSeq_constantTerm_mod_prime_iff {r p : ℕ}
    (hp : p.Prime) (P Q : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hQ : ∃ n, ¬ (p : ℤ) ∣ (P ^ n * Q).coeff 0) :
    (IsLinearlyRecurrentSeq (fun n => ((P ^ n * Q).coeff 0 : ZMod p)) ↔
        ∀ n, ¬ (p : ℤ) ∣ (P ^ n).coeff 0) ∧
      (¬ IsLinearlyRecurrentSeq (fun n => ((P ^ n * Q).coeff 0 : ZMod p)) →
        ({n : ℕ | (p : ℤ) ∣ (P ^ n * Q).coeff 0} : Set ℕ).HasDensity 1)

/-- **Linear recurrence of combinations of constant terms modulo $p$.** Let $p$ be a prime, let
$P, Q_1, \dots, Q_\ell$ be Laurent polynomials with integer coefficients in $r$ variables, let
$k_1, \dots, k_\ell \in \mathbb{N}$, and let $F \colon (\mathbb{Z}/p\mathbb{Z})^\ell \to X$ be a
map to a set $X$. Write $\operatorname{ct}[f]$ for the constant term of $f$ and, for
$n \in \mathbb{N}$, let
$b_n = F(\operatorname{ct}[P^{n+k_1} Q_1] \bmod p, \dots,
\operatorname{ct}[P^{n+k_\ell} Q_\ell] \bmod p)$.
Suppose $b_n \ne F(0, \dots, 0)$ for some $n$. Then $(b_n)$ is linearly recurrent if and only if
$p \nmid \operatorname{ct}[P^n]$ for all $n \in \mathbb{N}$, and if $p \mid \operatorname{ct}[P^n]$
for some $n$, then the set of $n$ with $b_n = F(0, \dots, 0)$ has natural density $1$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Corollary 17 (`jis-2026-26.4.2-cor-17`). -/
public theorem_wanted isLinearlyRecurrentSeq_combination_mod_prime_iff {r p ℓ : ℕ}
    {X : Type*} (hp : p.Prime) (P : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (F : (Fin ℓ → ZMod p) → X) (k : Fin ℓ → ℕ) (Q : Fin ℓ → AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hb : ∃ n, F (fun i => ((P ^ (n + k i) * Q i).coeff 0 : ZMod p)) ≠ F 0) :
    (IsLinearlyRecurrentSeq (fun n => F fun i => ((P ^ (n + k i) * Q i).coeff 0 : ZMod p)) ↔
        ∀ n, ¬ (p : ℤ) ∣ (P ^ n).coeff 0) ∧
      ((∃ n, (p : ℤ) ∣ (P ^ n).coeff 0) →
        ({n : ℕ | F (fun i => ((P ^ (n + k i) * Q i).coeff 0 : ZMod p)) = F 0} :
          Set ℕ).HasDensity 1)

/-- **Recurrence of constant-term sequences modulo a prime.** Let $p$ be a prime and let $P$ and
$Q$ be Laurent polynomials in $r$ variables with integer coefficients; write $\mathrm{ct}[F]$ for
the constant term of a Laurent polynomial $F$. If $p \nmid \mathrm{ct}[P^{n_0}]$ for some
$n_0 > 0$, then the sequence of residues $(\mathrm{ct}[P^n Q] \bmod p)_{n \ge 0}$ in
$\mathbb{Z}/p\mathbb{Z}$ is recurrent.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Proposition 19 (`jis-2026-26.4.2-prop-19`). -/
public theorem_wanted isRecurrentSeq_constantTerm_mod_prime {r p : ℕ} (hp : p.Prime)
    (P Q : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hP : ∃ n₀, 0 < n₀ ∧ ¬ (p : ℤ) ∣ (P ^ n₀).coeff 0) :
    IsRecurrentSeq fun n => ((P ^ n * Q).coeff 0 : ZMod p)

/-! ### Section 5: prime powers

`P̃` is any integer Laurent polynomial with `P^{p^{a-1}}(x) ≡ P̃(x^{p^ℓ}) (mod p^a)`
coefficientwise; the substitution `x ↦ x^q` is `AddMonoidAlgebra.mapDomain (q • ·)`. The paper
takes `ℓ` as large as possible; the statements below hold for every such pair `(ℓ, P̃)`. -/

/-- **Divisibility of constant terms of powers of $P$ and $\tilde P$.** Let $p$ be a prime, let
$a \ge 1$ and $\ell$ be natural numbers, and let $P$ and $\tilde P$ be Laurent polynomials in $r$
variables with integer coefficients such that $P^{p^{a-1}} \equiv \tilde P(x^{p^\ell}) \pmod{p^a}$
coefficientwise, where $\tilde P(x^q)$ is obtained from $\tilde P$ by replacing each monomial
$x^e$ with $x^{qe}$. Write $\operatorname{ct}[F]$ for the constant term of a Laurent polynomial
$F$. Then $p$ divides $\operatorname{ct}[P^{n_0}]$ for some natural number $n_0$ if and only if
$p$ divides $\operatorname{ct}[\tilde P^{n_1}]$ for some natural number $n_1$; moreover, for every
natural number $n_0$ with $p \mid \operatorname{ct}[P^{n_0}]$, also
$p \mid \operatorname{ct}[\tilde P^{n_0}]$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 22 (`jis-2026-26.4.2-lem-22`). -/
public theorem_wanted exists_constantTerm_pow_dvd_iff_tilde {r p a ℓ : ℕ} (hp : p.Prime)
    (ha : 0 < a) (P Pt : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hPt : ∀ j, (P ^ (p ^ (a - 1))).coeff j ≡
      (AddMonoidAlgebra.mapDomain (fun j => p ^ ℓ • j) Pt).coeff j [ZMOD (p : ℤ) ^ a]) :
    ((∃ n₀, (p : ℤ) ∣ (P ^ n₀).coeff 0) ↔ ∃ n₁, (p : ℤ) ∣ (Pt ^ n₁).coeff 0) ∧
      ∀ n₀, (p : ℤ) ∣ (P ^ n₀).coeff 0 → (p : ℤ) ∣ (Pt ^ n₀).coeff 0

/-- **Passing from $P$ to $\tilde P$ modulo $p^a$.** Let $p$ be a prime, let $a \ge 1$ and $\ell$
be natural numbers, and let $P$ and $\tilde P$ be Laurent polynomials in $r$ variables with
integer coefficients such that $P^{p^{a-1}} \equiv \tilde P(x^{p^\ell}) \pmod{p^a}$
coefficientwise, where $\tilde P(x^q)$ is obtained from $\tilde P$ by replacing each monomial
$x^e$ with $x^{qe}$. Write $\operatorname{ct}[F]$ for the constant term of a Laurent polynomial
$F$ and $\Lambda_q$ for Kohen's operator, which keeps the terms whose exponents are all divisible
by $q$ and replaces $x^{qj}$ by $x^j$. Then for every Laurent polynomial $Q$ in $r$ variables
with integer coefficients and all natural numbers $n$ and $k$,
$\operatorname{ct}[P^{p^{a-1} n + k} Q] \equiv
\operatorname{ct}[\tilde P^n \Lambda_{p^\ell}(P^k Q)] \pmod{p^a}$.

The statement holds for every natural number $k$; the paper restricts to $k < p^{a-1}$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Proposition 23 (`jis-2026-26.4.2-prop-23`). -/
public theorem_wanted constantTerm_pow_mul_modEq_tilde {r p a ℓ : ℕ} (hp : p.Prime)
    (ha : 0 < a) (P Pt : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hPt : ∀ j, (P ^ (p ^ (a - 1))).coeff j ≡
      (AddMonoidAlgebra.mapDomain (fun j => p ^ ℓ • j) Pt).coeff j [ZMOD (p : ℤ) ^ a])
    (Q : AddMonoidAlgebra ℤ (Fin r → ℤ)) (n k : ℕ) :
    (P ^ (p ^ (a - 1) * n + k) * Q).coeff 0 ≡
      (Pt ^ n * laurentCartier (p ^ ℓ) (P ^ k * Q)).coeff 0 [ZMOD (p : ℤ) ^ a]

/-- **Rowland–Zeilberger congruence modulo $p^a$.** Let $p$ be a prime, let $a$ be a natural
number, and let $\tilde P$ be a Laurent polynomial in $r$ variables with integer coefficients
such that $\tilde P^p \equiv \tilde P(x^p) \pmod{p^a}$ coefficientwise, where $\tilde P(x^p)$
is obtained from $\tilde P$ by replacing each monomial $x^e$ with $x^{pe}$. Write
$\operatorname{ct}[F]$ for the constant term of a Laurent polynomial $F$ and $\Lambda_p$ for
Kohen's operator, which keeps the terms whose exponents are all divisible by $p$ and replaces
$x^{pj}$ by $x^j$. Then for every Laurent polynomial $Q$ in $r$ variables with integer
coefficients and all natural numbers $n$ and $k$,
$\operatorname{ct}[\tilde P^{pn+k} Q] \equiv
\operatorname{ct}[\tilde P^n \Lambda_p(\tilde P^k Q)] \pmod{p^a}$.

The statement holds for every natural number $k$; the paper states it for $k \in \mathbb{F}_p$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 24 (`jis-2026-26.4.2-lem-24`). -/
public theorem_wanted constantTerm_tilde_pow_mul_modEq_laurentCartier {r p a : ℕ}
    (hp : p.Prime) (Pt : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hPt : ∀ j, (Pt ^ p).coeff j ≡
      (AddMonoidAlgebra.mapDomain (fun j => p • j) Pt).coeff j [ZMOD (p : ℤ) ^ a])
    (Q : AddMonoidAlgebra ℤ (Fin r → ℤ)) (n k : ℕ) :
    (Pt ^ (p * n + k) * Q).coeff 0 ≡ (Pt ^ n * laurentCartier p (Pt ^ k * Q)).coeff 0
      [ZMOD (p : ℤ) ^ a]

/-- **Degree bound for the Rowland–Zeilberger states mod $p^a$.** Let $p$ be a prime, let $a$
be a natural number, and let $\tilde P$ and $Q_0$ be Laurent polynomials in $r$ variables with
coefficients in $\mathbb{Z}/p^a\mathbb{Z}$. Write $\deg F$ for the largest absolute value of an
exponent of a variable occurring in $F$, and $\Lambda_p$ for the operator that keeps the terms
whose exponents are all multiples of $p$ and substitutes $x_s^p \mapsto x_s$. For every finite
list $k_1, \dots, k_n$ of natural numbers with each $k_t < p$, starting from $Q_0$ and applying
$Q \mapsto \Lambda_p(\tilde P^{k_t} Q)$ for $t = 1, \dots, n$ in turn gives a Laurent polynomial
of degree at most $\max(\deg \tilde P - 1, \deg Q_0)$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 25 (`jis-2026-26.4.2-lem-25`). -/
public theorem_wanted laurentDeg_foldl_laurentCartier_le_zmod {r p a : ℕ} (hp : p.Prime)
    (Pt Q₀ : AddMonoidAlgebra (ZMod (p ^ a)) (Fin r → ℤ)) (ks : List ℕ)
    (hks : ∀ k ∈ ks, k < p) :
    laurentDeg (ks.foldl (fun R k => laurentCartier p (Pt ^ k * R)) Q₀) ≤
      max (laurentDeg Pt - 1) (laurentDeg Q₀)

/-- **Kohen's linear representation step modulo $p^a$.** Let $p$ be a prime, let $a$ be a natural
number, and let $\tilde P$ be a Laurent polynomial in $r$ variables with integer coefficients such
that $\tilde P^p \equiv \tilde P(x^p) \pmod{p^a}$ coefficientwise, where $\tilde P(x^p)$ is
obtained from $\tilde P$ by replacing each monomial $x^e$ with $x^{pe}$. Write $\deg \tilde P$ for
the largest absolute value of an exponent of a single variable in a monomial occurring in
$\tilde P$ ($0$ if $\tilde P = 0$). Let $m$ be a natural number with $\deg \tilde P \le m + 1$,
and write $T = [-m, m]^r \subseteq \mathbb{Z}^r$ and $[x^e]F$ for the coefficient of $x^e$ in a
Laurent polynomial $F$. Then for every natural number $k < p$, every natural number $n$ and every
$i \in T$,
$$
[x^{-i}]\tilde P^{pn+k} \equiv
\sum_{j \in T} [x^{pj - i}]\tilde P^k \cdot [x^{-j}]\tilde P^n \pmod{p^a}.
$$

This is the entrywise form of Kohen's step $\tilde\gamma(k) \tilde V(n) = \tilde V(pn + k)$ over
$\mathbb{Z}/p^a\mathbb{Z}$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 28 (`jis-2026-26.4.2-lem-28`). -/
public theorem_wanted coeff_tilde_pow_modEq_sum_gamma_mul_V {r p a : ℕ} (hp : p.Prime)
    (Pt : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hPt : ∀ j, (Pt ^ p).coeff j ≡
      (AddMonoidAlgebra.mapDomain (fun j => p • j) Pt).coeff j [ZMOD (p : ℤ) ^ a])
    (m : ℕ) (hm : laurentDeg Pt ≤ m + 1) (k : ℕ) (hk : k < p) (n : ℕ) (i : Fin r → ℤ)
    (hi : i ∈ Fintype.piFinset fun _ : Fin r => Finset.Icc (-(m : ℤ)) m) :
    (Pt ^ (p * n + k)).coeff (-i) ≡
      ∑ j ∈ Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(m : ℤ)) m),
        (Pt ^ k).coeff (p • j - i) * (Pt ^ n).coeff (-j) [ZMOD (p : ℤ) ^ a]

/-- **Powers of $\tilde\gamma(0)$ modulo $p^a$ stabilize at a matrix unit.** Let $p$ be a prime,
let $a \ge 1$, $r$ and $m$ be natural numbers, let $T = \{-m, \dots, m\}^r \subseteq \mathbb{Z}^r$,
and let $\tilde\gamma(0)$ be the $T \times T$ matrix over $\mathbb{Z}/p^a\mathbb{Z}$ whose
$(i, j)$ entry is $1$ if $i = p j$ and $0$ otherwise. Then there is $s \in \mathbb{N}$ such that for
every $s' \ge s$, $\tilde\gamma(0)^{s'}$ is the matrix whose $(0, 0)$ entry is $1$ and whose other
entries are $0$.

Kohen's Lemma 30 prints $\tilde\gamma(0)^s$; as in Lemma 11, it is read for every exponent
$s' \ge s$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 30 (`jis-2026-26.4.2-lem-30`). -/
public theorem_wanted exists_gammaZero_pow_eq_single_zmod {p : ℕ} (hp : p.Prime)
    (a : ℕ) (ha : 0 < a) (r m : ℕ) :
    ∃ s : ℕ, ∀ s' ≥ s,
      (Matrix.of fun i j : ↥(Fintype.piFinset fun _ : Fin r => Finset.Icc (-(m : ℤ)) m) =>
        if (i : Fin r → ℤ) = p • (j : Fin r → ℤ) then (1 : ZMod (p ^ a)) else 0) ^ s' =
        Matrix.single ⟨0, by simp⟩ ⟨0, by simp⟩ 1

/-- **Density-one zeros of constant terms modulo $p^a$.** Let $p$ be a prime, let $a$ be a natural
number, and let $\tilde P$ be a Laurent polynomial in $r$ variables with integer coefficients such
that $\tilde P^p \equiv \tilde P(x^p) \pmod{p^a}$ coefficientwise, where $\tilde P(x^p)$ is
obtained from $\tilde P$ by replacing each monomial $x^e$ with $x^{pe}$. Write
$\operatorname{ct}[F]$ for the constant term of a Laurent polynomial $F$, and suppose that $p$
divides $\operatorname{ct}[\tilde P^{n_0}]$ for some natural number $n_0$. Then for every
Laurent polynomial $Q$ in $r$ variables with integer coefficients, the set of natural numbers $n$
such that $p^a$ divides $\operatorname{ct}[\tilde P^n Q]$ has natural density $1$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 31 (`jis-2026-26.4.2-lem-31`). -/
public theorem_wanted constantTerm_tilde_zero_density {r p a : ℕ} (hp : p.Prime)
    (Pt : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hPt : ∀ j, (Pt ^ p).coeff j ≡
      (AddMonoidAlgebra.mapDomain (fun j => p • j) Pt).coeff j [ZMOD (p : ℤ) ^ a])
    (h : ∃ n₀, (p : ℤ) ∣ (Pt ^ n₀).coeff 0) (Q : AddMonoidAlgebra ℤ (Fin r → ℤ)) :
    ({n : ℕ | (p : ℤ) ^ a ∣ (Pt ^ n * Q).coeff 0} : Set ℕ).HasDensity 1

/-- **Return to the initial coefficient vector modulo $p^a$.** Let $p$ be a prime, let
$a, m \in \mathbb{N}$, and let $\tilde P$ be a Laurent polynomial with integer coefficients in
variables $x_1, \dots, x_r$ such that for every $j \in \mathbb{Z}^r$ the coefficients of $x^j$ in
$\tilde P(x_1, \dots, x_r)^p$ and in $\tilde P(x_1^p, \dots, x_r^p)$ are congruent modulo $p^a$.
Suppose $\deg \tilde P \le m + 1$, where $\deg \tilde P$ is the largest absolute value of an
exponent of a single variable in a monomial occurring in $\tilde P$ (and $0$ if $\tilde P = 0$),
and let $T = \{-m, \dots, m\}^r$. Then there is $t_0 \in \mathbb{N}$ such that for every
$n \in \mathbb{N}$ for which $p$ does not divide the constant term of $\tilde P^n$, there is
$j < p^{t_0}$ such that for every $i \in T$ the coefficient of $x^{-i}$ in
$\tilde P^{p^{t_0} n + j}$ is congruent modulo $p^a$ to $1$ if $i = 0$ and to $0$ otherwise.

Equivalently, writing $\tilde V(n)$ for the vector of coefficients of $x^{-i}$ in $\tilde P^n$,
$i \in T$, reduced modulo $p^a$, some $\tilde V(p^{t_0} n + j)$ with $j < p^{t_0}$ equals
$\tilde V(0)$. This is the analogue modulo $p^a$ of Proposition 15.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Proposition 32 (`jis-2026-26.4.2-prop-32`). -/
public theorem_wanted exists_sigma_pow_V_contains_V_zero_tilde {r p a : ℕ} (hp : p.Prime)
    (Pt : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hPt : ∀ j, (Pt ^ p).coeff j ≡
      (AddMonoidAlgebra.mapDomain (fun j => p • j) Pt).coeff j [ZMOD (p : ℤ) ^ a])
    (m : ℕ) (hm : laurentDeg Pt ≤ m + 1) :
    ∃ t₀ : ℕ, ∀ n : ℕ, ¬ (p : ℤ) ∣ (Pt ^ n).coeff 0 → ∃ j < p ^ t₀,
      ∀ i ∈ Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(m : ℤ)) m),
        (Pt ^ (p ^ t₀ * n + j)).coeff (-i) ≡ if i = 0 then 1 else 0 [ZMOD (p : ℤ) ^ a]

/-- **Linear recurrence of constant terms modulo $p^a$.** Let $p$ be a prime, let $a \ge 1$, and
let $P, Q$ be Laurent polynomials with integer coefficients in $r$ variables; write
$\operatorname{ct}[f]$ for the constant term of $f$. Suppose $p^a \nmid \operatorname{ct}[P^n Q]$
for some $n \in \mathbb{N}$. Then the sequence $u_n = \operatorname{ct}[P^n Q] \bmod p^a$ is
linearly recurrent if and only if $p \nmid \operatorname{ct}[P^n]$ for all $n \in \mathbb{N}$, and
if $u$ is not linearly recurrent, then the set of $n$ with $p^a \mid \operatorname{ct}[P^n Q]$ has
natural density $1$.

In particular, as long as $u$ is not identically $0$, whether it is linearly recurrent does not
depend on $Q$ or $a$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Theorem 33 (`jis-2026-26.4.2-thm-33`). -/
public theorem_wanted isLinearlyRecurrentSeq_constantTerm_mod_primePow_iff {r p a : ℕ}
    (hp : p.Prime) (ha : 0 < a) (P Q : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hQ : ∃ n, ¬ (p : ℤ) ^ a ∣ (P ^ n * Q).coeff 0) :
    (IsLinearlyRecurrentSeq (fun n => ((P ^ n * Q).coeff 0 : ZMod (p ^ a))) ↔
        ∀ n, ¬ (p : ℤ) ∣ (P ^ n).coeff 0) ∧
      (¬ IsLinearlyRecurrentSeq (fun n => ((P ^ n * Q).coeff 0 : ZMod (p ^ a))) →
        ({n : ℕ | (p : ℤ) ^ a ∣ (P ^ n * Q).coeff 0} : Set ℕ).HasDensity 1)

/-- **Linear recurrence of combinations of constant terms modulo $p^a$.** Let $p$ be a prime,
let $a \ge 1$, let $P, Q_1, \dots, Q_\ell$ be Laurent polynomials with integer coefficients in
$r$ variables, let $k_1, \dots, k_\ell \in \mathbb{N}$, and let
$F \colon (\mathbb{Z}/p^a\mathbb{Z})^\ell \to X$ be a map to a set $X$. Write
$\operatorname{ct}[f]$ for the constant term of $f$ and, for $n \in \mathbb{N}$, let
$b_n = F(\operatorname{ct}[P^{n+k_1} Q_1] \bmod p^a, \dots,
\operatorname{ct}[P^{n+k_\ell} Q_\ell] \bmod p^a)$. Suppose $b_n \ne F(0, \dots, 0)$ for some $n$.
Then $(b_n)$ is linearly recurrent if and only if $p \nmid \operatorname{ct}[P^n]$ for all
$n \in \mathbb{N}$, and if $p \mid \operatorname{ct}[P^n]$ for some $n$, then the set of $n$ with
$b_n = F(0, \dots, 0)$ has natural density $1$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Corollary 34 (`jis-2026-26.4.2-cor-34`). -/
public theorem_wanted isLinearlyRecurrentSeq_combination_mod_primePow_iff {r p a ℓ : ℕ}
    {X : Type*} (hp : p.Prime) (ha : 0 < a) (P : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (F : (Fin ℓ → ZMod (p ^ a)) → X) (k : Fin ℓ → ℕ)
    (Q : Fin ℓ → AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hb : ∃ n, F (fun i => ((P ^ (n + k i) * Q i).coeff 0 : ZMod (p ^ a))) ≠ F 0) :
    (IsLinearlyRecurrentSeq
        (fun n => F fun i => ((P ^ (n + k i) * Q i).coeff 0 : ZMod (p ^ a))) ↔
        ∀ n, ¬ (p : ℤ) ∣ (P ^ n).coeff 0) ∧
      ((∃ n, (p : ℤ) ∣ (P ^ n).coeff 0) →
        ({n : ℕ | F (fun i => ((P ^ (n + k i) * Q i).coeff 0 : ZMod (p ^ a))) = F 0} :
          Set ℕ).HasDensity 1)

/-- **Recurrence of constant-term sequences modulo a prime power.** Let $p$ be a prime, let
$a \ge 1$, and let $P$ and $Q$ be Laurent polynomials in $r$ variables with integer coefficients;
write $\mathrm{ct}[F]$ for the constant term of a Laurent polynomial $F$. If
$p \nmid \mathrm{ct}[P^{n_0}]$ for some $n_0 > 0$, then the sequence of residues
$(\mathrm{ct}[P^n Q] \bmod p^a)_{n \ge 0}$ in $\mathbb{Z}/p^a\mathbb{Z}$ is recurrent.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Proposition 35 (`jis-2026-26.4.2-prop-35`). -/
public theorem_wanted isRecurrentSeq_constantTerm_mod_primePow {r p a : ℕ} (hp : p.Prime)
    (ha : 0 < a) (P Q : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hP : ∃ n₀, 0 < n₀ ∧ ¬ (p : ℤ) ∣ (P ^ n₀).coeff 0) :
    IsRecurrentSeq fun n => ((P ^ n * Q).coeff 0 : ZMod (p ^ a))

end

end MetaMathlibExt
