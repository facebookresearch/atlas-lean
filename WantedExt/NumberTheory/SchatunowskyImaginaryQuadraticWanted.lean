/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.Data.Nat.Nth
public import MathlibExt.NumberTheory.Schatunowsky
public import MathlibExt.NumberTheory.SchatunowskyImaginaryQuadratic

/-!
# Bertrand postulates and Schatunowsky-type theorems in ℕ and Gaussian and Eisenstein integers

Statement-only targets from Hirofumi Nakai, Ken Sasaki and Konoka Yoshida,
*Schatunowsky-type Theorems for Imaginary Quadratic Integer Rings of Class Number One*,
INTEGERS 26 (2026), Article A110. The Eisenstein integers are the ring of integers of
`CyclotomicField 3 ℚ`, with the field norm `Algebra.norm ℚ`.

For the paper's Sections 3-5 an imaginary quadratic field is a number field `K` with
`Module.finrank ℚ K = 2` and `IsTotallyComplex K`; "`m` is one of the integers of Proposition 1"
is `NumberField.classNumber K = 1`, and the Gaussian (`m = -1`) and Eisenstein (`m = -3`) cases
are the fields with `NumberField.discr K = -4` and `-3`. The norm `N(α)` is
`Ideal.absNorm (Ideal.span {α})`, `Ω(β)` is the number of prime ideal factors of `(β)` with
multiplicity, and `gcd(α, β) = 1` is `IsCoprime α β`. The paper's norm-ordered primes `π_n`
(Definition 1: one prime from each conjugate pair) and primorials `π_n#` (Definition 2) enter
only through `N(π_n)` and `N(π_n#)` and through divisibility by `π_n#`; since the prime ideals
of norm at most `N(π_n)` are exactly those lying over the first `n` rational primes in this
order, `(π_n#)` is their product, `N(π_n#)` is the product of their norms, and `π_n# ∣ α`
says that `α` lies in each of them.
-/

open NumberField

namespace MetaMathlibExt

@[expose] public section

/-- **Bertrand's postulate for Gaussian integers.** Let $N(a + bi) = a^2 + b^2$ be the norm on the
Gaussian integers $\mathbb{Z}[i]$. For every prime element $\pi$ of $\mathbb{Z}[i]$ with
$N(\pi) \ne 2$ (that is, $\pi$ is not an associate of $1 + i$) there is a prime element $\rho$
of $\mathbb{Z}[i]$ with $N(\pi) < N(\rho) \le 2N(\pi)$.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Lemma 2
(`integers-2026-A110-lem-2`). -/
public theorem_wanted gaussianInt_exists_prime_norm_between {π : GaussianInt} (hπ : Prime π)
    (hπ₂ : π.norm ≠ 2) :
    ∃ ρ : GaussianInt, Prime ρ ∧ π.norm < ρ.norm ∧ ρ.norm ≤ 2 * π.norm

/-- **Bertrand's postulate for Eisenstein integers.** Let $\mathcal{O}$ be the ring of integers of
the cyclotomic field $\mathbb{Q}(\zeta_3)$, and let $N$ be the field norm from $\mathbb{Q}(\zeta_3)$
to $\mathbb{Q}$. For every prime element $\pi$ of $\mathcal{O}$ there is a prime element $\rho$ of
$\mathcal{O}$ with $N(\pi) < N(\rho) \le 2N(\pi)$.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Lemma 3
(`integers-2026-A110-lem-3`). -/
public theorem_wanted eisenstein_exists_prime_norm_between
    {π : 𝓞 (CyclotomicField 3 ℚ)} (hπ : Prime π) :
    ∃ ρ : 𝓞 (CyclotomicField 3 ℚ), Prime ρ ∧
      Algebra.norm ℚ (π : CyclotomicField 3 ℚ) < Algebra.norm ℚ (ρ : CyclotomicField 3 ℚ) ∧
      Algebra.norm ℚ (ρ : CyclotomicField 3 ℚ) ≤ 2 * Algebra.norm ℚ (π : CyclotomicField 3 ℚ)

/-- **Iwata's generalization of Schatunowsky's theorem.** For every natural number $\ell$, there
are only finitely many natural numbers $a$ such that every natural number $b$ with $1 < b < a$
and $\gcd(a, b) = 1$ satisfies $\Omega(b) \le \ell$, where $\Omega(b)$ is the number of prime
factors of $b$ counted with multiplicity.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Theorem 2,
quoting Iwata (`integers-2026-A110-thm-2`). `ℓ = 0` is included (trivially finite). -/
public theorem_wanted nat_iwata_finite (ℓ : ℕ) :
    {a : ℕ | ∀ b : ℕ, 1 < b → b < a → Nat.Coprime a b →
      ArithmeticFunction.cardFactors b ≤ ℓ}.Finite

/-- **Dalezman's Schatunowsky theorem for the Gaussian integers.** Let $N(a + bi) = a^2 + b^2$ be
the norm on the Gaussian integers $\mathbb{Z}[i]$, and let $S$ be the set of
$\alpha \in \mathbb{Z}[i]$ such that every $\beta \in \mathbb{Z}[i]$ coprime to $\alpha$ with
$1 < N(\beta) < N(\alpha)$ is a Gaussian prime. Then $5 + 5i \in S$, every element of $S$ has
norm at most $50$, and every element of $S$ of norm $50$ is an associate of $5 + 5i$.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Theorem 3,
quoting Dalezman (`integers-2026-A110-thm-3`). -/
public theorem_wanted gaussianInt_schatunowsky_max_norm_five_add_five_i :
    let S : Set GaussianInt :=
      {α | ∀ β : GaussianInt, 1 < β.norm → β.norm < α.norm → IsCoprime α β → Prime β}
    (⟨5, 5⟩ : GaussianInt) ∈ S ∧ (∀ α ∈ S, α.norm ≤ 50) ∧
      ∀ α ∈ S, α.norm = 50 → Associated α ⟨5, 5⟩


/-- **Unit groups of imaginary quadratic fields.** Let $K$ be an imaginary quadratic field with
discriminant $d_K$. The unit group of its ring of integers $\mathcal{O}_K$ is cyclic, of order
$4$ if $d_K = -4$, of order $6$ if $d_K = -3$, and of order $2$ otherwise.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Proposition 2
(`integers-2026-A110-prop-2`). -/
public theorem_wanted imagQuadratic_units_isCyclic_card {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] :
    IsCyclic (𝓞 K)ˣ ∧
      Nat.card (𝓞 K)ˣ = if discr K = -4 then 4 else if discr K = -3 then 6 else 2

/-- **Ratios of consecutive prime ideal norms in an imaginary quadratic field tend to $1$.** Let
$K$ be an imaginary quadratic field, that is, a totally complex number field of degree $2$ over
$\mathbb{Q}$, with ring of integers $\mathcal{O}_K$. For $m \ge 1$ let $r_m$ be the least natural
number $x$ such that at least $m$ nonzero prime ideals of $\mathcal{O}_K$ have absolute norm at
most $x$; this is the $m$-th smallest norm of a nonzero prime ideal, counted with multiplicity.
Let $N(\pi_m)$ be the $m$-th smallest element of the set of absolute norms of nonzero prime
ideals of $\mathcal{O}_K$. Then the real quotients satisfy $r_{m+1}/r_m \to 1$ and
$N(\pi_{m+1})/N(\pi_m) \to 1$ as $m \to \infty$.

The sequence $r_m$ is the paper's $N(\rho_m)$, where $\rho_m$ runs over all primes up to units
(Definition 1). The statement holds for every imaginary quadratic field: the norms do not need
the paper's class-number-one assumption.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Lemma 1
(`integers-2026-A110-lem-1`). -/
public theorem_wanted tendsto_quadPrimeNorm_succ_div {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] :
    Filter.Tendsto (fun n : ℕ =>
        ((sInf {x : ℕ | n + 2 ≤
            Nat.card {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P ≤ x}} : ℕ) : ℝ) /
          ((sInf {x : ℕ | n + 1 ≤
            Nat.card {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P ≤ x}} : ℕ) : ℝ))
        Filter.atTop (nhds 1) ∧
      Filter.Tendsto (fun n : ℕ => (quadPrimeNorm K (n + 2) : ℝ) / quadPrimeNorm K (n + 1))
        Filter.atTop (nhds 1)

/-- **Prime norm powers eventually fall below the quadratic primorial.** Let $K$ be an imaginary
quadratic field. Put $N(\pi_0) = 1$ and, for $n \ge 1$, let $N(\pi_n)$ be the $n$-th smallest
number that is the norm of a nonzero prime ideal of $\mathcal{O}_K$; let $N(\pi_n\#)$ be the
product of the norms of the nonzero prime ideals of $\mathcal{O}_K$ of norm at most $N(\pi_n)$.
For every natural number $\ell$ there is $n_0$ such that $N(\pi_{n+1})^{\ell+1} < N(\pi_n\#)$
for all $n \ge n_0$.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Proposition 4
(`integers-2026-A110-prop-4`). -/
public theorem_wanted exists_quadPrimeNorm_pow_lt_quadPrimorialNorm {K : Type*} [Field K]
    [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (ℓ : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, quadPrimeNorm K (n + 1) ^ (ℓ + 1) < quadPrimorialNorm K n

/-- **Explicit primorial thresholds for the Gaussian integers.** Let $K$ be a number field of
discriminant $-4$ (so $K \cong \mathbb{Q}(i)$). Put $N(\pi_0) = 1$ and, for $n \ge 1$, let
$N(\pi_n)$ be the $n$-th smallest number that is the norm of a nonzero prime ideal of
$\mathcal{O}_K$; let $N(\pi_n\#)$ be the product of the norms of the nonzero prime ideals of
$\mathcal{O}_K$ of norm at most $N(\pi_n)$. For each pair $(\ell, n_\ell)$ among $(1, 3)$,
$(2, 4)$, $(3, 5)$, $(4, 5)$, $(5, 6)$, $(6, 7)$, $(7, 7)$ and every $n \ge n_\ell$,
$N(\pi_{n+1})^{\ell+1} < N(\pi_n\#)$.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Proposition 5
(`integers-2026-A110-prop-5`). -/
public theorem_wanted gaussian_quadPrimeNorm_pow_lt_quadPrimorialNorm {K : Type*} [Field K]
    [NumberField K]
    (hK : discr K = -4) :
    ∀ p ∈ [(1, 3), (2, 4), (3, 5), (4, 5), (5, 6), (6, 7), (7, 7)], ∀ n ≥ p.2,
      quadPrimeNorm K (n + 1) ^ (p.1 + 1) < quadPrimorialNorm K n

/-- **Explicit primorial thresholds for the Eisenstein integers.** Let $K$ be a number field of
discriminant $-3$ (so $K \cong \mathbb{Q}(\sqrt{-3})$). Put $N(\pi_0) = 1$ and, for $n \ge 1$, let
$N(\pi_n)$ be the $n$-th smallest number that is the norm of a nonzero prime ideal of
$\mathcal{O}_K$; let $N(\pi_n\#)$ be the product of the norms of the nonzero prime ideals of
$\mathcal{O}_K$ of norm at most $N(\pi_n)$. For each pair $(\ell, n_\ell)$ among $(1, 3)$,
$(2, 4)$, $(3, 5)$, $(4, 5)$, $(5, 6)$, $(6, 7)$, $(7, 8)$ and every $n \ge n_\ell$,
$N(\pi_{n+1})^{\ell+1} < N(\pi_n\#)$.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Proposition 6
(`integers-2026-A110-prop-6`). -/
public theorem_wanted eisenstein_quadPrimeNorm_pow_lt_quadPrimorialNorm {K : Type*} [Field K]
    [NumberField K]
    (hK : discr K = -3) :
    ∀ p ∈ [(1, 3), (2, 4), (3, 5), (4, 5), (5, 6), (6, 7), (7, 8)], ∀ n ≥ p.2,
      quadPrimeNorm K (n + 1) ^ (p.1 + 1) < quadPrimorialNorm K n

/-- **The first three Schatunowsky sets of the Gaussian integers.** Let $K$ be a number field
of discriminant $-4$ (so $K \cong \mathbb{Q}(i)$). For $\alpha \in \mathcal{O}_K$ let $N(\alpha)$
be the absolute norm of the ideal $(\alpha)$, and let $Q_\ell$ be the set of
$\alpha \in \mathcal{O}_K$ with $N(\alpha) > 1$ such that every $\beta \in \mathcal{O}_K$ coprime
to $\alpha$ with $1 < N(\beta) < N(\alpha)$ has at most $\ell$ prime ideal factors, counted with
multiplicity. Below, $\gamma$ ranges over $\mathcal{O}_K$ and $\pi$ over the elements of norm $2$.
Then $Q_1$ consists of the $\alpha$ with $1 < N(\alpha) \le 4$, the products $\gamma\pi$ with
$3 \le N(\gamma) \le 12$, and the associates of $5\pi$. The set $Q_2$ consists of the $\alpha$
with $1 < N(\alpha) \le 8$, the $\gamma\pi$ with $5 \le N(\gamma) \le 62$, the $5\gamma\pi$ with
$3 \le N(\gamma) \le 14$, and the $15\gamma\pi$ with $2 \le N(\gamma) \le 4$. The set $Q_3$
consists of the $\alpha$ with $1 < N(\alpha) \le 16$, the $\gamma\pi$ with
$9 \le N(\gamma) \le 312$, the $5\gamma\pi$ with $13 \le N(\gamma) \le 131$, the $15\gamma\pi$
with $15 \le N(\gamma) \le 63$, and the associates of $195\pi$. Moreover, the elements of largest
norm are unique up to units: for $(c, \ell) = (5, 1), (30, 2), (195, 3)$ there is a $\pi$ of
norm $2$ with $c\pi \in Q_\ell$ such that every $\alpha \in Q_\ell$ has $N(\alpha) \le N(c\pi)$,
with $\alpha$ an associate of $c\pi$ in case of equality.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Corollary 1
(`integers-2026-A110-cor-1`). -/
public theorem_wanted gaussian_quadSchatunowskySet_eq {K : Type*} [Field K] [NumberField K]
    (hK : discr K = -4) :
    quadSchatunowskySet K 1 =
        {α | (1 < Ideal.absNorm (Ideal.span {α}) ∧ Ideal.absNorm (Ideal.span {α}) ≤ 4) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ 3 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 12 ∧ α = γ * π) ∨
          (∃ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ Associated α (5 * π))} ∧
      quadSchatunowskySet K 2 =
        {α | (1 < Ideal.absNorm (Ideal.span {α}) ∧ Ideal.absNorm (Ideal.span {α}) ≤ 8) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ 5 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 62 ∧ α = γ * π) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ 3 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 14 ∧ α = γ * (5 * π)) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ 2 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 4 ∧ α = γ * (15 * π))} ∧
      quadSchatunowskySet K 3 =
        {α | (1 < Ideal.absNorm (Ideal.span {α}) ∧ Ideal.absNorm (Ideal.span {α}) ≤ 16) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ 9 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 312 ∧ α = γ * π) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ 13 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 131 ∧ α = γ * (5 * π)) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ 15 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 63 ∧ α = γ * (15 * π)) ∨
          (∃ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ Associated α (195 * π))} ∧
      (∃ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ (5 * π) ∈ quadSchatunowskySet K 1 ∧
          ∀ α ∈ quadSchatunowskySet K 1,
              Ideal.absNorm (Ideal.span {α}) ≤ Ideal.absNorm (Ideal.span {(5 * π)}) ∧
            (Ideal.absNorm (Ideal.span {α}) = Ideal.absNorm (Ideal.span {(5 * π)}) →
                Associated α (5 * π))) ∧
      (∃ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ (30 * π) ∈ quadSchatunowskySet K 2 ∧
          ∀ α ∈ quadSchatunowskySet K 2,
              Ideal.absNorm (Ideal.span {α}) ≤ Ideal.absNorm (Ideal.span {(30 * π)}) ∧
            (Ideal.absNorm (Ideal.span {α}) = Ideal.absNorm (Ideal.span {(30 * π)}) →
                Associated α (30 * π))) ∧
      (∃ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ (195 * π) ∈ quadSchatunowskySet K 3 ∧
          ∀ α ∈ quadSchatunowskySet K 3,
              Ideal.absNorm (Ideal.span {α}) ≤ Ideal.absNorm (Ideal.span {(195 * π)}) ∧
            (Ideal.absNorm (Ideal.span {α}) = Ideal.absNorm (Ideal.span {(195 * π)}) →
                Associated α (195 * π)))

/-- **The first three Schatunowsky sets of the Eisenstein integers.** Let $K$ be a number
field of discriminant $-3$ (so $K \cong \mathbb{Q}(\sqrt{-3})$). For $\alpha \in \mathcal{O}_K$ let
$N(\alpha)$ be the absolute norm of the ideal $(\alpha)$, and let $Q_\ell$ be the set of
$\alpha \in \mathcal{O}_K$ with $N(\alpha) > 1$ such that every $\beta \in \mathcal{O}_K$ coprime
to $\alpha$ with $1 < N(\beta) < N(\alpha)$ has at most $\ell$ prime ideal factors, counted with
multiplicity. Below, $\gamma$ ranges over $\mathcal{O}_K$ and $\pi$ over the elements of norm $3$.
Then $Q_1$ consists of the $\alpha$ with $1 < N(\alpha) \le 9$, the products $\gamma\pi$ with
$4 \le N(\gamma) \le 5$, and the products $2\gamma\pi$ with $2 \le N(\gamma) \le 4$. The set
$Q_2$ consists of the $\alpha$ with $1 < N(\alpha) \le 27$, the $\gamma\pi$ with
$10 \le N(\gamma) \le 21$, the $2\gamma\pi$ with $6 \le N(\gamma) \le 28$, and the $14\gamma\pi$
with $1 \le N(\gamma) \le 3$. The set $Q_3$ consists of the $\alpha$ with
$1 < N(\alpha) \le 81$, the $\gamma\pi$ with $28 \le N(\gamma) \le 85$, the $2\gamma\pi$ with
$22 \le N(\gamma) \le 200$, the $14\gamma\pi$ with $5 \le N(\gamma) \le 48$, and the associates
of $182\pi$. Moreover, the elements of largest norm are unique up to units: there is a $\pi$ of
norm $3$ with $4\pi \in Q_1$ such that every $\alpha \in Q_1$ has $N(\alpha) \le N(4\pi)$, with
$\alpha$ an associate of $4\pi$ in case of equality; $42 \in Q_2$, and every $\alpha \in Q_2$ has
$N(\alpha) \le N(42)$, with $\alpha$ an associate of $42$ in case of equality; and there is a
$\pi$ of norm $3$ with $182\pi \in Q_3$ such that every $\alpha \in Q_3$ has
$N(\alpha) \le N(182\pi)$, with $\alpha$ an associate of $182\pi$ in case of equality.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Corollary 2
(`integers-2026-A110-cor-2`). -/
public theorem_wanted eisenstein_quadSchatunowskySet_eq {K : Type*} [Field K] [NumberField K]
    (hK : discr K = -3) :
    quadSchatunowskySet K 1 =
        {α | (1 < Ideal.absNorm (Ideal.span {α}) ∧ Ideal.absNorm (Ideal.span {α}) ≤ 9) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ 4 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 5 ∧ α = γ * π) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ 2 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 4 ∧ α = γ * (2 * π))} ∧
      quadSchatunowskySet K 2 =
        {α | (1 < Ideal.absNorm (Ideal.span {α}) ∧ Ideal.absNorm (Ideal.span {α}) ≤ 27) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ 10 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 21 ∧ α = γ * π) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ 6 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 28 ∧ α = γ * (2 * π)) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ 1 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 3 ∧ α = γ * (14 * π))} ∧
      quadSchatunowskySet K 3 =
        {α | (1 < Ideal.absNorm (Ideal.span {α}) ∧ Ideal.absNorm (Ideal.span {α}) ≤ 81) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ 28 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 85 ∧ α = γ * π) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ 22 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 200 ∧ α = γ * (2 * π)) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ 5 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 48 ∧ α = γ * (14 * π)) ∨
          (∃ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ Associated α (182 * π))} ∧
      (∃ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ (4 * π) ∈ quadSchatunowskySet K 1 ∧
          ∀ α ∈ quadSchatunowskySet K 1,
              Ideal.absNorm (Ideal.span {α}) ≤ Ideal.absNorm (Ideal.span {(4 * π)}) ∧
            (Ideal.absNorm (Ideal.span {α}) = Ideal.absNorm (Ideal.span {(4 * π)}) →
                Associated α (4 * π))) ∧
      ((42 : 𝓞 K) ∈ quadSchatunowskySet K 2 ∧ ∀ α ∈ quadSchatunowskySet K 2,
          Ideal.absNorm (Ideal.span {α}) ≤ Ideal.absNorm (Ideal.span {(42 : 𝓞 K)}) ∧
            (Ideal.absNorm (Ideal.span {α}) = Ideal.absNorm (Ideal.span {(42 : 𝓞 K)}) →
                Associated α 42)) ∧
      (∃ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ (182 * π) ∈ quadSchatunowskySet K 3 ∧
          ∀ α ∈ quadSchatunowskySet K 3,
              Ideal.absNorm (Ideal.span {α}) ≤ Ideal.absNorm (Ideal.span {(182 * π)}) ∧
            (Ideal.absNorm (Ideal.span {α}) = Ideal.absNorm (Ideal.span {(182 * π)}) →
                Associated α (182 * π)))

end

end MetaMathlibExt
