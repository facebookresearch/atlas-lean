/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# `{p, q}`-Diophantine quadruples and quintuples

Statements from Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and
Quintuples*, INTEGERS 25 (2025), Article A92. An `S`-Diophantine `m`-tuple is a set of `m`
distinct positive integers whose pairwise products plus one are `S`-units
(`MetaMathlibExt.IsSDiophantineTuple`). For a quadruple `(a, b, c, d)` the paper writes
`s₁ = ab + 1`, `s₂ = ac + 1`, `s₃ = ad + 1`, `s₄ = bc + 1`, `s₅ = bd + 1`, `s₆ = cd + 1`,
`sᵢ = p ^ αᵢ * q ^ βᵢ`; here `αᵢ` and `βᵢ` are `padicValNat p sᵢ` and `padicValNat q sᵢ`.
Lemmas 1-7, Proposition 1 and Theorems 1 and 2 are stated as wanted theorems; Lemmas 1-5 quote
earlier results.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **$S$-Diophantine tuples.** Let $S$ be a finite set of natural numbers. A finite set $s$ of
natural numbers is an $S$-Diophantine tuple if all its elements are positive and, for all
distinct $a, b \in s$, every prime factor of $ab + 1$ lies in $S$. A tuple $(a_1, \dots, a_m)$ of
distinct positive integers is encoded by the set of its entries, which has $m$ elements.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and Quintuples*,
INTEGERS 25 (2025), Article A92, Section 1 (definition of `S`-Diophantine `m`-tuples). -/
def IsSDiophantineTuple (S s : Finset ℕ) : Prop :=
  (∀ a ∈ s, 0 < a) ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (a * b + 1).primeFactors ⊆ S

/-- **$(1, 3)$ is a $\{2\}$-Diophantine pair.** The set $\{1, 3\}$ is a $\{2\}$-Diophantine
tuple, since $1 \cdot 3 + 1 = 2^2$.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and Quintuples*,
INTEGERS 25 (2025), Article A92, Section 1 (definition of `S`-Diophantine `m`-tuples). -/
theorem isSDiophantineTuple_two_one_three : IsSDiophantineTuple {2} {1, 3} := by
  refine ⟨by decide, ?_⟩
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · rw [show 1 * 3 + 1 = 2 ^ 2 from rfl, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
  · rw [show 3 * 1 + 1 = 2 ^ 2 from rfl, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
  · exact absurd rfl hab

/-- **$(1, 3, 8)$ is a $\{2, 3, 5\}$-Diophantine triple.** The set $\{1, 3, 8\}$ is a
$\{2, 3, 5\}$-Diophantine tuple, since $1 \cdot 3 + 1 = 2^2$, $1 \cdot 8 + 1 = 3^2$ and
$3 \cdot 8 + 1 = 5^2$.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and Quintuples*,
INTEGERS 25 (2025), Article A92, Section 1 (definition of `S`-Diophantine `m`-tuples). -/
theorem isSDiophantineTuple_two_three_five_one_three_eight :
    IsSDiophantineTuple {2, 3, 5} {1, 3, 8} := by
  refine ⟨by decide, ?_⟩
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  have h4 : (4 : ℕ).primeFactors ⊆ {2, 3, 5} := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
    simp
  have h9 : (9 : ℕ).primeFactors ⊆ {2, 3, 5} := by
    rw [show (9 : ℕ) = 3 ^ 2 from rfl, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
    simp
  have h25 : (25 : ℕ).primeFactors ⊆ {2, 3, 5} := by
    rw [show (25 : ℕ) = 5 ^ 2 from rfl,
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_five]
    simp
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | exact absurd rfl hab | exact h4 | exact h9 | exact h25

/-- **$ac + 1$ does not divide $bc + 1$.** If $a < b < c$ are positive integers, then $ac + 1$
does not divide $bc + 1$.

The source states this for $S$-Diophantine triples; that hypothesis is not needed.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and Quintuples*,
INTEGERS 25 (2025), Article A92, Lemma 1, quoting Szalay and Ziegler (2013), Lemma 2.1
(`integers-2025-A92-lem-1`). -/
public theorem_wanted not_mul_add_one_dvd_mul_add_one {a b c : ℕ} (ha : 0 < a) (hab : a < b)
    (hbc : b < c) : ¬(a * c + 1 ∣ b * c + 1)

/-- **The two smallest valuations coincide.** Let $\ell$ be a prime and $a, b, c, d$ natural
numbers. Put $s_1 = ab + 1$, $s_2 = ac + 1$, $s_3 = ad + 1$, $s_4 = bc + 1$, $s_5 = bd + 1$,
$s_6 = cd + 1$, and let $v_i$ be the $\ell$-adic valuation of $s_i$. Then in each of the tuples
$(v_2, v_3, v_4, v_5)$, $(v_1, v_2, v_5, v_6)$ and $(v_1, v_3, v_4, v_6)$ the minimum value occurs
at two different positions.

Taking $\ell = p$ and $\ell = q$ gives the source's statements for the exponents of a
$\{p, q\}$-Diophantine quadruple. No Diophantine hypothesis is needed: the proof uses only the
identities $abcd = (s_1 - 1)(s_6 - 1) = (s_2 - 1)(s_5 - 1) = (s_3 - 1)(s_4 - 1)$.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and Quintuples*,
INTEGERS 25 (2025), Article A92, Lemma 2, quoting Szalay and Ziegler (2013), Proposition 1
(`integers-2025-A92-lem-2`). -/
public theorem_wanted padicValNat_two_smallest_eq {ℓ : ℕ} (hℓ : ℓ.Prime) (a b c d : ℕ) :
    let v : Fin 6 → ℕ := ![padicValNat ℓ (a * b + 1), padicValNat ℓ (a * c + 1),
      padicValNat ℓ (a * d + 1), padicValNat ℓ (b * c + 1), padicValNat ℓ (b * d + 1),
      padicValNat ℓ (c * d + 1)]
    let minTwice : (Fin 4 → ℕ) → Prop := fun x => ∃ i j, i ≠ j ∧ x i = x j ∧ ∀ k, x i ≤ x k
    minTwice ![v 1, v 2, v 3, v 4] ∧ minTwice ![v 0, v 1, v 4, v 5] ∧
      minTwice ![v 0, v 2, v 3, v 5]

/-- **$a$, $b$, $c$, $d$ divide gcds of reduced differences.** Let $a, b, c, d$ be natural numbers
and put $s_1 = ab + 1$, $s_2 = ac + 1$, $s_3 = ad + 1$, $s_4 = bc + 1$, $s_5 = bd + 1$,
$s_6 = cd + 1$. For indices $i, j$ let $t_{ij}$ be the integer $(s_j - s_i) / \gcd(s_j, s_i)$.
Then $a \mid \gcd(t_{12}, t_{13}, t_{23})$, $b \mid \gcd(t_{14}, t_{15}, t_{45})$,
$c \mid \gcd(t_{24}, t_{26}, t_{46})$ and $d \mid \gcd(t_{35}, t_{36}, t_{56})$ in $\mathbb{Z}$.

The source assumes that $\{a, b, c, d\}$ is $S$-Diophantine; that hypothesis is not needed.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and Quintuples*,
INTEGERS 25 (2025), Article A92, Lemma 3, quoting Szalay and Ziegler (2013), Lemma 3
(`integers-2025-A92-lem-3`). -/
public theorem_wanted dvd_gcd_sub_div_gcd (a b c d : ℕ) :
    let s : Fin 6 → ℤ := ![a * b + 1, a * c + 1, a * d + 1, b * c + 1, b * d + 1, c * d + 1]
    let t : Fin 6 → Fin 6 → ℤ := fun i j => (s j - s i) / gcd (s j) (s i)
    (a : ℤ) ∣ gcd (gcd (t 0 1) (t 0 2)) (t 1 2) ∧
      (b : ℤ) ∣ gcd (gcd (t 0 3) (t 0 4)) (t 3 4) ∧
      (c : ℤ) ∣ gcd (gcd (t 1 3) (t 1 5)) (t 3 5) ∧
      (d : ℤ) ∣ gcd (gcd (t 2 4) (t 2 5)) (t 4 5)

/-- **The Szalay–Ziegler system (4) has no solutions.** Let $p \ne q$ be odd primes and let
$a, b, c, d$ be integers with $0 < a < b < c < d$. Then there are no natural numbers
$\beta_1, \alpha_4, \beta_4, \alpha_2, \alpha_5, \alpha_3, \beta_3, \beta_6$ with
$ab + 1 = q^{\beta_1}$, $bc + 1 = p^{\alpha_4} q^{\beta_4}$, $ac + 1 = p^{\alpha_2}$,
$bd + 1 = p^{\alpha_5}$, $ad + 1 = p^{\alpha_3} q^{\beta_3}$ and $cd + 1 = q^{\beta_6}$.

Any solution would make $\{a, b, c, d\}$ a $\{p, q\}$-Diophantine quadruple.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and Quintuples*,
INTEGERS 25 (2025), Article A92, Lemma 4, System (4), quoting Szalay and Ziegler, INTEGERS 13
(2013), Section 4 (`integers-2025-A92-lem-4`). -/
public theorem_wanted not_exists_sDiophantine_system_four {p q a b c d : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) (ha : 0 < a) (hab : a < b)
    (hbc : b < c) (hcd : c < d) :
    ¬∃ β₁ α₄ β₄ α₂ α₅ α₃ β₃ β₆ : ℕ, a * b + 1 = q ^ β₁ ∧ b * c + 1 = p ^ α₄ * q ^ β₄ ∧
      a * c + 1 = p ^ α₂ ∧ b * d + 1 = p ^ α₅ ∧ a * d + 1 = p ^ α₃ * q ^ β₃ ∧
      c * d + 1 = q ^ β₆

/-- **Exponent cases for $\{p, q\}$-Diophantine quadruples with $p \equiv 3 \pmod 4$.** Let
$p \ne q$ be primes with $p \equiv 3 \pmod 4$, and let $a < b < c < d$ be natural numbers such
that $\{a, b, c, d\}$ is a $\{p, q\}$-Diophantine tuple. Write $s_1, \dots, s_6$ for
$ab + 1, ac + 1, ad + 1, bc + 1, bd + 1, cd + 1$, and let $\alpha_i$ and $\beta_i$ be the
exponents of $p$ and $q$ in the prime factorization of $s_i$. Then one of the following holds:
(I) $0 = \alpha_1 = \alpha_6 < \alpha_4 = \alpha_5 < \alpha_2 < \alpha_3$ and
$\beta_1 = \beta_2 = \beta_3 < \beta_4 < \beta_5 < \beta_6$;
(II) $0 = \alpha_1 = \alpha_6 < \alpha_2 = \alpha_5$, $\alpha_5 < \alpha_3$, $\alpha_5 < \alpha_4$
and $\beta_3 = \beta_4 < \beta_1 = \beta_2 < \beta_5 < \beta_6$;
(III) $0 = \alpha_2 = \alpha_5 < \alpha_1 = \alpha_3 \le \alpha_4 < \alpha_6$ and
$\beta_1 = \beta_6 < \beta_3 = \beta_4 < \beta_2 < \beta_5$;
(IV) $0 = \alpha_3 = \alpha_4 < \alpha_1 = \alpha_2 < \alpha_5 < \alpha_6$ and
$\beta_1 = \beta_6 < \beta_2 = \beta_5$, $\beta_5 < \beta_3$, $\beta_5 < \beta_4$.

These are the four cases of Table 1 of the source.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and Quintuples*,
INTEGERS 25 (2025), Article A92, Lemma 5 and Table 1, quoting Ziegler, Glas. Mat. 54 (2019),
Proposition 5.1 (`integers-2025-A92-lem-5`). -/
public theorem_wanted sDiophantine_quadruple_exponent_cases {p q a b c d : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (hp3 : p % 4 = 3) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hS : IsSDiophantineTuple {p, q} {a, b, c, d}) :
    let α₁ := padicValNat p (a * b + 1)
    let α₂ := padicValNat p (a * c + 1)
    let α₃ := padicValNat p (a * d + 1)
    let α₄ := padicValNat p (b * c + 1)
    let α₅ := padicValNat p (b * d + 1)
    let α₆ := padicValNat p (c * d + 1)
    let β₁ := padicValNat q (a * b + 1)
    let β₂ := padicValNat q (a * c + 1)
    let β₃ := padicValNat q (a * d + 1)
    let β₄ := padicValNat q (b * c + 1)
    let β₅ := padicValNat q (b * d + 1)
    let β₆ := padicValNat q (c * d + 1)
    (α₁ = 0 ∧ α₆ = 0 ∧ 0 < α₄ ∧ α₄ = α₅ ∧ α₅ < α₂ ∧ α₂ < α₃ ∧
        β₁ = β₂ ∧ β₂ = β₃ ∧ β₃ < β₄ ∧ β₄ < β₅ ∧ β₅ < β₆) ∨
      (α₁ = 0 ∧ α₆ = 0 ∧ 0 < α₂ ∧ α₂ = α₅ ∧ α₅ < α₃ ∧ α₅ < α₄ ∧
        β₃ = β₄ ∧ β₄ < β₁ ∧ β₁ = β₂ ∧ β₂ < β₅ ∧ β₅ < β₆) ∨
      (α₂ = 0 ∧ α₅ = 0 ∧ 0 < α₁ ∧ α₁ = α₃ ∧ α₃ ≤ α₄ ∧ α₄ < α₆ ∧
        β₁ = β₆ ∧ β₆ < β₃ ∧ β₃ = β₄ ∧ β₄ < β₂ ∧ β₂ < β₅) ∨
      (α₃ = 0 ∧ α₄ = 0 ∧ 0 < α₁ ∧ α₁ = α₂ ∧ α₂ < α₅ ∧ α₅ < α₆ ∧
        β₁ = β₆ ∧ β₆ < β₂ ∧ β₂ = β₅ ∧ β₅ < β₃ ∧ β₅ < β₄)

/-- **No $\{p, q\}$-Diophantine quadruple when $p$ or $q$ is $3$ modulo $4$.** Let $p \ne q$ be
primes with $p \equiv 3 \pmod 4$ or $q \equiv 3 \pmod 4$. Then no four-element set of natural
numbers is a $\{p, q\}$-Diophantine tuple; that is, there is no $\{p, q\}$-Diophantine quadruple.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and Quintuples*,
INTEGERS 25 (2025), Article A92, Theorem 1 (`integers-2025-A92-thm-1`). -/
public theorem_wanted not_exists_sDiophantine_quadruple_of_mod_four_eq_three {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h3 : p % 4 = 3 ∨ q % 4 = 3) :
    ¬∃ s : Finset ℕ, s.card = 4 ∧ IsSDiophantineTuple {p, q} s

/-- **There is no $\{p, q\}$-Diophantine quintuple.** Let $p < q$ be primes. Then no five-element
set of natural numbers is a $\{p, q\}$-Diophantine tuple; that is, there is no
$\{p, q\}$-Diophantine quintuple.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and Quintuples*,
INTEGERS 25 (2025), Article A92, Theorem 2 (`integers-2025-A92-thm-2`). -/
public theorem_wanted not_exists_sDiophantine_quintuple {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) :
    ¬∃ s : Finset ℕ, s.card = 5 ∧ IsSDiophantineTuple {p, q} s


/-- **Bounds in Case III for $\{p, q\}$-Diophantine quadruples.** Let $p$ and $q$ be primes with
$p \equiv 3 \pmod 4$, $p \ge 7$ and $q \equiv 1 \pmod 4$, and let $a < b < c < d$ be natural
numbers such that $\{a, b, c, d\}$ is a $\{p, q\}$-Diophantine tuple. Put $s_1 = ab + 1$,
$s_2 = ac + 1$, $s_3 = ad + 1$, $s_4 = bc + 1$, $s_5 = bd + 1$, $s_6 = cd + 1$, and let
$\alpha_i$ and $\beta_i$ be the $p$-adic and $q$-adic valuations of $s_i$. Suppose that
$0 = \alpha_2 = \alpha_5 < \alpha_1 = \alpha_3 \le \alpha_4 < \alpha_6$ and
$0 < \beta_1 = \beta_6 < \beta_3 = \beta_4 < \beta_2 < \beta_5$ (Case III of Table 1, with
$\beta_1 > 0$). Then, with $\beta = \beta_1$ and $\beta' = \beta_3$, we have
$d < 1.03\, q^{2(\beta' - \beta)}$ and $b < 1.03\, q^{\beta' - \beta}$.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and Quintuples*,
INTEGERS 25 (2025), Article A92, Lemma 6 (`integers-2025-A92-lem-6`). -/
public theorem_wanted sDiophantine_quadruple_caseIII_bounds {p q a b c d : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hp3 : p % 4 = 3) (hp7 : 7 ≤ p) (hq1 : q % 4 = 1) (hab : a < b)
    (hbc : b < c) (hcd : c < d) (hS : IsSDiophantineTuple {p, q} {a, b, c, d})
    (hcase : padicValNat p (a * c + 1) = 0 ∧ padicValNat p (b * d + 1) = 0 ∧
      0 < padicValNat p (a * b + 1) ∧ padicValNat p (a * b + 1) = padicValNat p (a * d + 1) ∧
      padicValNat p (a * d + 1) ≤ padicValNat p (b * c + 1) ∧
      padicValNat p (b * c + 1) < padicValNat p (c * d + 1) ∧
      0 < padicValNat q (a * b + 1) ∧ padicValNat q (a * b + 1) = padicValNat q (c * d + 1) ∧
      padicValNat q (c * d + 1) < padicValNat q (a * d + 1) ∧
      padicValNat q (a * d + 1) = padicValNat q (b * c + 1) ∧
      padicValNat q (b * c + 1) < padicValNat q (a * c + 1) ∧
      padicValNat q (a * c + 1) < padicValNat q (b * d + 1)) :
    let β := padicValNat q (a * b + 1)
    let β' := padicValNat q (a * d + 1)
    (d : ℝ) < 103 / 100 * (q : ℝ) ^ (2 * (β' - β)) ∧ (b : ℝ) < 103 / 100 * (q : ℝ) ^ (β' - β)

/-- **Bound on $b$ in Case IV for $\{p, q\}$-Diophantine quadruples.** Let $p$ and $q$ be
primes with $p \equiv 3 \pmod 4$, $p \ge 7$ and $q \equiv 1 \pmod 4$, and let $a < b < c < d$
be natural numbers such that $\{a, b, c, d\}$ is a $\{p, q\}$-Diophantine tuple. Write
$s_1, \dots, s_6$ for $ab + 1, ac + 1, ad + 1, bc + 1, bd + 1, cd + 1$, and let $\alpha_i$ and
$\beta_i$ be the exponents of $p$ and $q$ in the prime factorization of $s_i$. Suppose that
$0 = \alpha_3 = \alpha_4 < \alpha_1 = \alpha_2 < \alpha_5 < \alpha_6$ and
$0 < \beta_1 = \beta_6 < \beta_2 = \beta_5$, $\beta_5 < \beta_3$, $\beta_5 < \beta_4$. Then
$b < 1.042 \, q^{\beta_2 - \beta_1}$.

The assumptions on the exponents are Case IV of Table 1 of the source together with
$\beta_1 > 0$.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and Quintuples*,
INTEGERS 25 (2025), Article A92, Lemma 7 (`integers-2025-A92-lem-7`). -/
public theorem_wanted sDiophantine_quadruple_caseIV_bound {p q a b c d : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hp3 : p % 4 = 3) (hp7 : 7 ≤ p) (hq1 : q % 4 = 1) (hab : a < b)
    (hbc : b < c) (hcd : c < d) (hS : IsSDiophantineTuple {p, q} {a, b, c, d})
    (hcase : padicValNat p (a * d + 1) = 0 ∧ padicValNat p (b * c + 1) = 0 ∧
      0 < padicValNat p (a * b + 1) ∧ padicValNat p (a * b + 1) = padicValNat p (a * c + 1) ∧
      padicValNat p (a * c + 1) < padicValNat p (b * d + 1) ∧
      padicValNat p (b * d + 1) < padicValNat p (c * d + 1) ∧
      0 < padicValNat q (a * b + 1) ∧ padicValNat q (a * b + 1) = padicValNat q (c * d + 1) ∧
      padicValNat q (c * d + 1) < padicValNat q (a * c + 1) ∧
      padicValNat q (a * c + 1) = padicValNat q (b * d + 1) ∧
      padicValNat q (b * d + 1) < padicValNat q (a * d + 1) ∧
      padicValNat q (b * d + 1) < padicValNat q (b * c + 1)) :
    let β := padicValNat q (a * b + 1)
    let β' := padicValNat q (a * c + 1)
    (b : ℝ) < 1042 / 1000 * (q : ℝ) ^ (β' - β)

/-- **The fourteen exponent cases for $\{p, q\}$-Diophantine quadruples.** Let $p \ne q$ be
primes and let $a < b < c < d$ be natural numbers such that $\{a, b, c, d\}$ is a
$\{p, q\}$-Diophantine tuple. Write $s_1, \dots, s_6$ for
$ab + 1, ac + 1, ad + 1, bc + 1, bd + 1, cd + 1$, and let $\alpha_i$ and $\beta_i$ be the
exponents of $p$ and $q$ in the prime factorization of $s_i$. Then one of the following
fourteen cases holds:
(I) $\alpha_1 = \alpha_2 = \alpha_3 < \alpha_4 < \alpha_5$, $\alpha_3 < \alpha_6 < \alpha_5$,
$\beta_1 = \beta_4 = \beta_5 < \beta_2 < \beta_3$ and $\beta_5 < \beta_6 < \beta_3$;
(II) $\alpha_1 = \alpha_2 = \alpha_3 < \alpha_4 < \alpha_5 < \alpha_6$ and
$\beta_1 = \beta_6 < \beta_4 = \beta_5 < \beta_2 < \beta_3$;
(III) $\alpha_1 = \alpha_6 < \alpha_2 = \alpha_3 < \alpha_4 < \alpha_5$ and
$\beta_1 = \beta_4 = \beta_5 < \beta_2 < \beta_3 < \beta_6$;
(IV) $\alpha_2 = \alpha_5 < \alpha_1 = \alpha_3 < \alpha_4 < \alpha_6$ and
$\beta_1 = \beta_6 < \beta_3 = \beta_4 < \beta_2 < \beta_5$;
(V) $\alpha_2 = \alpha_5 < \alpha_1 = \alpha_4 < \alpha_3 < \alpha_6$ and
$\beta_1 = \beta_6 < \beta_3 = \beta_4 < \beta_2 < \beta_5$;
(VI) $\alpha_1 = \alpha_6 < \alpha_2 = \alpha_5$, $\alpha_5 < \alpha_3$, $\alpha_5 < \alpha_4$ and
$\beta_3 = \beta_4 < \beta_1 = \beta_2 < \beta_5 < \beta_6$;
(VII) $\alpha_2 = \alpha_5 < \alpha_3 = \alpha_4 < \alpha_1 < \alpha_6$ and
$\beta_1 = \beta_6 < \beta_3 = \beta_4 < \beta_2 < \beta_5$;
(VIII)-(XIV) the conditions of (I)-(VII) with $\alpha_i$ and $\beta_i$ exchanged for every $i$.

These are the cases of Table 2 of the source.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and Quintuples*,
INTEGERS 25 (2025), Article A92, Proposition 1 and Table 2 (`integers-2025-A92-prop-1`). -/
public theorem_wanted sDiophantine_quadruple_fourteen_cases {p q a b c d : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hS : IsSDiophantineTuple {p, q} {a, b, c, d}) :
    let α₁ := padicValNat p (a * b + 1)
    let α₂ := padicValNat p (a * c + 1)
    let α₃ := padicValNat p (a * d + 1)
    let α₄ := padicValNat p (b * c + 1)
    let α₅ := padicValNat p (b * d + 1)
    let α₆ := padicValNat p (c * d + 1)
    let β₁ := padicValNat q (a * b + 1)
    let β₂ := padicValNat q (a * c + 1)
    let β₃ := padicValNat q (a * d + 1)
    let β₄ := padicValNat q (b * c + 1)
    let β₅ := padicValNat q (b * d + 1)
    let β₆ := padicValNat q (c * d + 1)
    -- Case I
    (α₁ = α₂ ∧ α₂ = α₃ ∧ α₃ < α₄ ∧ α₃ < α₆ ∧ α₄ < α₅ ∧ α₆ < α₅ ∧ β₁ = β₄ ∧ β₄ = β₅ ∧ β₅ < β₂ ∧
      β₅ < β₆ ∧ β₂ < β₃ ∧ β₆ < β₃) ∨
    -- Case II
    (α₁ = α₂ ∧ α₂ = α₃ ∧ α₃ < α₄ ∧ α₄ < α₅ ∧ α₅ < α₆ ∧ β₁ = β₆ ∧ β₆ < β₄ ∧ β₄ = β₅ ∧ β₅ < β₂ ∧
      β₂ < β₃) ∨
    -- Case III
    (α₁ = α₆ ∧ α₆ < α₂ ∧ α₂ = α₃ ∧ α₃ < α₄ ∧ α₄ < α₅ ∧ β₁ = β₄ ∧ β₄ = β₅ ∧ β₅ < β₂ ∧ β₂ < β₃ ∧
      β₃ < β₆) ∨
    -- Case IV
    (α₂ = α₅ ∧ α₅ < α₁ ∧ α₁ = α₃ ∧ α₃ < α₄ ∧ α₄ < α₆ ∧ β₁ = β₆ ∧ β₆ < β₃ ∧ β₃ = β₄ ∧ β₄ < β₂ ∧
      β₂ < β₅) ∨
    -- Case V
    (α₂ = α₅ ∧ α₅ < α₁ ∧ α₁ = α₄ ∧ α₄ < α₃ ∧ α₃ < α₆ ∧ β₁ = β₆ ∧ β₆ < β₃ ∧ β₃ = β₄ ∧ β₄ < β₂ ∧
      β₂ < β₅) ∨
    -- Case VI
    (α₁ = α₆ ∧ α₆ < α₂ ∧ α₂ = α₅ ∧ α₅ < α₃ ∧ α₅ < α₄ ∧ β₃ = β₄ ∧ β₄ < β₁ ∧ β₁ = β₂ ∧ β₂ < β₅ ∧
      β₅ < β₆) ∨
    -- Case VII
    (α₂ = α₅ ∧ α₅ < α₃ ∧ α₃ = α₄ ∧ α₄ < α₁ ∧ α₁ < α₆ ∧ β₁ = β₆ ∧ β₆ < β₃ ∧ β₃ = β₄ ∧ β₄ < β₂ ∧
      β₂ < β₅) ∨
    -- Case VIII
    (α₁ = α₄ ∧ α₄ = α₅ ∧ α₅ < α₂ ∧ α₅ < α₆ ∧ α₂ < α₃ ∧ α₆ < α₃ ∧ β₁ = β₂ ∧ β₂ = β₃ ∧ β₃ < β₄ ∧
      β₃ < β₆ ∧ β₄ < β₅ ∧ β₆ < β₅) ∨
    -- Case IX
    (α₁ = α₆ ∧ α₆ < α₄ ∧ α₄ = α₅ ∧ α₅ < α₂ ∧ α₂ < α₃ ∧ β₁ = β₂ ∧ β₂ = β₃ ∧ β₃ < β₄ ∧ β₄ < β₅ ∧
      β₅ < β₆) ∨
    -- Case X
    (α₁ = α₄ ∧ α₄ = α₅ ∧ α₅ < α₂ ∧ α₂ < α₃ ∧ α₃ < α₆ ∧ β₁ = β₆ ∧ β₆ < β₂ ∧ β₂ = β₃ ∧ β₃ < β₄ ∧
      β₄ < β₅) ∨
    -- Case XI
    (α₁ = α₆ ∧ α₆ < α₃ ∧ α₃ = α₄ ∧ α₄ < α₂ ∧ α₂ < α₅ ∧ β₂ = β₅ ∧ β₅ < β₁ ∧ β₁ = β₃ ∧ β₃ < β₄ ∧
      β₄ < β₆) ∨
    -- Case XII
    (α₁ = α₆ ∧ α₆ < α₃ ∧ α₃ = α₄ ∧ α₄ < α₂ ∧ α₂ < α₅ ∧ β₂ = β₅ ∧ β₅ < β₁ ∧ β₁ = β₄ ∧ β₄ < β₃ ∧
      β₃ < β₆) ∨
    -- Case XIII
    (α₃ = α₄ ∧ α₄ < α₁ ∧ α₁ = α₂ ∧ α₂ < α₅ ∧ α₅ < α₆ ∧ β₁ = β₆ ∧ β₆ < β₂ ∧ β₂ = β₅ ∧ β₅ < β₃ ∧
      β₅ < β₄) ∨
    -- Case XIV
    (α₁ = α₆ ∧ α₆ < α₃ ∧ α₃ = α₄ ∧ α₄ < α₂ ∧ α₂ < α₅ ∧ β₂ = β₅ ∧ β₅ < β₃ ∧ β₃ = β₄ ∧ β₄ < β₁ ∧
      β₁ < β₆)

end

end MetaMathlibExt
