/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Fermat
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Fermat numbers modulo a prime (statements)

Statement-only targets from Klaška, *Fermat Numbers Modulo a Prime*. Fermat numbers are
`Nat.fermatNumber n = 2 ^ 2 ^ n + 1`. The paper's preperiod `h(p)` and period `k(p)` of
`n ↦ F_n mod p` are encoded as in `Nat.fermatNumber_mod_prime_exact_preperiod_period`
(`MathlibExt/NumberTheory/FermatResiduePeriod.lean`): the tail from `h` is periodic, no
earlier tail has a positive period, and every positive period of the tail from `h` is a
multiple of `k`. The index `ind_g(a)` with respect to a primitive root `g` is encoded by an
exponent `i` with `g ^ i = a`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Two of $F_0, \dots, F_p$ are congruent modulo $p$.** Write $F_n = 2^{2^n} + 1$. For every
positive integer $p$ there are natural numbers $i < j \le p$ with $F_i \equiv F_j \pmod p$.

This is the pigeonhole principle; $p$ need not be prime.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Lemma 2 (`jis-2025-25.8.7-lem-2`). -/
public theorem_wanted fermatNumber_modEq_exists_repeat (p : ℕ) (hp : 0 < p) :
    ∃ i j, i < j ∧ j ≤ p ∧ Nat.fermatNumber i ≡ Nat.fermatNumber j [MOD p]

/-- **Congruences between Fermat numbers propagate.** Write $F_n = 2^{2^n} + 1$. Let $m$, $i$ and
$j$ be natural numbers with $F_i \equiv F_j \pmod m$. Then $F_{i+t} \equiv F_{j+t} \pmod m$ for
every natural number $t$.

No condition on $m$, $i$ or $j$ is needed.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Lemma 4 (i) (`jis-2025-25.8.7-lem-4`). -/
public theorem_wanted fermatNumber_modEq_add (m i j : ℕ)
    (h : Nat.fermatNumber i ≡ Nat.fermatNumber j [MOD m]) (t : ℕ) :
    Nat.fermatNumber (i + t) ≡ Nat.fermatNumber (j + t) [MOD m]

/-- **Non-congruence of Fermat numbers passes to smaller indices.** Write $F_n = 2^{2^n} + 1$ for
the $n$-th Fermat number. Let $m$ be a natural number and let $i \le j$. If
$F_j \not\equiv F_{j+t} \pmod{m}$ for every $t \ge 1$, then $F_i \not\equiv F_{i+t} \pmod{m}$
for every $t \ge 1$.

The statement holds for every modulus $m$ and allows $i = j$; the paper takes $m = p$ prime and
$i < j$.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Lemma 4 (ii) (`jis-2025-25.8.7-lem-4`). -/
public theorem_wanted fermatNumber_not_modEq_add_of_le (m i j : ℕ) (hij : i ≤ j)
    (h : ∀ t, 0 < t → ¬ Nat.fermatNumber j ≡ Nat.fermatNumber (j + t) [MOD m]) :
    ∀ t, 0 < t → ¬ Nat.fermatNumber i ≡ Nat.fermatNumber (i + t) [MOD m]

/-- **Coincidences among Fermat residues.** Write $F_n = 2^{2^n} + 1$. Let $p$ be a prime, and let
$h$ and $k$ be the preperiod and the period of $n \mapsto F_n \bmod p$ in the following sense:
$k > 0$, the sequence $n \mapsto F_{h+n} \bmod p$ is periodic with period $k$, every positive
period of it is a multiple of $k$, and for no $h' < h$ is the sequence $n \mapsto F_{h'+n} \bmod p$
periodic with a positive period. Then for all natural numbers $i < j$, $F_i \equiv F_j \pmod p$
if and only if $i \ge h$ and $i \equiv j \pmod k$.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Lemma 6 (`jis-2025-25.8.7-lem-6`). -/
public theorem_wanted fermatNumber_modEq_iff_preperiod_period (p : ℕ) (hp : p.Prime)
    (h k : ℕ) (hk : 0 < k)
    (hper : Function.Periodic (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod p)) k)
    (hpre : ∀ h' < h, ¬ ∃ kp : ℕ, 0 < kp ∧
      Function.Periodic (fun n : ℕ => (Nat.fermatNumber (h' + n) : ZMod p)) kp)
    (hmin : ∀ kp : ℕ, 0 < kp →
      Function.Periodic (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod p)) kp → k ∣ kp)
    (i j : ℕ) (hij : i < j) :
    Nat.fermatNumber i ≡ Nat.fermatNumber j [MOD p] ↔ h ≤ i ∧ i ≡ j [MOD k]

/-- **The index of a residue and its multiplicative order.** Let $p$ be a prime, let $g$ be a
primitive root modulo $p$ (an element of $\mathbb{Z}/p\mathbb{Z}$ of multiplicative order
$p - 1$), and let $a \in \mathbb{Z}/p\mathbb{Z}$. If $g^i = a$ for a natural number $i$, then
$\gcd(p - 1, i) = (p - 1)/\operatorname{ord}_p(a)$, where $\operatorname{ord}_p(a)$ is the
multiplicative order of $a$ modulo $p$.

This holds for every natural number $i$ with $g^i = a$; the paper's index
$\operatorname{ind}_g(a)$, which lies between $1$ and $p - 1$, is one of them.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Lemma 8 (iv) (`jis-2025-25.8.7-lem-8`). -/
public theorem_wanted gcd_card_sub_one_exponent_eq_div_orderOf (p : ℕ) (hp : p.Prime)
    (g a : ZMod p) (hg : IsPrimitiveRoot g (p - 1)) (i : ℕ) (hi : g ^ i = a) :
    Nat.gcd (p - 1) i = (p - 1) / orderOf a

/-- **Coprime representatives of a residue class.** Let $\alpha$, $\beta$ and $\gamma$ be natural
numbers with $\gamma > 0$ and $\gcd(\alpha, \beta) = 1$. Then there is a natural number $c > 0$
with $\gcd(c, \gamma) = 1$ and $c \equiv \beta \pmod{\alpha}$.

The numbers $\alpha$ and $\beta$ need not be positive.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Lemma 10 (`jis-2025-25.8.7-lem-10`). -/
public theorem_wanted exists_coprime_modEq_of_coprime (α β γ : ℕ) (hγ : 0 < γ)
    (hαβ : Nat.Coprime α β) :
    ∃ c, 0 < c ∧ Nat.Coprime c γ ∧ c ≡ β [MOD α]

/-- **A primitive root in which a residue has index $(p-1)/\operatorname{ord}_p(a)$.** Let $p$ be
a prime and let $a$ be a nonzero residue modulo $p$, of multiplicative order
$\operatorname{ord}_p(a)$. Then there is a primitive root $g$ modulo $p$ (an element of order
$p - 1$ in $\mathbb{Z}/p\mathbb{Z}$) with $g^{(p-1)/\operatorname{ord}_p(a)} = a$.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Proposition 11 (`jis-2025-25.8.7-prop-11`). -/
public theorem_wanted exists_primitiveRoot_pow_card_sub_one_div_orderOf (p : ℕ)
    (hp : p.Prime) (a : ZMod p) (ha : a ≠ 0) :
    ∃ g : ZMod p, IsPrimitiveRoot g (p - 1) ∧ g ^ ((p - 1) / orderOf a) = a

/-- **Indices dividing $p - 1$.** Let $p$ be a prime, let $g$ be a primitive root modulo $p$ (an
element of order $p - 1$ in $\mathbb{Z}/p\mathbb{Z}$), let $a \in \mathbb{Z}/p\mathbb{Z}$ and let
$i$ be a natural number with $g^i = a$. Then $i$ divides $p - 1$ if and only if
$i = (p - 1)/\operatorname{ord}_p(a)$, where $\operatorname{ord}_p(a)$ is the multiplicative order
of $a$.

For $i$ outside $\{1, \dots, p - 1\}$ both sides are false, so the statement concerns the index
$\operatorname{ind}_g(a)$.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Proposition 13 (`jis-2025-25.8.7-prop-13`). -/
public theorem_wanted exponent_dvd_card_sub_one_iff (p : ℕ) (hp : p.Prime)
    (g a : ZMod p) (hg : IsPrimitiveRoot g (p - 1)) (i : ℕ) (hi : g ^ i = a) :
    i ∣ p - 1 ↔ i = (p - 1) / orderOf a

/-- **Uniqueness of the $2$-adic decomposition of the index of $2$.** Let $p$ be an odd prime and
write $p - 1 = 2^r u$ with $u$ odd. Then there is exactly one pair $(s, t)$ of natural numbers
with $s \le r$ and $t \mid u$ such that $g^{2^s t} = 2$ for some primitive root $g$ modulo $p$
(an element of order $p - 1$ in $\mathbb{Z}/p\mathbb{Z}$).

Since $2^s t$ divides $p - 1$, it lies in $\{1, \dots, p - 1\}$, so it is the index
$\operatorname{ind}_g(2)$ of $2$ with respect to $g$.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Corollary 14 (`jis-2025-25.8.7-cor-14`); also Theorem 15 (i). -/
public theorem_wanted existsUnique_twoAdic_index_of_two (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (r u : ℕ) (hu : Odd u) (hpu : p - 1 = 2 ^ r * u) :
    ∃! st : ℕ × ℕ, st.1 ≤ r ∧ st.2 ∣ u ∧
      ∃ g : ZMod p, IsPrimitiveRoot g (p - 1) ∧ g ^ (2 ^ st.1 * st.2) = 2

/-- **Preperiod and period of Fermat residues from the index of $2$.** Write $F_n = 2^{2^n} + 1$.
Let $p$ be an odd prime, write $p - 1 = 2^r u$ with $u$ odd, and let $s \le r$ and $t \mid u$ be
natural numbers such that $g^{2^s t} = 2$ for some primitive root $g$ modulo $p$ (an element of
order $p - 1$ in $\mathbb{Z}/p\mathbb{Z}$). Let $k$ be the multiplicative order of $2$ modulo
$u/t$, with $k = 1$ when $t = u$. Then the sequence $n \mapsto F_{r-s+n} \bmod p$ is periodic
with period $k$, every positive period of it is a multiple of $k$, and for no $h < r - s$ is the
sequence $n \mapsto F_{h+n} \bmod p$ periodic with a positive period. Thus $n \mapsto F_n \bmod p$
has preperiod $r - s$ and primitive period $k$.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Theorem 15 (ii) and (iii) (`jis-2025-25.8.7-thm-15`). -/
public theorem_wanted fermatNumber_mod_prime_preperiod_period_of_index (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (r u : ℕ) (hu : Odd u) (hpu : p - 1 = 2 ^ r * u)
    (s t : ℕ) (hs : s ≤ r) (ht : t ∣ u) (g : ZMod p) (hg : IsPrimitiveRoot g (p - 1))
    (hgi : g ^ (2 ^ s * t) = 2) :
    Function.Periodic (fun n : ℕ => (Nat.fermatNumber (r - s + n) : ZMod p))
        (orderOf (2 : ZMod (u / t))) ∧
      (∀ h < r - s, ¬ ∃ kp : ℕ, 0 < kp ∧
        Function.Periodic (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod p)) kp) ∧
      (∀ kp : ℕ, 0 < kp →
        Function.Periodic (fun n : ℕ => (Nat.fermatNumber (r - s + n) : ZMod p)) kp →
          orderOf (2 : ZMod (u / t)) ∣ kp)

/-- **Prime divisors of Fermat numbers and the order of $2$.** Write $F_n = 2^{2^n} + 1$ for the
$n$-th Fermat number. An odd prime $p$ divides $F_n$ if and only if the multiplicative order of
$2$ modulo $p$ equals $2^{n+1}$.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Lemma 17 (`jis-2025-25.8.7-lem-17`). -/
public theorem_wanted prime_dvd_fermatNumber_iff_orderOf_two (n p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    p ∣ Nat.fermatNumber n ↔ orderOf (2 : ZMod p) = 2 ^ (n + 1)

/-- **Prime divisors of Fermat numbers and the period of Fermat residues.** Write
$F_n = 2^{2^n} + 1$ for the $n$-th Fermat number. Let $p$ be an odd prime, let $h$ be a natural
number and let $k$ be a positive integer such that the sequence $n \mapsto F_{h+n} \bmod p$ is
periodic with period $k$ and every positive period of it is a multiple of $k$. Then $p$ divides
$F_n$ for some natural number $n$ if and only if $k = 1$.

Any such $h$ is at least the preperiod of $n \mapsto F_n \bmod p$, and $k$ is then the primitive
period of $n \mapsto F_n \bmod p$, which does not depend on $h$.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Proposition 18 (`jis-2025-25.8.7-prop-18`). -/
public theorem_wanted exists_prime_dvd_fermatNumber_iff_period_eq_one (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (h k : ℕ) (hk : 0 < k)
    (hper : Function.Periodic (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod p)) k)
    (hmin : ∀ kp : ℕ, 0 < kp →
      Function.Periodic (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod p)) kp → k ∣ kp) :
    (∃ n : ℕ, p ∣ Nat.fermatNumber n) ↔ k = 1

/-- **The power of $2$ dividing the order of $2$ modulo a prime.** Let $p$ be a prime and let
$\operatorname{ord}_p(2)$ be the multiplicative order of $2$ modulo $p$. If $p \equiv 7 \pmod 8$,
then $\operatorname{ord}_p(2)$ is odd. If $p \equiv 3 \pmod 8$, then $\operatorname{ord}_p(2)$ is
divisible by $2$ but not by $4$. If $p \equiv 5 \pmod 8$, then $\operatorname{ord}_p(2)$ is
divisible by $4$ but not by $8$.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Theorem 22, order statements (`jis-2025-25.8.7-thm-22`). -/
public theorem_wanted orderOf_two_twoAdic_of_mod_eight (p : ℕ) (hp : p.Prime) :
    (p % 8 = 7 → ¬ 2 ∣ orderOf (2 : ZMod p)) ∧
      (p % 8 = 3 → 2 ∣ orderOf (2 : ZMod p) ∧ ¬ 4 ∣ orderOf (2 : ZMod p)) ∧
      (p % 8 = 5 → 4 ∣ orderOf (2 : ZMod p) ∧ ¬ 8 ∣ orderOf (2 : ZMod p))

/-- **Every preperiod of Fermat residues occurs for a prime $p \equiv 1 \pmod 8$.** Write
$F_n = 2^{2^n} + 1$. For every natural number $v$ there is a prime $p \equiv 1 \pmod 8$ such that
the sequence $n \mapsto F_n \bmod p$ has preperiod exactly $v$: the sequence
$n \mapsto F_{v+n} \bmod p$ is periodic with some positive period, and for no $h < v$ is the
sequence $n \mapsto F_{h+n} \bmod p$ periodic with a positive period.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences 28
(2025), Article 25.8.7, Theorem 23 (`jis-2025-25.8.7-thm-23`). -/
public theorem_wanted exists_prime_one_mod_eight_fermat_preperiod (v : ℕ) :
    ∃ p : ℕ, p.Prime ∧ p % 8 = 1 ∧
      (∃ k : ℕ, 0 < k ∧
        Function.Periodic (fun n : ℕ => (Nat.fermatNumber (v + n) : ZMod p)) k) ∧
      ∀ h < v, ¬ ∃ kp : ℕ, 0 < kp ∧
        Function.Periodic (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod p)) kp

end

end MetaMathlibExt
