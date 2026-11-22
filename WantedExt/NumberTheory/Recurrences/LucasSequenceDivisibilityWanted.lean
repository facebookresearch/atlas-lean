/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.PrimitiveDivisor
public import MathlibExt.NumberTheory.Recurrences.LucasSequenceFirstKind
public import MathlibExt.NumberTheory.Recurrences.NondegenerateLucasPair
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Divisibility and parity lemmas for Lucas sequences

Statement-only requests from Lawrence Somer and Michal Křížek, *On Lucas and Frobenius
Pseudoprimes*, INTEGERS 25 (2025), Article A107. The Lucas sequences `U(P, Q)` and
`V(P, Q)` are `lucasU L` and `lucasV L` for `L : LucasSequenceParams` (so `Q ≠ 0`), with
`P = L.p`, `Q = L.q`, and discriminant `D = P² - 4Q`. By the source's Theorem 2.1, a pair
with `D > 0` is nondegenerate exactly when `P ≠ 0` and `Q ≠ 0`, so "nondegenerate with
`D > 0`" is the hypothesis pair `L.p ≠ 0`, `0 < L.p ^ 2 - 4 * L.q`. The source's
`U_{2m}/P` is the integer quotient `lucasU L (2 * m) / L.p`, exact by `P ∣ U_{2m}`.

The later statements use the source's rank of appearance (`lucasRankOfAppearance`), its
nondegeneracy (the canonical `IsNondegenerateLucasPair L.p L.q`), and its Section 3 pseudoprime
notions
(Lucas, second-kind, Dickson, Frobenius, Euler, Euler–Lucas, strong, and super pseudoprimes).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Doubling formula $U_{2n} = U_n V_n$ for Lucas sequences.** Let $P$ and $Q$ be integers with
$Q \ne 0$, and let $U$ and $V$ be the Lucas sequences $U(P, Q)$ and $V(P, Q)$. Then
$U_{2n} = U_n V_n$ for every natural number $n$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Proposition 2.3 (i) (`integers-2025-A107-prop-2-3`). -/
public theorem_wanted lucasU_two_mul_eq_lucasU_mul_lucasV
    (L : LucasSequenceParams) (n : ℕ) :
    lucasU L (2 * n) = lucasU L n * lucasV L n

/-- **Divisibility of Lucas sequences at divisible indices.** Let $U = U(P, Q)$ and
$V = V(P, Q)$ be the Lucas sequences with integer parameters $P$ and $Q \ne 0$, and let $m$ and
$n$ be natural numbers with $m \mid n$. Then $U_m \mid U_n$, and if moreover $n/m$ is odd, then
$V_m \mid V_n$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Proposition 2.3 (iii), (iv)
(`integers-2025-A107-prop-2-3`). -/
public theorem_wanted lucasU_dvd_and_lucasV_dvd_of_dvd
    (L : LucasSequenceParams) (m n : ℕ) (h : m ∣ n) :
    lucasU L m ∣ lucasU L n ∧ (Odd (n / m) → lucasV L m ∣ lucasV L n)

/-- **$P$ divides $U_{2n}$, and $V_n$ for odd $n$.** Let $P$ and $Q$ be integers with $Q \ne 0$,
and let $U$ and $V$ be the Lucas sequences $U(P, Q)$ and $V(P, Q)$. Then $P \mid U_{2n}$ for every
natural number $n$, and $P \mid V_n$ for every odd natural number $n$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Proposition 2.3 (v), (vi)
(`integers-2025-A107-prop-2-3`). -/
public theorem_wanted p_dvd_lucasU_two_mul_and_lucasV_of_odd
    (L : LucasSequenceParams) :
    (∀ n : ℕ, L.p ∣ lucasU L (2 * n)) ∧ ∀ n : ℕ, Odd n → L.p ∣ lucasV L n

/-- **Lucas sequences under negation of the first parameter.** For integers $P$ and $Q \ne 0$ and
every natural number $n$, the Lucas sequences $U$ and $V$ satisfy
$U_n(-P, Q) = (-1)^{n+1} U_n(P, Q)$ and $V_n(-P, Q) = (-1)^n V_n(P, Q)$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Proposition 2.3 (vii), (viii)
(`integers-2025-A107-prop-2-3`). -/
public theorem_wanted lucasU_lucasV_neg_p
    (L : LucasSequenceParams) (n : ℕ) :
    lucasU ⟨-L.p, L.q, L.q_ne_zero⟩ n = (-1) ^ (n + 1) * lucasU L n ∧
      lucasV ⟨-L.p, L.q, L.q_ne_zero⟩ n = (-1) ^ n * lucasV L n

/-- **Shift congruence for the Lucas recurrence.** Let $U = U(P, Q)$ be the Lucas sequence with
integer parameters $P$ and $Q \ne 0$, and let $(W_n)_{n \ge 0}$ be a sequence of integers with
$W_{n+2} = P W_{n+1} - Q W_n$ for every $n \ge 0$. If $t \ge 0$ and $m$ are integers with
$m \mid U_t$ and $\gcd(m, Q) = 1$, then $W_{n+t} \equiv U_{t+1} W_n \pmod{m}$ for every $n \ge 0$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 2.5 (`integers-2025-A107-lem-2-5`). -/
public theorem_wanted lucas_recurrence_add_modEq_of_dvd_lucasU
    (L : LucasSequenceParams) (W : ℕ → ℤ)
    (hW : ∀ n, W (n + 2) = L.p * W (n + 1) - L.q * W n)
    (t : ℕ) (m : ℤ) (ht : m ∣ lucasU L t) (hm : Int.gcd m L.q = 1) (n : ℕ) :
    W (n + t) ≡ lucasU L (t + 1) * W n [ZMOD m]

/-- **When $p^{i+1}$ divides $U_{2n}$, for a prime power $p^i$ exactly dividing $P$.** Let $P$ and
$Q$ be coprime integers with $Q \ne 0$, and let $U_n$ be the Lucas sequence $U(P, Q)$. Let $p$ be
a prime and $i \ge 1$ such that $p^i \mid P$ and $p^{i+1} \nmid P$. Then for every positive
integer $n$, $p^{i+1} \mid U_{2n}$ if and only if $p \mid n$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 2.6, first claim
(`integers-2025-A107-lem-2-6`). -/
public theorem_wanted prime_pow_succ_dvd_lucasU_two_mul_iff
    (L : LucasSequenceParams) (hcop : Int.gcd L.p L.q = 1)
    (p i : ℕ) (hp : p.Prime) (hi : 1 ≤ i)
    (hpi : (p : ℤ) ^ i ∣ L.p) (hpi' : ¬ (p : ℤ) ^ (i + 1) ∣ L.p)
    (n : ℕ) (hn : 0 < n) :
    (p : ℤ) ^ (i + 1) ∣ lucasU L (2 * n) ↔ p ∣ n

/-- **Coprimality of $U_{2n}/P$ and $P$.** Let $P$ and $Q$ be integers with $Q \ne 0$, $P \ne 0$
and $\gcd(P, Q) = 1$, and let $(U_n)$ be the Lucas sequence $U(P, Q)$. If $n$ is a positive
integer with $\gcd(n, P) = 1$, then $\gcd(U_{2n}/P, P) = 1$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 2.6, "in particular" claim
(`integers-2025-A107-lem-2-6`). -/
public theorem_wanted gcd_lucasU_two_mul_div_p_eq_one
    (L : LucasSequenceParams) (hcop : Int.gcd L.p L.q = 1) (hP : L.p ≠ 0)
    (n : ℕ) (hn : 0 < n) (hnP : Int.gcd n L.p = 1) :
    Int.gcd (lucasU L (2 * n) / L.p) L.p = 1

/-- **Lucas sequences modulo 2.** Let $U = U(P, Q)$ be the Lucas sequence with integer parameters
$P$ and $Q \ne 0$, let $D = P^2 - 4Q$, and suppose $2 \nmid \gcd(P, Q)$. Then $U$ is periodic
modulo $2$ from index $1$ on: there is $k > 0$ with $U_{n+k} \equiv U_n \pmod 2$ for every
$n \ge 1$. If $P$ is odd and $Q$ is even, then $U_n$ is odd for every $n \ge 1$. If $P$ is even
and $Q$ is odd, then for every $n \ge 0$, $2 \mid U_n$ if and only if $2 \mid n$; moreover
$2 \mid D$. If $P$ and $Q$ are both odd, then for every $n \ge 0$, $2 \mid U_n$ if and only if
$3 \mid n$.

The periodicity need not start at $n = 0$: for $P = 1$ and $Q = 2$, $U$ is $0, 1, 1, 1, \dots$
modulo $2$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 2.7 (`integers-2025-A107-lem-2-7`). -/
public theorem_wanted lucasU_mod_two
    (L : LucasSequenceParams) (h2 : ¬ 2 ∣ Int.gcd L.p L.q) :
    (∃ k : ℕ, 0 < k ∧ ∀ n, 1 ≤ n → lucasU L (n + k) ≡ lucasU L n [ZMOD 2]) ∧
      (Odd L.p → Even L.q → ∀ n, 1 ≤ n → ¬ 2 ∣ lucasU L n) ∧
      (Even L.p → Odd L.q →
        (∀ n, 2 ∣ lucasU L n ↔ 2 ∣ n) ∧ 2 ∣ L.p ^ 2 - 4 * L.q) ∧
      (Odd L.p → Odd L.q → ∀ n, 2 ∣ lucasU L n ↔ 3 ∣ n)

/-- **Lucas sequences modulo 3.** Let $U = U(P, Q)$ be the Lucas sequence with integer parameters
$P$ and $Q \ne 0$, let $D = P^2 - 4Q$, and suppose $3 \nmid \gcd(P, Q)$. Then $U$ is periodic
modulo $3$ from index $1$ on: there is $k > 0$ with $U_{n+k} \equiv U_n \pmod 3$ for every
$n \ge 1$. If $3 \mid Q$, then $3 \nmid U_n$ for every $n \ge 1$. If $3 \mid P$, then for every
$n \ge 0$, $3 \mid U_n$ if and only if $2 \mid n$. If $3 \nmid P$ and $Q \equiv -1 \pmod 3$,
then for every $n \ge 0$, $3 \mid U_n$ if and only if $4 \mid n$. If $3 \nmid P$ and
$Q \equiv 1 \pmod 3$, then for every $n \ge 0$, $3 \mid U_n$ if and only if $3 \mid n$; moreover
$3 \mid D$.

The periodicity need not start at $n = 0$: for $P = 1$ and $Q = 3$, $U$ is $0, 1, 1, 1, \dots$
modulo $3$. The source's values $\rho(3) = 2, 4, 3$ of the rank of apparition are the least
positive indices these equivalences give.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 2.8 (`integers-2025-A107-lem-2-8`). -/
public theorem_wanted lucasU_mod_three
    (L : LucasSequenceParams) (h3 : ¬ 3 ∣ Int.gcd L.p L.q) :
    (∃ k : ℕ, 0 < k ∧ ∀ n, 1 ≤ n → lucasU L (n + k) ≡ lucasU L n [ZMOD 3]) ∧
      (3 ∣ L.q → ∀ n, 1 ≤ n → ¬ 3 ∣ lucasU L n) ∧
      (3 ∣ L.p → ∀ n, 3 ∣ lucasU L n ↔ 2 ∣ n) ∧
      (¬ 3 ∣ L.p → L.q ≡ -1 [ZMOD 3] → ∀ n, 3 ∣ lucasU L n ↔ 4 ∣ n) ∧
      (¬ 3 ∣ L.p → L.q ≡ 1 [ZMOD 3] →
        (∀ n, 3 ∣ lucasU L n ↔ 3 ∣ n) ∧ 3 ∣ L.p ^ 2 - 4 * L.q)

/-- **Growth and positivity of Lucas sequences with positive discriminant.** Let $P, Q$ be
integers with $P \neq 0$, $Q \neq 0$ and $D = P^2 - 4Q > 0$, and let $U = U(P, Q)$ and
$V = V(P, Q)$ be the Lucas sequences. Then $|U_n| < |U_{n+1}|$ for every $n \ge 2$ and
$|V_n| < |V_{n+1}|$ for every $n \ge 1$; if $P > 0$, then $U_n > 0$ for every $n \ge 1$ and
$V_n > 0$ for every $n \ge 0$; and $|U_3| \ge 3$ unless $|P| = 1$ and $Q = -1$.

When $Q \neq 0$ and $D > 0$, the condition $P \neq 0$ is equivalent to the pair $(P, Q)$ being
nondegenerate (Theorem 2.1 of the source).

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 2.9 (`integers-2025-A107-lem-2-9`). -/
public theorem_wanted lucas_abs_strictMono_of_discr_pos
    (L : LucasSequenceParams) (hP : L.p ≠ 0) (hD : 0 < L.p ^ 2 - 4 * L.q) :
    (∀ n, 2 ≤ n → |lucasU L n| < |lucasU L (n + 1)|) ∧
      (∀ n, 1 ≤ n → |lucasV L n| < |lucasV L (n + 1)|) ∧
      (0 < L.p → (∀ n, 1 ≤ n → 0 < lucasU L n) ∧ ∀ n, 0 < lucasV L n) ∧
      (¬ (|L.p| = 1 ∧ L.q = -1) → 3 ≤ |lucasU L 3|)

/-- **$U_n$ divides none of $U_1, \dots, U_{n-1}$.** Let $P$ and $Q$ be integers with $P \ne 0$,
$Q \ne 0$ and $D = P^2 - 4Q > 0$, and let $U_n$ be the Lucas sequence $U(P, Q)$. Then for every
$n \ge 3$ and every $k$ with $0 < k < n$, $U_n$ does not divide $U_k$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Corollary 2.10 (`integers-2025-A107-cor-2-10`). -/
public theorem_wanted not_lucasU_dvd_lucasU_of_lt
    (L : LucasSequenceParams) (hP : L.p ≠ 0) (hD : 0 < L.p ^ 2 - 4 * L.q)
    (n : ℕ) (hn : 3 ≤ n) (k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    ¬ lucasU L n ∣ lucasU L k

/-- **Common divisors of $P$ and the discriminant.** Let $P$ and $Q$ be coprime integers and let
$D = P^2 - 4Q$. Then $\gcd(P, D)$ divides $4$, and $\gcd(P, D') = 1$ for every odd integer $D'$
dividing $D$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 4.9 (`integers-2025-A107-lem-4-9`). -/
public theorem_wanted gcd_p_discr_dvd_four
    (P Q : ℤ) (hcop : Int.gcd P Q = 1) :
    (Int.gcd P (P ^ 2 - 4 * Q) : ℤ) ∣ 4 ∧
      ∀ D' : ℤ, Odd D' → D' ∣ P ^ 2 - 4 * Q → Int.gcd P D' = 1

/-- **Parity of $U_m$ and $U_{2m}/P$ and their coprimality to $D$.** Let $P$ and $Q$ be coprime
integers with $P \ne 0$ and $Q \ne 0$, let $U_n$ be the Lucas sequence $U(P, Q)$, and let
$D = P^2 - 4Q$. Let $m$ be an odd natural number with $\gcd(m, PQD) = 1$, and with $3 \nmid m$ if
$P$ and $Q$ are both odd. Then $U_m$ and $U_{2m}/P$ are odd, and each of them is coprime to $D$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 4.10 (`integers-2025-A107-lem-4-10`). -/
public theorem_wanted odd_lucasU_coprime_discr
    (L : LucasSequenceParams) (hcop : Int.gcd L.p L.q = 1) (hP : L.p ≠ 0)
    (m : ℕ) (hm : Odd m) (hmc : Int.gcd m (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1)
    (h3 : Odd L.p → Odd L.q → ¬ 3 ∣ m) :
    Odd (lucasU L m) ∧ Odd (lucasU L (2 * m) / L.p) ∧
      Int.gcd (lucasU L m) (L.p ^ 2 - 4 * L.q) = 1 ∧
      Int.gcd (lucasU L (2 * m) / L.p) (L.p ^ 2 - 4 * L.q) = 1

/-- **Composite terms of Lucas sequences with positive discriminant.** Let $U = U(P, Q)$ be the
Lucas sequence with integer parameters $P \ne 0$ and $Q \ne 0$ such that $\gcd(P, Q) = 1$ and
$D = P^2 - 4Q > 0$, and let $m \ge 5$ be an odd integer. If $m$ is not prime, then $U_m$ is
composite; and $U_{2m}/P$ is always composite. Here an integer $N$ is composite when $|N| > 1$
and $|N|$ is not prime.

Since $D > 0$, the conditions $P \ne 0$ and $Q \ne 0$ say that $U$ is nondegenerate. The quotient
$U_{2m}/P$ is an integer because $P \mid U_{2m}$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Corollary 4.2 (`integers-2025-A107-cor-4-2`). -/
public theorem_wanted lucasU_composite_of_discr_pos
    (L : LucasSequenceParams) (hcop : Int.gcd L.p L.q = 1) (hP : L.p ≠ 0)
    (hD : 0 < L.p ^ 2 - 4 * L.q) (m : ℕ) (hm5 : 5 ≤ m) (hm : Odd m) :
    (¬ m.Prime → 1 < (lucasU L m).natAbs ∧ ¬ (lucasU L m).natAbs.Prime) ∧
      (1 < (lucasU L (2 * m) / L.p).natAbs ∧ ¬ (lucasU L (2 * m) / L.p).natAbs.Prime)

/-- **Pseudoprime candidates from a Lucas sequence.** Let $U = U(P, Q)$ be the Lucas sequence with
integer parameters $P \ne 0$ and $Q \ne 0$ such that $\gcd(P, Q) = 1$ and $D = P^2 - 4Q > 0$.
Let $m > 1$ be an odd integer with $\gcd(m, PQD) = 1$, and assume $3 \nmid m$ when $P$ and $Q$
are both odd. Put $N_1 = U_m$ and $N_2 = U_{2m}/P$. Then $N_1$ and $N_2$ are positive and odd,
and $\gcd(N_1 N_2, PQD) = 1$. If $m$ is not prime, then $N_1$ and $N_2$ are composite, that is,
$|N_i| > 1$ and $|N_i|$ is not prime for $i = 1, 2$. If $P$ is odd, or $P \equiv 0 \pmod 4$ and
$Q \equiv -1 \pmod 4$, or $P \equiv 2 \pmod 4$ and $Q \equiv -1 \pmod 8$, then the Jacobi
symbols satisfy $(D/m) = (D/|N_1|) = (D/|N_2|)$.

Since $D > 0$, the conditions $P \ne 0$ and $Q \ne 0$ say that $U$ is nondegenerate. The quotient
$U_{2m}/P$ is an integer because $P \mid U_{2m}$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 6.1 (`integers-2025-A107-lem-6-1`). -/
public theorem_wanted lucasU_pseudoprime_candidates_jacobiSym
    (L : LucasSequenceParams) (hcop : Int.gcd L.p L.q = 1) (hP : L.p ≠ 0)
    (hD : 0 < L.p ^ 2 - 4 * L.q) (m : ℕ) (hm1 : 1 < m) (hm : Odd m)
    (hmc : Int.gcd m (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1)
    (h3 : Odd L.p → Odd L.q → ¬ 3 ∣ m) :
    0 < lucasU L m ∧ 0 < lucasU L (2 * m) / L.p ∧
      Odd (lucasU L m) ∧ Odd (lucasU L (2 * m) / L.p) ∧
      Int.gcd (lucasU L m * (lucasU L (2 * m) / L.p))
        (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
      (¬ m.Prime →
        (1 < (lucasU L m).natAbs ∧ ¬ (lucasU L m).natAbs.Prime) ∧
          (1 < (lucasU L (2 * m) / L.p).natAbs ∧
            ¬ (lucasU L (2 * m) / L.p).natAbs.Prime)) ∧
      (Odd L.p ∨ (L.p ≡ 0 [ZMOD 4] ∧ L.q ≡ -1 [ZMOD 4]) ∨
          (L.p ≡ 2 [ZMOD 4] ∧ L.q ≡ -1 [ZMOD 8]) →
        jacobiSym (L.p ^ 2 - 4 * L.q) m =
            jacobiSym (L.p ^ 2 - 4 * L.q) (lucasU L m).natAbs ∧
          jacobiSym (L.p ^ 2 - 4 * L.q) m =
            jacobiSym (L.p ^ 2 - 4 * L.q) (lucasU L (2 * m) / L.p).natAbs)


/-- **Classification of degenerate Lucas sequences.** Let $P, Q$ be integers, let
$\alpha, \beta \in \mathbb{C}$ satisfy $\alpha + \beta = P$ and $\alpha\beta = Q$ (so they are the
roots of $x^2 - Px + Q$), and let $D = P^2 - 4Q$. Let $(u_n)$ be the Lucas sequence of the first
kind with parameters $P, Q$, and let $(v_n)$ be the integer sequence with $v_0 = 2$, $v_1 = P$ and
$v_{n+2} = P v_{n+1} - Q v_n$ for all $n$. Suppose that $Q = 0$ or that $\alpha/\beta$ is a root
of unity. Then either (i) $Q = 0$, $D = P^2$, and $u_n = P^{n-1}$ and $v_n = P^n$ for every
$n \ge 1$; or there is a nonzero integer $M$ such that one of the following holds:
(ii) $\alpha/\beta = 1$, $P = 2M$, $Q = M^2$ and $D = 0$;
(iii) $\alpha/\beta = -1$, $P = 0$, $Q = M$ and $D = -4M$;
(iv) $\alpha/\beta$ is a primitive cube root of unity, $P = M$, $Q = M^2$ and $D = -3M^2$;
(v) $\alpha/\beta$ is a primitive fourth root of unity, $P = 2M$, $Q = 2M^2$ and $D = -4M^2$;
(vi) $\alpha/\beta$ is a primitive sixth root of unity, $P = 3M$, $Q = 3M^2$ and $D = -3M^2$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 2.1 (`integers-2025-A107-thm-2-1`). -/
public theorem_wanted lucas_degenerate_cases (P Q : ℤ) (α β : ℂ) (hsum : α + β = P)
    (hprod : α * β = Q) (u v : ℕ → ℤ) (hu : IsLucasSequenceFirstKind P Q u)
    (hv0 : v 0 = 2) (hv1 : v 1 = P) (hv : ∀ n, v (n + 2) = P * v (n + 1) - Q * v n)
    (hdeg : Q = 0 ∨ IsOfFinOrder (α / β)) :
    (Q = 0 ∧ P ^ 2 - 4 * Q = P ^ 2 ∧ ∀ n : ℕ, 1 ≤ n → u n = P ^ (n - 1) ∧ v n = P ^ n) ∨
    ∃ M : ℤ, M ≠ 0 ∧
      ((α / β = 1 ∧ P = 2 * M ∧ Q = M ^ 2 ∧ P ^ 2 - 4 * Q = 0) ∨
       (α / β = -1 ∧ P = 0 ∧ Q = M ∧ P ^ 2 - 4 * Q = -4 * M) ∨
       (IsPrimitiveRoot (α / β) 3 ∧ P = M ∧ Q = M ^ 2 ∧ P ^ 2 - 4 * Q = -3 * M ^ 2) ∨
       (IsPrimitiveRoot (α / β) 4 ∧ P = 2 * M ∧ Q = 2 * M ^ 2 ∧ P ^ 2 - 4 * Q = -4 * M ^ 2) ∨
       (IsPrimitiveRoot (α / β) 6 ∧ P = 3 * M ∧ Q = 3 * M ^ 2 ∧ P ^ 2 - 4 * Q = -3 * M ^ 2))

/-! ### Rank of appearance and the pseudoprime notions of Section 3

The definitions below follow Section 2 and Definitions 3.1–3.13 of the source. -/

/-- **Rank of appearance in a Lucas sequence.** Let $U = U(P, Q)$ be the Lucas sequence with
integer parameters $P$ and $Q \ne 0$. The rank of appearance $\rho(m)$ of a natural number $m$ in
$U$ is the least positive integer $r$ with $m \mid U_r$; when no positive $r$ has $m \mid U_r$,
$\rho(m) = 0$.

When $m \ge 1$ and $\gcd(m, Q) = 1$, such an $r$ always exists (the source defines $\rho(m)$ only
in this case); it can also exist when $\gcd(m, Q) \ne 1$. For $m = 0$ it need not exist even when
$\gcd(0, Q) = |Q| = 1$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Section 2. -/
public noncomputable def lucasRankOfAppearance (L : LucasSequenceParams) (m : ℕ) : ℕ :=
  sInf {r : ℕ | 0 < r ∧ (m : ℤ) ∣ lucasU L r}

/-- **Rank of appearance is at most any positive index of divisibility.** Let $P, Q$ be integers
with $Q \neq 0$, let $U = U(P, Q)$ be the Lucas sequence, and write $\rho(m)$ for the rank of
appearance of a natural number $m$ in $U$. If $r > 0$ and $m \mid U_r$, then $\rho(m) \le r$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Section 2 (definition of `ρ` as a least index). -/
public theorem lucasRankOfAppearance_le_of_dvd (L : LucasSequenceParams) {m r : ℕ}
    (hr : 0 < r) (hm : (m : ℤ) ∣ lucasU L r) : lucasRankOfAppearance L m ≤ r :=
  Nat.sInf_le ⟨hr, hm⟩

/-- **The rank of appearance in a Lucas sequence is attained.** Let $U = U(P, Q)$ be a Lucas
sequence and $m$ a natural number. If $m \mid U_r$ for some positive integer $r$, then the rank of
appearance $\rho(m)$ of $m$ in $U$ is positive and $m \mid U_{\rho(m)}$.

Together with the bound $\rho(m) \le r$ for every positive $r$ with $m \mid U_r$, this makes
$\rho(m)$ the least such index.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Section 2 (definition of `ρ` as a least index). -/
public theorem lucasRankOfAppearance_spec (L : LucasSequenceParams) {m : ℕ}
    (h : ∃ r, 0 < r ∧ (m : ℤ) ∣ lucasU L r) :
    0 < lucasRankOfAppearance L m ∧ (m : ℤ) ∣ lucasU L (lucasRankOfAppearance L m) :=
  Nat.sInf_mem h

/-- **Rank of appearance of $1$.** For all integers $P, Q$ with $Q \neq 0$, the rank of
appearance of $1$ in the Lucas sequence $U(P, Q)$ is $1$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Section 2 (definition of `ρ`). -/
public theorem lucasRankOfAppearance_one (L : LucasSequenceParams) :
    lucasRankOfAppearance L 1 = 1 := by
  have hmem : (1 : ℕ) ∈ {r : ℕ | 0 < r ∧ ((1 : ℕ) : ℤ) ∣ lucasU L r} :=
    ⟨Nat.one_pos, by simp⟩
  exact le_antisymm (Nat.sInf_le hmem) (Nat.sInf_mem ⟨1, hmem⟩).1

/-- **Index of the Lucas pseudoprime congruences.** Let $P, Q$ be integers with $Q \neq 0$ and
$D = P^2 - 4Q$. For a natural number $N$, the index is $N - (D/N)$, where $(D/N)$ is the Jacobi
symbol, replaced by $0$ when this difference is negative. For $N > 1$ the difference is positive.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, congruences (3.1), (3.4). -/
public def lucasPseudoprimeIndex (L : LucasSequenceParams) (N : ℕ) : ℕ :=
  ((N : ℤ) - jacobiSym (L.p ^ 2 - 4 * L.q) N).toNat

/-- **Lucas pseudoprimes.** Let $P, Q$ be integers with $Q \neq 0$, let $U_n$ be the Lucas
sequence of $(P, Q)$ and let $D = P^2 - 4Q$. A natural number $N$ is a Lucas pseudoprime with
parameters $P, Q$ if $N$ is odd and composite, $\gcd(N, QD) = 1$ and $N$ divides
$U_{N - (D/N)}$, where $(D/N)$ is the Jacobi symbol.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.1. -/
public def IsLucasPseudoprime (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
    (N : ℤ) ∣ lucasU L (lucasPseudoprimeIndex L N)

/-- **Lucas pseudoprimes of the second kind.** Let $P, Q$ be integers with $Q \neq 0$, let $U_n$
be the Lucas sequence of $(P, Q)$ and let $D = P^2 - 4Q$. A natural number $N$ is a Lucas
pseudoprime of the second kind with parameters $P, Q$ if $N$ is odd and composite,
$\gcd(N, QD) = 1$ and $U_N \equiv (D/N) \pmod{N}$, where $(D/N)$ is the Jacobi symbol.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.2. -/
public def IsLucasPseudoprimeSecondKind (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
    lucasU L N ≡ jacobiSym (L.p ^ 2 - 4 * L.q) N [ZMOD N]

/-- **Dickson pseudoprimes.** Let $P$ and $Q \ne 0$ be integers with discriminant
$D = P^2 - 4Q$, and let $(V_n)$ be the companion Lucas sequence $V(P, Q)$. A natural number $N$
is a Dickson pseudoprime with parameters $P$ and $Q$ if $N$ is odd, $N > 1$, $N$ is not prime,
$\gcd(N, QD) = 1$, and $V_N \equiv P \pmod N$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.3. -/
public def IsDicksonPseudoprime (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
    lucasV L N ≡ L.p [ZMOD N]

/-- **Dickson pseudoprimes of the second kind.** Let $P$ and $Q \ne 0$ be integers with
discriminant $D = P^2 - 4Q$, and let $(V_n)$ be the companion Lucas sequence $V(P, Q)$. A
natural number $N$ is a Dickson pseudoprime of the second kind with parameters $P$ and $Q$ if
$N$ is odd, $N > 1$, $N$ is not prime, $\gcd(N, QD) = 1$, and
$V_{N - (D/N)} \equiv 2Q^{(1 - (D/N))/2} \pmod N$, where $(D/N)$ is the Jacobi symbol.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.4. -/
public def IsDicksonPseudoprimeSecondKind (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
    lucasV L (lucasPseudoprimeIndex L N) ≡
      2 * L.q ^ ((1 - jacobiSym (L.p ^ 2 - 4 * L.q) N) / 2).toNat [ZMOD N]

/-- **Frobenius pseudoprime for Lucas parameters.** Let $U$ and $V$ be the Lucas sequences with
integer parameters $P$ and $Q \neq 0$, and let $D = P^2 - 4Q$. A natural number $N$ is a
Frobenius pseudoprime with parameters $P, Q$ when $\gcd(N, PQD) = 1$ and $N$ is a Lucas
pseudoprime, a Lucas pseudoprime of the second kind, a Dickson pseudoprime and a Dickson
pseudoprime of the second kind with parameters $P, Q$. Equivalently, $\gcd(N, PQD) = 1$, $N$ is
odd and composite, and, writing $\varepsilon = (D/N)$ for the Jacobi symbol, $N$ satisfies the
congruences $U_{N-\varepsilon} \equiv 0$, $U_N \equiv \varepsilon$, $V_N \equiv P$ and
$V_{N-\varepsilon} \equiv 2Q^{(1-\varepsilon)/2}$ modulo $N$.

This is the notion of the source, not Grantham's Frobenius pseudoprime defined through quotient
rings of polynomials.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.5. -/
public def IsLucasFrobeniusPseudoprime (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Int.gcd N (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧ IsLucasPseudoprime L N ∧
    IsLucasPseudoprimeSecondKind L N ∧ IsDicksonPseudoprime L N ∧
      IsDicksonPseudoprimeSecondKind L N

/-- **Euler pseudoprime.** Let $a$ be an integer. A natural number $N$ is an Euler pseudoprime to
the base $a$ when $N$ is odd and composite, $\gcd(a, N) = 1$, and
$a^{(N-1)/2} \equiv (a/N) \pmod N$, where $(a/N)$ is the Jacobi symbol.

The source states the definition for positive odd $a$ and applies it to the base $Q$ (for
example $Q = -1$ in Remark 3.8); here $a$ is any integer.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.7. -/
public def IsEulerPseudoprime (a : ℤ) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd a N = 1 ∧ a ^ ((N - 1) / 2) ≡ jacobiSym a N [ZMOD N]

/-- **Euler–Lucas pseudoprime.** Let $U$ and $V$ be the Lucas sequences with integer parameters
$P$ and $Q \neq 0$, and let $D = P^2 - 4Q$. A natural number $N$ is an Euler–Lucas pseudoprime
with parameters $P, Q$ when $N$ is odd and composite, $\gcd(N, QD) = 1$, and, writing
$\varepsilon = (D/N)$ for the Jacobi symbol, $N \mid U_{(N-\varepsilon)/2}$ if the Jacobi symbol
$(Q/N)$ equals $1$, and $N \mid V_{(N-\varepsilon)/2}$ if $(Q/N) = -1$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.9. -/
public def IsEulerLucasPseudoprime (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
    (jacobiSym L.q N = 1 → (N : ℤ) ∣ lucasU L (lucasPseudoprimeIndex L N / 2)) ∧
    (jacobiSym L.q N = -1 → (N : ℤ) ∣ lucasV L (lucasPseudoprimeIndex L N / 2))

/-- **Strong Lucas pseudoprimes.** Let $P, Q$ be integers with $Q \neq 0$, let $U_n$ and $V_n$ be
the Lucas sequences of $(P, Q)$ and let $D = P^2 - 4Q$. A natural number $N$ is a strong Lucas
pseudoprime with parameters $P, Q$ if $N$ is odd and composite, $\gcd(N, QD) = 1$, and, writing
$N - (D/N) = 2^s d$ with $d$ odd, where $(D/N)$ is the Jacobi symbol, either $N \mid U_d$ or
$N \mid V_{2^r d}$ for some $r$ with $0 \le r < s$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.10. -/
public def IsStrongLucasPseudoprime (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
    ∃ s d : ℕ, Odd d ∧ lucasPseudoprimeIndex L N = 2 ^ s * d ∧
      ((N : ℤ) ∣ lucasU L d ∨ ∃ r < s, (N : ℤ) ∣ lucasV L (2 ^ r * d))

/-- **Super pseudoprime.** Let $P, Q$ be integers with $Q \neq 0$, let $D = P^2 - 4Q$, and let $S$
be a property of natural numbers. A natural number $N$ is a super pseudoprime of type $S$ with
parameters $(P, Q)$ when $N$ is odd, $N > 1$, $N$ is not prime, $\gcd(N, QD) = 1$, and every
divisor $d > 1$ of $N$ is prime or has property $S$.

Taking for $S$ the property of being a Lucas, strong Lucas or Frobenius pseudoprime with
parameters $(P, Q)$ gives the super Lucas, super strong Lucas and super Frobenius pseudoprimes.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.13. -/
public def IsSuperPseudoprime (L : LucasSequenceParams) (S : ℕ → Prop) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
    ∀ d : ℕ, d ∣ N → 1 < d → d.Prime ∨ S d

/-- **$9$ is a Lucas pseudoprime for $(P, Q) = (1, 5)$.** The number $9$ is a Lucas pseudoprime
with parameters $P = 1$ and $Q = 5$.

Here the discriminant is $D = P^2 - 4Q = -19$, the Jacobi symbol $(D/9)$ is $1$, and $9$
divides $U_8 = -279$, where $U_n$ is the Lucas sequence of $(1, 5)$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.1 (example). -/
public theorem isLucasPseudoprime_one_five_nine :
    IsLucasPseudoprime ⟨1, 5, by decide⟩ 9 := by
  have hj : jacobiSym ((1 : ℤ) ^ 2 - 4 * 5) 9 = 1 := by norm_num
  refine ⟨by decide, by norm_num, by norm_num, by decide, ?_⟩
  simp only [lucasPseudoprimeIndex, hj]
  decide

/-- **$9$ is a strong Lucas pseudoprime for $(P, Q) = (1, 5)$.** The number $9$ is a strong
Lucas pseudoprime with parameters $P = 1$ and $Q = 5$.

Here $D = P^2 - 4Q = -19$, the Jacobi symbol $(D/9)$ is $1$, $9 - (D/9) = 8 = 2^3 \cdot 1$, and
$9$ divides $V_2 = -9$, where $V_n$ is the companion Lucas sequence of $(1, 5)$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.10 (example). -/
public theorem isStrongLucasPseudoprime_one_five_nine :
    IsStrongLucasPseudoprime ⟨1, 5, by decide⟩ 9 := by
  have hj : jacobiSym ((1 : ℤ) ^ 2 - 4 * 5) 9 = 1 := by norm_num
  refine ⟨by decide, by norm_num, by norm_num, by decide, 3, 1, odd_one, ?_,
    Or.inr ⟨1, by norm_num, by decide⟩⟩
  simp only [lucasPseudoprimeIndex, hj]
  decide

/-- **9 is an Euler–Lucas pseudoprime for P = 1, Q = 5.** For the Lucas sequences $U$ and $V$
with parameters $P = 1$ and $Q = 5$, the number $9$ is an Euler–Lucas pseudoprime.

Here $D = P^2 - 4Q = -19$, the Jacobi symbols $(D/9)$ and $(5/9)$ both equal $1$, and $U_4 = -9$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.9 (example). -/
public theorem isEulerLucasPseudoprime_one_five_nine :
    IsEulerLucasPseudoprime ⟨1, 5, by decide⟩ 9 := by
  have hj : jacobiSym ((1 : ℤ) ^ 2 - 4 * 5) 9 = 1 := by norm_num
  have hq : jacobiSym (5 : ℤ) 9 = 1 := by norm_num
  refine ⟨by decide, by norm_num, by norm_num, by decide, fun _ => ?_, fun h => ?_⟩
  · simp only [lucasPseudoprimeIndex, hj]
    decide
  · simp only [hq] at h
    norm_num at h

/-- **9 is a Frobenius pseudoprime for P = 4, Q = -1.** For the Lucas sequences with parameters
$P = 4$ and $Q = -1$, so that $D = P^2 - 4Q = 20$, the number $9$ is a Frobenius pseudoprime.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.5 (example). -/
public theorem isLucasFrobeniusPseudoprime_four_neg_one_nine :
    IsLucasFrobeniusPseudoprime ⟨4, -1, by decide⟩ 9 := by
  have hj : jacobiSym ((4 : ℤ) ^ 2 - 4 * (-1)) 9 = 1 := by norm_num
  refine ⟨by decide, ⟨by decide, by norm_num, by norm_num, by decide, ?_⟩,
    ⟨by decide, by norm_num, by norm_num, by decide, ?_⟩,
    ⟨by decide, by norm_num, by norm_num, by decide, by decide⟩,
    ⟨by decide, by norm_num, by norm_num, by decide, ?_⟩⟩ <;>
  simp only [lucasPseudoprimeIndex, hj] <;> decide

set_option exponentiation.threshold 300 in
/-- **561 is an Euler pseudoprime to the base 2.** The composite number $561 = 3 \cdot 11 \cdot 17$
is an Euler pseudoprime to the base $2$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.7 (example). -/
public theorem isEulerPseudoprime_two_561 : IsEulerPseudoprime 2 561 := by
  have hj : jacobiSym 2 561 = 1 := by norm_num
  refine ⟨by decide, by norm_num, by norm_num, by decide, ?_⟩
  rw [hj]
  decide

/-- **$9$ is a super Lucas pseudoprime for $(P, Q) = (1, 5)$.** The number $9$ is a super Lucas
pseudoprime with parameters $P = 1$, $Q = 5$: its divisors greater than $1$ are $3$, a prime, and
$9$, a Lucas pseudoprime with these parameters.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.13 (example). -/
public theorem isSuperPseudoprime_one_five_nine :
    IsSuperPseudoprime ⟨1, 5, by decide⟩ (IsLucasPseudoprime ⟨1, 5, by decide⟩) 9 := by
  refine ⟨by decide, by norm_num, by norm_num, by decide, fun d hd hd1 => ?_⟩
  have hle : d ≤ 9 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d
  all_goals first
    | (left; norm_num; done)
    | (right; exact isLucasPseudoprime_one_five_nine)
    | (exfalso; revert hd; norm_num)

/-! ### Statements -/

/-- **Properties of the rank of appearance in a Lucas sequence.** Let $U = U(P, Q)$ be the Lucas
sequence with integer parameters $P$ and $Q \ne 0$, let $D = P^2 - 4Q$, let $\rho(m)$ be the rank
of appearance of $m$ in $U$, and write $(a/n)$ for the Jacobi symbol. Let $r$ and $s$ range over
positive integers and $p$ over primes. Then:
(i) if $\gcd(r, Q) = 1$, then $r \mid U_s$ if and only if $\rho(r) \mid s$;
(ii) if $p$ is odd and $p \nmid Q$, then $p \mid U_{p - (D/p)}$;
(iii) if $p \mid D$ and $p \nmid Q$, then $\rho(p) = p$;
(iv) if $p \nmid 2QD$, then $p \mid U_{(p - (D/p))/2}$ if and only if $(Q/p) = 1$;
(v) if $p$ is odd, $p \nmid Q$, and $k \ge 0$ satisfies $\rho(p^k) = \rho(p)$ and
$\rho(p^{k+1}) \ne \rho(p)$, then $\rho(p^j) = p^{\max(j - k, 0)} \rho(p)$ for every $j \ge 1$;
(vi) if $\gcd(rs, Q) = 1$ and $r \mid s$, then $\rho(r) \mid \rho(s)$;
(vii) if $\gcd(P, Q) = 1$, then $\gcd(U_r, U_s) = |U_{\gcd(r, s)}|$;
(viii) if $\gcd(r, s) = 1$ and $\gcd(rs, Q) = 1$, then
$\rho(rs) = \operatorname{lcm}(\rho(r), \rho(s))$;
(ix) if $\gcd(P, Q) = 1$ and $p \mid Q$, then $p \nmid U_n$ for every $n \ge 1$;
(x) if $\gcd(P, Q) = 1$, $p$ is odd and $p \nmid Q$, then $p \equiv (D/p) \pmod{\rho(p)}$.

Part (v) fails for $p = 2$: for $(P, Q) = (1, -1)$ one has $\rho(2) = 3$, $\rho(4) = 6$ and
$\rho(8) = 6 \ne 12$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 2.4 (`integers-2025-A107-thm-2-4`). -/
public theorem_wanted lucasRankOfAppearance_properties (L : LucasSequenceParams) :
    (∀ r s : ℕ, 0 < r → 0 < s → Int.gcd r L.q = 1 →
      ((r : ℤ) ∣ lucasU L s ↔ lucasRankOfAppearance L r ∣ s)) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ L.q →
      (p : ℤ) ∣ lucasU L ((p : ℤ) - jacobiSym (L.p ^ 2 - 4 * L.q) p).toNat) ∧
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ L.p ^ 2 - 4 * L.q → ¬ (p : ℤ) ∣ L.q →
      lucasRankOfAppearance L p = p) ∧
    (∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ 2 * L.q * (L.p ^ 2 - 4 * L.q) →
      ((p : ℤ) ∣ lucasU L (((p : ℤ) - jacobiSym (L.p ^ 2 - 4 * L.q) p).toNat / 2) ↔
        jacobiSym L.q p = 1)) ∧
    (∀ p k : ℕ, p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ L.q →
      lucasRankOfAppearance L (p ^ k) = lucasRankOfAppearance L p →
      lucasRankOfAppearance L (p ^ (k + 1)) ≠ lucasRankOfAppearance L p →
      ∀ j : ℕ, 1 ≤ j →
        lucasRankOfAppearance L (p ^ j) = p ^ (j - k) * lucasRankOfAppearance L p) ∧
    (∀ r s : ℕ, 0 < r → 0 < s → Int.gcd ((r * s : ℕ) : ℤ) L.q = 1 → r ∣ s →
      lucasRankOfAppearance L r ∣ lucasRankOfAppearance L s) ∧
    (Int.gcd L.p L.q = 1 → ∀ r s : ℕ, 0 < r → 0 < s →
      (Int.gcd (lucasU L r) (lucasU L s) : ℤ) = |lucasU L (Nat.gcd r s)|) ∧
    (∀ r s : ℕ, 0 < r → 0 < s → Nat.gcd r s = 1 → Int.gcd ((r * s : ℕ) : ℤ) L.q = 1 →
      lucasRankOfAppearance L (r * s) =
        Nat.lcm (lucasRankOfAppearance L r) (lucasRankOfAppearance L s)) ∧
    (Int.gcd L.p L.q = 1 → ∀ p : ℕ, p.Prime → (p : ℤ) ∣ L.q →
      ∀ n : ℕ, 1 ≤ n → ¬ (p : ℤ) ∣ lucasU L n) ∧
    (Int.gcd L.p L.q = 1 → ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ L.q →
      (p : ℤ) ≡ jacobiSym (L.p ^ 2 - 4 * L.q) p [ZMOD lucasRankOfAppearance L p])

/-- **Strong Lucas pseudoprimes are Euler–Lucas pseudoprimes.** Let $P$ and $Q \ne 0$ be
integers. Every strong Lucas pseudoprime with parameters $P$ and $Q$ is an Euler–Lucas
pseudoprime with parameters $P$ and $Q$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 3.12 (`integers-2025-A107-thm-3-12`). -/
public theorem_wanted isEulerLucasPseudoprime_of_isStrongLucasPseudoprime
    (L : LucasSequenceParams) (N : ℕ) (h : IsStrongLucasPseudoprime L N) :
    IsEulerLucasPseudoprime L N

/-- **Strong Lucas pseudoprimes via the $2$-adic valuation of ranks.** Let $P, Q$ be integers
such that the Lucas pair $(P, Q)$ is nondegenerate, let $D = P^2 - 4Q$, and let $\rho(m)$ be the
rank of appearance of $m$ in the Lucas sequence $U(P, Q)$. Let $N$ be a Lucas pseudoprime with
parameters $P, Q$ such that $\gcd(N, PQD) = 1$. Then $\rho(p^k) = \rho(p)$ for every prime $p$
dividing $N$, where $p^k$ is the exact power of $p$ dividing $N$; and $N$ is a strong Lucas
pseudoprime with parameters $P, Q$ if and only if the $2$-adic valuations $\nu_2(\rho(p))$ are
equal for all primes $p$ dividing $N$.

The source prints $\rho(p_i^{k_i}) = p_i$, which is false: for $(P, Q) = (1, -1)$ and
$N = 323 = 17 \cdot 19$ one has $\rho(17) = 9$ and $\rho(19) = 18$. The statement uses
$\rho(p_i)$, as in Theorems 3.16 and 3.17.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 3.14 (`integers-2025-A107-thm-3-14`). -/
public theorem_wanted isStrongLucasPseudoprime_iff_padicValNat_two_eq
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (N : ℕ)
    (hN : IsLucasPseudoprime L N)
    (hgcd : Int.gcd N (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1) :
    (∀ p ∈ N.primeFactors,
      lucasRankOfAppearance L (p ^ N.factorization p) = lucasRankOfAppearance L p) ∧
    (IsStrongLucasPseudoprime L N ↔ ∀ p ∈ N.primeFactors, ∀ q ∈ N.primeFactors,
      padicValNat 2 (lucasRankOfAppearance L p) = padicValNat 2 (lucasRankOfAppearance L q))

/-- **Lucas pseudoprimes of odd rank are strong.** Let $P, Q$ be integers such that the Lucas
pair $(P, Q)$ is nondegenerate, and let $\rho(N)$ be the rank of appearance of $N$ in the Lucas
sequence $U(P, Q)$. If $N$ is a Lucas pseudoprime with parameters $P, Q$ and $\rho(N)$ is odd,
then $N$ is a strong Lucas pseudoprime with parameters $P, Q$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Corollary 3.15 (`integers-2025-A107-cor-3-15`). -/
public theorem_wanted isStrongLucasPseudoprime_of_odd_lucasRankOfAppearance
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (N : ℕ)
    (hN : IsLucasPseudoprime L N)
    (hodd : Odd (lucasRankOfAppearance L N)) : IsStrongLucasPseudoprime L N

/-- **Rank of appearance and super Lucas pseudoprimes.** Let $P, Q$ be integers with $Q \neq 0$
such that the pair $(P, Q)$ is nondegenerate, let $D = P^2 - 4Q$, and write $\rho(m)$ for the rank
of appearance of $m$ in the Lucas sequence $U(P, Q)$. Let $N > 1$ be an odd number that is not
prime, with $\gcd(N, QD) = 1$, and for each prime $p \mid N$ let $k_p$ be the exponent of $p$ in
$N$ and let $m_p \ge k_p$ satisfy $\rho(p^{m_p}) = \rho(p)$ and $\rho(p^{m_p + 1}) \neq \rho(p)$.
Let $h$ be the least common multiple of the $\rho(p)$ over the primes $p \mid N$. Then
$\rho(N) = h$, and $N$ is a super Lucas pseudoprime with parameters $(P, Q)$ if and only if
$p \equiv (D/p) \pmod h$ for every prime $p \mid N$, where $(D/p)$ is the Jacobi symbol.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 3.16 (`integers-2025-A107-thm-3-16`). -/
public theorem_wanted lucasRankOfAppearance_eq_lcm_and_isSuperPseudoprime_iff
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (N : ℕ) (hNodd : Odd N)
    (hN1 : 1 < N)
    (hNc : ¬ N.Prime) (hcop : Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1) (m : ℕ → ℕ)
    (hm : ∀ p ∈ N.primeFactors,
      lucasRankOfAppearance L (p ^ m p) = lucasRankOfAppearance L p ∧
        lucasRankOfAppearance L (p ^ (m p + 1)) ≠ lucasRankOfAppearance L p ∧
          N.factorization p ≤ m p) :
    lucasRankOfAppearance L N = N.primeFactors.lcm (lucasRankOfAppearance L) ∧
    (IsSuperPseudoprime L (IsLucasPseudoprime L) N ↔ ∀ p ∈ N.primeFactors,
      (p : ℤ) ≡ jacobiSym (L.p ^ 2 - 4 * L.q) p
        [ZMOD ((N.primeFactors.lcm (lucasRankOfAppearance L) : ℕ) : ℤ)])

/-- **Super strong Lucas pseudoprimes from equal ranks of appearance.** Let $P, Q$ be integers
with $Q \neq 0$ such that the pair $(P, Q)$ is nondegenerate, let $D = P^2 - 4Q$, and write
$\rho(m)$ for the rank of appearance of $m$ in the Lucas sequence $U(P, Q)$. Let $N > 1$ be an
odd number that is not prime, with $\gcd(N, PQD) = 1$, such that for every prime $p \mid N$,
with $p^{k}$ the exact power of $p$ dividing $N$, $\rho(p^{k}) = \rho(p)$, and $\rho(p) = \rho(q)$
for all primes $p, q \mid N$. Then $N$ is a super strong Lucas pseudoprime with parameters
$(P, Q)$, and if $Q = \pm 1$ it is also a super Frobenius pseudoprime with parameters $(P, Q)$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 3.17 (`integers-2025-A107-thm-3-17`). -/
public theorem_wanted isSuperPseudoprime_of_lucasRankOfAppearance_eq
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (N : ℕ) (hNodd : Odd N)
    (hN1 : 1 < N)
    (hNc : ¬ N.Prime) (hcop : Int.gcd N (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1)
    (hρ : ∀ p ∈ N.primeFactors, ∀ q ∈ N.primeFactors,
      lucasRankOfAppearance L (p ^ N.factorization p) = lucasRankOfAppearance L p ∧
        lucasRankOfAppearance L p = lucasRankOfAppearance L q) :
    IsSuperPseudoprime L (IsStrongLucasPseudoprime L) N ∧
      (L.q = 1 ∨ L.q = -1 → IsSuperPseudoprime L (IsLucasFrobeniusPseudoprime L) N)

/-- **From Euler–Lucas to Frobenius pseudoprimes.** Let $P$ and $Q \neq 0$ be integers forming a
nondegenerate Lucas pair, and let $D = P^2 - 4Q$. If $N$ is an Euler–Lucas pseudoprime with
parameters $P, Q$ and an Euler pseudoprime to the base $Q$, and $\gcd(N, PQD) = 1$, then $N$ is a
Frobenius pseudoprime with parameters $P, Q$.

The base $Q$ is any nonzero integer; the source's Definition 3.7 is stated for positive odd bases.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 3.18 (`integers-2025-A107-thm-3-18`). -/
public theorem_wanted isLucasFrobeniusPseudoprime_of_isEulerLucasPseudoprime
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (N : ℕ)
    (hEL : IsEulerLucasPseudoprime L N) (hE : IsEulerPseudoprime L.q N)
    (hcop : Int.gcd N (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1) :
    IsLucasFrobeniusPseudoprime L N

/-- **From strong Lucas to Frobenius pseudoprimes when Q = ±1.** Let $P$ and $Q$ be integers
forming a nondegenerate Lucas pair with $Q = 1$ or $Q = -1$, and let $D = P^2 - 4Q$. If $N$ is a
strong Lucas pseudoprime with parameters $P, Q$ and $\gcd(N, PD) = 1$, then $N$ is a Frobenius
pseudoprime with parameters $P, Q$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 3.19 (`integers-2025-A107-thm-3-19`). -/
public theorem_wanted isLucasFrobeniusPseudoprime_of_isStrongLucasPseudoprime
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (hQ : L.q = 1 ∨ L.q = -1)
    (N : ℕ)
    (hcop : Int.gcd N (L.p * (L.p ^ 2 - 4 * L.q)) = 1) (h : IsStrongLucasPseudoprime L N) :
    IsLucasFrobeniusPseudoprime L N

/-- **Carmichael's primitive divisor theorem.** Let $P$ and $Q$ be coprime integers forming a
nondegenerate Lucas pair with discriminant $D = P^2 - 4Q > 0$, and let $(U_n)$ be the Lucas
sequence $U(P, Q)$. Then for every $n \ge 1$ with $n \notin \{1, 2, 6, 12\}$, the term $U_n$ has
a primitive prime divisor: a prime $p$ that divides $U_n$ but divides no $U_s$ with $1 \le s < n$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 4.1 (`integers-2025-A107-thm-4-1`). -/
public theorem_wanted exists_isPrimitivePrimeDivisor_lucasU_of_discr_pos
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (hcop : Int.gcd L.p L.q = 1)
    (hD : 0 < L.p ^ 2 - 4 * L.q) (n : ℕ) (hn : 1 ≤ n) (hn' : n ∉ ({1, 2, 6, 12} : Finset ℕ)) :
    ∃ p : ℕ, IntegerSequence.IsPrimitivePrimeDivisor (lucasU L) n p

/-- **Bilu–Hanrot–Voutier theorem for Lucas sequences.** Let $P$ and $Q$ be coprime integers
forming a nondegenerate Lucas pair, and let $(U_n)$ be the Lucas sequence $U(P, Q)$. Then for
every $n \ge 1$ with $n \notin \{1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 18, 30\}$, the term $U_n$
has a primitive prime divisor: a prime $p$ that divides $U_n$ but divides no $U_s$ with
$1 \le s < n$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 4.3 (`integers-2025-A107-thm-4-3`). -/
public theorem_wanted exists_isPrimitivePrimeDivisor_lucasU
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (hcop : Int.gcd L.p L.q = 1)
    (n : ℕ) (hn : 1 ≤ n)
    (hn' : n ∉ ({1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 18, 30} : Finset ℕ)) :
    ∃ p : ℕ, IntegerSequence.IsPrimitivePrimeDivisor (lucasU L) n p

/-- **Rotkiewicz: strong Lucas and Frobenius pseudoprimes with two prime factors.** Let $P$ and
$Q$ be integers forming a nondegenerate Lucas pair with $Q = \pm 1$. Then infinitely many
products $N = p_1 p_2$ of two distinct odd primes $p_1$ and $p_2$ are both strong Lucas
pseudoprimes and Frobenius pseudoprimes with parameters $P$ and $Q$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 4.5 (`integers-2025-A107-thm-4-5`). -/
public theorem_wanted infinite_strong_frobenius_pseudoprimes_two_primes
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (hQ : L.q = 1 ∨ L.q = -1) :
    {N : ℕ | (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧ Odd p₁ ∧ Odd p₂ ∧ N = p₁ * p₂) ∧
      IsStrongLucasPseudoprime L N ∧ IsLucasFrobeniusPseudoprime L N}.Infinite

/-- **Rotkiewicz: Frobenius pseudoprimes in arithmetic progressions.** Let $P$ and $Q$ be
integers forming a nondegenerate Lucas pair with $Q = \pm 1$, and let $a$ and $b$ be coprime
positive integers. Then infinitely many natural numbers $N \equiv b \pmod a$ are Frobenius
pseudoprimes with parameters $P$ and $Q$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 4.6 (`integers-2025-A107-thm-4-6`). -/
public theorem_wanted infinite_frobenius_pseudoprimes_modEq
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (hQ : L.q = 1 ∨ L.q = -1)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    {N : ℕ | N ≡ b [MOD a] ∧ IsLucasFrobeniusPseudoprime L N}.Infinite

/-- **Lucas-type pseudoprime properties are unchanged by $P \mapsto -P$.** Let $P$ and $Q$ be
integers such that the Lucas pair $(P, Q)$ is nondegenerate, let $D = P^2 - 4Q$, and let $N > 1$
be an odd natural number with $\gcd(N, QD) = 1$. Then $N$ is a Lucas pseudoprime for $(P, Q)$ if
and only if it is one for $(-P, Q)$, and the same holds for Lucas pseudoprimes of the second
kind, Dickson pseudoprimes, Dickson pseudoprimes of the second kind, and Frobenius pseudoprimes.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 4.7 (`integers-2025-A107-thm-4-7`). -/
public theorem_wanted pseudoprime_iff_neg_p
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (N : ℕ) (hN : Odd N)
    (hN1 : 1 < N)
    (hcop : Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1) :
    (IsLucasPseudoprime L N ↔ IsLucasPseudoprime ⟨-L.p, L.q, L.q_ne_zero⟩ N) ∧
    (IsLucasPseudoprimeSecondKind L N ↔
      IsLucasPseudoprimeSecondKind ⟨-L.p, L.q, L.q_ne_zero⟩ N) ∧
    (IsDicksonPseudoprime L N ↔ IsDicksonPseudoprime ⟨-L.p, L.q, L.q_ne_zero⟩ N) ∧
    (IsDicksonPseudoprimeSecondKind L N ↔
      IsDicksonPseudoprimeSecondKind ⟨-L.p, L.q, L.q_ne_zero⟩ N) ∧
    (IsLucasFrobeniusPseudoprime L N ↔ IsLucasFrobeniusPseudoprime ⟨-L.p, L.q, L.q_ne_zero⟩ N)

/-- **Composite terms $|U_p|$ are super strong Lucas pseudoprimes.** Let $P, Q$ be integers with
$\gcd(P, Q) = 1$ such that the Lucas pair $(P, Q)$ is nondegenerate, let $U_n$ be the Lucas
sequence of $(P, Q)$ and let $D = P^2 - 4Q$. Let $p \ge 5$ be a prime with $\gcd(p, PQD) = 1$
such that $|U_p|$ is composite. Then $|U_p|$ is a super strong Lucas pseudoprime with parameters
$P, Q$, and if $Q = \pm 1$ it is also a super Frobenius pseudoprime with parameters $P, Q$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 5.1, first two sentences
(`integers-2025-A107-thm-5-1`). -/
public theorem_wanted isSuperPseudoprime_natAbs_lucasU_prime
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (hcop : Int.gcd L.p L.q = 1)
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hpD : Int.gcd p (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1)
    (h1 : 1 < (lucasU L p).natAbs) (hc : ¬ (lucasU L p).natAbs.Prime) :
    IsSuperPseudoprime L (IsStrongLucasPseudoprime L) (lucasU L p).natAbs ∧
      (L.q = 1 ∨ L.q = -1 →
        IsSuperPseudoprime L (IsLucasFrobeniusPseudoprime L) (lucasU L p).natAbs)

/-- **Compositeness criteria for $|U_p|$.** Let $P$ and $Q$ be coprime integers such that the
Lucas pair $(P, Q)$ is nondegenerate, let $U_n$ be the Lucas sequence $U(P, Q)$, let
$D = P^2 - 4Q$, and write $\left(\frac{a}{b}\right)$ for the Jacobi symbol. Call a prime $p$
admissible if $p \ge 5$ and $\gcd(p, PQD) = 1$. Then the following hold.

First, if $Q$ is the square of an integer and $D > 0$, then for every admissible prime $p$, $|U_p|$
is greater than $1$, is not prime, and has at least two distinct prime factors.

Second, let $p$ be an admissible prime such that $2p + 1$ is prime and
$\left(\frac{D}{2p+1}\right) = \left(\frac{Q}{2p+1}\right) = 1$. Then $2p + 1 \mid |U_p|$ if
$|U_p| > 2p + 1$; and if $D > 0$, then $|U_p| > 2p + 1$ unless $p = 5$, $|P| = 1$ and $Q = -2$.

Third, if $D < 0$, there is a constant $C$ such that $|U_p| > 2p + 1$ for every prime $p \ge C$.

Fourth, let $p$ be an admissible prime such that $2p - 1$ is prime,
$\left(\frac{D}{2p-1}\right) = -1$ and $\left(\frac{Q}{2p-1}\right) = 1$. Then $2p - 1 \mid |U_p|$
if $|U_p| > 2p - 1$; and if $D > 0$, then $|U_p| > 2p - 1$ unless $p = 7$, $|P| = 1$ and $Q = -1$.

The source states the bound for $D < 0$ in both parts (ii) and (iii) of Theorem 5.1, as printed
with $2p + 1$ in each; the third claim above is that bound.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 5.1 (i)–(iii) (`integers-2025-A107-thm-5-1`). -/
public theorem_wanted natAbs_lucasU_prime_composite_criteria
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (hcop : Int.gcd L.p L.q = 1) :
    (∀ p : ℕ, p.Prime → 5 ≤ p → Int.gcd p (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1 →
      (∃ c : ℤ, L.q = c ^ 2) → 0 < L.p ^ 2 - 4 * L.q →
        1 < (lucasU L p).natAbs ∧ ¬ (lucasU L p).natAbs.Prime ∧
          2 ≤ (lucasU L p).natAbs.primeFactors.card) ∧
    (∀ p : ℕ, p.Prime → 5 ≤ p → Int.gcd p (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1 →
      (2 * p + 1).Prime → jacobiSym (L.p ^ 2 - 4 * L.q) (2 * p + 1) = 1 →
        jacobiSym L.q (2 * p + 1) = 1 →
          (2 * p + 1 < (lucasU L p).natAbs → 2 * p + 1 ∣ (lucasU L p).natAbs) ∧
          (0 < L.p ^ 2 - 4 * L.q → ¬ (p = 5 ∧ |L.p| = 1 ∧ L.q = -2) →
            2 * p + 1 < (lucasU L p).natAbs)) ∧
    (L.p ^ 2 - 4 * L.q < 0 → ∃ C : ℕ, ∀ p : ℕ, p.Prime → C ≤ p →
      2 * p + 1 < (lucasU L p).natAbs) ∧
    (∀ p : ℕ, p.Prime → 5 ≤ p → Int.gcd p (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1 →
      (2 * p - 1).Prime → jacobiSym (L.p ^ 2 - 4 * L.q) (2 * p - 1) = -1 →
        jacobiSym L.q (2 * p - 1) = 1 →
          (2 * p - 1 < (lucasU L p).natAbs → 2 * p - 1 ∣ (lucasU L p).natAbs) ∧
          (0 < L.p ^ 2 - 4 * L.q → ¬ (p = 7 ∧ |L.p| = 1 ∧ L.q = -1) →
            2 * p - 1 < (lucasU L p).natAbs))

/-- **Super strong Lucas pseudoprimes from composed Lucas pairs.** Let $P_1, Q_1$ be integers
with $\gcd(P_1, Q_1) = 1$ such that the Lucas pair $(P_1, Q_1)$ is nondegenerate, with Lucas
sequences $U_n(P_1, Q_1)$, $V_n(P_1, Q_1)$ and discriminant $D_1 = P_1^2 - 4Q_1$. Let $k \ge 2$
with $\gcd(D_1, k) = 1$, let $\varepsilon = \pm 1$, and let $P = \varepsilon V_k(P_1, Q_1)$,
$Q = Q_1^k$ and $D = P^2 - 4Q$. Let $p$ be a prime with $p \nmid k D_1$ and $\gcd(p, PQD) = 1$,
such that $p \ge 5$ if $D > 0$, $p \ge 11$ if $D < 0$, and $p \ne 13$ if $|P_1| = 1$ and
$Q_1 = 2$. Then $\gcd(P, Q) = 1$, the Lucas pair $(P, Q)$ is nondegenerate,
$D = D_1 U_k(P_1, Q_1)^2$, and $|U_p(P, Q)|$ is a super strong Lucas pseudoprime with parameters
$P, Q$; if moreover $Q_1 = \pm 1$, it is also a super Frobenius pseudoprime with parameters
$P, Q$. Finally, $2^{\omega(k)} \le \tau(k) \le \tau(|U_p(P, Q)|)$, where $\omega(k)$ is the
number of distinct prime factors of $k$ and $\tau(n)$ is the number of positive divisors of $n$.

The source writes the exclusion as "$p \ne 13$ if $P = \pm 1$, $Q = 2$", which is vacuous for
$Q = Q_1^k$ with $k \ge 2$; read for $(P, Q)$ it fails: $(P_1, Q_1, k) = (1, 2, 2)$ gives
$(P, Q) = (\mp 3, 4)$ and $|U_{13}(3, 4)| = 181$, a prime. Without $\gcd(p, PQD) = 1$, the
standing hypothesis of Theorem 5.1, it fails as well: $(P_1, Q_1, k, p) = (-3, -1, 3, 5)$ gives
$D = 1300$ and $5 \mid U_5(\pm 36, -1)$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 5.1 (iv) (`integers-2025-A107-thm-5-1`). -/
public theorem_wanted isSuperPseudoprime_natAbs_lucasU_prime_of_lucasV
    (L₁ : LucasSequenceParams) (hL₁ : IsNondegenerateLucasPair L₁.p L₁.q)
    (hcop₁ : Int.gcd L₁.p L₁.q = 1)
    (k : ℕ) (hk : 2 ≤ k) (hkD : Int.gcd (L₁.p ^ 2 - 4 * L₁.q) k = 1) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (L : LucasSequenceParams) (hLp : L.p = ε * lucasV L₁ k)
    (hLq : L.q = L₁.q ^ k) (p : ℕ) (hp : p.Prime)
    (hpk : ¬ (p : ℤ) ∣ k * (L₁.p ^ 2 - 4 * L₁.q))
    (hpD : Int.gcd p (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1)
    (h5 : 0 < L.p ^ 2 - 4 * L.q → 5 ≤ p) (h11 : L.p ^ 2 - 4 * L.q < 0 → 11 ≤ p)
    (h13 : |L₁.p| = 1 → L₁.q = 2 → p ≠ 13) :
    Int.gcd L.p L.q = 1 ∧ IsNondegenerateLucasPair L.p L.q ∧
      L.p ^ 2 - 4 * L.q = (L₁.p ^ 2 - 4 * L₁.q) * lucasU L₁ k ^ 2 ∧
      IsSuperPseudoprime L (IsStrongLucasPseudoprime L) (lucasU L p).natAbs ∧
      (L₁.q = 1 ∨ L₁.q = -1 →
        IsSuperPseudoprime L (IsLucasFrobeniusPseudoprime L) (lucasU L p).natAbs) ∧
      2 ^ k.primeFactors.card ≤ k.divisors.card ∧
      k.divisors.card ≤ (lucasU L p).natAbs.divisors.card

/-- **Super Lucas pseudoprimes of the form $|U_{2p}/P|$.** Let $P, Q$ be integers with $Q \neq 0$
such that the pair $(P, Q)$ is nondegenerate and $\gcd(P, Q) = 1$, let $D = P^2 - 4Q$, and let
$U = U(P, Q)$ be the Lucas sequence. Let $p \ge 5$ be a prime with $\gcd(p, PQD) = 1$ such that
$(p, |P|, Q)$ is none of $(5, 1, 2)$, $(5, 1, 3)$, $(5, 2, 3)$, $(5, 12, 55)$ and $(13, 1, 2)$.
Then $|U_{2p}/P|$, with $U_{2p}/P$ the integer quotient, is a super Lucas pseudoprime with
parameters $(P, Q)$. Moreover, for $\varepsilon = \pm 1$ the Lucas sequences of the excluded
parameters satisfy $|U_{10}(\varepsilon, 2)| = 11$, $|U_{10}(\varepsilon, 3)| = 31$,
$|U_{10}(2\varepsilon, 3)/(2\varepsilon)| = 11$,
$|U_{10}(12\varepsilon, 55)/(12\varepsilon)| = 3739$ and $|U_{26}(\varepsilon, 2)| = 181$, and
$11$, $31$, $3739$ and $181$ are prime.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 5.3 (`integers-2025-A107-thm-5-3`). -/
public theorem_wanted isSuperPseudoprime_natAbs_lucasU_two_mul_prime_div
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (hcop : Int.gcd L.p L.q = 1)
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpD : Int.gcd p (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1)
    (hexc : ¬ ((p = 5 ∧ |L.p| = 1 ∧ L.q = 2) ∨ (p = 5 ∧ |L.p| = 1 ∧ L.q = 3) ∨
      (p = 5 ∧ |L.p| = 2 ∧ L.q = 3) ∨ (p = 5 ∧ |L.p| = 12 ∧ L.q = 55) ∨
      (p = 13 ∧ |L.p| = 1 ∧ L.q = 2))) :
    IsSuperPseudoprime L (IsLucasPseudoprime L) (lucasU L (2 * p) / L.p).natAbs ∧
    ∀ ε : ℤ, (ε = 1 ∨ ε = -1) →
      (lucasU ⟨ε, 2, by decide⟩ 10).natAbs = 11 ∧ (lucasU ⟨ε, 3, by decide⟩ 10).natAbs = 31 ∧
      (lucasU ⟨2 * ε, 3, by decide⟩ 10 / (2 * ε)).natAbs = 11 ∧
      (lucasU ⟨12 * ε, 55, by decide⟩ 10 / (12 * ε)).natAbs = 3739 ∧
      (lucasU ⟨ε, 2, by decide⟩ 26).natAbs = 181 ∧
      Nat.Prime 11 ∧ Nat.Prime 31 ∧ Nat.Prime 3739 ∧ Nat.Prime 181

/-- **Strong Lucas pseudoprimes among the terms $|U_m|$.** Let $P, Q$ be integers with
$\gcd(P, Q) = 1$ such that the Lucas pair $(P, Q)$ is nondegenerate and $D = P^2 - 4Q > 0$, and
let $U_n$ be the Lucas sequence of $(P, Q)$. Suppose that $P$ is odd, or $P \equiv 0 \pmod 4$ and
$Q \equiv -1 \pmod 4$, or $P \equiv 2 \pmod 4$ and $Q \equiv -1 \pmod 8$. Let $m \ge 5$ be an
odd prime or a Lucas pseudoprime of the second kind with parameters $P, Q$, such that
$\gcd(m, PQD) = 1$, such that $3 \nmid m$ if $P$ and $Q$ are both odd, and such that $|U_m|$ is
not prime if $m$ is prime. Then $|U_m|$ is a strong Lucas pseudoprime with parameters $P, Q$.

The source states the result for $N_1 = U_m$, which is positive by its Lemma 6.1.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 6.2 (`integers-2025-A107-thm-6-2`). -/
public theorem_wanted isStrongLucasPseudoprime_natAbs_lucasU
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (hcop : Int.gcd L.p L.q = 1)
    (hD : 0 < L.p ^ 2 - 4 * L.q) (m : ℕ) (hm5 : 5 ≤ m)
    (hm : (m.Prime ∧ Odd m) ∨ IsLucasPseudoprimeSecondKind L m)
    (hmD : Int.gcd m (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1)
    (h3 : Odd L.p → Odd L.q → ¬ 3 ∣ m) (hcomp : m.Prime → ¬ (lucasU L m).natAbs.Prime)
    (hPQ : Odd L.p ∨ (L.p ≡ 0 [ZMOD 4] ∧ L.q ≡ -1 [ZMOD 4]) ∨
      (L.p ≡ 2 [ZMOD 4] ∧ L.q ≡ -1 [ZMOD 8])) :
    IsStrongLucasPseudoprime L (lucasU L m).natAbs

/-- **$|U_m|$ is a strong Lucas and Frobenius pseudoprime when $Q = \pm 1$.** Let $P$ and $Q$ be
integers with $Q = 1$ or $Q = -1$ such that the Lucas pair $(P, Q)$ is nondegenerate, let $U_n$
be the Lucas sequence $U(P, Q)$, and let $D = P^2 - 4Q$. Let $m \ge 5$ be either an odd prime or
a Lucas pseudoprime of the second kind for $(P, Q)$, with $\gcd(m, PD) = 1$ and with $3 \nmid m$
if $P$ is odd. Then $D > 0$, $\gcd(U_m, PD) = 1$, and $3 \nmid U_m$ if $P$ is odd. Suppose
moreover that $|U_m|$ is not prime whenever $m$ is prime and $Q = -1$, and that $P$ is odd, or
$P$ is even and $Q = -1$. Then $|U_m|$ is both a strong Lucas pseudoprime and a Frobenius
pseudoprime for $(P, Q)$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 6.3 (`integers-2025-A107-thm-6-3`). -/
public theorem_wanted lucasU_strong_frobenius_of_q_eq_one_or_neg_one
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (hQ : L.q = 1 ∨ L.q = -1)
    (m : ℕ)
    (hm5 : 5 ≤ m) (hm : (m.Prime ∧ Odd m) ∨ IsLucasPseudoprimeSecondKind L m)
    (hmD : Int.gcd m (L.p * (L.p ^ 2 - 4 * L.q)) = 1) (h3 : Odd L.p → ¬ 3 ∣ m) :
    0 < L.p ^ 2 - 4 * L.q ∧ Int.gcd (lucasU L m) (L.p * (L.p ^ 2 - 4 * L.q)) = 1 ∧
      (Odd L.p → ¬ 3 ∣ lucasU L m) ∧
      ((m.Prime → L.q = -1 → ¬ (lucasU L m).natAbs.Prime) →
        (Odd L.p ∨ (Even L.p ∧ L.q = -1)) →
          IsStrongLucasPseudoprime L (lucasU L m).natAbs ∧
            IsLucasFrobeniusPseudoprime L (lucasU L m).natAbs)

/-- **Lucas pseudoprimes from even-index Lucas terms divided by P.** Let $U$ be the Lucas sequence
with parameters $P$ and $Q$ forming a nondegenerate Lucas pair, with $\gcd(P, Q) = 1$ and
$D = P^2 - 4Q > 0$. Let $m \ge 5$ be either an odd prime or a Frobenius pseudoprime with
parameters $P, Q$, such that $\gcd(m, PQD) = 1$, and $3 \nmid m$ if $P$ and $Q$ are both odd.
Suppose that $P$ is odd, or $P \equiv 0 \pmod 4$ and $Q \equiv -1 \pmod 4$, or
$P \equiv 2 \pmod 4$ and $Q \equiv -1 \pmod 8$. Then $N_2 = |U_{2m}/P|$ is a Lucas pseudoprime
with parameters $P, Q$.

Here $U_{2m}/P$ is the integer quotient, exact because $P \mid U_{2m}$; by Lemma 6.1 it is
positive, so $N_2 = U_{2m}/P$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 6.5 (`integers-2025-A107-thm-6-5`). -/
public theorem_wanted isLucasPseudoprime_natAbs_lucasU_two_mul_div
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (hcop : Int.gcd L.p L.q = 1)
    (hD : 0 < L.p ^ 2 - 4 * L.q) (m : ℕ) (hm5 : 5 ≤ m)
    (hm : (m.Prime ∧ Odd m) ∨ IsLucasFrobeniusPseudoprime L m)
    (hmD : Int.gcd m (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1)
    (h3 : Odd L.p → Odd L.q → ¬ 3 ∣ m)
    (hPQ : Odd L.p ∨ (L.p ≡ 0 [ZMOD 4] ∧ L.q ≡ -1 [ZMOD 4]) ∨
      (L.p ≡ 2 [ZMOD 4] ∧ L.q ≡ -1 [ZMOD 8])) :
    IsLucasPseudoprime L (lucasU L (2 * m) / L.p).natAbs

/-- **$|U_{2m}/P|$ is a Lucas pseudoprime when $Q = \pm 1$.** Let $P$ and $Q$ be integers with
$Q = 1$ or $Q = -1$ such that the Lucas pair $(P, Q)$ is nondegenerate, let $U_n$ be the Lucas
sequence $U(P, Q)$, and let $D = P^2 - 4Q$. Let $m \ge 5$ be either an odd prime or a Lucas
pseudoprime for $(P, Q)$, with $\gcd(m, PD) = 1$ and with $3 \nmid m$ if $P$ is odd, and put
$N_2 = U_{2m}/P$. Then $D > 0$, $\gcd(N_2, PD) = 1$, and $3 \nmid N_2$ if $P$ is odd; and if $P$
is odd, or $P$ is even and $Q = -1$, then $|N_2|$ is a Lucas pseudoprime for $(P, Q)$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 6.6 (`integers-2025-A107-thm-6-6`). -/
public theorem_wanted lucasU_two_mul_div_isLucasPseudoprime_of_q_eq_one_or_neg_one
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (hQ : L.q = 1 ∨ L.q = -1)
    (m : ℕ)
    (hm5 : 5 ≤ m) (hm : (m.Prime ∧ Odd m) ∨ IsLucasPseudoprime L m)
    (hmD : Int.gcd m (L.p * (L.p ^ 2 - 4 * L.q)) = 1) (h3 : Odd L.p → ¬ 3 ∣ m) :
    0 < L.p ^ 2 - 4 * L.q ∧
      Int.gcd (lucasU L (2 * m) / L.p) (L.p * (L.p ^ 2 - 4 * L.q)) = 1 ∧
      (Odd L.p → ¬ 3 ∣ lucasU L (2 * m) / L.p) ∧
      (Odd L.p ∨ (Even L.p ∧ L.q = -1) →
        IsLucasPseudoprime L (lucasU L (2 * m) / L.p).natAbs)

/-- **Frobenius criterion for Lucas pseudoprimes that are not strong.** Let $U$ be the Lucas
sequence with parameters $P$ and $Q$, where $Q = 1$ or $Q = -1$, and let $D = P^2 - 4Q$. Let $N$
be a Lucas pseudoprime with parameters $P, Q$ such that $\gcd(N, D) = 1$ and $N$ is not a strong
Lucas pseudoprime, let $\rho(N)$ be the rank of appearance of $N$ in $U$, and let $k$ be a natural
number with $2^k \mid \rho(N)$ and $2^{k+1} \nmid \rho(N)$. Write $(D/N)$ for the Jacobi symbol.
If $Q = -1$, then $N$ is a Frobenius pseudoprime with parameters $P, Q$ if and only if
$N \equiv (D/N) \pmod{2^{k+1}}$ and $(D/N) = 1$. If $Q = 1$, then $N$ is a Frobenius pseudoprime
with parameters $P, Q$ if and only if $N \equiv (D/N) \pmod{2^{k+1}}$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 6.9 (`integers-2025-A107-thm-6-9`). -/
public theorem_wanted isLucasFrobeniusPseudoprime_iff_of_not_isStrongLucasPseudoprime
    (L : LucasSequenceParams) (hQ : L.q = 1 ∨ L.q = -1) (N : ℕ) (hN : IsLucasPseudoprime L N)
    (hND : Int.gcd N (L.p ^ 2 - 4 * L.q) = 1) (hns : ¬ IsStrongLucasPseudoprime L N) (k : ℕ)
    (hk : 2 ^ k ∣ lucasRankOfAppearance L N) (hk' : ¬ 2 ^ (k + 1) ∣ lucasRankOfAppearance L N) :
    (L.q = -1 → (IsLucasFrobeniusPseudoprime L N ↔
      (N : ℤ) ≡ jacobiSym (L.p ^ 2 - 4 * L.q) N [ZMOD 2 ^ (k + 1)] ∧
        jacobiSym (L.p ^ 2 - 4 * L.q) N = 1)) ∧
    (L.q = 1 → (IsLucasFrobeniusPseudoprime L N ↔
      (N : ℤ) ≡ jacobiSym (L.p ^ 2 - 4 * L.q) N [ZMOD 2 ^ (k + 1)]))

/-- **When $|U_{2m}/P|$ is a Frobenius pseudoprime, for $Q = \pm 1$.** Let $P$ and $Q$ be integers
with $Q = 1$ or $Q = -1$ such that the Lucas pair $(P, Q)$ is nondegenerate, let $U_n$ be the
Lucas sequence $U(P, Q)$, and let $D = P^2 - 4Q$. Let $m \ge 5$ be either an odd prime or a Lucas
pseudoprime for $(P, Q)$, with $\gcd(m, PD) = 1$ and with $3 \nmid m$ if $P$ is odd, and write
$\left(\frac{D}{m}\right)$ for the Jacobi symbol. Suppose that $P$ is odd, or $P$ is even and
$Q = -1$, and put $N_2 = |U_{2m}/P|$. Then $D > 0$ and $N_2$ is a Lucas pseudoprime for $(P, Q)$.
Moreover, $N_2$ is a Frobenius pseudoprime for $(P, Q)$ if and only if:
$m \equiv \left(\frac{D}{m}\right) \pmod 6$ and $\left(\frac{D}{m}\right) = 1$, when $P$ is odd
and $Q = -1$; $m \equiv \left(\frac{D}{m}\right) \pmod 6$, when $P$ is odd and $Q = 1$; and
$m \equiv \left(\frac{D}{m}\right) \pmod 4$ and $\left(\frac{D}{m}\right) = 1$, when $P$ is even
and $Q = -1$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 6.10 (`integers-2025-A107-thm-6-10`). -/
public theorem_wanted lucasU_two_mul_div_isLucasFrobeniusPseudoprime_iff
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (hQ : L.q = 1 ∨ L.q = -1)
    (m : ℕ)
    (hm5 : 5 ≤ m) (hm : (m.Prime ∧ Odd m) ∨ IsLucasPseudoprime L m)
    (hmD : Int.gcd m (L.p * (L.p ^ 2 - 4 * L.q)) = 1) (h3 : Odd L.p → ¬ 3 ∣ m)
    (hPQ : Odd L.p ∨ (Even L.p ∧ L.q = -1)) :
    0 < L.p ^ 2 - 4 * L.q ∧ IsLucasPseudoprime L (lucasU L (2 * m) / L.p).natAbs ∧
    (Odd L.p → L.q = -1 →
      (IsLucasFrobeniusPseudoprime L (lucasU L (2 * m) / L.p).natAbs ↔
        (m : ℤ) ≡ jacobiSym (L.p ^ 2 - 4 * L.q) m [ZMOD 6] ∧
          jacobiSym (L.p ^ 2 - 4 * L.q) m = 1)) ∧
    (Odd L.p → L.q = 1 →
      (IsLucasFrobeniusPseudoprime L (lucasU L (2 * m) / L.p).natAbs ↔
        (m : ℤ) ≡ jacobiSym (L.p ^ 2 - 4 * L.q) m [ZMOD 6])) ∧
    (Even L.p → L.q = -1 →
      (IsLucasFrobeniusPseudoprime L (lucasU L (2 * m) / L.p).natAbs ↔
        (m : ℤ) ≡ jacobiSym (L.p ^ 2 - 4 * L.q) m [ZMOD 4] ∧
          jacobiSym (L.p ^ 2 - 4 * L.q) m = 1))

/-- **Frobenius and non-Frobenius pseudoprimes of the form $U_{2m}/P$.** Let $P$ and $Q$ be
integers forming a nondegenerate Lucas pair with $Q = \pm 1$, with $P$ odd if $Q = 1$, and let
$(U_n)$ be the Lucas sequence $U(P, Q)$. Call $m$ admissible if it is an odd prime or a Lucas
pseudoprime with parameters $P$ and $Q$. Then infinitely many natural numbers $N = |U_{2m}/P|$
with $m$ admissible are both Lucas pseudoprimes and Frobenius pseudoprimes with parameters $P$
and $Q$, and infinitely many such $N$ are Lucas pseudoprimes but not Frobenius pseudoprimes.

Nondegeneracy is assumed explicitly, and the statement fails without it: for $(P, Q) = (1, 1)$
the sequence $U$ runs $0, 1, 1, 0, -1, -1, \dots$, so $U_{2m}/P \in \{0, \pm 1\}$ is never a
pseudoprime.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 6.11 (`integers-2025-A107-thm-6-11`). -/
public theorem_wanted infinite_lucasU_two_mul_div_frobenius_and_not
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (hQ : L.q = 1 ∨ L.q = -1)
    (hP : L.q = 1 → Odd L.p) :
    {N : ℕ | ∃ m : ℕ, ((m.Prime ∧ Odd m) ∨ IsLucasPseudoprime L m) ∧
      N = (lucasU L (2 * m) / L.p).natAbs ∧ IsLucasPseudoprime L N ∧
        IsLucasFrobeniusPseudoprime L N}.Infinite ∧
    {N : ℕ | ∃ m : ℕ, ((m.Prime ∧ Odd m) ∨ IsLucasPseudoprime L m) ∧
      N = (lucasU L (2 * m) / L.p).natAbs ∧ IsLucasPseudoprime L N ∧
        ¬ IsLucasFrobeniusPseudoprime L N}.Infinite

end

end MetaMathlibExt
