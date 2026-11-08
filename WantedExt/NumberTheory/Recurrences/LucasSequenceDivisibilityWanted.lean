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

/-- Double-index identity `U_{2n} = U_n V_n`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Proposition 2.3 (i) (`integers-2025-A107-prop-2-3`). -/
public theorem_wanted lucasU_two_mul_eq_lucasU_mul_lucasV
    (L : LucasSequenceParams) (n : ℕ) :
    lucasU L (2 * n) = lucasU L n * lucasV L n

/-- Divisibility: if `m ∣ n` then `U_m ∣ U_n`, and if moreover `n/m` is odd then
`V_m ∣ V_n`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Proposition 2.3 (iii), (iv)
(`integers-2025-A107-prop-2-3`). -/
public theorem_wanted lucasU_dvd_and_lucasV_dvd_of_dvd
    (L : LucasSequenceParams) (m n : ℕ) (h : m ∣ n) :
    lucasU L m ∣ lucasU L n ∧ (Odd (n / m) → lucasV L m ∣ lucasV L n)

/-- `P ∣ U_{2n}` for every `n`, and `P ∣ V_n` for every odd `n`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Proposition 2.3 (v), (vi)
(`integers-2025-A107-prop-2-3`). -/
public theorem_wanted p_dvd_lucasU_two_mul_and_lucasV_of_odd
    (L : LucasSequenceParams) :
    (∀ n : ℕ, L.p ∣ lucasU L (2 * n)) ∧ ∀ n : ℕ, Odd n → L.p ∣ lucasV L n

/-- Changing the sign of `P`: `U_n(-P, Q) = (-1)^{n+1} U_n(P, Q)` and
`V_n(-P, Q) = (-1)^n V_n(P, Q)`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Proposition 2.3 (vii), (viii)
(`integers-2025-A107-prop-2-3`). -/
public theorem_wanted lucasU_lucasV_neg_p
    (L : LucasSequenceParams) (n : ℕ) :
    lucasU ⟨-L.p, L.q, L.q_ne_zero⟩ n = (-1) ^ (n + 1) * lucasU L n ∧
      lucasV ⟨-L.p, L.q, L.q_ne_zero⟩ n = (-1) ^ n * lucasV L n

/-- Let `W` satisfy the Lucas recursion `W_{n+2} = P W_{n+1} - Q W_n`. If `m ∣ U_t` and
`gcd(m, Q) = 1`, then `W_{n+t} ≡ U_{t+1} W_n (mod m)` for all `n ≥ 0`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 2.5 (`integers-2025-A107-lem-2-5`). -/
public theorem_wanted lucas_recurrence_add_modEq_of_dvd_lucasU
    (L : LucasSequenceParams) (W : ℕ → ℤ)
    (hW : ∀ n, W (n + 2) = L.p * W (n + 1) - L.q * W n)
    (t : ℕ) (m : ℤ) (ht : m ∣ lucasU L t) (hm : Int.gcd m L.q = 1) (n : ℕ) :
    W (n + t) ≡ lucasU L (t + 1) * W n [ZMOD m]

/-- Let `gcd(P, Q) = 1` and let `p` be a prime with `p^i ∥ P`, `i ≥ 1`. Then for every
positive `n`, `p^{i+1} ∣ U_{2n}` if and only if `p ∣ n`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 2.6, first claim
(`integers-2025-A107-lem-2-6`). -/
public theorem_wanted prime_pow_succ_dvd_lucasU_two_mul_iff
    (L : LucasSequenceParams) (hcop : Int.gcd L.p L.q = 1)
    (p i : ℕ) (hp : p.Prime) (hi : 1 ≤ i)
    (hpi : (p : ℤ) ^ i ∣ L.p) (hpi' : ¬ (p : ℤ) ^ (i + 1) ∣ L.p)
    (n : ℕ) (hn : 0 < n) :
    (p : ℤ) ^ (i + 1) ∣ lucasU L (2 * n) ↔ p ∣ n

/-- Let `gcd(P, Q) = 1` and `P ≠ 0`. If `n` is a positive integer with `gcd(n, P) = 1`,
then `gcd(U_{2n}/P, P) = 1`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 2.6, "in particular" claim
(`integers-2025-A107-lem-2-6`). -/
public theorem_wanted gcd_lucasU_two_mul_div_p_eq_one
    (L : LucasSequenceParams) (hcop : Int.gcd L.p L.q = 1) (hP : L.p ≠ 0)
    (n : ℕ) (hn : 0 < n) (hnP : Int.gcd n L.p = 1) :
    Int.gcd (lucasU L (2 * n) / L.p) L.p = 1

/-- Behaviour of `U(P, Q)` modulo `2` when `2 ∤ gcd(P, Q)`: `U` is periodic modulo `2`
from `n = 1` on (not from `n = 0` in general: `P = 1`, `Q = 2` gives `U ≡ 0, 1, 1, 1, …`); if `P` is
odd and `Q` even then `U_n` is odd for `n ≥ 1`; if `P` is even and
`Q` odd then `2 ∣ U_n ↔ 2 ∣ n` and `2 ∣ D`; if `P` and `Q` are odd then
`2 ∣ U_n ↔ 3 ∣ n`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 2.7 (`integers-2025-A107-lem-2-7`). -/
public theorem_wanted lucasU_mod_two
    (L : LucasSequenceParams) (h2 : ¬ 2 ∣ Int.gcd L.p L.q) :
    (∃ k : ℕ, 0 < k ∧ ∀ n, 1 ≤ n → lucasU L (n + k) ≡ lucasU L n [ZMOD 2]) ∧
      (Odd L.p → Even L.q → ∀ n, 1 ≤ n → ¬ 2 ∣ lucasU L n) ∧
      (Even L.p → Odd L.q →
        (∀ n, 2 ∣ lucasU L n ↔ 2 ∣ n) ∧ 2 ∣ L.p ^ 2 - 4 * L.q) ∧
      (Odd L.p → Odd L.q → ∀ n, 2 ∣ lucasU L n ↔ 3 ∣ n)

/-- Behaviour of `U(P, Q)` modulo `3` when `3 ∤ gcd(P, Q)`: `U` is periodic modulo `3`
from `n = 1` on (not from `n = 0` in general: `P = 1`, `Q = 3` gives `U ≡ 0, 1, 1, 1, …`); if
`3 ∣ Q` then `3 ∤ U_n` for `n ≥ 1`; if `3 ∣ P` then `3 ∣ U_n ↔ 2 ∣ n`;
if `3 ∤ P` and `Q ≡ -1 (mod 3)` then `3 ∣ U_n ↔ 4 ∣ n`; if `3 ∤ P` and `Q ≡ 1 (mod 3)`
then `3 ∣ U_n ↔ 3 ∣ n` and `3 ∣ D`. The source's values `ρ(3) = 2, 4, 3` of the rank of
apparition are the least positive indices these equivalences give.

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

/-- For nondegenerate `U(P, Q)`, `V(P, Q)` with `D > 0`: `|U_n|` is strictly increasing
for `n ≥ 2` and `|V_n|` for `n ≥ 1`; if `P > 0` then `U_n > 0` for `n ≥ 1` and `V_n > 0`
for `n ≥ 0`; and `|U_3| ≥ 3` unless `|P| = -Q = 1`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 2.9 (`integers-2025-A107-lem-2-9`). -/
public theorem_wanted lucas_abs_strictMono_of_discr_pos
    (L : LucasSequenceParams) (hP : L.p ≠ 0) (hD : 0 < L.p ^ 2 - 4 * L.q) :
    (∀ n, 2 ≤ n → |lucasU L n| < |lucasU L (n + 1)|) ∧
      (∀ n, 1 ≤ n → |lucasV L n| < |lucasV L (n + 1)|) ∧
      (0 < L.p → (∀ n, 1 ≤ n → 0 < lucasU L n) ∧ ∀ n, 0 < lucasV L n) ∧
      (¬ (|L.p| = 1 ∧ L.q = -1) → 3 ≤ |lucasU L 3|)

/-- For nondegenerate `U(P, Q)` with `D > 0` and `n ≥ 3`, the rank of apparition of
`U_n` is `n`: `U_n` divides no `U_k` with `0 < k < n`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Corollary 2.10 (`integers-2025-A107-cor-2-10`). -/
public theorem_wanted not_lucasU_dvd_lucasU_of_lt
    (L : LucasSequenceParams) (hP : L.p ≠ 0) (hD : 0 < L.p ^ 2 - 4 * L.q)
    (n : ℕ) (hn : 3 ≤ n) (k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    ¬ lucasU L n ∣ lucasU L k

/-- If `gcd(P, Q) = 1` then `gcd(P, D) ∣ 4`, and `gcd(P, D') = 1` for every odd
divisor `D'` of `D = P² - 4Q`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 4.9 (`integers-2025-A107-lem-4-9`). -/
public theorem_wanted gcd_p_discr_dvd_four
    (P Q : ℤ) (hcop : Int.gcd P Q = 1) :
    (Int.gcd P (P ^ 2 - 4 * Q) : ℤ) ∣ 4 ∧
      ∀ D' : ℤ, Odd D' → D' ∣ P ^ 2 - 4 * Q → Int.gcd P D' = 1

/-- Let `gcd(P, Q) = 1`, `P ≠ 0`, and let `m` be odd with `gcd(m, PQD) = 1` and
`3 ∤ m` when `P ≡ Q ≡ 1 (mod 2)`. Then `N₁ = U_m` and `N₂ = U_{2m}/P` are odd and
coprime to `D`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 4.10 (`integers-2025-A107-lem-4-10`). -/
public theorem_wanted odd_lucasU_coprime_discr
    (L : LucasSequenceParams) (hcop : Int.gcd L.p L.q = 1) (hP : L.p ≠ 0)
    (m : ℕ) (hm : Odd m) (hmc : Int.gcd m (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1)
    (h3 : Odd L.p → Odd L.q → ¬ 3 ∣ m) :
    Odd (lucasU L m) ∧ Odd (lucasU L (2 * m) / L.p) ∧
      Int.gcd (lucasU L m) (L.p ^ 2 - 4 * L.q) = 1 ∧
      Int.gcd (lucasU L (2 * m) / L.p) (L.p ^ 2 - 4 * L.q) = 1

/-- For nondegenerate `U(P, Q)` with `gcd(P, Q) = 1` and `D > 0`, and odd `m ≥ 5`:
if `m` is composite then `U_m` is composite, and `U_{2m}/P` is always composite
(an integer `N` is composite when `|N| > 1` and `|N|` is not prime).

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Corollary 4.2 (`integers-2025-A107-cor-4-2`). -/
public theorem_wanted lucasU_composite_of_discr_pos
    (L : LucasSequenceParams) (hcop : Int.gcd L.p L.q = 1) (hP : L.p ≠ 0)
    (hD : 0 < L.p ^ 2 - 4 * L.q) (m : ℕ) (hm5 : 5 ≤ m) (hm : Odd m) :
    (¬ m.Prime → 1 < (lucasU L m).natAbs ∧ ¬ (lucasU L m).natAbs.Prime) ∧
      (1 < (lucasU L (2 * m) / L.p).natAbs ∧ ¬ (lucasU L (2 * m) / L.p).natAbs.Prime)

/-- Let `U(P, Q)` be nondegenerate with `gcd(P, Q) = 1` and `D > 0`, and let `m > 1` be
odd with `gcd(m, PQD) = 1` and `3 ∤ m` when `P ≡ Q ≡ 1 (mod 2)`. Then `N₁ = U_m` and
`N₂ = U_{2m}/P` are positive, odd, and `gcd(N₁N₂, PQD) = 1`; if `m` is composite both are
composite; and `(D/m) = (D/N₁) = (D/N₂)` (Jacobi symbols) whenever `P` is odd, or
`P ≡ 0 (mod 4)` and `Q ≡ -1 (mod 4)`, or `P ≡ 2 (mod 4)` and `Q ≡ -1 (mod 8)`.

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


/-- Degenerate Lucas sequences: let `α, β ∈ ℂ` be the roots of `x² - Px + Q` (so `α + β = P`,
`αβ = Q`), `D = P² - 4Q`, and `U`, `V` the sequences with `U_0 = 0`, `U_1 = 1`, `V_0 = 2`,
`V_1 = P` and `W_{n+2} = P W_{n+1} - Q W_n`. If the pair is degenerate (`Q = 0`, or `α/β` is a
root of unity), then one of: (i) `Q = 0`, `D = P²`, `U_n = P^{n-1}`, `V_n = P^n` for `n ≥ 1`;
or, for some nonzero integer `M`, (ii) `α/β = 1`, `P = 2M`, `Q = M²`, `D = 0`;
(iii) `α/β = -1`, `P = 0`, `Q = M`, `D = -4M`; (iv) `α/β` a primitive cube root of unity,
`P = M`, `Q = M²`, `D = -3M²`; (v) a primitive fourth root, `P = 2M`, `Q = 2M²`,
`D = -4M²`; (vi) a primitive sixth root, `P = 3M`, `Q = 3M²`, `D = -3M²`. Degeneracy is
taken in the theorem's own sense (`Q = 0` or `α/β` a root of unity, Mathlib's
`IsOfFinOrder`); `U` is given by `IsLucasSequenceFirstKind P Q` and `V` by its recurrence,
because `MetaMathlibExt.LucasSequenceParams` requires `Q ≠ 0`.

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

/-- The rank of appearance `ρ(m)` of `m` in `U(P, Q)`: the least positive `r` with `m ∣ U_r`
(the source assumes `gcd(m, Q) = 1`, under which it exists). When no positive `r` has
`m ∣ U_r`, `sInf` makes this `0`; lack of coprimality alone does not force that.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Section 2. -/
public noncomputable def lucasRankOfAppearance (L : LucasSequenceParams) (m : ℕ) : ℕ :=
  sInf {r : ℕ | 0 < r ∧ (m : ℤ) ∣ lucasU L r}

/-- `ρ(m) ≤ r` whenever `0 < r` and `m ∣ U_r`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Section 2 (definition of `ρ` as a least index). -/
public theorem lucasRankOfAppearance_le_of_dvd (L : LucasSequenceParams) {m r : ℕ}
    (hr : 0 < r) (hm : (m : ℤ) ∣ lucasU L r) : lucasRankOfAppearance L m ≤ r :=
  Nat.sInf_le ⟨hr, hm⟩

/-- Specification of `ρ(m)`: when some positive `r` has `m ∣ U_r`, `ρ(m)` is itself positive
and `m ∣ U_{ρ(m)}`; with `lucasRankOfAppearance_le_of_dvd` it is the least such index.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Section 2 (definition of `ρ` as a least index). -/
public theorem lucasRankOfAppearance_spec (L : LucasSequenceParams) {m : ℕ}
    (h : ∃ r, 0 < r ∧ (m : ℤ) ∣ lucasU L r) :
    0 < lucasRankOfAppearance L m ∧ (m : ℤ) ∣ lucasU L (lucasRankOfAppearance L m) :=
  Nat.sInf_mem h

/-- `ρ(1) = 1`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Section 2 (definition of `ρ`). -/
public theorem lucasRankOfAppearance_one (L : LucasSequenceParams) :
    lucasRankOfAppearance L 1 = 1 := by
  have hmem : (1 : ℕ) ∈ {r : ℕ | 0 < r ∧ ((1 : ℕ) : ℤ) ∣ lucasU L r} :=
    ⟨Nat.one_pos, by simp⟩
  exact le_antisymm (Nat.sInf_le hmem) (Nat.sInf_mem ⟨1, hmem⟩).1

/-- The index `N - (D/N)` of congruences (3.1) and (3.4), with `(D/N)` the Jacobi symbol (as a
natural number; it is positive for the odd `N > 1` coprime to `D` that the source considers).

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, congruences (3.1), (3.4). -/
public def lucasPseudoprimeIndex (L : LucasSequenceParams) (N : ℕ) : ℕ :=
  ((N : ℤ) - jacobiSym (L.p ^ 2 - 4 * L.q) N).toNat

/-- Lucas pseudoprime with parameters `P, Q`: a positive odd composite `N` with
`gcd(N, QD) = 1` and `U_{N-(D/N)} ≡ 0 (mod N)`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.1. -/
public def IsLucasPseudoprime (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
    (N : ℤ) ∣ lucasU L (lucasPseudoprimeIndex L N)

/-- Lucas pseudoprime of the second kind: positive odd composite `N`, `gcd(N, QD) = 1`,
`U_N ≡ (D/N) (mod N)`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.2. -/
public def IsLucasPseudoprimeSecondKind (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
    lucasU L N ≡ jacobiSym (L.p ^ 2 - 4 * L.q) N [ZMOD N]

/-- Dickson pseudoprime: positive odd composite `N`, `gcd(N, QD) = 1`, `V_N ≡ P (mod N)`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.3. -/
public def IsDicksonPseudoprime (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
    lucasV L N ≡ L.p [ZMOD N]

/-- Dickson pseudoprime of the second kind: positive odd composite `N`, `gcd(N, QD) = 1`,
`V_{N-(D/N)} ≡ 2Q^{(1-(D/N))/2} (mod N)`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.4. -/
public def IsDicksonPseudoprimeSecondKind (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
    lucasV L (lucasPseudoprimeIndex L N) ≡
      2 * L.q ^ ((1 - jacobiSym (L.p ^ 2 - 4 * L.q) N) / 2).toNat [ZMOD N]

/-- Frobenius pseudoprime with parameters `P, Q` in the source's sense (congruences
(3.1)–(3.4) and `gcd(N, PQD) = 1`; not Grantham's polynomial notion
`Nat.IsFrobeniusPseudoprime`).

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.5. -/
public def IsLucasFrobeniusPseudoprime (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Int.gcd N (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧ IsLucasPseudoprime L N ∧
    IsLucasPseudoprimeSecondKind L N ∧ IsDicksonPseudoprime L N ∧
      IsDicksonPseudoprimeSecondKind L N

/-- Euler pseudoprime to the base `a`: odd composite `N`, `gcd(a, N) = 1`, and
`a^{(N-1)/2} ≡ (a/N) (mod N)`. The source states the definition for positive odd `a` and applies
it to the base `Q` (for example `Q = -1` in Remark 3.8); here `a` is any integer.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.7. -/
public def IsEulerPseudoprime (a : ℤ) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd a N = 1 ∧ a ^ ((N - 1) / 2) ≡ jacobiSym a N [ZMOD N]

/-- Euler–Lucas pseudoprime: odd composite `N`, `gcd(N, QD) = 1`, and
`U_{(N-(D/N))/2} ≡ 0` if `(Q/N) = 1`, `V_{(N-(D/N))/2} ≡ 0` if `(Q/N) = -1` (mod `N`).

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.9. -/
public def IsEulerLucasPseudoprime (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
    (jacobiSym L.q N = 1 → (N : ℤ) ∣ lucasU L (lucasPseudoprimeIndex L N / 2)) ∧
    (jacobiSym L.q N = -1 → (N : ℤ) ∣ lucasV L (lucasPseudoprimeIndex L N / 2))

/-- Strong Lucas pseudoprime: odd composite `N`, `gcd(N, QD) = 1`, `N - (D/N) = 2^s d` with `d`
odd, and `U_d ≡ 0` or `V_{2^r d} ≡ 0 (mod N)` for some `0 ≤ r < s`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.10. -/
public def IsStrongLucasPseudoprime (L : LucasSequenceParams) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
    ∃ s d : ℕ, Odd d ∧ lucasPseudoprimeIndex L N = 2 ^ s * d ∧
      ((N : ℤ) ∣ lucasU L d ∨ ∃ r < s, (N : ℤ) ∣ lucasV L (2 ^ r * d))

/-- Super pseudoprime of type `S`: odd composite `N`, `gcd(N, QD) = 1`, every divisor `> 1` of
`N` prime or of type `S` (super Lucas, super strong Lucas, super Frobenius pseudoprimes for
`S = IsLucasPseudoprime L`, `IsStrongLucasPseudoprime L`, `IsLucasFrobeniusPseudoprime L`).

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.13. -/
public def IsSuperPseudoprime (L : LucasSequenceParams) (S : ℕ → Prop) (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧ Int.gcd N (L.q * (L.p ^ 2 - 4 * L.q)) = 1 ∧
    ∀ d : ℕ, d ∣ N → 1 < d → d.Prime ∨ S d

/-- `9` is a Lucas pseudoprime with `(P, Q) = (1, 5)` (`D = -19`, `U_8 = -279`).

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.1 (example). -/
public theorem isLucasPseudoprime_one_five_nine :
    IsLucasPseudoprime ⟨1, 5, by decide⟩ 9 := by
  have hj : jacobiSym ((1 : ℤ) ^ 2 - 4 * 5) 9 = 1 := by norm_num
  refine ⟨by decide, by norm_num, by norm_num, by decide, ?_⟩
  simp only [lucasPseudoprimeIndex, hj]
  decide

/-- `9` is a strong Lucas pseudoprime with `(P, Q) = (1, 5)`: `8 = 2^3 · 1` and `V_2 = -9`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.10 (example). -/
public theorem isStrongLucasPseudoprime_one_five_nine :
    IsStrongLucasPseudoprime ⟨1, 5, by decide⟩ 9 := by
  have hj : jacobiSym ((1 : ℤ) ^ 2 - 4 * 5) 9 = 1 := by norm_num
  refine ⟨by decide, by norm_num, by norm_num, by decide, 3, 1, odd_one, ?_,
    Or.inr ⟨1, by norm_num, by decide⟩⟩
  simp only [lucasPseudoprimeIndex, hj]
  decide

/-- `9` is an Euler–Lucas pseudoprime with `(P, Q) = (1, 5)`: `(5/9) = 1` and `U_4 = -9`.

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

/-- `9` is a Frobenius pseudoprime with `(P, Q) = (4, -1)` (`D = 20`).

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
/-- `561` is an Euler pseudoprime to the base `2`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Definition 3.7 (example). -/
public theorem isEulerPseudoprime_two_561 : IsEulerPseudoprime 2 561 := by
  have hj : jacobiSym 2 561 = 1 := by norm_num
  refine ⟨by decide, by norm_num, by norm_num, by decide, ?_⟩
  rw [hj]
  decide

/-- `9` is a super Lucas pseudoprime with `(P, Q) = (1, 5)`: its divisors `3` and `9` are a
prime and a Lucas pseudoprime.

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

/-- Properties of the rank of appearance `ρ`, for any `U(P, Q)` (`Q ≠ 0`), positive `r, s` and
primes `p`: (i) if `gcd(r, Q) = 1` then `r ∣ U_s ↔ ρ(r) ∣ s`; (ii) odd `p ∤ Q` divides
`U_{p-(D/p)}`; (iii) `p ∣ D`, `p ∤ Q` gives `ρ(p) = p`; (iv) for `p ∤ 2QD`,
`p ∣ U_{(p-(D/p))/2} ↔ (Q/p) = 1` (the source omits "`p ∣`"); (v) for odd `p ∤ Q` with
`ρ(p^k) = ρ(p) ≠ ρ(p^{k+1})`, `ρ(p^j) = p^{max(j-k,0)} ρ(p)` for `j ≥ 1` (false for `p = 2`:
`(P, Q) = (1, -1)` has `ρ(2) = 3`, `ρ(4) = 6`, `ρ(8) = 6 ≠ 12`); (vi) `gcd(rs, Q) = 1`,
`r ∣ s` give `ρ(r) ∣ ρ(s)`; (vii) `gcd(P, Q) = 1` gives `gcd(U_r, U_s) = |U_{gcd(r,s)}|`;
(viii) `gcd(r, s) = gcd(rs, Q) = 1` gives `ρ(rs) = lcm(ρ(r), ρ(s))`; (ix) `gcd(P, Q) = 1`,
`p ∣ Q` give `p ∤ U_n` for `n ≥ 1`; (x) `gcd(P, Q) = 1` and odd `p ∤ Q` give
`p ≡ (D/p) (mod ρ(p))`.

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

/-- A strong Lucas pseudoprime is an Euler–Lucas pseudoprime.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 3.12 (`integers-2025-A107-thm-3-12`). -/
public theorem_wanted isEulerLucasPseudoprime_of_isStrongLucasPseudoprime
    (L : LucasSequenceParams) (N : ℕ) (h : IsStrongLucasPseudoprime L N) :
    IsEulerLucasPseudoprime L N

/-- For nondegenerate `U(P, Q)` and a Lucas pseudoprime `N` with `gcd(N, PQD) = 1`: every prime
power `p^k ∥ N` has `ρ(p^k) = ρ(p)`, and `N` is a strong Lucas pseudoprime iff the `2`-adic
valuations `ν₂(ρ(p))` agree for all primes `p ∣ N`. The source prints `ρ(p_i^{k_i}) = p_i`,
which is false: `(P, Q) = (1, -1)`, `N = 323 = 17 · 19` has `ρ(17) = 9`, `ρ(19) = 18`; the
statement uses `ρ(p_i)`, as in Theorems 3.16 and 3.17.

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

/-- For nondegenerate `U(P, Q)`, a Lucas pseudoprime `N` with `ρ(N)` odd is a strong Lucas
pseudoprime.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Corollary 3.15 (`integers-2025-A107-cor-3-15`). -/
public theorem_wanted isStrongLucasPseudoprime_of_odd_lucasRankOfAppearance
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (N : ℕ)
    (hN : IsLucasPseudoprime L N)
    (hodd : Odd (lucasRankOfAppearance L N)) : IsStrongLucasPseudoprime L N

/-- For nondegenerate `U(P, Q)`, let `N = ∏ p^{k_p}` be odd composite with `gcd(N, QD) = 1`, and
for each prime `p ∣ N` let `m_p ≥ k_p` satisfy `ρ(p^{m_p}) = ρ(p) ≠ ρ(p^{m_p+1})`. With
`h = lcm_{p ∣ N} ρ(p)`: `ρ(N) = h`, and `N` is a super Lucas pseudoprime iff
`p ≡ (D/p) (mod h)` for every prime `p ∣ N`.

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

/-- For nondegenerate `U(P, Q)` and odd composite `N` with `gcd(N, PQD) = 1` such that
`ρ(p^{k_p}) = ρ(p)` for every `p^{k_p} ∥ N` and all `ρ(p)`, `p ∣ N`, are equal: `N` is a super
strong Lucas pseudoprime, and a super Frobenius pseudoprime when `Q = ±1`.

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

/-- For nondegenerate `U(P, Q)`, an Euler–Lucas pseudoprime `N` that is an Euler pseudoprime to
the base `Q`, with `gcd(N, PQD) = 1`, is a Frobenius pseudoprime (the base `Q` is any nonzero
integer; the source's Definition 3.7 is stated for positive odd bases).

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 3.18 (`integers-2025-A107-thm-3-18`). -/
public theorem_wanted isLucasFrobeniusPseudoprime_of_isEulerLucasPseudoprime
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (N : ℕ)
    (hEL : IsEulerLucasPseudoprime L N) (hE : IsEulerPseudoprime L.q N)
    (hcop : Int.gcd N (L.p * L.q * (L.p ^ 2 - 4 * L.q)) = 1) :
    IsLucasFrobeniusPseudoprime L N

/-- For nondegenerate `U(P, Q)` with `Q = ±1`, a strong Lucas pseudoprime `N` with
`gcd(N, PD) = 1` is a Frobenius pseudoprime.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 3.19 (`integers-2025-A107-thm-3-19`). -/
public theorem_wanted isLucasFrobeniusPseudoprime_of_isStrongLucasPseudoprime
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (hQ : L.q = 1 ∨ L.q = -1)
    (N : ℕ)
    (hcop : Int.gcd N (L.p * (L.p ^ 2 - 4 * L.q)) = 1) (h : IsStrongLucasPseudoprime L N) :
    IsLucasFrobeniusPseudoprime L N

/-- Carmichael: for nondegenerate `U(P, Q)` with `gcd(P, Q) = 1` and `D > 0`, `U_n` has a
primitive prime divisor (a prime `p` with `ρ(p) = n`) for every `n ≥ 1` outside `{1, 2, 6, 12}`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 4.1 (`integers-2025-A107-thm-4-1`). -/
public theorem_wanted exists_isPrimitivePrimeDivisor_lucasU_of_discr_pos
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (hcop : Int.gcd L.p L.q = 1)
    (hD : 0 < L.p ^ 2 - 4 * L.q) (n : ℕ) (hn : 1 ≤ n) (hn' : n ∉ ({1, 2, 6, 12} : Finset ℕ)) :
    ∃ p : ℕ, IntegerSequence.IsPrimitivePrimeDivisor (lucasU L) n p

/-- Bilu–Hanrot–Voutier: for nondegenerate `U(P, Q)` with `gcd(P, Q) = 1`, `U_n` has a primitive
prime divisor for every `n ≥ 1` outside `{1, …, 8, 10, 12, 13, 18, 30}`.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 4.3 (`integers-2025-A107-thm-4-3`). -/
public theorem_wanted exists_isPrimitivePrimeDivisor_lucasU
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (hcop : Int.gcd L.p L.q = 1)
    (n : ℕ) (hn : 1 ≤ n)
    (hn' : n ∉ ({1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 18, 30} : Finset ℕ)) :
    ∃ p : ℕ, IntegerSequence.IsPrimitivePrimeDivisor (lucasU L) n p

/-- Rotkiewicz: for nondegenerate `U(P, Q)` with `Q = ±1`, infinitely many products `p₁p₂` of
distinct odd primes are both strong Lucas and Frobenius pseudoprimes.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 4.5 (`integers-2025-A107-thm-4-5`). -/
public theorem_wanted infinite_strong_frobenius_pseudoprimes_two_primes
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (hQ : L.q = 1 ∨ L.q = -1) :
    {N : ℕ | (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧ Odd p₁ ∧ Odd p₂ ∧ N = p₁ * p₂) ∧
      IsStrongLucasPseudoprime L N ∧ IsLucasFrobeniusPseudoprime L N}.Infinite

/-- Rotkiewicz: for nondegenerate `U(P, Q)` with `Q = ±1` and coprime positive `a, b`, the
progression `ax + b` contains infinitely many Frobenius pseudoprimes.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Theorem 4.6 (`integers-2025-A107-thm-4-6`). -/
public theorem_wanted infinite_frobenius_pseudoprimes_modEq
    (L : LucasSequenceParams) (hL : IsNondegenerateLucasPair L.p L.q) (hQ : L.q = 1 ∨ L.q = -1)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    {N : ℕ | N ≡ b [MOD a] ∧ IsLucasFrobeniusPseudoprime L N}.Infinite

/-- For nondegenerate `U(P, Q)` and odd `N > 1` with `gcd(N, QD) = 1`, each of the Lucas,
Lucas second-kind, Dickson, Dickson second-kind and Frobenius pseudoprime properties holds for
`(P, Q)` iff it holds for `(-P, Q)`.

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

/-- For nondegenerate `U(P, Q)` with `gcd(P, Q) = 1` and a prime `p ≥ 5` with `gcd(p, PQD) = 1`:
if `N₁ = |U_p|` is composite then it is a super strong Lucas pseudoprime, and also a super
Frobenius pseudoprime when `Q = ±1`.

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

/-- Compositeness criteria for `|U_p|` (same hypotheses as Theorem 5.1): (i) if `Q` is a perfect
square and `D > 0`, `|U_p|` is composite with at least two distinct prime factors; (ii) if `2p+1`
is prime, `|U_p| > 2p+1` and `(D/(2p+1)) = (Q/(2p+1)) = 1`, then `2p+1 ∣ |U_p|`; when `D > 0`
these Jacobi conditions force `|U_p| > 2p+1` unless `(p, P, Q) = (5, ±1, -2)`, and when `D < 0`
some `C₁` gives `|U_p| > 2p+1` for all primes `p ≥ C₁`; (iii) if `2p-1` is prime,
`|U_p| > 2p-1`, `(D/(2p-1)) = -1` and `(Q/(2p-1)) = 1`, then `2p-1 ∣ |U_p|`; when `D > 0` these
conditions force `|U_p| > 2p-1` unless `(p, P, Q) = (7, ±1, -1)`, and when `D < 0` some `C₂`
gives `|U_p| > 2p+1` for all primes `p ≥ C₂` (as printed).

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

/-- Composition construction: let `U(P₁, Q₁)` be nondegenerate with `gcd(P₁, Q₁) = 1` and
discriminant `D₁`, `k ≥ 2` with `gcd(D₁, k) = 1`, and `P = ±V_k(P₁, Q₁)`, `Q = Q₁^k`. Then
`gcd(P, Q) = 1`, `U(P, Q)` is nondegenerate with `D = D₁ U_k(P₁, Q₁)²`, and for a prime
`p ∤ kD₁` with `gcd(p, PQD) = 1` (the standing hypothesis of Theorem 5.1), `p ≥ 5` if `D > 0`,
`p ≥ 11` if `D < 0`, and `p ≠ 13` if `(P₁, Q₁) = (±1, 2)`, `|U_p(P, Q)|` is a super strong
Lucas pseudoprime (super Frobenius if `Q₁ = ±1`) with at least `τ(k) ≥ 2^{ω(k)}` divisors. The
source writes the exclusion as "`p ≠ 13` if `P = ±1`, `Q = 2`", which is vacuous for `Q = Q₁^k`,
`k ≥ 2`; read for `(P, Q)` it fails: `(P₁, Q₁, k) = (1, 2, 2)` gives `(P, Q) = (∓3, 4)` and
`|U_13(3, 4)| = 181`, a prime. Without `gcd(p, PQD) = 1` it fails as well:
`(P₁, Q₁, k, p) = (-3, -1, 3, 5)` gives `D = 1300` and `5 ∣ U_5(±36, -1)`.

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

/-- For nondegenerate `U(P, Q)` with `gcd(P, Q) = 1` and a prime `p ≥ 5` with
`gcd(p, PQD) = 1`, `N₂ = |U_{2p}/P|` is a super Lucas pseudoprime unless `(p, P, Q)` is
`(5, ±1, 2)`, `(5, ±1, 3)`, `(5, ±2, 3)`, `(5, ±12, 55)` or `(13, ±1, 2)`; in those cases
`|U_10(±1, 2)| = 11`, `|U_10(±1, 3)| = 31`, `|U_10(±2, 3)/2| = 11`, `|U_10(±12, 55)/12| = 3739`,
`|U_26(±1, 2)| = 181`, all primes.

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

/-- For nondegenerate `U(P, Q)` with `gcd(P, Q) = 1` and `D > 0`, let `m ≥ 5` be an odd prime or
a Lucas pseudoprime of the second kind with `gcd(m, PQD) = 1` and `3 ∤ m` if `P ≡ Q ≡ 1
(mod 2)`, and `N₁ = U_m` (composite if `m` is prime). Then `N₁` is a strong Lucas pseudoprime if
`P` is odd, or `P ≡ 0 (mod 4)` and `Q ≡ -1 (mod 4)`, or `P ≡ 2 (mod 4)` and `Q ≡ -1 (mod 8)`
(`N₁ = |U_m|`, positive by Lemma 6.1).

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

/-- For nondegenerate `U(P, Q)` with `Q = ±1` (so `D > 0`), let `m ≥ 5` be an odd prime or a
Lucas pseudoprime of the second kind with `gcd(m, PD) = 1` and `3 ∤ m` if `P` is odd, and
`N₁ = U_m`. Then `gcd(N₁, PD) = 1` and `3 ∤ N₁` if `P` is odd; and if `N₁` is composite when `m`
is prime and `Q = -1`, then `N₁` is a strong Lucas and a Frobenius pseudoprime when `P` is odd,
or `P` is even and `Q = -1`.

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

/-- For nondegenerate `U(P, Q)` with `gcd(P, Q) = 1` and `D > 0`, let `m ≥ 5` be an odd prime or
a Frobenius pseudoprime with `gcd(m, PQD) = 1` and `3 ∤ m` if `P ≡ Q ≡ 1 (mod 2)`. Then
`N₂ = U_{2m}/P` is a Lucas pseudoprime if `P` is odd, or `P ≡ 0 (mod 4)` and `Q ≡ -1 (mod 4)`,
or `P ≡ 2 (mod 4)` and `Q ≡ -1 (mod 8)` (`N₂ = |U_{2m}/P|`, positive by Lemma 6.1).

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

/-- For nondegenerate `U(P, Q)` with `Q = ±1` (so `D > 0`), let `m ≥ 5` be an odd prime or a
Lucas pseudoprime with `gcd(m, PD) = 1` and `3 ∤ m` if `P` is odd, and `N₂ = U_{2m}/P`. Then
`gcd(N₂, PD) = 1`, `3 ∤ N₂` if `P` is odd, and `N₂` is a Lucas pseudoprime if `P` is odd, or `P`
is even and `Q = -1`.

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

/-- For `U(P, Q)` with `Q = ±1`, let `N` be a Lucas pseudoprime with `gcd(N, D) = 1` that is not a
strong Lucas pseudoprime, and `2^k ∥ ρ(N)`. If `Q = -1`, `N` is a Frobenius pseudoprime iff
`N ≡ (D/N) (mod 2^{k+1})` and `(D/N) = 1`; if `Q = 1`, iff `N ≡ (D/N) (mod 2^{k+1})`.

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

/-- For nondegenerate `U(P, Q)` with `Q = ±1` (so `D > 0`), let `m ≥ 5` be an odd prime or a
Lucas pseudoprime with `gcd(m, PD) = 1` and `3 ∤ m` if `P` is odd, `N₂ = U_{2m}/P`, and suppose
`P` is odd, or `P` is even and `Q = -1`. Then `N₂` is a Lucas pseudoprime, and `N₂` is a
Frobenius pseudoprime iff: `m ≡ (D/m) (mod 6)` and `(D/m) = 1` (`P` odd, `Q = -1`);
`m ≡ (D/m) (mod 6)` (`P` odd, `Q = 1`); `m ≡ (D/m) (mod 4)` and `(D/m) = 1` (`P` even, `Q = -1`).

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

/-- For nondegenerate `U(P, Q)` with `Q = ±1` and `P` odd if `Q = 1`, there are infinitely many
Lucas pseudoprimes `U_{2m}/P` (`m` an odd prime or a Lucas pseudoprime) that are Frobenius
pseudoprimes and infinitely many that are not. Nondegeneracy is added (the record omits it):
`(P, Q) = (1, 1)` has `U = 0, 1, 1, 0, -1, -1, …`, so `U_{2m}/P ∈ {0, ±1}` is never a
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
