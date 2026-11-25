/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.NumberTheory.PrimitiveDivisor
public import MathlibExt.NumberTheory.RieselRepdigit101
public import MathlibExt.NumberTheory.SierpinskiRepinteger18107

/-!
# Further results on Sierpiński and Riesel repdigits, repintegers and repstrings

Statements from Bispels et al., *On Sierpiński and Riesel Repdigits and Repintegers*,
INTEGERS 26 (2026), Article A12.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Covering-produced Sierpiński numbers give infinitely many Sierpiński repintegers.** Let $k$
be a Sierpiński number that has Sierpiński covering data, so that $k$ is produced as a Sierpiński
number by the covering system method. Then for every natural number $b \ge 2$ there are infinitely
many $t \ge 1$ such that the $b$-repinteger $k_b^{(t)} = k\,(b^{\ell t} - 1)/(b^{\ell} - 1)$, where
$\ell$ is the number of base-$b$ digits of $k$ (so $k_b^{(t)}$ is $k$ written $t$ times in base
$b$), is a Sierpiński number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.3
(`integers-2026-A12-thm-3-3`). -/
public theorem_wanted infinite_sierpinski_repintegers {k : ℕ} (hk : IsSierpinskiNumber k)
    {S : Finset (ℕ × ℕ × ℕ)} (hS : IsSierpinskiCoveringData k S) {b : ℕ} (hb : 2 ≤ b) :
    {t : ℕ | 1 ≤ t ∧ IsSierpinskiNumber (repstring b k 0 t)}.Infinite

/-- **Covering-produced Riesel numbers give infinitely many Riesel repintegers.** Let $k$ be a
Riesel number that has Riesel covering data, so that $k$ is produced as a Riesel number by the
covering system method. Then for every natural number $b \ge 2$ there are infinitely many $t \ge 1$
such that the $b$-repinteger $k_b^{(t)} = k\,(b^{\ell t} - 1)/(b^{\ell} - 1)$, where $\ell$ is the
number of base-$b$ digits of $k$ (so $k_b^{(t)}$ is $k$ written $t$ times in base $b$), is a Riesel
number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.4 (stated in record
`integers-2026-A12-thm-3-3`). -/
public theorem_wanted infinite_riesel_repintegers {k : ℕ} (hk : IsRieselNumber k)
    {S : Finset (ℕ × ℕ × ℕ)} (hS : IsRieselCoveringData k S) {b : ℕ} (hb : 2 ≤ b) :
    {t : ℕ | 1 ≤ t ∧ IsRieselNumber (repstring b k 0 t)}.Infinite

/-- **Binary repintegers of 18107 that are Riesel numbers.** For every natural number
$t \equiv 31 \pmod{56}$, the binary repinteger $18107_2^{(t)} = 18107\,(2^{15t} - 1)/(2^{15} - 1)$,
whose binary expansion is that of $18107$ (fifteen binary digits) written $t$ times, is a Riesel
number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.6
(`integers-2026-A12-thm-3-6`). -/
public theorem_wanted isRieselNumber_repstring_18107 {t : ℕ} (ht : t ≡ 31 [MOD 56]) :
    IsRieselNumber (repstring 2 18107 0 t)

/-- **Infinitely many Sierpiński repdigits in every base $b > 78557$.** Let $b > 78557$ be a
natural number. Then there are infinitely many Sierpiński numbers of the form $k(b^t - 1)/(b - 1)$
with $1 \le k < b$ and $t \ge 1$, that is, $b$-repdigits: the digit $k$ written $t$ times in
base $b$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Corollary 3.7
(`integers-2026-A12-cor-3-7`). -/
public theorem_wanted infinite_sierpinski_repdigits {b : ℕ} (hb : 78557 < b) :
    {N : ℕ | ∃ k t : ℕ, 1 ≤ k ∧ k < b ∧ 1 ≤ t ∧ N = repstring b k 0 t ∧
      IsSierpinskiNumber N}.Infinite

/-- **Infinitely many Riesel repdigits in every base $b > 509203$.** Let $b > 509203$ be a
natural number. Then there are infinitely many Riesel numbers of the form $k(b^t - 1)/(b - 1)$ with
$1 \le k < b$ and $t \ge 1$, that is, $b$-repdigits: the digit $k$ written $t$ times in base $b$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Corollary 3.8
(`integers-2026-A12-cor-3-8`). -/
public theorem_wanted infinite_riesel_repdigits {b : ℕ} (hb : 509203 < b) :
    {N : ℕ | ∃ k t : ℕ, 1 ≤ k ∧ k < b ∧ 1 ≤ t ∧ N = repstring b k 0 t ∧
      IsRieselNumber N}.Infinite

/-- **Repdigits with digit 41 that are Sierpiński numbers.** Let $b$ and $t$ be natural numbers
with $b \equiv 87 \pmod{11184810}$ and $t \equiv 59 \pmod{120}$. Then the base-$b$ repdigit
$41_b^{(t)} = 41\,(b^t - 1)/(b - 1)$ is a Sierpiński number. Since $b \ge 87 > 41$, its $t$
base-$b$ digits all equal $41$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.9
(`integers-2026-A12-thm-3-9`). -/
public theorem_wanted isSierpinskiNumber_repstring_41 {b t : ℕ} (hb : b ≡ 87 [MOD 11184810])
    (ht : t ≡ 59 [MOD 120]) : IsSierpinskiNumber (repstring b 41 0 t)

/-- **Infinitely many Sierpiński repunits from primitive divisors of $2^{2^j} - 1$.** Let $\tau$
be a natural number. For $1 \le j \le \tau$ let $p_j$ be a primitive prime divisor of
$2^{2^j} - 1$ in the sequence $(2^m - 1)_{m \ge 0}$, and let $q \ne p_\tau$ be a primitive prime
divisor of $2^{2^\tau} - 1$ in the same sequence. Let $b > 2$ be a natural number with $q \nmid b$.
For $1 \le j \le \tau$ put $\ell_j = 1$ if $p_j \mid b$, $\ell_j = p_j$ if $p_j \nmid b$ and
$b \equiv 1 \pmod{p_j}$, and otherwise $\ell_j = \operatorname{ord}_{p_j}(b)$, the multiplicative
order of $b$ modulo $p_j$; let $L = \operatorname{lcm}(2, \ell_1, \dots, \ell_\tau)$. Suppose that
either (i) $b \equiv 1 \pmod q$ and $q \nmid L$, or (ii) $b \not\equiv 1 \pmod q$ and there is a
natural number $s \equiv 1 \pmod L$ with $(b^s - 1)/(b - 1) \equiv -1 \pmod q$. Then there are
infinitely many Sierpiński numbers among the $b$-repunits $(b^t - 1)/(b - 1)$ with $t \ge 1$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.11
(`integers-2026-A12-thm-3-11`). -/
public theorem_wanted infinite_sierpinski_repunits_of_primitive_divisors (τ : ℕ) (p : ℕ → ℕ)
    (hp : ∀ j ∈ Finset.Icc 1 τ,
      IntegerSequence.IsPrimitivePrimeDivisor (fun m => (2 : ℤ) ^ m - 1) (2 ^ j) (p j))
    (q : ℕ) (hq : IntegerSequence.IsPrimitivePrimeDivisor (fun m => (2 : ℤ) ^ m - 1) (2 ^ τ) q)
    (hqp : q ≠ p τ) (b : ℕ) (hb : 2 < b) (hbq : ¬ q ∣ b)
    (hcase :
      let ℓ : ℕ → ℕ := fun j =>
        if p j ∣ b then 1 else if b ≡ 1 [MOD p j] then p j else orderOf (b : ZMod (p j))
      let L : ℕ := Nat.lcm 2 ((Finset.Icc 1 τ).lcm ℓ)
      (b ≡ 1 [MOD q] ∧ ¬ q ∣ L) ∨
        (¬ b ≡ 1 [MOD q] ∧ ∃ t : ℕ, (((b ^ t - 1) / (b - 1) : ℕ) : ℤ) ≡ -1 [ZMOD q] ∧
          t ≡ 1 [MOD L])) :
    {N : ℕ | ∃ t : ℕ, 1 ≤ t ∧ N = repstring b 1 0 t ∧ IsSierpinskiNumber N}.Infinite

/-- **Infinitely many Sierpiński repunits in bases $b \equiv 1, 147, 265, 378 \pmod{641}$ with
$b \not\equiv 1 \pmod 5$.** Let $b > 2$ be a natural number with $b \equiv c \pmod{641}$ for some
$c \in \{1, 147, 265, 378\}$ and $b \not\equiv 1 \pmod 5$. Then there are infinitely many
Sierpiński numbers among the $b$-repunits $(b^t - 1)/(b - 1)$ with $t \ge 1$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Corollary 3.12
(`integers-2026-A12-cor-3-12`). -/
public theorem_wanted infinite_sierpinski_repunits_mod_641 {b : ℕ} (hb : 2 < b)
    (h641 : ∃ c ∈ ({1, 147, 265, 378} : Finset ℕ), b ≡ c [MOD 641]) (h5 : ¬ b ≡ 1 [MOD 5]) :
    {N : ℕ | ∃ t : ℕ, 1 ≤ t ∧ N = repstring b 1 0 t ∧ IsSierpinskiNumber N}.Infinite

/-- **Infinitely many Riesel repunits from primitive divisors of $2^{2^j} - 1$.** Let $\tau$ be a
natural number. For $1 \le j \le \tau$ let $p_j$ be a primitive prime divisor of $2^{2^j} - 1$ in
the sequence $(2^m - 1)_{m \ge 0}$, let $q \ne p_\tau$ be a primitive prime divisor of
$2^{2^\tau} - 1$ in the same sequence, and put $P = p_1 \cdots p_\tau$. Let $b > 2$ be a natural
number with $b \equiv 1 \pmod P$, and suppose that (i) $q \mid b$, or (ii) $b \equiv 1 \pmod q$, or
(iii) $q \nmid b$, $b \not\equiv 1 \pmod q$ and $\gcd(P, \operatorname{ord}_q(b)) = 1$, where
$\operatorname{ord}_q(b)$ is the multiplicative order of $b$ modulo $q$. Then there are infinitely
many Riesel numbers among the $b$-repunits $(b^t - 1)/(b - 1)$ with $t \ge 1$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.13
(`integers-2026-A12-thm-3-13`). -/
public theorem_wanted infinite_riesel_repunits_of_primitive_divisors (τ : ℕ) (p : ℕ → ℕ)
    (hp : ∀ j ∈ Finset.Icc 1 τ,
      IntegerSequence.IsPrimitivePrimeDivisor (fun m => (2 : ℤ) ^ m - 1) (2 ^ j) (p j))
    (q : ℕ) (hq : IntegerSequence.IsPrimitivePrimeDivisor (fun m => (2 : ℤ) ^ m - 1) (2 ^ τ) q)
    (hqp : q ≠ p τ) (b : ℕ) (hb : 2 < b) (hbP : b ≡ 1 [MOD ∏ j ∈ Finset.Icc 1 τ, p j])
    (hcase : q ∣ b ∨ b ≡ 1 [MOD q] ∨
      (¬ q ∣ b ∧ ¬ b ≡ 1 [MOD q] ∧
        Nat.Coprime (∏ j ∈ Finset.Icc 1 τ, p j) (orderOf (b : ZMod q)))) :
    {N : ℕ | ∃ t : ℕ, 1 ≤ t ∧ N = repstring b 1 0 t ∧ IsRieselNumber N}.Infinite

/-- **Infinitely many Riesel repunits in bases $b \equiv 16518444216571 \pmod{2^{64} - 1}$.**
Let $b$ be a natural number with $b \equiv 16518444216571 \pmod{18446744073709551615}$, where
$18446744073709551615 = 2^{64} - 1$. Then there are infinitely many Riesel numbers among the
$b$-repunits $(b^t - 1)/(b - 1)$ with $t \ge 1$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Corollary 3.14
(`integers-2026-A12-cor-3-14`). -/
public theorem_wanted infinite_riesel_repunits_mod_two_pow_64_sub_one {b : ℕ}
    (hb : b ≡ 16518444216571 [MOD 18446744073709551615]) :
    {N : ℕ | ∃ t : ℕ, 1 ≤ t ∧ N = repstring b 1 0 t ∧ IsRieselNumber N}.Infinite

/-- **Binary repstrings of 659 that are Sierpiński numbers.** For every natural number $t$ with
$t \equiv 131 \pmod{2730}$ or $t \equiv 1361 \pmod{2730}$, the binary repstring
$659_2^{(2;t)} = 659\,(2^{12t} - 1)/(2^{12} - 1)$ is a Sierpiński number. Its binary expansion is
that of $659$ (ten binary digits) written $t$ times with two zeros between consecutive copies.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 4.3
(`integers-2026-A12-thm-4-3`). -/
public theorem_wanted isSierpinskiNumber_repstring_659 {t : ℕ}
    (ht : t ≡ 131 [MOD 2730] ∨ t ≡ 1361 [MOD 2730]) : IsSierpinskiNumber (repstring 2 659 2 t)

/-- **Binary repstrings of 659 that are Riesel numbers.** For every natural number $t$ with
$t \equiv 1369 \pmod{2730}$ or $t \equiv 2599 \pmod{2730}$, the binary repstring
$659_2^{(2;t)} = 659\,(2^{12t} - 1)/(2^{12} - 1)$ is a Riesel number. Its binary expansion is that
of $659$ (ten binary digits) written $t$ times with two zeros between consecutive copies.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 4.4
(`integers-2026-A12-thm-4-4`). -/
public theorem_wanted isRieselNumber_repstring_659 {t : ℕ}
    (ht : t ≡ 1369 [MOD 2730] ∨ t ≡ 2599 [MOD 2730]) : IsRieselNumber (repstring 2 659 2 t)

/-- **Theorem 4.6 (Sierpiński and Riesel repstring coverings correspond).** Let $k \ge 1$,
$\mathfrak{t} \ge 1$, $w \ge 1$ and $z \ge 0$ be natural numbers. There is a single finite set
of triples that is Sierpiński covering data for the $2$-repstring $k_2^{(z;t)}$ for every
$t \ge 1$ with $t \equiv \mathfrak{t} \pmod{w}$ if and only if there is a single finite set
of triples that is Riesel covering data for $k_2^{(z;t')}$ for every $t' \ge 1$ with
$t' \equiv -\mathfrak{t} \pmod{w}$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 4.6
(`integers-2026-A12-thm-4-6`). -/
public theorem_wanted sierpinskiCoveringData_repstring_iff_riesel {k 𝔱 w : ℕ} (hk : 1 ≤ k)
    (h𝔱 : 1 ≤ 𝔱) (hw : 1 ≤ w) (z : ℕ) :
    (∃ S : Finset (ℕ × ℕ × ℕ), ∀ t : ℕ, 1 ≤ t → t ≡ 𝔱 [MOD w] →
        IsSierpinskiCoveringData (repstring 2 k z t) S) ↔
      ∃ S' : Finset (ℕ × ℕ × ℕ), ∀ t' : ℕ, 1 ≤ t' → (t' : ℤ) ≡ -(𝔱 : ℤ) [ZMOD w] →
        IsRieselCoveringData (repstring 2 k z t') S'

end

end MetaMathlibExt
