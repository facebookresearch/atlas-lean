/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import WantedExt.NumberTheory.GobelSequenceWanted

/-!
# Residues of `k`-Göbel sequences modulo prime powers (statements)

Statement-only targets from Yuh Kobayashi and Shin-ichiro Seki, *On the Length over Which
k-Göbel Sequences Remain Integers*: the auxiliary residue sequence `g_{k,p,r}(n)` (after
Matsuhira, Matsusaka, and Tsuchida) and the two facts about it quoted as Lemmas 2 and 3. The
`k`-Göbel sequence `g_{k,n}` is `gobelSequence k 2 n`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Residue sequence of the $k$-Göbel sequence.** Fix natural numbers $k$, $p$, $r$ and write
$\nu_p$ for the $p$-adic valuation. The residue sequence $g_{k,p,r}(n)$, meant for $n \ge 1$ with
$\nu_p(n!) \le r$, takes values in $\mathbb{Z}/p^{r - \nu_p(n!)}\mathbb{Z} \cup \{F\}$, where $F$
is a failure value; a residue class is represented by its least nonnegative representative. It
is defined by $g_{k,p,r}(0) = F$, $g_{k,p,r}(1) = 2 \bmod p^r$ and, for $n \ge 2$, as follows.
If $g_{k,p,r}(n-1) = F$ then $g_{k,p,r}(n) = F$. Otherwise let $g_{k,p,r}(n-1) = a$ and let $N$
be the least nonnegative residue of $(n-1)a + a^k$ modulo $p^{r - \nu_p((n-1)!)}$, with $a^k$
computed by modular exponentiation. If $N \not\equiv 0 \pmod{p^{\nu_p(n)}}$ then
$g_{k,p,r}(n) = F$; otherwise $g_{k,p,r}(n) = (N/p^{\nu_p(n)}) \cdot c \bmod p^{r - \nu_p(n!)}$,
where $c$ is the inverse of the quotient $n/p^{\nu_p(n)}$ modulo $p^{r - \nu_p(n!)}$ (it exists
when $p$ is prime; when no inverse exists, $c$ is the junk value that Mathlib's inverse in
$\mathbb{Z}/p^{r - \nu_p(n!)}\mathbb{Z}$ returns, which need not be $0$).

For a prime $p$ with $\nu_p(n!) \le r$ we have $\nu_p(n) + (r - \nu_p(n!)) = r - \nu_p((n-1)!)$,
so the reduction keeps exactly the information both the divisibility test and the next residue
need, and the recursion agrees with the source's, which tests and divides $(n-1)a + a^k$ itself.
Values with $\nu_p(n!) > r$ and at $n = 0$ are junk and never used.

Source: Yuh Kobayashi and Shin-ichiro Seki, *On the Length over Which k-Göbel Sequences Remain
Integers*, INTEGERS 26 (2026), Article A23, Section 2 (definition of `g_{k,p,r}`, after
Matsuhira, Matsusaka, and Tsuchida, Definition 9). -/
public def gobelResidue (k p r : ℕ) : ℕ → Option ℕ
  | 0 => none
  | 1 => some (2 % p ^ r)
  | n + 2 =>
    match gobelResidue k p r (n + 1) with
    | none => none
    | some a =>
      let N := (((n + 1 : ℕ) : ZMod (p ^ (r - padicValNat p (n + 1).factorial))) * a +
        (a : ZMod (p ^ (r - padicValNat p (n + 1).factorial))) ^ k).val
      if N % p ^ padicValNat p (n + 2) ≠ 0 then none
      else
        some ((N / p ^ padicValNat p (n + 2) *
          (((n + 2) / p ^ padicValNat p (n + 2) :
            ZMod (p ^ (r - padicValNat p (n + 2).factorial)))⁻¹).val) %
            p ^ (r - padicValNat p (n + 2).factorial))

/-- **Initial value of the Göbel residue sequence.** For all natural numbers $k$, $p$, $r$, the
residue sequence satisfies $g_{k,p,r}(1) = 2 \bmod p^r$, the residue class of $2$ modulo $p^r$
(represented by the remainder of $2$ on division by $p^r$).

Source: Yuh Kobayashi and Shin-ichiro Seki, *On the Length over Which k-Göbel Sequences Remain
Integers*, INTEGERS 26 (2026), Article A23, Section 2 (definition of `g_{k,p,r}`). -/
public theorem gobelResidue_one (k p r : ℕ) : gobelResidue k p r 1 = some (2 % p ^ r) := rfl

/-- **Failure of the Göbel residue sequence persists.** For all natural numbers $k$, $p$, $r$ and
every $n \ge 1$, if the residue sequence takes the failure value at $n$, that is
$g_{k,p,r}(n) = F$, then $g_{k,p,r}(n + 1) = F$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *On the Length over Which k-Göbel Sequences Remain
Integers*, INTEGERS 26 (2026), Article A23, Section 2 (definition of `g_{k,p,r}`). -/
public theorem gobelResidue_succ_of_eq_none (k p r n : ℕ) (hn : 1 ≤ n)
    (h : gobelResidue k p r n = none) : gobelResidue k p r (n + 1) = none := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [gobelResidue, h]

/-- **Example value of the Göbel residue sequence.** For $k = 2$, $p = 3$ and $r = 1$, the
residue sequence satisfies $g_{2,3,1}(2) = 0 \bmod 3$; in particular it is not the failure value
$F$. Indeed $g_{2,3,1}(1) = 2$ and
$(1 \cdot 2 + 2^2) \cdot 2^{-1} = 6 \cdot 2^{-1} \equiv 0 \pmod 3$.

Source: Yuh Kobayashi and Shin-ichiro Seki, *On the Length over Which k-Göbel Sequences Remain
Integers*, INTEGERS 26 (2026), Article A23, Section 2 (definition of `g_{k,p,r}`). -/
public theorem gobelResidue_two_three_one_two : gobelResidue 2 3 1 2 = some 0 := by
  decide +kernel

/-- **Failure of the residue sequence detects non-integrality.** Let $k \ge 2$ and $r \ge 1$ be
integers, let $p$ be a prime, write $\nu_p$ for the $p$-adic valuation, and let $n \ge 1$ be an
integer with $\nu_p(n!) \le r$. Then the residue sequence $g_{k,p,r}$ takes the failure value $F$
at $n$, that is $g_{k,p,r}(n) = F$, if and only if the value $g_{k,2}(n)$ of the $(k, 2)$-Göbel
sequence has negative $p$-adic valuation, that is $g_{k,2}(n) \notin \mathbb{Z}_{(p)}$.

This is Lemma 10 of Matsuhira, Matsusaka, and Tsuchida.

Source: Yuh Kobayashi and Shin-ichiro Seki, *On the Length over Which k-Göbel Sequences Remain
Integers*, INTEGERS 26 (2026), Article A23, Lemma 2 (`integers-2026-A23-lem-2`). -/
public theorem_wanted gobelResidue_eq_none_iff (k p r n : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r)
    (hp : p.Prime) (hn : 1 ≤ n) (hnr : padicValNat p n.factorial ≤ r) :
    gobelResidue k p r n = none ↔ padicValRat p (gobelSequence k 2 n) < 0

/-- **Periodicity of the Göbel residue sequence in the exponent.** Let $p$ be a prime, $r \ge 1$,
and $k$, $l$ integers with $r + 1 \le k \le l$ and $k \equiv l \pmod{\varphi(p^r)}$, where
$\varphi$ is Euler's totient function. Write $\nu_p$ for the $p$-adic valuation. Then every
integer $n \ge 1$ with $\nu_p(n!) \le r$ satisfies $g_{k,p,r}(n) = g_{l,p,r}(n)$, where both
sides are values of the residue sequence (so either both are the failure value $F$ or both are
the same residue class).

This is Proposition 12 of Matsuhira, Matsusaka, and Tsuchida.

Source: Yuh Kobayashi and Shin-ichiro Seki, *On the Length over Which k-Göbel Sequences Remain
Integers*, INTEGERS 26 (2026), Article A23, Lemma 3 (`integers-2026-A23-lem-3`). -/
public theorem_wanted gobelResidue_eq_of_modEq_totient (p r k l n : ℕ) (hp : p.Prime)
    (hr : 1 ≤ r) (hk : r + 1 ≤ k) (hkl : k ≤ l) (hmod : k ≡ l [MOD (p ^ r).totient])
    (hn : 1 ≤ n) (hnr : padicValNat p n.factorial ≤ r) :
    gobelResidue k p r n = gobelResidue l p r n

end

end MetaMathlibExt
