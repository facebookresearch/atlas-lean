/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.GobelResidueExponentPeriod
public import WantedExt.NumberTheory.GobelSequenceWanted

/-!
# Residues of `k`-Göbel sequences modulo prime powers (statements)

The residue sequence `g_{k,p,r}(n)` and its exponent periodicity are re-exported here.
The remaining target is Lemma 2 of Yuh Kobayashi and Shin-ichiro Seki, *On the Length over Which
k-Göbel Sequences Remain Integers*. The `k`-Göbel sequence `g_{k,n}` is `gobelSequence k 2 n`.
-/

namespace MetaMathlibExt

@[expose] public section

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

end

end MetaMathlibExt
