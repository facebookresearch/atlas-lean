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
public import MathlibExt.NumberTheory.GobelResidue

/-!
# Residues of `k`-Göbel sequences modulo prime powers (statements)

The residue sequence `g_{k,p,r}(n)` and its exponent periodicity are re-exported here.
Lemma 2 of Yuh Kobayashi and Shin-ichiro Seki, *On the Length over Which k-Göbel Sequences Remain
Integers*, is proved as `gobelResidue_eq_none_iff` in `MathlibExt.NumberTheory.GobelResidue`. The
`k`-Göbel sequence `g_{k,n}` is `gobelSequence k 2 n`.
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

end

end MetaMathlibExt
