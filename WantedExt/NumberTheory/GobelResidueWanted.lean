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

/-- The residue sequence `g_{k,p,r}(n) ∈ ℤ/p^{r - ν_p(n!)}ℤ ∪ {F}` of the `k`-Göbel sequence, for
`n ≥ 1` with `ν_p(n!) ≤ r`: `g_{k,p,r}(1) = 2 mod p^r`; if `g_{k,p,r}(n-1) = F` then
`g_{k,p,r}(n) = F`; if `g_{k,p,r}(n-1) = a mod p^{r - ν_p((n-1)!)}` and
`(n-1)a + a^k ≢ 0 (mod p^{ν_p(n)})` then `g_{k,p,r}(n) = F`; otherwise
`g_{k,p,r}(n) = ((n-1)a + a^k)/p^{ν_p(n)} · c mod p^{r - ν_p(n!)}` with
`c (n/p^{ν_p(n)}) ≡ 1 (mod p^{r - ν_p(n!)})`. Here `F` is `none`, and a residue class is
`some` of its least nonnegative representative. The numerator `(n-1)a + a^k` is computed modulo
`p^{r - ν_p((n-1)!)}` (modular exponentiation, never the full `a^k`); since
`ν_p(n) + (r - ν_p(n!)) = r - ν_p((n-1)!)`, this keeps exactly the information both the
divisibility test and the next residue need. Values with `ν_p(n!) > r` and at `n = 0` are
junk and never used.

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

/-- Initial value `g_{k,p,r}(1) = 2 mod p^r`.

Source: Yuh Kobayashi and Shin-ichiro Seki, *On the Length over Which k-Göbel Sequences Remain
Integers*, INTEGERS 26 (2026), Article A23, Section 2 (definition of `g_{k,p,r}`). -/
public theorem gobelResidue_one (k p r : ℕ) : gobelResidue k p r 1 = some (2 % p ^ r) := rfl

/-- Once the residue sequence fails (`F`), it stays `F`.

Source: Yuh Kobayashi and Shin-ichiro Seki, *On the Length over Which k-Göbel Sequences Remain
Integers*, INTEGERS 26 (2026), Article A23, Section 2 (definition of `g_{k,p,r}`). -/
public theorem gobelResidue_succ_of_eq_none (k p r n : ℕ) (hn : 1 ≤ n)
    (h : gobelResidue k p r n = none) : gobelResidue k p r (n + 1) = none := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [gobelResidue, h]

/-- For `k = 2`, `p = 3`, `r = 1`: `g(2) = (1·2 + 2²) · 2⁻¹ = 0 mod 3`.

Source: Yuh Kobayashi and Shin-ichiro Seki, *On the Length over Which k-Göbel Sequences Remain
Integers*, INTEGERS 26 (2026), Article A23, Section 2 (definition of `g_{k,p,r}`). -/
public theorem gobelResidue_two_three_one_two : gobelResidue 2 3 1 2 = some 0 := by
  decide +kernel

/-- Lemma 2 (Matsuhira–Matsusaka–Tsuchida, Lemma 10): for `k ≥ 2`, `r ≥ 1`, a prime `p` and a
positive integer `n` with `ν_p(n!) ≤ r`, `g_{k,p,r}(n) = F` if and only if `g_{k,n} ∉ ℤ_(p)`.

Source: Yuh Kobayashi and Shin-ichiro Seki, *On the Length over Which k-Göbel Sequences Remain
Integers*, INTEGERS 26 (2026), Article A23, Lemma 2 (`integers-2026-A23-lem-2`). -/
public theorem_wanted gobelResidue_eq_none_iff (k p r n : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r)
    (hp : p.Prime) (hn : 1 ≤ n) (hnr : padicValNat p n.factorial ≤ r) :
    gobelResidue k p r n = none ↔ padicValRat p (gobelSequence k 2 n) < 0

/-- Lemma 3 (Matsuhira–Matsusaka–Tsuchida, Proposition 12): for a prime `p`, `r ≥ 1`, and
integers `r + 1 ≤ k ≤ l` with `k ≡ l (mod φ(p^r))`, every positive integer `n` with
`ν_p(n!) ≤ r` has `g_{k,p,r}(n) = g_{l,p,r}(n)`.

Source: Yuh Kobayashi and Shin-ichiro Seki, *On the Length over Which k-Göbel Sequences Remain
Integers*, INTEGERS 26 (2026), Article A23, Lemma 3 (`integers-2026-A23-lem-3`). -/
public theorem_wanted gobelResidue_eq_of_modEq_totient (p r k l n : ℕ) (hp : p.Prime)
    (hr : 1 ≤ r) (hk : r + 1 ≤ k) (hkl : k ≤ l) (hmod : k ≡ l [MOD (p ^ r).totient])
    (hn : 1 ≤ n) (hnr : padicValNat p n.factorial ≤ r) :
    gobelResidue k p r n = gobelResidue l p r n

end

end MetaMathlibExt
