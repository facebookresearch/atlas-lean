/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.PowModTotient

/-!
# Periodicity of Göbel residues in the exponent

For a prime `p`, the recursively computed Göbel residues agree for sufficiently large
exponents congruent modulo `Nat.totient (p ^ r)`.
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

-- At precision zero the ring is trivial; otherwise a base is either a unit or a
-- multiple of `p`, whose large enough powers vanish.
private theorem natCast_pow_eq_of_modEq_totient {p r s k l : ℕ} (hp : p.Prime)
    (hs : s ≤ r) (hk : r + 1 ≤ k) (hkl : k ≤ l) (hmod : k ≡ l [MOD (p ^ r).totient])
    (a : ℕ) : (a : ZMod (p ^ s)) ^ k = (a : ZMod (p ^ s)) ^ l := by
  rcases s with _ | s
  · rw [pow_zero]
    exact Subsingleton.elim _ _
  by_cases ha : p ∣ a
  · have hzero (e : ℕ) (he : s + 1 ≤ e) : (a : ZMod (p ^ (s + 1))) ^ e = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact (pow_dvd_pow p he).trans (pow_dvd_pow_of_dvd ha e)
    rw [hzero k (by omega), hzero l (by omega)]
  · have hcop : a.Coprime (p ^ (s + 1)) := (hp.coprime_iff_not_dvd.mpr ha).symm.pow_right _
    have hmod' := hmod.of_dvd (Nat.totient_dvd_of_dvd (pow_dvd_pow p hs))
    have hlarge : 1 < p ^ (s + 1) := one_lt_pow₀ hp.one_lt (Nat.succ_ne_zero s)
    rw [← Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff]
    change a ^ k % p ^ (s + 1) = a ^ l % p ^ (s + 1)
    rw [Nat.pow_totient_mod hlarge hcop (k := k), Nat.pow_totient_mod hlarge hcop (k := l)]
    exact congrArg (fun e => a ^ e % p ^ (s + 1)) hmod'

/-- **Periodicity of the Göbel residue sequence in the exponent.** Let $p$ be a prime, $r \ge 1$,
and $k$, $l$ integers with $r + 1 \le k \le l$ and $k \equiv l \pmod{\varphi(p^r)}$, where
$\varphi$ is Euler's totient function. Write $\nu_p$ for the $p$-adic valuation. Then every
integer $n \ge 1$ with $\nu_p(n!) \le r$ satisfies $g_{k,p,r}(n) = g_{l,p,r}(n)$, where both
sides are values of the residue sequence (so either both are the failure value $F$ or both are
the same residue class).

This is Proposition 12 of Matsuhira, Matsusaka, and Tsuchida.

Source: Yuh Kobayashi and Shin-ichiro Seki, *On the Length over Which k-Göbel Sequences Remain
Integers*, INTEGERS 26 (2026), Article A23, Lemma 3 (`integers-2026-A23-lem-3`). -/
public theorem gobelResidue_eq_of_modEq_totient (p r k l n : ℕ) (hp : p.Prime)
    (hr : 1 ≤ r) (hk : r + 1 ≤ k) (hkl : k ≤ l) (hmod : k ≡ l [MOD (p ^ r).totient])
    (hn : 1 ≤ n) (hnr : padicValNat p n.factorial ≤ r) :
    gobelResidue k p r n = gobelResidue l p r n := by
  obtain ⟨r₀, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction m with
  | zero => rfl
  | succ m ih =>
    have hval : padicValNat p (m + 1).factorial ≤ padicValNat p (m + 2).factorial := by
      simp only [Nat.padicValNat_def]
      exact (Nat.pow_dvd_iff_le_multiplicity hp.ne_one (Nat.factorial_ne_zero (m + 2))).mp
        ((pow_multiplicity_dvd _ _).trans (Nat.factorial_dvd_factorial (by omega)))
    have hprev := hval.trans hnr
    -- The two recurrences now inspect the same option, then the same representative `N`.
    rw [gobelResidue.eq_3, gobelResidue.eq_3, ih hprev]
    cases gobelResidue l p r₀.succ (m + 1) with
    | none => rfl
    | some a =>
      dsimp only
      rw [natCast_pow_eq_of_modEq_totient hp (Nat.sub_le _ _) hk hkl hmod a]

end

end MetaMathlibExt
