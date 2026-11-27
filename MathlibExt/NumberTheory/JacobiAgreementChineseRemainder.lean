/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.Squarefree

/-!
# Chinese remainder lifts into the Jacobi agreement set

Let `n` be odd and squarefree, `p'` a prime divisor of `n` and `n' = n / p'`. Squarefreeness
makes `n'` and `p'` coprime, so the Chinese remainder theorem lifts a unit `y` of `ℤ/n'ℤ` with
Jacobi symbol `(y/n') = 1` together with any unit `z` of `ℤ/p'ℤ` to a unit `x` of `ℤ/nℤ`. The
Jacobi symbol is multiplicative in the modulus and the factor `n'` contributes `(y/n') = 1`, so
`(x/n) = (x/p')`: the lift lies in the set `L(n;p')` of units whose Jacobi symbols modulo `n` and
modulo `p'` agree.

This is Lemma 4.7 of Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants
Related to the Jacobi Symbol* (arXiv:2111.14477v3).
-/

namespace MetaMathlibExt
namespace jacobi_kernel_prod_units_subset_crt_image

/-- The Jacobi symbol of a natural number only depends on its residue class. -/
private theorem jacobiSym_congr {a b n : ℕ} (h : a ≡ b [MOD n]) :
    jacobiSym a n = jacobiSym b n :=
  jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr h)

end jacobi_kernel_prod_units_subset_crt_image

open jacobi_kernel_prod_units_subset_crt_image in
/-- **Chinese remainder lifts into the Jacobi agreement set.** Let $n$ be an odd squarefree natural
number, $p'$ a prime divisor of $n$ and $n' = n/p'$. For a residue $x$ modulo $N$ and an odd $m$,
write $(x/m)$ for the Jacobi symbol $(a/m)$ of the representative $0 \le a < N$ of $x$. Let $U(m)$
be the group of units of $\mathbb{Z}_m = \mathbb{Z}/m\mathbb{Z}$, let
$S(n') = \{y \in U(n') : (y/n') = 1\}$ and $L(n;p') = \{x \in U(n) : (x/n) = (x/p')\}$, and for
$m \mid n$ let $f_{n,m} : \mathbb{Z}_n \to \mathbb{Z}_m$ be reduction modulo $m$. Then for every
$y \in S(n')$ and every $z \in U(p')$ there is $x \in L(n;p')$ with $f_{n,n'}(x) = y$ and
$f_{n,p'}(x) = z$. That is, the Chinese remainder isomorphism
$\psi = (f_{n,n'}, f_{n,p'}) : U(n) \to U(n') \times U(p')$ satisfies
$S(n') \times U(p') \subseteq \psi(L(n;p'))$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 31
(`jis-2024-24.1.7-lem-31`). -/
public theorem jacobi_kernel_prod_units_subset_crt_image (n p' : ℕ) (hn : Odd n)
    (hsf : Squarefree n) (hp' : p'.Prime) (hp'n : p' ∣ n) (y : ZMod (n / p'))
    (hy : y ∈ {x : ZMod (n / p') | IsUnit x ∧ jacobiSym ((x.val : ℕ) : ℤ) (n / p') = 1})
    (z : ZMod p') (hz : IsUnit z) :
    ∃ x ∈ {x : ZMod n | IsUnit x ∧
        jacobiSym ((x.val : ℕ) : ℤ) n = jacobiSym ((x.val : ℕ) : ℤ) p'},
      ZMod.castHom (Nat.div_dvd_of_dvd hp'n) (ZMod (n / p')) x = y ∧
        ZMod.castHom hp'n (ZMod p') x = z := by
  obtain ⟨hyu, hyJ⟩ := hy
  have hp0 : p' ≠ 0 := hp'.ne_zero
  have hm : n / p' * p' = n := Nat.div_mul_cancel hp'n
  have hm0 : n / p' ≠ 0 := (Nat.div_ne_zero_iff_of_dvd hp'n).mpr ⟨hn.pos.ne', hp0⟩
  have : NeZero (n / p') := ⟨hm0⟩
  have : NeZero p' := ⟨hp0⟩
  -- Squarefreeness makes the two factors coprime.
  have hcop : Nat.Coprime (n / p') p' := Nat.coprime_of_squarefree_mul (hm.symm ▸ hsf)
  have hycop : Nat.Coprime y.val (n / p') := by
    simpa using ZMod.val_coe_unit_coprime hyu.unit
  have hzcop : Nat.Coprime z.val p' := by
    simpa using ZMod.val_coe_unit_coprime hz.unit
  -- The Chinese remainder lift of `(y, z)`, taken below `n`.
  obtain ⟨c, hcn, hcy, hcz⟩ : ∃ c : ℕ, c < n ∧ c ≡ y.val [MOD n / p'] ∧ c ≡ z.val [MOD p'] :=
    ⟨_, (Nat.chineseRemainder_lt_mul hcop _ _ hm0 hp0).trans_eq hm,
      (Nat.chineseRemainder hcop y.val z.val).prop⟩
  refine ⟨(c : ZMod n), ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [ZMod.isUnit_iff_coprime, ← hm]
    exact Nat.Coprime.mul_right ((Nat.ModEq.gcd_eq hcy).trans hycop)
      ((Nat.ModEq.gcd_eq hcz).trans hzcop)
  · -- The factor `n / p'` contributes `(y / (n / p')) = 1`.
    have hmul := jacobiSym.mul_right' (c : ℤ) hm0 hp0
    rw [hm] at hmul
    rw [ZMod.val_natCast_of_lt hcn, hmul, jacobiSym_congr hcy, hyJ, one_mul]
  · rw [map_natCast, (ZMod.natCast_eq_natCast_iff ..).mpr hcy, ZMod.natCast_zmod_val]
  · rw [map_natCast, (ZMod.natCast_eq_natCast_iff ..).mpr hcz, ZMod.natCast_zmod_val]

end MetaMathlibExt
