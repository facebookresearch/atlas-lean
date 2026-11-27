/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.Nat.Multiplicity

/-!
# Binomial congruences and Ducci sequences

For prime `p` and positive `k`, Pascal's identity gives the alternating residues of row `p ^ k - 1`
in `choose_prime_pow_sub_one_mod`. Substituting `X ^ (p ^ (k - 1))` for `X` in `(X + 1) ^ (p - 1)`
gives `(X + 1) ^ (p ^ k - p ^ (k - 1))` in characteristic `p`. Its coefficients give the binomial
congruence of Lewis and Tefft for Ducci sequences. For even length, `ducci_pred_iff` characterizes
the image of the Ducci map by the vanishing of the alternating coordinate sum.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.DucciWanted

/-- **Ducci coefficients.** For natural numbers $n$, $r$ and $s$, the Ducci coefficient is
$a_{r,s} = \sum_{0 \le j \le r,\ j \equiv s - 1 \ (\mathrm{mod}\ n)} \binom{r}{j}$, where $s - 1$
is read as $0$ when $s = 0$ and congruence modulo $0$ is equality.

For $1 \le s \le n$, $a_{r,s}$ is the coefficient of $x_s$ in the first entry of $D^r(x)$, where
the Ducci map $D$ on $\mathbb{Z}_m^n$ sends $(x_1, \dots, x_n)$ to
$(x_1 + x_2, x_2 + x_3, \dots, x_n + x_1)$. -/
def ducciCoeff (n r s : ℕ) : ℕ :=
  ∑ j ∈ (Finset.range (r + 1)).filter
    (fun j => j % n = (s - 1) % n), Nat.choose r j

/-- **Binomial coefficients $\binom{p^k - 1}{j}$ modulo $p$.** Let $p$ be a prime, let $k \ge 1$,
and let $j$ be an integer with $0 \le j \le p^k - 1$. Then
$\binom{p^k - 1}{j} \equiv (-1)^j \pmod{p}$.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
Lemma 1. -/
theorem choose_prime_pow_sub_one_mod (p k j : ℕ)
    (hp : p.Prime) (hk : 1 ≤ k) (hj : j ≤ p ^ k - 1) :
    ((Nat.choose (p ^ k - 1) j : ℤ) : ZMod p) = (-1) ^ j := by
  rw [Int.cast_natCast]
  have hpos : 1 ≤ p ^ k := hp.one_le.trans (Nat.le_self_pow (Nat.ne_of_gt hk) p)
  induction j with
  | zero => simp
  | succ j ih =>
    have hzero := (ZMod.natCast_eq_zero_iff _ p).2
      (hp.dvd_choose_pow j.succ_ne_zero (by omega : j.succ ≠ p ^ k))
    have hpascal := Nat.choose_succ_succ (p ^ k - 1) j
    rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hpos] at hpascal
    rw [hpascal, Nat.cast_add, ih (Nat.le_of_succ_le hj)] at hzero
    simpa [pow_succ] using eq_neg_of_add_eq_zero_right hzero

open Polynomial in
set_option linter.unusedVariables false in
/-- **Binomial coefficients $\binom{p^k - p^{k-1}}{j}$ modulo $p$.** Let $p$ be an odd prime,
let $k \ge 2$, and let $j$ be an integer with $0 \le j \le p^k - p^{k-1}$. If $j = c\,p^{k-1}$
for an integer $c$, then $\binom{p^k - p^{k-1}}{j} \equiv (-1)^c \pmod{p}$; otherwise
$\binom{p^k - p^{k-1}}{j} \equiv 0 \pmod{p}$.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
Lemma 2. -/
theorem choose_prime_pow_sub_mod (p k j : ℕ)
    (hp : p.Prime) (hpo : p ≠ 2) (hk : 2 ≤ k)
    (hj : j ≤ p ^ k - p ^ (k - 1)) :
    ((Nat.choose (p ^ k - p ^ (k - 1)) j : ℤ) : ZMod p) =
      if j % p ^ (k - 1) = 0 then (-1) ^ (j / p ^ (k - 1))
      else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  let q := p ^ (k - 1)
  have hq : 0 < q := pow_pos hp.pos _
  have htop : p ^ k - q = q * (p - 1) := by
    dsimp [q]
    rw [Nat.mul_sub, Nat.mul_one, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hc : j / q ≤ p - 1 := calc
    j / q ≤ q * (p - 1) / q := Nat.div_le_div_right (htop ▸ hj)
    _ = p - 1 := Nat.mul_div_cancel_left _ hq
  have hcoeff := choose_prime_pow_sub_one_mod p 1 (j / q) hp le_rfl (by simpa using hc)
  simp only [pow_one, Int.cast_natCast] at hcoeff
  have hexpand : (X + 1 : (ZMod p)[X]) ^ (q * (p - 1)) =
      expand (ZMod p) q ((X + 1) ^ (p - 1)) := by
    simp [q, pow_mul, add_pow_char_pow]
  change ((Nat.choose (p ^ k - q) j : ℤ) : ZMod p) =
    if j % q = 0 then (-1) ^ (j / q) else 0
  rw [Int.cast_natCast, htop, ← coeff_X_add_one_pow, hexpand, coeff_expand hq,
    coeff_X_add_one_pow, hcoeff]
  simp only [Nat.dvd_iff_mod_eq_zero]

/-- The Ducci map on `ℤ_m^n`:
`D(x)_i = x_i + x_{i+1}`, indices cyclic.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
INTEGERS 26 (2026), Article A17, Section 1. -/
def ducciMap (m n : ℕ) [NeZero n] (x : Fin n → ZMod m) : Fin n → ZMod m :=
  fun i => x i + x (i + 1)

open Fin.NatCast in
/-- **Ducci predecessor criterion for even length.** Let $m \ge 0$ be an integer, let $n \ge 2$ be
even, and write $\mathbb{Z}_m = \mathbb{Z}/m\mathbb{Z}$ (so $\mathbb{Z}_0 = \mathbb{Z}$). A tuple
$x = (x_1, \dots, x_n) \in \mathbb{Z}_m^n$ has a Ducci predecessor, that is, a tuple
$y \in \mathbb{Z}_m^n$ with $y_i + y_{i+1} = x_i$ for all $i$ (indices taken cyclically, so
$y_{n+1} = y_1$), if and only if $x_1 - x_2 + x_3 - \cdots + x_{n-1} - x_n = 0$ in $\mathbb{Z}_m$.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
Theorem 2. -/
theorem ducci_pred_iff (m n : ℕ) [NeZero n]
    (hn : Even n) (x : Fin n → ZMod m) :
    (∃ y : Fin n → ZMod m, ∀ i : Fin n, y i + y (i + 1) = x i) ↔
      ∑ i : Fin n, (-1 : ZMod m) ^ i.val * x i = 0 := by
  -- The alternating sum telescopes to the difference of the endpoint values.
  have telescope (y : ℕ → ZMod m) (step : ∀ k : ℕ, y k + y (k + 1) = x k) :
      ∑ i : Fin n, (-1 : ZMod m) ^ i.val * x i = y 0 - y n := by
    calc
      _ = ∑ k ∈ Finset.range n, (-1 : ZMod m) ^ k * x k := by
        simpa using Fin.sum_univ_eq_sum_range (fun k : ℕ => (-1 : ZMod m) ^ k * x k) n
      _ = ∑ k ∈ Finset.range n, ((-1 : ZMod m) ^ k * y k - (-1) ^ (k + 1) * y (k + 1)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← step k]
        simp [mul_add, pow_succ]
      _ = y 0 - y n := by
        simpa [hn.neg_one_pow] using Finset.sum_range_sub' (fun k => (-1 : ZMod m) ^ k * y k) n
  constructor
  · rintro ⟨y, hy⟩
    simpa using telescope (fun k => y k) (fun k => by simpa using hy k)
  · intro h
    let y : ℕ → ZMod m := Nat.rec 0 (fun k previous => x k - previous)
    have step (k : ℕ) : y k + y (k + 1) = x k := by
      change y k + (x k - y k) = x k
      exact add_sub_cancel _ _
    have close : y 0 = y n := sub_eq_zero.mp ((telescope y step).symm.trans h)
    refine ⟨fun i => y i.val, fun i => ?_⟩
    have next : y (i + 1).val = y (i.val + 1) := by
      rcases Nat.lt_or_eq_of_le i.isLt with hi | hi
      · rw [Fin.val_add_one_of_lt' hi]
      · have wrap : i + 1 = 0 := by
          simpa using congrArg (fun k : ℕ => (k : Fin n)) hi
        rw [wrap, Fin.val_zero, show i.val + 1 = n from hi]
        exact close
    simpa only [next, Fin.cast_val_eq_self] using step i.val

/-- The basic tuple `(0, …, 0, 1) ∈ ℤ_m^n`.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
INTEGERS 26 (2026), Article A17, Section 1 (basic Ducci sequence). -/
def ducciBasic (m n : ℕ) [NeZero n] : Fin n → ZMod m :=
  fun i => if i.val = n - 1 then 1 else 0

/-- `L_m(n) = Len(0, …, 0, 1)`: the least `α` such that
`D^{α+β}(u) = D^α(u)` for some `β ≥ 1`, `u` the basic
tuple. The modulus is positive (`[NeZero m]`), so `ℤ_m^n` is
finite and such `α` exists; for `m = 0` the sequence in
`ℤ^n` need not recur.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
INTEGERS 26 (2026), Article A17, Definition 1 and Section 1. -/
noncomputable def ducciMaxLength (m n : ℕ) [NeZero m] [NeZero n] : ℕ :=
  sInf {α | ∃ β, 1 ≤ β ∧
    (ducciMap m n)^[α + β] (ducciBasic m n) = (ducciMap m n)^[α] (ducciBasic m n)}

/-- Characteristic value: in `ℤ_5^4`, `D(0, 0, 0, 1) = (0, 0, 1, 1)`.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
INTEGERS 26 (2026), Article A17, Section 1 (example). -/
theorem ducciMap_basic_five_four :
    ducciMap 5 4 (ducciBasic 5 4) = ![0, 0, 1, 1] := by
  decide

/-- `L_m(n)` is at most any `α` that returns after some
`β ≥ 1` steps.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
INTEGERS 26 (2026), Article A17, Definition 1. -/
theorem ducciMaxLength_le {m n : ℕ} [NeZero m] [NeZero n] {α β : ℕ} (hβ : 1 ≤ β)
    (h : (ducciMap m n)^[α + β] (ducciBasic m n) = (ducciMap m n)^[α] (ducciBasic m n)) :
    ducciMaxLength m n ≤ α :=
  Nat.sInf_le ⟨β, hβ, h⟩

/-- Characteristic value: `L_5(4) ≤ 1`, from the paper's
example `D^5(0, 0, 0, 1) = D(0, 0, 0, 1)` in `ℤ_5^4`.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
INTEGERS 26 (2026), Article A17, Section 1 (example). -/
theorem ducciMaxLength_five_four_le : ducciMaxLength 5 4 ≤ 1 :=
  ducciMaxLength_le (β := 4) (by decide) (by decide)

end MathlibExt.NumberTheory.DucciWanted
