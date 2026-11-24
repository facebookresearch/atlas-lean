/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Interval.Finset.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Totient
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Ring

/-!
# Colorings for `x - y = z ^ k`

Let `c : ZMod p → Fin 3` be rainbow-free for `x - y = z ^ k`: no solution has `c x`, `c y`, `c z`
pairwise distinct. For `a i : ZMod p` and `ℓ : ℕ`, the `aᵏ`-string at `i` of length `ℓ` is
`i aᵏ, (i + 1) aᵏ, …, (i + ℓ - 1) aᵏ`. If it takes exactly two colors, it contains the color `c a`.

A string taking two colors changes color between two consecutive terms `y = (i + t) aᵏ` and
`x = (i + t + 1) aᵏ`. Since `x - y = aᵏ`, the solution `(x, y, a)` is not rainbow, which forces
`c a = c y` or `c a = c x`. This is the proof of Lemma 4.5 in Katie Ansaldi, Gabriel Cowley,
Eric Green, Kihyun Kim and JT Rapp, *Rainbow Free Colorings and Rainbow Numbers for x-y=z^2*,
arXiv:2305.15133v1 (2023), which treats `x - y = z ^ k`. The proof does not use the hypotheses
that `c` is surjective, that `a ≠ 0` and that `p` is prime, which the statement keeps.

The digraph `G^k_p` has vertex set `ZMod p` and edges `a → a ^ k`, so `m` steps lead from `a` to
`a ^ k ^ m`. Let `t` be the largest divisor of `p - 1` coprime to `k`. A nonzero `a` lies on a cycle
of `G^k_p` exactly when its multiplicative order `n` divides `t`; this is Theorem 4.11 of the arXiv
version cited above, quoted there from earlier work without proof. In the unit group, `a ^ j = a`
holds exactly when `j ≡ 1 [MOD n]`, and `n ∣ p - 1` by Lagrange's theorem. A cycle `a ^ k ^ m = a`
with `m ≥ 1` makes `k` coprime to `n`, so `lcm n t` is a divisor of `p - 1` coprime to `k`, and the
maximality of `t` gives `lcm n t = t`, that is `n ∣ t`. Conversely, if `n ∣ t`, then `k` is a unit
modulo `n`, and its order `m ≥ 1` in `(ZMod n)ˣ` satisfies `k ^ m ≡ 1 [MOD n]`. The proof does not
use the hypothesis that `p` is odd, which the statement keeps.

## Main results

* `MetaMathlibExt.exists_small_gap_of_limsup_count` gives a recurring positive gap below `n₀`
  when the count of a set in `[1, n]` exceeds `n / n₀` by arbitrarily large amounts.
* `MetaMathlibExt.color_dominant_powStrings_of_rainbowFree_zmod`: in an exact rainbow-free
  3-coloring of `ℤ/pℤ` for `x - y = z ^ k`, every bichromatic `aᵏ`-string with `a ≠ 0` contains
  the color `c a`.
* `MetaMathlibExt.color_one_dominant_of_rainbowFree_powDiff`: every bichromatic interval of
  positive integers contains the color of one.
* `MetaMathlibExt.exists_coprime_same_colors_of_coprime_dist` gives coprime representatives
  preserving both colors and the distance when the distance is coprime to the modulus.
* `MetaMathlibExt.isCycleVertex_powMap_iff_orderOf_dvd`: a nonzero `a : ZMod p` satisfies
  `a ^ k ^ m = a` for some `m ≥ 1` if and only if `orderOf a` divides the largest divisor of
  `p - 1` coprime to `k`.

## Implementation notes

This module does not import the field structure on `ZMod p` (`Mathlib.Algebra.Field.ZMod`). With
it in scope, `orderOf a`, `a ^ j` and `a ≠ 0` for `a : ZMod p` would elaborate through that
instance rather than `ZMod.commRing`, so the cycle-vertex proof works in the unit group
`(ZMod p)ˣ` and takes `Fintype.card (ZMod p)ˣ = p - 1` from `Mathlib.Data.Nat.Totient`.
-/

public section

namespace MetaMathlibExt

namespace exists_small_gap_of_limsup_count

/-- More points than blocks of length `k` force a pair less than `k` apart. -/
private theorem exists_close_pair {s : Finset ℕ} {n k : ℕ} (hk : 0 < k)
    (hs : ∀ x ∈ s, x ≤ n) (hc : n / k + 1 < s.card) :
    ∃ x ∈ s, ∃ y ∈ s, x < y ∧ y < x + k := by
  by_contra! hsep
  have hmono : StrictMonoOn (· / k) (s : Set ℕ) := by
    intro x hx y hy hxy
    calc
      x / k < (x + k) / k := by rw [Nat.add_div_right _ hk]; omega
      _ ≤ y / k := Nat.div_le_div_right (hsep x hx y hy hxy)
  have hmap : Set.MapsTo (· / k) s (Finset.range (n / k + 1)) := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (hs x hx)))
  have hle := Finset.card_le_card_of_injOn _ hmap hmono.injOn
  exact hc.not_ge (by simpa using hle)

end exists_small_gap_of_limsup_count

open Filter exists_small_gap_of_limsup_count in
/-- **Zhan's small-gap lemma.** Let $S$ be a set of natural numbers, let $n_0 \ge 2$ be an
integer, and write $S(n)$ for the number of elements of $S \cap \{1, \dots, n\}$. If
$\limsup_{n \to \infty} (S(n) - n / n_0) = \infty$, that is, for every real $M$ there are
arbitrarily large $n$ with $S(n) - n / n_0 > M$, then there is an integer $d$ with
$1 \le d \le n_0 - 1$ such that $j$ and $j + d$ both lie in $S$ for arbitrarily large $j$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 3
(`integers-2024-A105-lem-3`). -/
theorem exists_small_gap_of_limsup_count (S : Set ℕ) [DecidablePred (· ∈ S)]
    (n₀ : ℕ) (hn₀ : 2 ≤ n₀)
    (hS : ∀ M : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧
      M < (((Finset.Icc 1 n).filter (· ∈ S)).card : ℝ) - n / n₀) :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ n₀ - 1 ∧ ∀ i : ℕ, ∃ j : ℕ, i < j ∧ j ∈ S ∧ j + d ∈ S := by
  let gaps := Finset.Icc 1 (n₀ - 1)
  suffices h : ∃ᶠ j in atTop, ∃ d ∈ gaps, j ∈ S ∧ j + d ∈ S by
    obtain ⟨d, hd, hj⟩ := gaps.frequently_exists.mp h
    exact ⟨d, (Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2, frequently_atTop'.mp hj⟩
  apply frequently_atTop'.mpr
  intro i
  obtain ⟨n, -, hn⟩ := hS (i + 1) i
  let s := (Finset.Icc 1 n).filter (· ∈ S)
  -- Discarding the first `i` positions still leaves more points than quotient blocks.
  have hcount : i + 1 + n / n₀ < s.card := by
    have hdiv : ((n / n₀ : ℕ) : ℝ) ≤ n / n₀ := Nat.cast_div_le
    exact_mod_cast (add_le_add_right hdiv ((i : ℝ) + 1)).trans_lt (lt_sub_iff_add_lt.mp hn)
  have htail : n / n₀ + 1 < (s \ Finset.Icc 1 i).card := by
    have hle := Finset.card_le_card_sdiff_add_card (s := s) (t := Finset.Icc 1 i)
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at hle
    omega
  obtain ⟨x, hx, y, hy, hxy, hdist⟩ := exists_close_pair (by omega : 0 < n₀)
    (fun x hx => (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hx).1).1).2) htail
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc] at hx hy
  refine ⟨x, by omega, y - x, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hx.1.2, ?_⟩
  simpa [Nat.add_sub_of_le hxy.le] using hy.1.2

namespace color_dominant_powStrings_of_rainbowFree_zmod

/-- A string `f 0, f 1, …, f (ℓ - 1)` that takes at least two values changes value between two
consecutive positions. -/
private theorem exists_succ_ne_of_one_lt_card_image {α : Type*} [DecidableEq α] (f : ℕ → α)
    (ℓ : ℕ) (h : 1 < ((Finset.range ℓ).image f).card) : ∃ t, t + 1 < ℓ ∧ f t ≠ f (t + 1) := by
  by_contra! hne
  have hconst : ∀ t < ℓ, f t = f 0 := by
    intro t ht
    induction t with
    | zero => rfl
    | succ n ih => rw [← hne n ht, ih (by omega)]
  have hsub : (Finset.range ℓ).image f ⊆ {f 0} := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_singleton.2 (hconst t (Finset.mem_range.1 ht))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_singleton] at hcard
  omega

end color_dominant_powStrings_of_rainbowFree_zmod

-- The statement keeps the hypotheses `hc` (the coloring is exact) and `ha`, which the proof does
-- not use.
set_option linter.unusedVariables false in
open color_dominant_powStrings_of_rainbowFree_zmod in
/-- **Dominant colors on power-step strings modulo a prime.** Let $p$ be a prime and $k$ a natural
number, and let $c$ be a coloring of $\mathbb{Z}/p\mathbb{Z}$ with three colors that uses every
color and is rainbow-free for $x - y = z^k$: no $x, y, z \in \mathbb{Z}/p\mathbb{Z}$ with
$x - y = z^k$ have $c(x), c(y), c(z)$ pairwise distinct. Let $a \ne 0$ and $i$ be elements of
$\mathbb{Z}/p\mathbb{Z}$ and let $\ell$ be a natural number. If the elements $(i + t)a^k$ for
$0 \le t < \ell$ take exactly two colors, then one of these elements has the color $c(a)$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 9
(`integers-2024-A105-lem-9`). -/
theorem color_dominant_powStrings_of_rainbowFree_zmod (p k : ℕ) [Fact p.Prime]
    (c : ZMod p → Fin 3) (hc : Function.Surjective c)
    (hrf : ∀ x y z : ZMod p, x - y = z ^ k → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (a : ZMod p) (ha : a ≠ 0) (i : ZMod p) (ℓ : ℕ)
    (hbi : ((Finset.range ℓ).image fun t : ℕ => c ((i + t) * a ^ k)).card = 2) :
    c a ∈ (Finset.range ℓ).image fun t : ℕ => c ((i + t) * a ^ k) := by
  obtain ⟨t, ht, hne⟩ :=
    exists_succ_ne_of_one_lt_card_image (fun t : ℕ => c ((i + t) * a ^ k)) ℓ (by omega)
  -- The consecutive terms `y = (i + t) aᵏ` and `x = (i + t + 1) aᵏ` differ by `aᵏ`.
  have hsol : (i + ((t + 1 : ℕ) : ZMod p)) * a ^ k - (i + (t : ZMod p)) * a ^ k = a ^ k := by
    push_cast
    ring
  by_contra hmem
  refine hrf _ _ a hsol ⟨Ne.symm hne, fun h => hmem ?_, fun h => hmem ?_⟩
  · exact Finset.mem_image.2 ⟨t, Finset.mem_range.2 (by omega), h⟩
  · exact Finset.mem_image.2 ⟨t + 1, Finset.mem_range.2 ht, h⟩

-- The statement retains the exactness hypothesis of the source.
set_option linter.unusedVariables false in
open color_dominant_powStrings_of_rainbowFree_zmod in
/-- **The color of one dominates bichromatic strings.** Let $r$ and $k$ be natural numbers and let
$c$ be a coloring of the positive integers with $r$ colors that uses every color on some positive
integer and is rainbow-free for $x - y = z^k$: no positive integers $x, y, z$ with $x = y + z^k$
have $c(x), c(y), c(z)$ pairwise distinct. Then for every positive integer $i$ and every natural
number $\ell$, if $c$ takes exactly two colors on $i, i + 1, \dots, i + \ell - 1$, one of these
integers has the color $c(1)$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 1
(`integers-2024-A105-lem-1`). -/
theorem color_one_dominant_of_rainbowFree_powDiff (r k : ℕ) (c : ℕ → Fin r)
    (hc : ∀ j : Fin r, ∃ i : ℕ, 0 < i ∧ c i = j)
    (hrf : ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x = y + z ^ k →
      ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (i ℓ : ℕ) (hi : 0 < i) (hbi : ((Finset.Ico i (i + ℓ)).image c).card = 2) :
    c 1 ∈ (Finset.Ico i (i + ℓ)).image c := by
  have hIco : (Finset.range ℓ).image (i + ·) = Finset.Ico i (i + ℓ) := by
    simpa only [Nat.Ico_zero_eq_range, Nat.add_zero] using Finset.image_add_left_Ico 0 ℓ i
  rw [← hIco, Finset.image_image] at hbi ⊢
  obtain ⟨t, ht, hne⟩ := exists_succ_ne_of_one_lt_card_image (c ∘ (i + ·)) ℓ (by omega)
  by_contra hmem
  refine hrf (i + (t + 1)) (i + t) 1 (by omega) (by omega) Nat.one_pos
    (by simp [Nat.add_assoc]) ⟨hne.symm, fun h => hmem ?_, fun h => hmem ?_⟩
  · exact Finset.mem_image.2 ⟨t, Finset.mem_range.2 (by omega), h⟩
  · exact Finset.mem_image.2 ⟨t + 1, Finset.mem_range.2 ht, h⟩

/-- **Coprime representatives at a coprime distance.** Let $n$ be a natural number and let $c$ be a
coloring of $\mathbb{Z}/n\mathbb{Z}$ with three colors, used to color every positive integer by its
residue modulo $n$. If $i_1, i_2$ are positive integers with $\gcd(|i_1 - i_2|, n) = 1$, then there
are coprime positive integers $j_1, j_2$ with $|j_1 - j_2| = |i_1 - i_2|$ such that $j_1$ has the
color of $i_1$ and $j_2$ has the color of $i_2$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 8
(`integers-2024-A105-lem-8`). -/
theorem exists_coprime_same_colors_of_coprime_dist
    (n : ℕ) (c : ZMod n → Fin 3) (i₁ i₂ : ℕ) (hi₁ : 0 < i₁) (hi₂ : 0 < i₂)
    (hd : Nat.Coprime ((i₁ : ℤ) - i₂).natAbs n) :
    ∃ j₁ j₂ : ℕ, 0 < j₁ ∧ 0 < j₂ ∧ Nat.Coprime j₁ j₂ ∧ c j₁ = c i₁ ∧ c j₂ = c i₂ ∧
      ((j₁ : ℤ) - j₂).natAbs = ((i₁ : ℤ) - i₂).natAbs := by
  wlog hle : i₁ ≤ i₂ generalizing i₁ i₂
  · have hdist : ((i₂ : ℤ) - i₁).natAbs = ((i₁ : ℤ) - i₂).natAbs := by omega
    obtain ⟨b, a, hb, ha, hcop, h₂, h₁, hab⟩ :=
      this i₂ i₁ hi₂ hi₁ (hdist ▸ hd) (by omega)
    exact ⟨a, b, ha, hb, hcop.symm, h₁, h₂, by omega⟩
  let d := i₂ - i₁
  have hdist : ((i₁ : ℤ) - i₂).natAbs = d := by dsimp [d]; omega
  rw [hdist] at hd ⊢
  -- Choose the predecessor so that the first representative is positive even for zero moduli.
  obtain ⟨x, hx, hi⟩ := Nat.chineseRemainder hd 0 (i₁ - 1)
  have hx₁ : x + 1 ≡ i₁ [MOD n] := by
    simpa only [Nat.sub_add_cancel hi₁] using hi.add_right 1
  have hx₂ : x + 1 + d ≡ i₂ [MOD n] := by
    simpa only [d, Nat.add_sub_of_le hle] using hx₁.add_right d
  refine ⟨x + 1, x + 1 + d, Nat.succ_pos _, by omega, ?_, ?_, ?_, by omega⟩
  · rw [Nat.coprime_self_add_right, Nat.Coprime, (hx.add_right 1).gcd_eq]
    simp
  · exact congrArg c ((ZMod.natCast_eq_natCast_iff ..).2 hx₁)
  · exact congrArg c ((ZMod.natCast_eq_natCast_iff ..).2 hx₂)

namespace isCycleVertex_powMap_iff_orderOf_dvd

/-- Every nonzero element of `ZMod p` is a unit when `p` is prime. -/
private theorem isUnit_of_ne_zero {p : ℕ} [hp : Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    IsUnit a := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  rw [← ZMod.natCast_zmod_val a, ZMod.isUnit_iff_coprime]
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 fun hdvd => ha ?_)
  rw [← ZMod.val_eq_zero]
  exact Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt a)

/-- The order of a unit of `ZMod p` divides `p - 1`. -/
private theorem orderOf_dvd_sub_one {p : ℕ} [hp : Fact p.Prime] (u : (ZMod p)ˣ) :
    orderOf u ∣ p - 1 := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  rw [← Nat.totient_prime hp.out, ← ZMod.card_units_eq_totient]
  exact orderOf_dvd_card

/-- If `k` is coprime to a positive integer `n`, then `k ^ m ≡ 1 [MOD n]` for some `m ≥ 1`. -/
private theorem exists_pow_modEq_one {n k : ℕ} (hn : 0 < n) (hkn : Nat.Coprime k n) :
    ∃ m : ℕ, 1 ≤ m ∧ k ^ m ≡ 1 [MOD n] := by
  have : NeZero n := ⟨hn.ne'⟩
  refine ⟨orderOf (ZMod.unitOfCoprime k hkn), orderOf_pos _, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one, ← ZMod.coe_unitOfCoprime k hkn,
    ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]

end isCycleVertex_powMap_iff_orderOf_dvd

-- The statement keeps the hypothesis `hp` (the prime is odd) of the source, which the proof does
-- not use.
set_option linter.unusedVariables false in
open isCycleVertex_powMap_iff_orderOf_dvd in
/-- **Cycle vertices of the $k$-th power map modulo $p$.** Let $p$ be an odd prime, $k$ a natural
number, and $t$ the largest divisor of $p - 1$ that is coprime to $k$. A nonzero
$a \in \mathbb{Z}/p\mathbb{Z}$ lies on a cycle of the map $x \mapsto x^k$, that is,
$a^{k^m} = a$ for some $m \ge 1$, if and only if the multiplicative order of $a$ divides $t$.

Only this characterization is stated; the source's further claims (there are $t + 1$ cycle
vertices, and two components exactly when $t = 1$) are not.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Theorem 6 (after
Lucheta, Miller and Reiter)
(`integers-2024-A105-thm-6`). -/
theorem isCycleVertex_powMap_iff_orderOf_dvd (p k : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (t : ℕ) (ht : t ∣ p - 1) (htk : Nat.Coprime t k)
    (htmax : ∀ s : ℕ, s ∣ p - 1 → Nat.Coprime s k → s ≤ t) (a : ZMod p) (ha : a ≠ 0) :
    (∃ m : ℕ, 1 ≤ m ∧ a ^ (k ^ m) = a) ↔ orderOf a ∣ t := by
  obtain ⟨u, rfl⟩ := isUnit_of_ne_zero ha
  have hn : 0 < orderOf u := orderOf_pos u
  -- `u ^ j = u` exactly when `j ≡ 1` modulo the order of `u`.
  have hpow (j : ℕ) : (u : ZMod p) ^ j = u ↔ j ≡ 1 [MOD orderOf u] := by
    rw [← Units.val_pow_eq_pow_val, Units.val_inj, ← pow_eq_pow_iff_modEq, pow_one]
  simp only [hpow, orderOf_units]
  constructor
  · rintro ⟨m, hm, hmod⟩
    -- A cycle makes `k` coprime to the order of `u`.
    have hnk : Nat.Coprime (orderOf u) k := by
      have h1 : Nat.Coprime (k ^ m) (orderOf u) := by
        rw [Nat.Coprime, hmod.gcd_eq, Nat.gcd_one_left]
      exact ((Nat.coprime_pow_left_iff hm k _).1 h1).symm
    have ht0 : 0 < t :=
      Nat.pos_of_dvd_of_pos ht (by have := (Fact.out : p.Prime).two_le; omega)
    -- `lcm (orderOf u) t` divides `p - 1` and is coprime to `k`, so it is at most `t`.
    have hl : Nat.lcm (orderOf u) t = t := by
      refine le_antisymm (htmax _ (Nat.lcm_dvd (orderOf_dvd_sub_one u) ht) ?_)
        (Nat.le_of_dvd (Nat.lcm_pos hn ht0) (Nat.dvd_lcm_right _ _))
      exact Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul _ _) (Nat.Coprime.mul_left hnk htk)
    exact hl ▸ Nat.dvd_lcm_left _ _
  · intro hdvd
    exact exists_pow_modEq_one hn (Nat.Coprime.coprime_dvd_left hdvd htk).symm

/-- **Large multiples of the gcd are nonnegative combinations.** Let $i$ and $j$ be positive
integers. There is an $n_0$ such that every integer $m > n_0$ divisible by $\gcd(i, j)$ can be
written as $m = ui + vj$ with nonnegative integers $u$ and $v$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Theorem 2
(`integers-2024-A105-thm-2`). -/
theorem exists_forall_gcd_dvd_eq_add_mul (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    ∃ n₀ : ℕ, ∀ m : ℕ, n₀ < m → Nat.gcd i j ∣ m → ∃ u v : ℕ, m = u * i + v * j := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  refine ⟨(a * b).pred, fun m hm hdvd ↦ ?_⟩
  obtain ⟨u, v, huv⟩ :=
    Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le a.succ b.succ m hdvd (Nat.le_of_pred_lt hm)
  exact ⟨u, v, huv.symm⟩

end MetaMathlibExt
