/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Normalization identities for finite continued fractions

A finite continued fraction with integer entries is evaluated from the right in ℚ.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Value of a finite continued fraction.** For a finite list $a_0, a_1, \dots, a_t$ of integers
(possibly zero or negative), the value $[a_0; a_1, \dots, a_t]$ is the rational number
$a_0 + 1/(a_1 + 1/(\cdots + 1/a_t))$, computed from the right: the empty list has value $0$, and
the list $a_0, a_1, \dots, a_t$ has value $a_0 + v^{-1}$, where $v$ is the value of the list
$a_1, \dots, a_t$. In particular $[a] = a + 0^{-1} = a$; here and at any vanishing intermediate
denominator, $0^{-1}$ is taken to be $0$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13 (bracket notation). -/
public def finiteContFrac (l : List ℤ) : ℚ :=
  l.foldr (fun (a : ℤ) (x : ℚ) => (a : ℚ) + x⁻¹) 0

/-- **Recursion for finite continued fractions.** For every integer $a$ and all integers
$l_1, \dots, l_n$ with $n \ge 0$, $[a; l_1, \dots, l_n] = a + [l_1; l_2, \dots, l_n]^{-1}$, where
the empty continued fraction (the case $n = 0$) has value $0$ and $0^{-1}$ is taken to be $0$
whenever $[l_1; l_2, \dots, l_n] = 0$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13 (bracket notation). -/
public theorem finiteContFrac_cons (a : ℤ) (l : List ℤ) :
    finiteContFrac (a :: l) = a + (finiteContFrac l)⁻¹ := rfl

/-- **Continued fraction of length one.** For every integer $a$, the finite continued fraction
$[a]$ has value $a$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13 (bracket notation). -/
public theorem finiteContFrac_singleton (a : ℤ) : finiteContFrac [a] = a := by
  simp [finiteContFrac]

/-- **The continued fraction $[1; 2, 2]$.** The finite continued fraction $[1; 2, 2]$ has value
$7/5$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13 (bracket notation). -/
public theorem finiteContFrac_one_two_two : finiteContFrac [1, 2, 2] = 7 / 5 := by
  norm_num [finiteContFrac]

/-- **A zero partial quotient merges its neighbours.** For all integers $a$ and $b$ and all finite
lists of integers $u_1, \dots, u_m$ and $v_1, \dots, v_n$ ($m, n \ge 0$), the finite continued
fractions satisfy $[u_1, \dots, u_m, a, 0, b, v_1, \dots, v_n] =
[u_1, \dots, u_m, a + b, v_1, \dots, v_n]$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13, equation (`eq:normzero`)
(`jis-2026-26.3.6-lem-13`). -/
public theorem finiteContFrac_zero_merge (l s : List ℤ) (a b : ℤ) :
    finiteContFrac (l ++ a :: 0 :: b :: s) = finiteContFrac (l ++ (a + b) :: s) := by
  induction l with
  | nil => simp only [List.nil_append, finiteContFrac_cons, Int.cast_zero, zero_add, inv_inv,
      Int.cast_add, add_assoc]
  | cons c l ih => simp only [List.cons_append, finiteContFrac_cons, ih]

namespace finiteContFrac_neg_block

/-- **Negating every entry negates the value.** For every finite list of integers
$s_1, \dots, s_n$ ($n \ge 0$), the finite continued fractions satisfy
$[-s_1; -s_2, \dots, -s_n] = -[s_1; s_2, \dots, s_n]$. Here the brackets denote `finiteContFrac`,
evaluated from the right, with the empty list valued $0$ and with $0^{-1} = 0$ whenever an
intermediate value is zero: the ordinary $[1; 0]$ is undefined, but its value here is $1$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13 (bracket notation). -/
public theorem map_neg (s : List ℤ) :
    finiteContFrac (s.map (fun b => -b)) = -finiteContFrac s := by
  induction s with
  | nil => simp [finiteContFrac]
  | cons b s ih => simp [finiteContFrac_cons, ih, add_comm]

/-- **Positive entries give a positive value.** For every nonempty finite list of integers
$s_1, \dots, s_n$ ($n \ge 1$) with $s_i \ge 1$ for every $i$, the finite continued fraction
$[s_1; s_2, \dots, s_n]$ is positive.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13 (bracket notation). -/
public theorem pos (s : List ℤ) (hs : ∀ b ∈ s, 1 ≤ b) (hne : s ≠ []) :
    0 < finiteContFrac s := by
  induction s with
  | nil => contradiction
  | cons b s ih =>
    have hb : (0 : ℚ) < b := by exact_mod_cast (show 0 < b from hs b (by simp))
    rcases eq_or_ne s [] with rfl | h
    · simpa only [finiteContFrac_singleton] using hb
    · exact add_pos hb (inv_pos.mpr (ih (fun c hc => hs c (List.mem_cons_of_mem _ hc)) h))

end finiteContFrac_neg_block

/-- **Normalizing a negated block.** Let $x \ge 0$ be an integer, let $t \ge 2$ and let
$a_1, \dots, a_t$ be integers with $a_i \ge 1$ for every $i$. Then for every finite list of
integers $b_1, \dots, b_m$ ($m \ge 0$), the finite continued fractions satisfy
$[b_1, \dots, b_m, x, -a_t, -a_{t-1}, \dots, -a_1] =
[b_1, \dots, b_m, x - 1, 1, a_t - 1, a_{t-1}, \dots, a_1]$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13, equation (`eq:normnegblock`)
(`jis-2026-26.3.6-lem-13`). -/
public theorem finiteContFrac_neg_block (l : List ℤ) (x : ℕ) (a : List ℤ) (aₜ : ℤ)
    (ha : ∀ b ∈ a, 1 ≤ b) (ha_ne : a ≠ []) (haₜ : 1 ≤ aₜ) :
    finiteContFrac (l ++ (x : ℤ) :: -aₜ :: (a.map (fun b => -b)).reverse) =
      finiteContFrac (l ++ ((x : ℤ) - 1) :: 1 :: (aₜ - 1) :: a.reverse) := by
  induction l with
  | cons b l ih => simp only [List.cons_append, finiteContFrac_cons, ih]
  | nil =>
    have hv : 0 < finiteContFrac a.reverse :=
      finiteContFrac_neg_block.pos _ (fun b hb => ha b (by simpa using hb)) (by simpa using ha_ne)
    let c : ℚ := (aₜ - 1 : ℚ) + (finiteContFrac a.reverse)⁻¹
    have ht : (1 : ℚ) ≤ aₜ := by exact_mod_cast haₜ
    have hc : 0 < c := add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht) (inv_pos.mpr hv)
    have hden : -(aₜ : ℚ) + -(finiteContFrac a.reverse)⁻¹ = -(c + 1) := by
      dsimp [c]
      ring
    simp only [List.nil_append, ← List.map_reverse, finiteContFrac_cons,
      finiteContFrac_neg_block.map_neg, Int.cast_neg, inv_neg, Int.cast_sub, Int.cast_one, hden]
    change (x : ℚ) + -(c + 1)⁻¹ = (x - 1 : ℚ) + (1 + c⁻¹)⁻¹
    field_simp
    ring

end

end MetaMathlibExt
