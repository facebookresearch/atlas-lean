/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

section

open scoped BigOperators

private theorem frisch_sum_succ (n b c : ℕ) :
    ∑ k ∈ Finset.range (n + 1 + 1),
      (-1 : ℚ) ^ k * (Nat.choose (n + 1) k : ℚ) * (Nat.choose (b + k) c : ℚ)⁻¹ =
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * (Nat.choose (b + k) c : ℚ)⁻¹) -
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * (Nat.choose (b + 1 + k) c : ℚ)⁻¹) := by
  have pascal : ∀ k : ℕ, (-1 : ℚ) ^ (k + 1) * (Nat.choose (n + 1) (k + 1) : ℚ) *
      (Nat.choose (b + (k + 1)) c : ℚ)⁻¹ =
      ((-1 : ℚ) ^ (k + 1) * (Nat.choose n k : ℚ) * (Nat.choose (b + 1 + k) c : ℚ)⁻¹) +
      ((-1 : ℚ) ^ (k + 1) * (Nat.choose n (k + 1) : ℚ) *
        (Nat.choose (b + (k + 1)) c : ℚ)⁻¹) := by
    intro k
    have hb : b + (k + 1) = b + 1 + k := by omega
    rw [Nat.choose_succ_succ, hb]
    push_cast
    ring
  have hneg : ∀ k : ℕ, (-1 : ℚ) ^ (k + 1) * (Nat.choose n k : ℚ) *
      (Nat.choose (b + 1 + k) c : ℚ)⁻¹ =
      -((-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * (Nat.choose (b + 1 + k) c : ℚ)⁻¹) := by
    intro k
    rw [pow_succ]
    ring
  have hvanish : (-1 : ℚ) ^ (n + 1) * (Nat.choose n (n + 1) : ℚ) *
      (Nat.choose (b + (n + 1)) c : ℚ)⁻¹ = 0 := by
    rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n), Nat.cast_zero, mul_zero, zero_mul]
  have hg0 : (-1 : ℚ) ^ 0 * (Nat.choose (n + 1) 0 : ℚ) * (Nat.choose (b + 0) c : ℚ)⁻¹ =
      (-1 : ℚ) ^ 0 * (Nat.choose n 0 : ℚ) * (Nat.choose (b + 0) c : ℚ)⁻¹ := by
    simp
  have hLg : ∑ k ∈ Finset.range (n + 1 + 1),
      (-1 : ℚ) ^ k * (Nat.choose (n + 1) k : ℚ) * (Nat.choose (b + k) c : ℚ)⁻¹ =
      (∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (k + 1) * (Nat.choose (n + 1) (k + 1) : ℚ) *
        (Nat.choose (b + (k + 1)) c : ℚ)⁻¹) +
      ((-1 : ℚ) ^ 0 * (Nat.choose (n + 1) 0 : ℚ) * (Nat.choose (b + 0) c : ℚ)⁻¹) :=
    Finset.sum_range_succ' _ _
  have hsplit : (∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (k + 1) * (Nat.choose (n + 1) (k + 1) : ℚ) *
        (Nat.choose (b + (k + 1)) c : ℚ)⁻¹) =
      (∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (k + 1) * (Nat.choose n k : ℚ) * (Nat.choose (b + 1 + k) c : ℚ)⁻¹) +
      (∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (k + 1) * (Nat.choose n (k + 1) : ℚ) *
        (Nat.choose (b + (k + 1)) c : ℚ)⁻¹) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => pascal k)
  have e1 : (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ (k + 1) * (Nat.choose n k : ℚ) * (Nat.choose (b + 1 + k) c : ℚ)⁻¹) =
      -(∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * (Nat.choose (b + 1 + k) c : ℚ)⁻¹) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun k _ => hneg k)
  have hss : ∑ k ∈ Finset.range (n + 1 + 1),
      (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * (Nat.choose (b + k) c : ℚ)⁻¹ =
      (∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (k + 1) * (Nat.choose n (k + 1) : ℚ) *
        (Nat.choose (b + (k + 1)) c : ℚ)⁻¹) +
      ((-1 : ℚ) ^ 0 * (Nat.choose n 0 : ℚ) * (Nat.choose (b + 0) c : ℚ)⁻¹) :=
    Finset.sum_range_succ' _ _
  have hlast : ∑ k ∈ Finset.range (n + 1 + 1),
      (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * (Nat.choose (b + k) c : ℚ)⁻¹ =
      (∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * (Nat.choose (b + k) c : ℚ)⁻¹) +
      ((-1 : ℚ) ^ (n + 1) * (Nat.choose n (n + 1) : ℚ) *
        (Nat.choose (b + (n + 1)) c : ℚ)⁻¹) :=
    Finset.sum_range_succ _ _
  have e2 : (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ (k + 1) * (Nat.choose n (k + 1) : ℚ) *
      (Nat.choose (b + (k + 1)) c : ℚ)⁻¹) =
      (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * (Nat.choose (b + k) c : ℚ)⁻¹) -
      ((-1 : ℚ) ^ 0 * (Nat.choose n 0 : ℚ) * (Nat.choose (b + 0) c : ℚ)⁻¹) := by
    rw [hvanish, add_zero] at hlast
    linear_combination hlast - hss
  rw [hLg, hsplit, e1, e2, hg0]
  ring

private theorem frisch_step (m d : ℕ) (hd : d ≤ m) :
    (Nat.choose m d : ℚ)⁻¹ - (Nat.choose (m + 1) (d + 1) : ℚ)⁻¹ =
    ((m - d : ℕ) : ℚ) / (((m - d : ℕ) : ℚ) + 1) * (Nat.choose (m + 1) d : ℚ)⁻¹ := by
  have h1 : d + 1 ≤ m + 1 := by omega
  have h2 : d ≤ m + 1 := by omega
  have hmd1 : m + 1 - (d + 1) = m - d := by omega
  have hmd2 : m + 1 - d = (m - d) + 1 := by omega
  have hF0 : (Nat.factorial m : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hF1 : (Nat.factorial (m + 1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (m + 1)
  have ha : (Nat.choose m d : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hd).ne'
  have hb : (Nat.choose (m + 1) (d + 1) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos h1).ne'
  have hc2 : (Nat.choose (m + 1) d : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos h2).ne'
  have key0 := Nat.choose_mul_factorial_mul_factorial hd
  have key1 := Nat.choose_mul_factorial_mul_factorial h1
  have key2 := Nat.choose_mul_factorial_mul_factorial h2
  rw [hmd1] at key1
  rw [hmd2] at key2
  have q0 : (Nat.choose m d : ℚ) * (Nat.factorial d : ℚ) * (Nat.factorial (m - d) : ℚ) =
      (Nat.factorial m : ℚ) := by
    exact_mod_cast key0
  have q1 : (Nat.choose (m + 1) (d + 1) : ℚ) * (Nat.factorial (d + 1) : ℚ) *
      (Nat.factorial (m - d) : ℚ) = (Nat.factorial (m + 1) : ℚ) := by
    exact_mod_cast key1
  have q2 : (Nat.choose (m + 1) d : ℚ) * (Nat.factorial d : ℚ) *
      (Nat.factorial ((m - d) + 1) : ℚ) = (Nat.factorial (m + 1) : ℚ) := by
    exact_mod_cast key2
  have eFd : (Nat.factorial (d + 1) : ℚ) = ((d : ℚ) + 1) * (Nat.factorial d : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have eFmd : (Nat.factorial ((m - d) + 1) : ℚ) =
      ((((m - d : ℕ)) : ℚ) + 1) * (Nat.factorial (m - d) : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hw : ((m : ℕ) : ℚ) = ((((m - d : ℕ))) : ℚ) + (((d : ℕ)) : ℚ) := by
    rw [Nat.cast_sub hd]; ring
  have eFm0 : (Nat.factorial (m + 1) : ℚ) = ((((m : ℕ)) : ℚ) + 1) *
      (Nat.factorial m : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hw] at eFm0
  have ia : (Nat.choose m d : ℚ)⁻¹ =
      ((Nat.factorial d : ℚ) * (Nat.factorial (m - d) : ℚ)) / (Nat.factorial m : ℚ) := by
    have q0' : (Nat.choose m d : ℚ) *
        (((Nat.factorial d : ℚ) * (Nat.factorial (m - d) : ℚ))) =
        (Nat.factorial m : ℚ) := by
      rw [← mul_assoc]; exact q0
    rw [eq_div_iff hF0, ← q0', inv_mul_cancel_left₀ ha]
  have ib : (Nat.choose (m + 1) (d + 1) : ℚ)⁻¹ =
      ((Nat.factorial (d + 1) : ℚ) * (Nat.factorial (m - d) : ℚ)) /
      (Nat.factorial (m + 1) : ℚ) := by
    have q1' : (Nat.choose (m + 1) (d + 1) : ℚ) *
        (((Nat.factorial (d + 1) : ℚ) * (Nat.factorial (m - d) : ℚ))) =
        (Nat.factorial (m + 1) : ℚ) := by
      rw [← mul_assoc]; exact q1
    rw [eq_div_iff hF1, ← q1', inv_mul_cancel_left₀ hb]
  have ic : (Nat.choose (m + 1) d : ℚ)⁻¹ =
      ((Nat.factorial d : ℚ) * (Nat.factorial ((m - d) + 1) : ℚ)) /
      (Nat.factorial (m + 1) : ℚ) := by
    have q2' : (Nat.choose (m + 1) d : ℚ) *
        (((Nat.factorial d : ℚ) * (Nat.factorial ((m - d) + 1) : ℚ))) =
        (Nat.factorial (m + 1) : ℚ) := by
      rw [← mul_assoc]; exact q2
    rw [eq_div_iff hF1, ← q2', inv_mul_cancel_left₀ hc2]
  rw [ia, ib, ic, eFd, eFmd, eFm0]
  have hu1 : ((((m - d : ℕ))) : ℚ) + 1 ≠ 0 := ne_of_gt (by positivity)
  have huv1 : ((((m - d : ℕ))) : ℚ) + ((((d : ℕ))) : ℚ) + 1 ≠ 0 :=
    ne_of_gt (by positivity)
  have hprod : ((((((m - d : ℕ))) : ℚ) + ((((d : ℕ))) : ℚ) + 1) *
      (Nat.factorial m : ℚ)) ≠ 0 :=
    mul_ne_zero huv1 hF0
  field_simp
  ring

/-- **Frisch's alternating reciprocal-binomial identity.** For natural numbers $n$, $b$ and $c$
with $0 < c \le b$, the rational numbers
$\sum_{k=0}^{n} (-1)^k \binom{n}{k} \binom{b+k}{c}^{-1}$ and
$\frac{c}{n+c} \binom{n+b}{b-c}^{-1}$ are equal.

Source: H. W. Gould and Jocelyn Quaintance, "On the Binomial Identities of Frisch and
Klamkin," Journal of Integer Sequences 19 (2016), who attribute the identity to Ragnar Frisch,
"Sur les semi-invariants et moments employés dans l'étude des distributions statistiques"
(1926); lines 92–95 of <https://cs.uwaterloo.ca/journals/JIS/VOL19/Gould/gould8.tex> (file
SHA-256 `b38bfe08323efbec75bc33f6da717129832836c79d90d8e431401ac89cdbdca8`, span SHA-256
`691e02314c5d82e730769faea9e6ec288c4c72eea77ffc63d27318a55e1bdded`). The inverse Frisch
identity, Abel's infinite variant and the Klamkin identities are not included. Proves the
former `WantedExt` entry `frisch_alternating_reciprocal_binomial`.
-/
theorem frisch_alternating_reciprocal_binomial
    (n b c : ℕ) (hc : 0 < c) (hcb : c ≤ b) :
    ∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) * (Nat.choose (b + k) c : ℚ)⁻¹ =
      (c : ℚ) / (n + c) * (Nat.choose (n + b) (b - c) : ℚ)⁻¹ := by
  induction n generalizing b with
  | zero =>
    simp only [Finset.sum_range_one, pow_zero, Nat.choose_self, Nat.cast_one,
      Nat.add_zero, one_mul, Nat.cast_zero, zero_add]
    have hcs : Nat.choose b (b - c) = Nat.choose b c := Nat.choose_symm hcb
    rw [hcs]
    have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
    rw [div_self hcQ, one_mul]
  | succ n ih =>
    rw [frisch_sum_succ n b c, ih b hcb, ih (b + 1) (by omega)]
    have e1 : n + (b + 1) = (n + b) + 1 := by omega
    have e2 : (b + 1) - c = (b - c) + 1 := by omega
    have e3 : n + 1 + b = (n + b) + 1 := by omega
    rw [e1, e2, e3]
    have hstep := frisch_step (n + b) (b - c) (by omega)
    have e4 : (n + b) - (b - c) = n + c := by omega
    rw [e4] at hstep
    have e4Q : ((((n + c : ℕ))) : ℚ) = ((n : ℚ) + (c : ℚ)) := by push_cast; ring
    rw [e4Q] at hstep
    have e5Q : (((n + 1 : ℕ)) : ℚ) + ((c : ℕ) : ℚ) =
        ((((n : ℕ)) : ℚ) + (((c : ℕ)) : ℚ)) + 1 := by push_cast; ring
    rw [e5Q]
    have hncQ : ((n : ℚ) + (c : ℚ)) ≠ 0 := by
      have h : n + c ≠ 0 := by omega
      exact_mod_cast h
    have hu1 : (((n : ℚ) + (c : ℚ)) + 1) ≠ 0 := ne_of_gt (by positivity)
    rw [← mul_sub, hstep]
    field_simp

end

end MetaMathlibExt
