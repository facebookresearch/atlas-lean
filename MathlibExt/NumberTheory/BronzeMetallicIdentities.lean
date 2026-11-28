/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Metallic identities for the bronze numbers

Multiplication by the bronze ratio or its complementary Beatty ratio gives six identities
for the bronze numbers and their two companion sequences.

## References

* Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial Games with
  Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, pp. 1–38, Section 4 and Proposition 3.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Bronze Lucas parameters.** The bronze Lucas parameters are the Lucas sequence parameters
$(P, Q) = (3, -1)$. The Lucas sequence $U(3, -1)$ is the sequence of bronze numbers $B_n$, with
$B_0 = 0$, $B_1 = 1$ and $B_{n+2} = 3B_{n+1} + B_n$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4 (bronze numbers). -/
def bronzeLucasParams : LucasSequenceParams where
  p := 3
  q := -1
  q_ne_zero := by decide

/-- The second Lucas parameter of the bronze sequence is $-1$. -/
theorem bronzeLucasParams_q : bronzeLucasParams.q = -1 := rfl

/-- **Recurrence of the bronze numbers.** Let $B_n$ be the bronze numbers, the terms of the Lucas
sequence $U(3, -1)$. For every natural number $n$, $B_{n+2} = 3B_{n+1} + B_n$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4 (bronze numbers). -/
theorem lucasU_bronzeLucasParams_add_two (n : ℕ) :
    lucasU bronzeLucasParams (n + 2) =
      3 * lucasU bronzeLucasParams (n + 1) + lucasU bronzeLucasParams n := by
  simp [lucasU, bronzeLucasParams]

/-- **The first bronze numbers.** Let $B_n$ be the bronze numbers, the terms of the Lucas sequence
$U(3, -1)$. Then $B_0, B_1, B_2, B_3, B_4, B_5$ are $0, 1, 3, 10, 33, 109$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4 (bronze numbers). -/
theorem lucasU_bronzeLucasParams_values :
    (List.range 6).map (lucasU bronzeLucasParams) = [0, 1, 3, 10, 33, 109] := by
  decide

/-- **Companion bronze numbers of the first type.** Let $B_n$ denote the bronze numbers, the
Lucas sequence $U(3, -1)$: $B_0 = 0$, $B_1 = 1$ and $B_{n+2} = 3B_{n+1} + B_n$. For every
natural number $n$, the $n$-th companion bronze number of the first type is the integer
$C_n = B_{n+1} - 2B_n$.

Thus $C_0 = C_1 = 1$, $C_{n+2} = 3C_{n+1} + C_n$, and $C_n = B_n + B_{n-1}$ for $n \ge 1$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4 (companion bronze
numbers of the first type). -/
def bronzeCompanionFirst (n : ℕ) : ℤ :=
  lucasU bronzeLucasParams (n + 1) - 2 * lucasU bronzeLucasParams n

/-- **Companion bronze numbers of the second type.** Let $B_n$ denote the bronze numbers, the
Lucas sequence $U(3, -1)$: $B_0 = 0$, $B_1 = 1$ and $B_{n+2} = 3B_{n+1} + B_n$. For every
natural number $n$, the $n$-th companion bronze number of the second type is the integer
$D_n = B_{n+1} - B_n$.

Thus $D_0 = 1$, $D_1 = 2$, $D_{n+2} = 3D_{n+1} + D_n$, and $D_n = 2B_n + B_{n-1}$ for $n \ge 1$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4 (companion bronze
numbers of the second type). -/
def bronzeCompanionSecond (n : ℕ) : ℤ :=
  lucasU bronzeLucasParams (n + 1) - lucasU bronzeLucasParams n

/-- **First companion bronze numbers at a successor index.** For every natural number $n$,
$C_{n+1} = B_{n+1} + B_n$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4. -/
theorem bronzeCompanionFirst_succ (n : ℕ) :
    bronzeCompanionFirst (n + 1) =
      lucasU bronzeLucasParams (n + 1) + lucasU bronzeLucasParams n := by
  simp only [bronzeCompanionFirst, lucasU_bronzeLucasParams_add_two n]
  ring

/-- **Second companion bronze numbers at a successor index.** For every natural number $n$,
$D_{n+1} = 2B_{n+1} + B_n$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4. -/
theorem bronzeCompanionSecond_succ (n : ℕ) :
    bronzeCompanionSecond (n + 1) =
      2 * lucasU bronzeLucasParams (n + 1) + lucasU bronzeLucasParams n := by
  simp only [bronzeCompanionSecond, lucasU_bronzeLucasParams_add_two n]
  ring

/-- **Recurrence for the companion bronze numbers of the first type.** For every natural number
$n$, the companion bronze numbers $C_n$ of the first type satisfy $C_{n+2} = 3C_{n+1} + C_n$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4. -/
theorem bronzeCompanionFirst_add_two (n : ℕ) :
    bronzeCompanionFirst (n + 2) = 3 * bronzeCompanionFirst (n + 1) + bronzeCompanionFirst n := by
  simp only [bronzeCompanionFirst, lucasU_bronzeLucasParams_add_two (n + 1),
    lucasU_bronzeLucasParams_add_two n]
  ring

/-- **Recurrence for the companion bronze numbers of the second type.** For every natural number
$n$, the companion bronze numbers $D_n$ of the second type satisfy $D_{n+2} = 3D_{n+1} + D_n$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4. -/
theorem bronzeCompanionSecond_add_two (n : ℕ) :
    bronzeCompanionSecond (n + 2) =
      3 * bronzeCompanionSecond (n + 1) + bronzeCompanionSecond n := by
  simp only [bronzeCompanionSecond, lucasU_bronzeLucasParams_add_two (n + 1),
    lucasU_bronzeLucasParams_add_two n]
  ring

/-- **Initial companion bronze numbers.** The companion bronze numbers $C_n$ of the first type
satisfy $(C_0, C_1, C_2, C_3, C_4) = (1, 1, 4, 13, 43)$, and the companion bronze numbers $D_n$
of the second type satisfy $(D_0, D_1, D_2, D_3, D_4) = (1, 2, 7, 23, 76)$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Section 4. -/
theorem bronzeCompanion_values :
    (List.range 5).map bronzeCompanionFirst = [1, 1, 4, 13, 43] ∧
      (List.range 5).map bronzeCompanionSecond = [1, 2, 7, 23, 76] := by
  decide

private theorem bronze_mul_metallic_identities.bronze_error (n : ℕ) :
    (lucasU bronzeLucasParams (n + 1) : ℝ) -
        lucasU bronzeLucasParams n * ((3 + Real.sqrt 13) / 2) =
      (-((Real.sqrt 13 - 3) / 2)) ^ n := by
  induction n with
  | zero => norm_num [lucasU]
  | succ n ih =>
    rw [pow_succ, ← ih, lucasU_bronzeLucasParams_add_two]
    push_cast
    linear_combination
      -((lucasU bronzeLucasParams n : ℝ) / 4) * Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)

/-- **Metallic identities for the bronze numbers.** Let $\alpha = (3 + \sqrt{13})/2$,
$\beta = (5 + \sqrt{13})/6$ and $\gamma = (\sqrt{13} - 3)/2$, let $B_n$ be the bronze numbers,
and let $C_n$ and $D_n$ be the companion bronze numbers of the first and second type. For every
natural number $k$, the following hold in $\mathbb{R}$:
(1) $B_{2k+1}\alpha = B_{2k+2} + \gamma^{2k+1}$;
(2) $C_{2k}\alpha = C_{2k+1} + \frac{13 + \sqrt{13}}{2\sqrt{13}}\gamma^{2k}$;
(3) $D_{2k}\alpha = D_{2k+1} + \frac{13 - \sqrt{13}}{2\sqrt{13}}\gamma^{2k}$;
(4) $3B_{2k+1}\beta = C_{2k+2} + \frac{13 - 3\sqrt{13}}{2\sqrt{13}}\gamma^{2k}$;
(5) $(B_{2k+1} + C_{2k+2})\beta = D_{2k+2} + \frac{65 - 17\sqrt{13}}{6\sqrt{13}}\gamma^{2k}$;
(6) $D_{2k}\beta = B_{2k+1} + \frac{13 - \sqrt{13}}{6\sqrt{13}}\gamma^{2k}$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Proposition 3. -/
theorem bronze_mul_metallic_identities (k : ℕ) :
    let α : ℝ := (3 + Real.sqrt 13) / 2
    let β : ℝ := (5 + Real.sqrt 13) / 6
    let γ : ℝ := (Real.sqrt 13 - 3) / 2
    (lucasU bronzeLucasParams (2 * k + 1) : ℝ) * α =
        lucasU bronzeLucasParams (2 * k + 2) + γ ^ (2 * k + 1) ∧
      (bronzeCompanionFirst (2 * k) : ℝ) * α = bronzeCompanionFirst (2 * k + 1) +
        (13 + Real.sqrt 13) / (2 * Real.sqrt 13) * γ ^ (2 * k) ∧
      (bronzeCompanionSecond (2 * k) : ℝ) * α = bronzeCompanionSecond (2 * k + 1) +
        (13 - Real.sqrt 13) / (2 * Real.sqrt 13) * γ ^ (2 * k) ∧
      (3 * lucasU bronzeLucasParams (2 * k + 1) : ℝ) * β = bronzeCompanionFirst (2 * k + 2) +
        (13 - 3 * Real.sqrt 13) / (2 * Real.sqrt 13) * γ ^ (2 * k) ∧
      ((lucasU bronzeLucasParams (2 * k + 1) + bronzeCompanionFirst (2 * k + 2) : ℤ) : ℝ) * β =
        bronzeCompanionSecond (2 * k + 2) +
          (65 - 17 * Real.sqrt 13) / (6 * Real.sqrt 13) * γ ^ (2 * k) ∧
      (bronzeCompanionSecond (2 * k) : ℝ) * β = lucasU bronzeLucasParams (2 * k + 1) +
        (13 - Real.sqrt 13) / (6 * Real.sqrt 13) * γ ^ (2 * k) := by
  have h := bronze_mul_metallic_identities.bronze_error (2 * k)
  rw [(even_two_mul k).neg_pow] at h
  -- Express every sequence term using the adjacent pair at 2k and 2k + 1.
  dsimp only
  rw [pow_succ]
  simp only [bronzeCompanionFirst, bronzeCompanionSecond,
    lucasU_bronzeLucasParams_add_two (2 * k + 1), lucasU_bronzeLucasParams_add_two (2 * k)]
  push_cast
  -- Substituting the even-index error leaves six polynomial identities in √13.
  rw [sub_eq_iff_eq_add.mp h]
  generalize ((Real.sqrt 13 - 3) / 2) ^ (2 * k) = e
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
  have hs₀ : Real.sqrt 13 ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> grind only

end

end MetaMathlibExt
